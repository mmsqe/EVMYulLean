import Lake
open Lake DSL System

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.32.0"

-- In-tree ABI cross-validation (both repos pin Lean/mathlib v4.32.0): pull
-- evm-abi-lean's verified codec so the ERC-20 selector *values* and the calldata
-- *layout* are checked inside this build, not only out-of-process (abi_crossval.sh).
--
-- Pinned to an upstream commit rather than a sibling path: everything `AbiCrossval`
-- needs beyond the codec now lives HERE, under `EvmYul/Venom/AbiLean/` --
--   * `AbiLean.Hash`      -- pure-Lean keccak + the 4-byte selector (a hash is a
--                            separate primitive from the codec, and it is this repo
--                            that needs it kernel-reducible, unlike our `ffi.KEC`);
--   * `AbiLean.Args`      -- retired: a signature's arguments are definitionally the
--                            tuple of its types, which `abi_codec` compiles directly;
--   * `AbiLean.CodecEval` -- retired: `abi_codec` (upstream `EvmAbi.Compile.Meta`)
--                            compiles a codec for a fixed type, and compiled code has
--                            no recursion in it, so the kernel evaluates it directly.
-- What is taken from the library is the codec *and* its compiler: `abi_codec`
-- emits a codec specialised to one signature plus the proof that it is
-- `EvmAbi.encode` there, which is what makes a concrete encoding kernel-reducible
-- here. The dependency stays plain upstream and reproducibly pinnable, and
-- `AbiCrossval` remains 0 `native_decide`.
--
-- Pin at or after #32, where the compiler landed on main; it also fixes the
-- four names a compiled codec emits — `decode` is the *prefix* decoder and
-- `decodeStrict` the whole-buffer one, matching the runtime API.
--
-- This is #40's head rather than main: since #38 `ValBA (.uint m)` carries a
-- `Binary.UInt256` instead of a `Nat` (see `AbiCrossval.amtBin`), and only #40
-- reads words through the proof-carrying `ofBEByteArrayAt` that `binary` main
-- now exports.  Repoint at main once #40 merges.
require «abi-lean» from git
  "https://github.com/yihuang/evm-abi-lean.git" @ "69b3f96b58eeb1a06a077ee2193d3cc48d5038bb"

-- pull lean-endianness's verified BE/LE codecs (package `binary` since the
-- Endianness -> Binary rename) so EVMYulLean's hand-rolled byte codecs
-- (fromBytesBigEndian / encodeNumBytes / Mem.toBytes32 — the PUSH-literal and EVM-word
-- encoders every layout proof rests on) are cross-validated in-build against an
-- independently verified implementation (see the `EndiannessCrossval` target).
--
-- This root pin is the one `abi-lean` is built against too, so it has to satisfy
-- BOTH: `decodeBEBytesFrom` / `ByteArray.size_eq_toList_length` for its windowed
-- reads and, since #34, `encodeBEBytes` / `encodeBEU_mod_of_dvd` for its word
-- encoder; and `encodeBEMinU` / `minBytes`, which `EndiannessCrossval` needs for
-- minimal-byte PUSH literals.  That used to take a fork, upstream having only
-- the first pair — no longer: lean-binary#1 merged the minimal-length codecs
-- alongside #6's word reader, so main is the rev that has both.
require «binary» from git
  "https://github.com/yihuang/lean-binary.git" @ "5b6b371355817a352f200514e8848febd3a189a4"

package «evmyul» {
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]
}

def cloneWithCache (pkg : NPackage __name__) (dirname url : String) : FetchM (Job GitRepo) := do
  let repoDir : GitRepo := ⟨pkg.dir / dirname⟩
  if !(← repoDir.dir.pathExists) then dbg_trace s!"Cloning: {url}"; GitRepo.clone url repoDir
  return pure repoDir

target cloneSha2 pkg : GitRepo := cloneWithCache pkg "sha2" "https://github.com/amosnier/sha-2.git"

target cloneKeccak256 pkg : GitRepo := cloneWithCache pkg "keccak256" "https://github.com/brainhub/SHA3IUF.git"

def hash256CDir (hash256repo : GitRepo) : FilePath :=
  hash256repo.dir

abbrev compiler := "cc"

target ffi.o pkg : FilePath := do
  let sha2 ← (←cloneSha2.fetch).await
  let keccak256 ← (←cloneKeccak256.fetch).await
  let oFile := pkg.buildDir / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "EvmYul" / "FFI" / "ffi.c"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", sha2.dir.toString,
    "-I", keccak256.dir.toString
  ]
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildFFILib (pkg : Package) (repo : GitRepo) (fileName : String) : FetchM (Job FilePath) := do
  let srcJob ← inputTextFile $ repo.dir / fileName |>.addExtension "c"
  let oFile := pkg.buildDir / fileName |>.addExtension "o"
  let includeArgs := #["-I", repo.dir.toString]
  let weakArgs := includeArgs
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildSha256Obj (pkg : Package) (fileName : String) := do
  buildFFILib pkg (← (←cloneSha2.fetch).await).1 fileName

def buildKeccak256Obj (pkg : Package) (fileName : String) := do
  buildFFILib pkg (← (←cloneKeccak256.fetch).await).1 fileName

extern_lib libleanffi pkg := do
  -- In the static lib we include:
  -- the `sha-256` library itself
  let sha256O ← buildSha256Obj pkg "sha-256"
  let keccak256 ← buildKeccak256Obj pkg "sha3"
  -- our own `ffi.c`
  let ffiO ← ffi.o.fetch

  -- Opportunistically populate the EthereumTests git submodule (used
  -- by the conformance test suite). Resolve the path against the
  -- package directory, and run `git submodule update --init` from
  -- there too — otherwise downstream consumers building against
  -- this package as a submodule / sibling would have the command
  -- run from their own (wrong) cwd.
  let ethereumTestsDir := pkg.dir / "EthereumTests"
  if !(← ethereumTestsDir.pathExists) then
    dbg_trace s!"Cloning EthereumTests into a submodule at {ethereumTestsDir}."
    discard <| IO.Process.run
      { cmd := "git",
        args := #["submodule", "update", "--init", "EthereumTests"],
        cwd := some pkg.dir }

  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[sha256O, keccak256, ffiO]

-- No `Conform.lean` root module exists; v4.31 Lake's default glob would flag the
-- missing root as "bad imports", so glob the submodules explicitly.
lean_lib «Conform» where
  globs := #[.submodules `Conform]

@[default_target]
lean_lib «EvmYul»

-- In-tree evm-abi-lean ↔ EVMYulLean selector cross-validation. Kept as its own
-- target (not part of `EvmYul`) so the default build stays decoupled from the
-- sibling `../evm-abi-lean` checkout; `lake build AbiCrossval` runs the check.
lean_lib «AbiCrossval» where
  globs := #[.one `EvmYul.Venom.AbiCrossval]

-- In-tree lean-endianness ↔ EVMYulLean byte-codec cross-validation (∀-theorems:
-- decoder agreement, PUSH-literal roundtrip through the external decoder, and
-- Mem.toBytes32 = the verified fixed-width BE codec). `lake build EndiannessCrossval`.
lean_lib «EndiannessCrossval» where
  globs := #[.one `EvmYul.Venom.EndiannessCrossval]

-- Bridge from the native ABI dispatch front-end to the Hol codegen IR + the
-- codegen-acceptance witness (a native_decide fact). Its own target so the
-- computational axiom stays out of the core `EvmYul` audit.
lean_lib «AbiCodegen» where
  globs := #[.one `EvmYul.Venom.AbiCodegen]

@[test_driver]
lean_exe «conform» where
  root := `Conform.Main

lean_exe «yulSemanticsTests» where
  root := `EvmYul.Yul.YulSemanticsTests.Main

-- A/B harness for the byte codec; see the module doc.
lean_exe «codecBench» where
  root := `EvmYul.CodecBench

lean_exe «venom_run» where
  root := `EvmYul.Venom.Run
