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
-- The library's own scope stays the codec roundtrip, so the dependency is plain
-- upstream and reproducibly pinnable. `AbiCrossval` remains 0 `native_decide`.
require «abi-lean» from git
  "https://github.com/yihuang/evm-abi-lean.git" @ "20bac1478367350f4fd42592569e3291f93cb24e"

-- pull lean-endianness's verified BE/LE codecs (package `binary` since the
-- Endianness -> Binary rename) so EVMYulLean's hand-rolled byte codecs
-- (fromBytesBigEndian / encodeNumBytes / Mem.toBytes32 — the PUSH-literal and EVM-word
-- encoders every layout proof rests on) are cross-validated in-build against an
-- independently verified implementation (see the `EndiannessCrossval` target).
--
-- This root pin is the one `abi-lean` is built against too, so it has to satisfy
-- BOTH: `decodeBEBytesFrom` / `ByteArray.size_eq_toList_length`, which
-- evm-abi-lean's windowed reads need, and `encodeBEMinU` / `minBytes`, which
-- `EndiannessCrossval` needs for minimal-byte PUSH literals.  Upstream
-- `yihuang/lean-binary` has only the first pair; this fork's `codec` branch is
-- that upstream rev plus the minimal-length codecs, so it is the rev that has
-- both.  Bumping `abi-lean` without bumping this fails inside the dependency.
require «binary» from git
  "https://github.com/mmsqe/lean-endianness.git" @ "58eede11d60410035bda452fe81b678743c3b47b"

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

lean_exe «venom_run» where
  root := `EvmYul.Venom.Run
