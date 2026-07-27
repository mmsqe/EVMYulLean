import Lake
open Lake DSL System

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.31.0"

-- In-tree ABI cross-validation (now that both repos pin Lean/mathlib v4.31.0):
-- pull evm-abi-lean's computable keccak/encoder so the ERC-20 selector *values*
-- are checked inside this build instead of only out-of-process (abi_crossval.sh).
-- Pinned to a commit for reproducible verification (see the `AbiCrossval` target);
-- The pin tracks upstream main (modular Roundtrip split + the general
-- `roundtrip_wf`/`roundtrip_args_wff` capstones); sorry-free at this pin.
require «abi-lean» from git
  "https://github.com/yihuang/evm-abi-lean.git" @ "c6c2a9afa7cb725c5a515f56f8ee911a4e88feb0"

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
