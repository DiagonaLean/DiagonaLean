/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Synthetic.MetaprogramCheck

/-! # Checking that no metaprogram changes the environment

Run by CI, after the library is built, as
`lake env lean --run scripts/CheckMetaprograms.lean [ROOT]`, where `ROOT` is the repository root
and defaults to the current directory. It checks the `.lean` files under `ROOT/DiagonaLean/` and
`ROOT/DiagonaLean.lean`, parsing each in the environment of the built library; the rules and the
allowlist are in `DiagonaLean.Synthetic.MetaprogramCheck`. The fixture
`scripts/metaprogram-fixture` must be rejected, and `scripts/CheckMetaprogramsTest.lean` tests the
parser-based checks on small inputs.
-/

open Lean System DiagonaLean.Synthetic.MetaprogramCheck

/-- The files checked: the `.lean` files under `ROOT/DiagonaLean/`, and `ROOT/DiagonaLean.lean`. -/
def checkedFiles (root : FilePath) : IO (Array FilePath) := do
  let paths ← (root / "DiagonaLean").walkDir
  let files := (paths.filter (·.extension == some "lean")).qsort (·.toString < ·.toString)
  return files.push (root / "DiagonaLean.lean")

/-- Checks the repository at the root given as the first argument, prints every forbidden use and
every file that does not parse, and returns `1` if there is one. Importing the library with its
initializers, which register the syntax of Mathlib's tactics, needs `enableInitializersExecution`,
which Lean marks `unsafe`; the script is outside the library, which the check covers. -/
unsafe def main (args : List String) : IO UInt32 := do
  let root : FilePath := args.headD "."
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `DiagonaLean }] {} (loadExts := true)
  let files ← checkedFiles root
  let failures ← checkFiles env root files
  if failures == 0 then
    IO.println s!"check_metaprograms: {files.size} files checked, no forbidden uses"
    return 0
  IO.println s!"check_metaprograms: {failures} forbidden uses; see the module docstring of \
    DiagonaLean/Synthetic/MetaprogramCheck.lean"
  return 1
