/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.Synthetic.AxiomCheck

/-! # Checking the axioms of every declaration

Run by CI, after the library is built, as `lake env lean --run scripts/CheckAxioms.lean`. Every
declaration of a `DiagonaLean` module may depend only on `propext`, `Classical.choice` and
`Quot.sound`, and on `sorryAx` in the files of `sorryAllowances`; the rules are in
`DiagonaLean.Synthetic.AxiomCheck`.
-/

open Lean DiagonaLean.Synthetic.AxiomCheck

/-- Checks the library, prints every declaration that depends on another axiom, and returns `1`
if there is one. Importing the library with its initializers needs `enableInitializersExecution`,
which Lean marks `unsafe`; the script is outside the library. -/
unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `DiagonaLean }] {} (loadExts := true)
  let decls := libraryDecls env
  let ctx : Core.Context := { fileName := "CheckAxioms", fileMap := default }
  let st : Core.State := { env }
  let (out, _) ← (violations decls).toIO ctx st
  for line in out do IO.println line
  if out.isEmpty then
    IO.println s!"check_axioms: {decls.size} declarations checked, only standard axioms"
    return 0
  IO.println s!"check_axioms: {out.size} declarations depend on other axioms; see the module \
    docstring of DiagonaLean/Synthetic/AxiomCheck.lean"
  return 1
