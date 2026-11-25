/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import Lean

@[expose] public section

/-! # Checking the axioms of every declaration

`#check_reductions` checks the axioms of synthetic reductions only. The proved layer
(`HaltReduction`, `HaltHard`) and the theorems built on it have no such check, so an `axiom` or a
`sorry` there gives a false result, and the commands that use it by name (`HaltSource`,
`HaltHardFact`, `halt_results`) show no warning where it is used. This check covers every
declaration of the library: each may depend only on `propext`, `Classical.choice` and
`Quot.sound`. A library `axiom`, `sorry` and `native_decide` (whose proofs depend on
`Lean.ofReduceBool`) are reported.

Work in progress may use `sorry` in the files listed in `sorryAllowances`. The allowance is for
the declarations of those files only: a declaration elsewhere that uses one of them depends on
`sorryAx` and is reported. An `axiom` is never allowed, and `#check_reductions` still rejects
`sorry` in a synthetic reduction, wherever it is.

`scripts/CheckAxioms.lean` runs the check over the library in CI, and
`scripts/CheckAxiomsTest.lean` tests it.

## Main declarations

* `standardAxioms`: the axioms every declaration may depend on.
* `sorryAllowances`: the work-in-progress files whose declarations may also depend on `sorryAx`.
* `violations`: the report lines for a list of declarations.
-/

namespace DiagonaLean.Synthetic.AxiomCheck

open Lean

/-- The axioms every declaration may depend on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The files, relative to the root, whose declarations may also depend on `sorryAx`: work in
progress. Add a file with a comment saying what is missing, and remove it when the proofs are
done. -/
def sorryAllowances : List String := []

/-- The file, relative to the root, of the module `m`, such as `DiagonaLean/Halt/Basic.lean`. -/
def fileOfModule (m : Name) : String :=
  "/".intercalate (m.components.map (·.toString)) ++ ".lean"

/-- The axioms of `c` that are not allowed, given whether `sorryAx` is. -/
def badAxioms (c : Name) (sorryOk : Bool) : CoreM (Array Name) := do
  let axs : Array Name ← collectAxioms c
  return axs.filter fun a => !standardAxioms.contains a && !(sorryOk && a == ``sorryAx)

/-- The report lines for the declarations `decls`, each with whether it may depend on `sorryAx`:
one line per `axiom`, and one per declaration that depends on an axiom not allowed. -/
def violations (decls : Array (Name × Bool)) : CoreM (Array String) := do
  let mut out := #[]
  for (c, sorryOk) in decls do
    if (← getEnv).find? c matches some (.axiomInfo _) then
      out := out.push s!"`{c}` is an axiom"
      continue
    let bad ← badAxioms c sorryOk
    unless bad.isEmpty do
      let names := ", ".intercalate (bad.toList.map fun a => s!"`{a}`")
      out := out.push s!"`{c}` depends on {names}"
  return out

/-- The declarations of the environment's modules whose names start with `root`, each with whether
its file is in `sorryAllowances`. -/
def libraryDecls (env : Environment) (root : Name := `DiagonaLean) :
    Array (Name × Bool) := Id.run do
  let mut out := #[]
  for (c, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless m.getRoot == root do continue
    out := out.push (c, sorryAllowances.contains (fileOfModule m))
  return out.qsort (·.1.toString < ·.1.toString)

end DiagonaLean.Synthetic.AxiomCheck
