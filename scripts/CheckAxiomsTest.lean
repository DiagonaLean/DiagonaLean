import DiagonaLean

/-! Tests of the axiom check (`DiagonaLean.Synthetic.AxiomCheck`), run by CI: an `axiom`, `sorry`,
`native_decide`, the allowance for `sorry`, and a declaration that builds on an allowed `sorry`.
The attacks of 2026-11-25 are the first cases: an axiom registered as `HaltHardFact`, and one
stated through `halt_results`. -/

open Lean DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.AxiomCheck

/-- A computable problem: a proof that it is undecidable is false. -/
def IsOne (n : ℕ) : Prop := n = 1

namespace Clean

theorem ok : IsOne 1 := rfl

end Clean

namespace ViaRegistry

axiom fakeHard : HaltHard IsOne

instance : HaltHardFact IsOne := ⟨fakeHard⟩

theorem result : ¬ ComputablePred IsOne := by
  hard_reduce_from IsOne with (fun n : ℕ => n)
  · exact hp
  · exact hq

end ViaRegistry

namespace ViaHaltResults

axiom fakeRed : HaltReduction IsOne

halt_results IsOne from fakeRed

end ViaHaltResults

namespace WithSorry

set_option warn.sorry false in
theorem wip : IsOne 2 := sorry

/-- Builds on `wip`. -/
theorem user : ∃ n, IsOne n ∧ n ≠ 1 := ⟨2, wip, by decide⟩

end WithSorry

namespace WithNativeDecide

theorem nd : 2 + 2 = 4 := by native_decide

end WithNativeDecide

/-- Runs the check over the declarations of this file whose names start with `pre`, with
`sorryAx` allowed for the names in `wip`. -/
def runOn (pre : Name) (wip : List Name := []) : CoreM Unit := do
  let env ← getEnv
  let decls := (env.constants.map₂.toList.map (·.1)).filter fun c =>
    pre.isPrefixOf c && !c.isInternal
  let decls := (decls.toArray.qsort (·.toString < ·.toString)).map fun c => (c, wip.contains c)
  let out ← violations decls
  if out.isEmpty then logInfo "no violations" else logInfo ("\n".intercalate out.toList)

/-- info: no violations -/
#guard_msgs in
run_meta runOn `Clean

/--
info: `ViaRegistry.fakeHard` is an axiom
`ViaRegistry.instHaltHardFactNatIsOne` depends on `ViaRegistry.fakeHard`
`ViaRegistry.result` depends on `ViaRegistry.fakeHard`
-/
#guard_msgs in
run_meta runOn `ViaRegistry

/--
info: `ViaHaltResults.fakeRed` is an axiom
`ViaHaltResults.haltHard` depends on `ViaHaltResults.fakeRed`
`ViaHaltResults.not_computablePred` depends on `ViaHaltResults.fakeRed`
`ViaHaltResults.not_machineDecidable` depends on `ViaHaltResults.fakeRed`
-/
#guard_msgs in
run_meta runOn `ViaHaltResults

-- Without the allowance, both are reported.
/--
info: `WithSorry.user` depends on `sorryAx`
`WithSorry.wip` depends on `sorryAx`
-/
#guard_msgs in
run_meta runOn `WithSorry

-- With the allowance for `wip`, a declaration that builds on it is still reported.
/-- info: `WithSorry.user` depends on `sorryAx` -/
#guard_msgs in
run_meta runOn `WithSorry [`WithSorry.wip]

-- `native_decide` depends on `Lean.ofReduceBool` (and on an auxiliary axiom of its own).
/-- info: `WithNativeDecide.nd` depends on -/
#guard_msgs (substring := true) in
run_meta runOn `WithNativeDecide

/-- info: "DiagonaLean/Halt/Basic.lean" -/
#guard_msgs in
#eval fileOfModule `DiagonaLean.Halt.Basic
