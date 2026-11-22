import DiagonaLean.Foundations.Computability.ReduceFrom
import DiagonaLean.MPCP.Hardness
import DiagonaLean.PCP.Primrec
import DiagonaLean.PCP.Undecidable

/-! Tests for `reduce_from`, run by CI: one case per goal shape, the link upgrade, and the errors. -/

open DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions DiagonaLean.PCP.Reduction DiagonaLean.MPCP.Reduction

/-- The alphabet of the MPCP and PCP instances built from machines. -/
abbrev A := Alpha ℕ DiagonaLean.Foundations.Computability.Normalize.Sym2

/-- PCP over the alphabet of `mpcpReducesPCP`'s target. -/
abbrev PCPA := @DiagonaLean.PCP.DecisionProblem (Ext A)

/-! ### Proved goals -/

/-- A synthetic link whose function `fun_prop` reads is upgraded with no goal left. -/
example : HaltReduction HaltCanon := by
  reduce_from (ComputableReduction.refl HaltCanon) via (SynthReduction.refl HaltCanon)

/-- MPCP to PCP: `mpcpToPcp` has no `fun_prop` lemma, so the computability of the link is left. -/
example : HaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via (mpcpReducesPCP (α := A))
  exact mpcpToPcp_primrec.to_comp

example : HaltHard PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via (mpcpReducesPCP (α := A))
  exact mpcpToPcp_primrec.to_comp

example : ¬ ComputablePred PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via (mpcpReducesPCP (α := A))
  exact mpcpToPcp_primrec.to_comp

/-- The encoding's computability is closed by `assumption`. -/
example {enc : DiagonaLean.PCP.Stack (Ext A) → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via (mpcpReducesPCP (α := A))
  exact mpcpToPcp_primrec.to_comp

/-- A proved link needs nothing more. -/
example : HaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via
    (ComputableReduction.ofSynth (mpcpReducesPCP (α := A)) mpcpToPcp_primrec.to_comp)

/-! ### Synthetic goals -/

/-- A proved source and a synthetic link give a synthetic result, through the bridge. -/
def synthFromProved : SynthHaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via (mpcpReducesPCP (α := A))

/-- Both synthetic. -/
def synthFromSynth : SynthHaltReduction PCPA := by
  reduce_from haltReducesMPCP via (mpcpReducesPCP (α := A))

/-! ### Errors -/

/--
error: reduce_from: the source `haltReducesMPCP` is a synthetic halting reduction, but the goal needs a proved one. A halting reduction is upgraded at its root, by a reduction from `HaltCanon` proved computable, not by a computability proof of the link.
-/
#guard_msgs in
example : HaltHard PCPA := by
  reduce_from haltReducesMPCP via (mpcpReducesPCP (α := A))

/--
error: reduce_from: the goal
  True
is not one of `SynthHaltReduction q`, `HaltReduction q`, `HaltHard q`, `¬ ComputablePred q`, `¬ MachineDecidable enc q`
-/
#guard_msgs in
example : True := by
  reduce_from DiagonaLean.MPCP.fromHalt via (mpcpReducesPCP (α := A))
