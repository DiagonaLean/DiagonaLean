import DiagonaLean.Foundations.Computability.ReduceFrom
import DiagonaLean.MPCP.Hardness
import DiagonaLean.PCP.Primrec
import DiagonaLean.PCP.Undecidable
import DiagonaLean.MatMort.Primrec
import DiagonaLean.EmpCFG.MachineLevel
import DiagonaLean.AmbigCFG.MachineLevel

/-! Tests for `reduce_from`, run by CI: one case per goal shape, the link upgrade, and the errors. -/

open DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions DiagonaLean.PCP.Reduction DiagonaLean.MPCP.Reduction

/-- The alphabet of the MPCP and PCP instances built from machines. -/
abbrev A := Alpha ℕ DiagonaLean.Foundations.Computability.Normalize.Sym2

/-- PCP over the alphabet of `PCP.synthFromMPCP`'s target. -/
abbrev PCPA := @DiagonaLean.PCP.DecisionProblem (Ext A)

/-! ### Proved goals -/

/-- A synthetic link whose function `fun_prop` reads is upgraded with no goal left. -/
example : HaltReduction HaltCanon := by
  reduce_from (ComputableReduction.refl HaltCanon) via (SynthReduction.refl HaltCanon)

/-- MPCP to PCP: `mpcpToPcp`'s `fun_prop` lemma closes the computability of the link. -/
example : HaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via (DiagonaLean.PCP.synthFromMPCP (α := A))

example : HaltHard PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via (DiagonaLean.PCP.synthFromMPCP (α := A))

example : ¬ ComputablePred PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via (DiagonaLean.PCP.synthFromMPCP (α := A))

/-- The encoding's computability is closed by `assumption`. -/
example {enc : DiagonaLean.PCP.Stack (Ext A) → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via (DiagonaLean.PCP.synthFromMPCP (α := A))

/-- A proved link needs nothing more. -/
example : HaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via
    (ComputableReduction.ofSynth (DiagonaLean.PCP.synthFromMPCP (α := A)) mpcpToPcp_primrec.to_comp)

/-! ### Link upgrades by `fun_prop`

Each link's function has a `fun_prop` lemma, so `reduce_from` reduces `r.f` to that function
(`ReduceFrom.unfoldField`, which keeps it folded) and closes its computability. -/

example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem DiagonaLean.MatMort.Reduction.S23)) :
    HaltHard DiagonaLean.MatMort.DecisionProblem := by
  reduce_from h via DiagonaLean.MatMort.synthFromPCP

example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem Bool)) :
    HaltHard (fun c : DiagonaLean.Foundations.Grammar.CFGCode (DiagonaLean.EmpCFG.Reduction.Term Bool) ×
        DiagonaLean.Foundations.Grammar.CFGCode (DiagonaLean.EmpCFG.Reduction.Term Bool) =>
      DiagonaLean.EmpCFG.IntersectionNonempty c.1.toCFG c.2.toCFG) := by
  reduce_from h via (DiagonaLean.EmpCFG.synthCodeFromPCP (α := Bool))

example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem Bool)) :
    HaltHard (fun c : DiagonaLean.Foundations.Grammar.CFGCode (Bool ⊕ ℕ) =>
      DiagonaLean.AmbigCFG.DecisionProblem c.toCFG) := by
  reduce_from h via (DiagonaLean.AmbigCFG.synthCodeFromPCP (α := Bool))

example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem (Ext Bool))) :
    HaltHard (@DiagonaLean.PCP.DecisionProblem Bool) := by
  reduce_from h via
    (DiagonaLean.PCP.synthAlphabetLift (γ₁ := Ext Bool) false true (by decide))

/-! ### Synthetic goals -/

/-- A proved source and a synthetic link give a synthetic result, through the bridge. -/
def synthFromProved : SynthHaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via (DiagonaLean.PCP.synthFromMPCP (α := A))

/-- Both synthetic. -/
def synthFromSynth : SynthHaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.synthFromHalt via (DiagonaLean.PCP.synthFromMPCP (α := A))

/-! ### Errors -/

/--
error: reduce_from: the source `DiagonaLean.MPCP.synthFromHalt` is a synthetic halting reduction, but the goal needs a proved one. A halting reduction is upgraded at its root, by a reduction from `HaltCanon` proved computable, not by a computability proof of the link.
-/
#guard_msgs in
example : HaltHard PCPA := by
  reduce_from DiagonaLean.MPCP.synthFromHalt via (DiagonaLean.PCP.synthFromMPCP (α := A))

/--
error: reduce_from: the goal
  True
is not one of `SynthHaltReduction q`, `HaltReduction q`, `HaltHard q`, `¬ ComputablePred q`, `¬ MachineDecidable enc q`
-/
#guard_msgs in
example : True := by
  reduce_from DiagonaLean.MPCP.fromHalt via (DiagonaLean.PCP.synthFromMPCP (α := A))
