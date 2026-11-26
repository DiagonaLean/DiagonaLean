import DiagonaLean.Foundations.Computability.ReduceFrom
import DiagonaLean.MPCP.Hardness
import DiagonaLean.PCP.Primrec
import DiagonaLean.PCP.Undecidable
import DiagonaLean.MatMort.Primrec
import DiagonaLean.EmpCFG.MachineLevel
import DiagonaLean.AmbigCFG.MachineLevel
import DiagonaLean.Foundations.Codes.Tactic
import DiagonaLean.GrammarMem.Hardness

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

/-! ### `code_lift` on `reduce_from`

A halting reduction is composed with the lift of a functor on codes; the goal picks the synthetic
lift or the proved one, whose computability `code_lift_computable` closes. -/

example {α : Type} [Primcodable α] (b0 b1 : α) (hne : b0 ≠ b1) :
    HaltReduction (@DiagonaLean.MPCP.DecisionProblem α) := by
  code_lift DiagonaLean.MPCP.Reduction.mpcpFunctor from DiagonaLean.MPCP.fromHalt

example : HaltHard (@DiagonaLean.MPCP.DecisionProblem Bool) := by
  have hne : false ≠ true := by decide
  code_lift DiagonaLean.MPCP.Reduction.mpcpFunctor from DiagonaLean.MPCP.fromHalt

example {α : Type} (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction (@DiagonaLean.MPCP.DecisionProblem α) := by
  code_lift DiagonaLean.MPCP.Reduction.mpcpFunctor from DiagonaLean.MPCP.fromHalt

/-! ### Synthetic goals -/

/-- A proved source and a synthetic link give a synthetic result, through the bridge. -/
def synthFromProved : SynthHaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via (DiagonaLean.PCP.synthFromMPCP (α := A))

/-- Both synthetic. -/
def synthFromSynth : SynthHaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.synthFromHalt via (DiagonaLean.PCP.synthFromMPCP (α := A))

/-- A link out of a subtype (type 0 grammar codes): `prim_subtype_val` with the predicate's
`@[fun_prop]` lemma `isType0_prim`. -/
def fromSubtypeLink : HaltReduction (@DiagonaLean.GrammarMem.DecisionProblem Bool) := by
  reduce_from DiagonaLean.GrammarMem.emptyWordFromHalt via DiagonaLean.GrammarMem.synthFromEmptyWord

/-! ### Negative sources

A source `h : ¬ ComputablePred p` transfers along a link, so no halting reduction is needed. -/

/-- A synthetic link, upgraded: its computability is closed by `fun_prop`. -/
example : ¬ ComputablePred PCPA := by
  reduce_from DiagonaLean.MPCP.MachineLevel.not_computablePred_mpcp via (DiagonaLean.PCP.synthFromMPCP (α := A))

/-- A proved link needs nothing more. -/
example : ¬ ComputablePred PCPA := by
  reduce_from DiagonaLean.MPCP.MachineLevel.not_computablePred_mpcp via
    (ComputableReduction.ofSynth (DiagonaLean.PCP.synthFromMPCP (α := A)) mpcpToPcp_primrec.to_comp)

/-- The encoding's computability is closed by `assumption`. -/
example {enc : DiagonaLean.PCP.Stack (Ext A) → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc PCPA := by
  reduce_from DiagonaLean.MPCP.MachineLevel.not_computablePred_mpcp via (DiagonaLean.PCP.synthFromMPCP (α := A))

/-! ### Errors -/

/--
error: reduce_from: the source `DiagonaLean.MPCP.MachineLevel.not_computablePred_mpcp` is a negative result (`¬ ComputablePred`), so it proves only a goal `¬ ComputablePred q` or `¬ MachineDecidable enc q`; the other goals need a halting reduction as the source.
-/
#guard_msgs in
example : HaltHard PCPA := by
  reduce_from DiagonaLean.MPCP.MachineLevel.not_computablePred_mpcp via
    (DiagonaLean.PCP.synthFromMPCP (α := A))

/--
error: reduce_from: the source `(1 : ℕ)` is neither a reduction nor a negative result: its type is
  ℕ
expected a `SynthReduction` (`⪯_s`, `SynthHaltReduction`), a `ComputableReduction` (`HaltReduction`) or `¬ ComputablePred p`
-/
#guard_msgs in
example : ¬ ComputablePred PCPA := by
  reduce_from (1 : ℕ) via (DiagonaLean.PCP.synthFromMPCP (α := A))

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

/-! ### Adversarial cases -/

/-- The link behind two layers of definitions is still read: `unfoldField` reaches the function. -/
def layer1 : @DiagonaLean.MPCP.DecisionProblem A ⪯_s PCPA := DiagonaLean.PCP.synthFromMPCP (α := A)
def layer2 : @DiagonaLean.MPCP.DecisionProblem A ⪯_s PCPA := layer1

example : HaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via layer2

/-- A composite link: the function is a composition, and `fun_prop` reads it. -/
example : HaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via
    (SynthReduction.trans (SynthReduction.refl _) (DiagonaLean.PCP.synthFromMPCP (α := A)))

/-- A classical link: the tactic does not close its computability, which is unprovable. -/
noncomputable def cheat : HaltCanon ⪯_s (fun b : Bool => b = true) :=
  ⟨fun x => @decide (HaltCanon x) (Classical.propDecidable _), fun x => by simp⟩

/--
error: unsolved goals
⊢ Computable cheat.f
-/
#guard_msgs in
noncomputable def cheatProved : HaltReduction (fun b : Bool => b = true) := by
  reduce_from (ComputableReduction.refl HaltCanon) via cheat

-- A source that does not exist reports the unknown identifier, not a vague type.
/--
error: Unknown identifier `DiagonaLean.Nonexistent`
-/
#guard_msgs in
example : HaltReduction PCPA := by
  reduce_from DiagonaLean.Nonexistent via layer2

-- A source and a link that do not meet say which is which.
/--
error: reduce_from: the source `(ComputableReduction.refl HaltCanon)` reduces to
  HaltCanon
but the link `layer2` starts from
  DiagonaLean.MPCP.DecisionProblem
-/
#guard_msgs in
example : HaltReduction PCPA := by
  reduce_from (ComputableReduction.refl HaltCanon) via layer2
