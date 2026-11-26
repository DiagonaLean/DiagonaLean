import DiagonaLean.Foundations.Computability.ReduceFrom
import DiagonaLean.MPCP.Hardness
import DiagonaLean.PCP.Primrec
import DiagonaLean.PCP.Undecidable
import DiagonaLean.MatMort.Primrec
import DiagonaLean.EmpCFG.MachineLevel
import DiagonaLean.AmbigCFG.MachineLevel
import DiagonaLean.Foundations.Codes.Tactic
import DiagonaLean.GrammarMem.Hardness
import DiagonaLean.MatMort.MachineLevel
import DiagonaLean.SemiThue.Undecidable

/-! Tests for `reduce_from`, run by CI: one case per goal shape, the link upgrade, and the errors. -/

open DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions DiagonaLean.PCP.Reduction DiagonaLean.MPCP.Reduction

/-- The alphabet of the MPCP and PCP instances built from machines. -/
abbrev A := Alpha ℕ DiagonaLean.Foundations.Computability.Normalize.Sym2

/-- PCP over the alphabet of the target of `mpcpToPcp`. -/
abbrev PCPA := @DiagonaLean.PCP.DecisionProblem (Ext A)

/-- A bundled link from MPCP to PCP, for the tests of `via`. The library builds its reductions from
the function and its correctness (`mpcp_reducesto_pcp_spec`) instead. -/
def mpcpLink : @DiagonaLean.MPCP.DecisionProblem A ⪯_s PCPA :=
  ⟨fun x => mpcpToPcp x.1 x.2, mpcp_reducesto_pcp_spec⟩

/-- MPCP over `A` is not a computable predicate: a negative source for the tests. -/
theorem mpcpNeg : ¬ ComputablePred (@DiagonaLean.MPCP.DecisionProblem A) :=
  DiagonaLean.MPCP.fromHalt.not_computablePred

/-! ### Proved goals -/

/-- A synthetic link whose function `fun_prop` reads is upgraded with no goal left. -/
example : HaltReduction HaltCanon := by
  reduce_from (ComputableReduction.refl HaltCanon) via (SynthReduction.refl HaltCanon)

/-- MPCP to PCP: `mpcpToPcp`'s `fun_prop` lemma closes the computability of the link. -/
example : HaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via mpcpLink

example : HaltHard PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via mpcpLink

example : ¬ ComputablePred PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via mpcpLink

/-- The encoding's computability is closed by `assumption`. -/
example {enc : DiagonaLean.PCP.Stack (Ext A) → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via mpcpLink

/-- A proved link needs nothing more. -/
example : HaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via
    (ComputableReduction.ofSynth mpcpLink mpcpToPcp_primrec.to_comp)

/-! ### Link upgrades by `fun_prop`

Each link's function has a `fun_prop` lemma, so `reduce_from` reduces `r.f` to that function
(`ReduceFrom.unfoldField`, which keeps it folded) and closes its computability. -/

example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem DiagonaLean.MatMort.Reduction.S23)) :
    HaltHard DiagonaLean.MatMort.DecisionProblem := by
  reduce_from h via (⟨DiagonaLean.MatMort.Reduction.matImage,
    DiagonaLean.MatMort.Reduction.pcp_reducesto_matMort_spec⟩ :
    @DiagonaLean.PCP.DecisionProblem DiagonaLean.MatMort.Reduction.S23 ⪯_s
      DiagonaLean.MatMort.DecisionProblem)

example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem Bool)) :
    HaltHard (fun c : DiagonaLean.Foundations.Grammar.CFGCode (DiagonaLean.EmpCFG.Reduction.Term Bool) ×
        DiagonaLean.Foundations.Grammar.CFGCode (DiagonaLean.EmpCFG.Reduction.Term Bool) =>
      DiagonaLean.EmpCFG.IntersectionNonempty c.1.toCFG c.2.toCFG) := by
  reduce_from h via (SynthReduction.mk DiagonaLean.EmpCFG.MachineLevel.empCode
    (DiagonaLean.EmpCFG.MachineLevel.pcp_reducesto_empCFGCode_spec (α := Bool)))

example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem Bool)) :
    HaltHard (fun c : DiagonaLean.Foundations.Grammar.CFGCode (Bool ⊕ ℕ) =>
      DiagonaLean.AmbigCFG.DecisionProblem c.toCFG) := by
  reduce_from h via (SynthReduction.mk DiagonaLean.AmbigCFG.MachineLevel.ambCode
    (DiagonaLean.AmbigCFG.MachineLevel.pcp_reducesto_ambigCFGCode_spec (α := Bool)))

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
  reduce_from DiagonaLean.MPCP.fromHalt via mpcpLink

/-- Both synthetic. -/
def synthFromSynth : SynthHaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.synthFromHalt via mpcpLink

/-- A link out of a subtype (type 0 grammar codes): `prim_subtype_val` with the predicate's
`@[fun_prop]` lemma `isType0_prim`. -/
def fromSubtypeLink : HaltReduction (@DiagonaLean.GrammarMem.DecisionProblem Bool) := by
  reduce_from DiagonaLean.GrammarMem.emptyWordFromHalt via
    (⟨fun g => (g.1, []), fun _ => Iff.rfl⟩ :
      (fun g : { g : DiagonaLean.GrammarMem.GrammarCode Bool // DiagonaLean.GrammarMem.IsType0 g } =>
        DiagonaLean.GrammarMem.EmptyWordProblem g.1) ⪯_s @DiagonaLean.GrammarMem.DecisionProblem Bool)

/-! ### Negative sources

A source `h : ¬ ComputablePred p` transfers along a link, so no halting reduction is needed. -/

/-- A synthetic link, upgraded: its computability is closed by `fun_prop`. -/
example : ¬ ComputablePred PCPA := by
  reduce_from mpcpNeg via mpcpLink

/-- A proved link needs nothing more. -/
example : ¬ ComputablePred PCPA := by
  reduce_from mpcpNeg via
    (ComputableReduction.ofSynth mpcpLink mpcpToPcp_primrec.to_comp)

/-- The encoding's computability is closed by `assumption`. -/
example {enc : DiagonaLean.PCP.Stack (Ext A) → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc PCPA := by
  reduce_from mpcpNeg via mpcpLink

/-! ### Errors -/

/--
error: reduce_from: the source `mpcpNeg` is a negative result (`¬ ComputablePred`), so it proves only a goal `¬ ComputablePred q` or `¬ MachineDecidable enc q`; the other goals need a halting reduction as the source.
-/
#guard_msgs in
example : HaltHard PCPA := by
  reduce_from mpcpNeg via
    mpcpLink

/--
error: reduce_from: the source `(1 : ℕ)` is neither a reduction nor a negative result: its type is
  ℕ
expected a `SynthReduction` (`⪯_s`, `SynthHaltReduction`), a `ComputableReduction` (`HaltReduction`) or `¬ ComputablePred p`
-/
#guard_msgs in
example : ¬ ComputablePred PCPA := by
  reduce_from (1 : ℕ) via mpcpLink

/--
error: reduce_from: the source `DiagonaLean.MPCP.synthFromHalt` is a synthetic halting reduction, but the goal needs a proved one. A halting reduction is upgraded at its root, by a reduction from `HaltCanon` proved computable, not by a computability proof of the link.
-/
#guard_msgs in
example : HaltHard PCPA := by
  reduce_from DiagonaLean.MPCP.synthFromHalt via mpcpLink

/--
error: reduce_from: the goal
  True
is not one of `SynthHaltReduction q`, `HaltReduction q`, `HaltHard q`, `¬ ComputablePred q`, `¬ MachineDecidable enc q`
-/
#guard_msgs in
example : True := by
  reduce_from DiagonaLean.MPCP.fromHalt via mpcpLink

/-! ### Adversarial cases -/

/-- The link behind two layers of definitions is still read: `unfoldField` reaches the function. -/
def layer1 : @DiagonaLean.MPCP.DecisionProblem A ⪯_s PCPA := mpcpLink
def layer2 : @DiagonaLean.MPCP.DecisionProblem A ⪯_s PCPA := layer1

example : HaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via layer2

/-- A composite link: the function is a composition, and `fun_prop` reads it. -/
example : HaltReduction PCPA := by
  reduce_from DiagonaLean.MPCP.fromHalt via
    (SynthReduction.trans (SynthReduction.refl _) mpcpLink)

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

/-! ### The link as a function and a proof (`synth_reduce_from … with`)

`synth_reduce_from h with f using spec` builds the link `⟨f, spec⟩` from the function and its
correctness; the goal must be `SynthHaltReduction q`. -/

open DiagonaLean.MatMort.Reduction

/-- The whole statement. -/
example (h : SynthHaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  synth_reduce_from h with matImage using pcp_reducesto_matMort_spec

/-- The two directions, as two lemmas. -/
example (h : SynthHaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  synth_reduce_from h with matImage using matmort_of_pcp pcp_of_matmort

/-- The function alone leaves `forward` and `backward`, with named hypotheses. -/
example (h : SynthHaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  synth_reduce_from h with matImage
  · exact matmort_of_pcp hp
  · exact pcp_of_matmort hq

/-- `unfold` also unfolds both problems one step: `hp` is the existential of PCP. -/
example (h : SynthHaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  synth_reduce_from h with matImage unfold
  · obtain ⟨A, hne, hmem, heq⟩ := hp
    exact matmort_of_pcp (by unfold DiagonaLean.PCP.DecisionProblem; exact ⟨A, hne, hmem, heq⟩)
  · exact pcp_of_matmort hq

/-- A problem that is a lambda (the AmbigCFG instance type) is unfolded after beta. -/
example (h : SynthHaltReduction (@DiagonaLean.PCP.DecisionProblem Bool)) :
    SynthHaltReduction (@DiagonaLean.PCP.DecisionProblem Bool) := by
  synth_reduce_from h with id unfold
  · exact hp
  · exact hq

/-- A function given as a lambda is read too (it uses only trusted constants). -/
example (h : SynthHaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  synth_reduce_from h with (fun K => matImage K) using matmort_of_pcp pcp_of_matmort

/-- `via` composes with a bundled link, on a synthetic goal. -/
example (h : SynthHaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  synth_reduce_from h via (⟨matImage, pcp_reducesto_matMort_spec⟩ :
    @DiagonaLean.PCP.DecisionProblem S23 ⪯_s DiagonaLean.MatMort.DecisionProblem)

/-! ### A problem as the source: found by the naming convention -/

/-- `SemiThue.synthFromHaltBool` is the source for the problem over `Bool`. -/
example : SynthHaltReduction (@DiagonaLean.SemiThue.DecisionProblem Bool) := by
  reduce_from (@DiagonaLean.SemiThue.DecisionProblem Bool) via (SynthReduction.refl _)

example : SynthHaltReduction (@DiagonaLean.SemiThue.DecisionProblem Bool) := by
  synth_reduce_from (@DiagonaLean.SemiThue.DecisionProblem Bool) with id using (fun _ => Iff.rfl)

/-! ### Errors of `synth_reduce_from` and of the lookup -/

noncomputable def badF : DiagonaLean.PCP.Stack S23 → Finset (Matrix (Fin 3) (Fin 3) ℤ) := matImage

/--
error: synth_reduce_from: the link function `badF` is marked `noncomputable`. The function of a synthetic reduction must be a compiled program. For a proved result, use a proved link, or prove `Computable` of the function.
-/
#guard_msgs in
example (h : SynthHaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  synth_reduce_from h with badF using pcp_reducesto_matMort_spec

/--
error: synth_reduce_from: the link function uses `Classical.choice`, which has no compiled code (classical choice). The function of a synthetic reduction must be a compiled program. For a proved result, use a proved link, or prove `Computable` of the function.
-/
#guard_msgs in
example (h : SynthHaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  synth_reduce_from h with
    (fun K => (Classical.choice ⟨matImage K⟩ : Finset (Matrix (Fin 3) (Fin 3) ℤ)))
    using matmort_of_pcp pcp_of_matmort

def stubImpl : DiagonaLean.PCP.Stack S23 → Finset (Matrix (Fin 3) (Fin 3) ℤ) := matImage

@[implemented_by stubImpl]
def stubF : DiagonaLean.PCP.Stack S23 → Finset (Matrix (Fin 3) (Fin 3) ℤ) :=
  fun K => Classical.choice ⟨matImage K⟩

/--
error: synth_reduce_from: the link function `stubF` uses `implemented_by`. The function of a synthetic reduction must be a compiled program. For a proved result, use a proved link, or prove `Computable` of the function.
-/
#guard_msgs in
example (h : SynthHaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  synth_reduce_from h with stubF using pcp_reducesto_matMort_spec

-- the message embeds Lean's own mismatch text, which is not stable, so only the failure is checked
#guard_msgs (drop error) in
example (h : SynthHaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  synth_reduce_from h with matImage using pcp_of_matmort matmort_of_pcp

/--
error: synth_reduce_from: the goal
  HaltHard DiagonaLean.MatMort.DecisionProblem
is not `SynthHaltReduction q`. For a proved goal, use `reduce_from … via`.
-/
#guard_msgs in
example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    HaltHard DiagonaLean.MatMort.DecisionProblem := by
  synth_reduce_from h with matImage using pcp_reducesto_matMort_spec

/--
error: reduce_from: `DiagonaLean.MatMort.DecisionProblem` is a problem, not a reduction, so the tactic looks for a synthetic halting reduction to it in the namespace `DiagonaLean.MatMort`, by the names `synthFromHalt` and `synthFromHaltBool`, and finds none that applies. Give the source explicitly.
-/
#guard_msgs in
example : SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  synth_reduce_from DiagonaLean.MatMort.DecisionProblem with matImage
    using pcp_reducesto_matMort_spec

/-! ### `reduce_from_pcp … with`: the letters and the proof that they differ stay automatic -/

example : SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  reduce_from_pcp over_letters (0 : S23) (1 : S23) with matImage
    using pcp_reducesto_matMort_spec

example : SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  reduce_from_pcp over_letters (0 : S23) (1 : S23) with matImage
    using matmort_of_pcp pcp_of_matmort

example : SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  reduce_from_pcp over_letters (0 : S23) (1 : S23) with matImage
  · exact matmort_of_pcp hp
  · exact pcp_of_matmort hq

example : SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  reduce_from_pcp over_letters (0 : S23) (1 : S23) with matImage unfold
  · obtain ⟨A, hne, hmem, heq⟩ := hp
    exact matmort_of_pcp (by unfold DiagonaLean.PCP.DecisionProblem; exact ⟨A, hne, hmem, heq⟩)
  · exact pcp_of_matmort hq

/-! ### Hard goals: `hard_reduce_from … with`, and `reduce_from … with` choosing by the goal

The link is `⟨f, computable, proof⟩`; `Computable f` is tried with `fun_prop` and left open if that
fails. The source is a proved halting reduction, `HaltHard p`, a negative result, or a problem with
a `HaltSource` instance. -/

example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    HaltHard DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from h with matImage using pcp_reducesto_matMort_spec

example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    HaltReduction DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from h with matImage using matmort_of_pcp pcp_of_matmort

/-- The function alone leaves `forward` and `backward`; `Computable matImage` is closed. -/
example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    ¬ ComputablePred DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from h with matImage
  · exact matmort_of_pcp hp
  · exact pcp_of_matmort hq

example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    ¬ ComputablePred DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from h with matImage unfold
  · obtain ⟨A, hne, hmem, heq⟩ := hp
    exact matmort_of_pcp (by unfold DiagonaLean.PCP.DecisionProblem; exact ⟨A, hne, hmem, heq⟩)
  · exact pcp_of_matmort hq

/-- A source that is only the fact `HaltHard p`. -/
example (h : HaltHard (@DiagonaLean.PCP.DecisionProblem S23)) :
    ¬ ComputablePred DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from h with matImage using pcp_reducesto_matMort_spec

/-- A negative source. -/
example (h : ¬ ComputablePred (@DiagonaLean.PCP.DecisionProblem S23)) :
    ¬ ComputablePred DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from h with matImage using pcp_reducesto_matMort_spec

example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem S23))
    {enc : Finset (Matrix (Fin 3) (Fin 3) ℤ) → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from h with matImage using pcp_reducesto_matMort_spec

/-- `reduce_from … with` goes to `synth_reduce_from` or `hard_reduce_from` by the goal. -/
example (h : SynthHaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  reduce_from h with matImage using pcp_reducesto_matMort_spec

example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    HaltHard DiagonaLean.MatMort.DecisionProblem := by
  reduce_from h with matImage using pcp_reducesto_matMort_spec

/-- A function without a `fun_prop` lemma leaves `Computable` open, stated on the function. -/
def plainF : DiagonaLean.PCP.Stack S23 → Finset (Matrix (Fin 3) (Fin 3) ℤ) := matImage

example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    HaltHard DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from h with plainF using pcp_reducesto_matMort_spec
  exact matImage_primrec.to_comp

/-! #### A problem as the source, through `HaltSource` -/

example : HaltHard (@DiagonaLean.SemiThue.DecisionProblem Bool) := by
  hard_reduce_from (@DiagonaLean.SemiThue.DecisionProblem Bool) with id using (fun _ => Iff.rfl)

example : ¬ ComputablePred DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from DiagonaLean.MatMort.DecisionProblem with id using (fun _ => Iff.rfl)

/-! #### Errors of `hard_reduce_from` -/

abbrev PCPS23 := @DiagonaLean.PCP.DecisionProblem S23

/--
error: hard_reduce_from: the source `h` is a synthetic halting reduction, but a hard goal needs a proved one. A halting reduction is upgraded at its root, from `HaltCanon`, not by a computability proof of the link.
-/
#guard_msgs in
example (h : SynthHaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    HaltHard DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from h with matImage using pcp_reducesto_matMort_spec

/--
error: hard_reduce_from: the source `h` is a proposition (`HaltHard`), but the goal `HaltReduction q` is data. Use a source that is a `HaltReduction`.
-/
#guard_msgs in
example (h : HaltHard (@DiagonaLean.PCP.DecisionProblem S23)) :
    HaltReduction DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from h with matImage using pcp_reducesto_matMort_spec

/--
error: hard_reduce_from: the source `h` is a negative result (`¬ ComputablePred`), so it proves only a goal `¬ ComputablePred q` or `¬ MachineDecidable enc q`.
-/
#guard_msgs in
example (h : ¬ ComputablePred (@DiagonaLean.PCP.DecisionProblem S23)) :
    HaltHard DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from h with matImage using pcp_reducesto_matMort_spec

/--
error: hard_reduce_from: the goal
  SynthHaltReduction DiagonaLean.MatMort.DecisionProblem
is synthetic; use `synth_reduce_from`.
-/
#guard_msgs in
example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem S23)) :
    SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from h with matImage using pcp_reducesto_matMort_spec

/--
error: hard_reduce_from: `PCPS23` is a problem, so the tactic looks for an instance of `HaltSource` or `HaltHardFact` for it, and finds none. Register one, or give the source explicitly.
-/
#guard_msgs in
example : HaltHard DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from PCPS23 with matImage using pcp_reducesto_matMort_spec

/-! #### Chains of links

Links separated by commas: `with f …` or `via r`, composed in order. Every link but the last gives
its correctness with `using`. -/

open DiagonaLean.PCP.AlphabetLift in
/-- Three links to a proved goal: MPCP to PCP, the change of alphabet, PCP to mortality. -/
example : HaltReduction DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from DiagonaLean.MPCP.fromHalt
    with (fun x => mpcpToPcp x.1 x.2) using mpcp_reducesto_pcp_spec,
    with (liftInstance (0 : S23) 1) using (pcp_alphabet_lift_spec 0 1 (by decide)),
    with matImage using pcp_reducesto_matMort_spec

open DiagonaLean.PCP.AlphabetLift in
/-- The same chain to a synthetic goal, from a proved source. -/
example : SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  synth_reduce_from DiagonaLean.MPCP.fromHalt
    with (fun x => mpcpToPcp x.1 x.2) using mpcp_reducesto_pcp_spec,
    with (liftInstance (0 : S23) 1) using (pcp_alphabet_lift_spec 0 1 (by decide)),
    with matImage using pcp_reducesto_matMort_spec

open DiagonaLean.PCP.AlphabetLift in
/-- A bundled synthetic link, upgraded by `fun_prop`, then two functions; `reduce_from` chooses the
layer by the goal. -/
example : ¬ ComputablePred DiagonaLean.MatMort.DecisionProblem := by
  reduce_from DiagonaLean.MPCP.fromHalt via mpcpLink,
    with (liftInstance (0 : S23) 1) using (pcp_alphabet_lift_spec 0 1 (by decide)),
    with matImage using pcp_reducesto_matMort_spec

open DiagonaLean.PCP.AlphabetLift in
example : SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  reduce_from DiagonaLean.MPCP.synthFromHalt via mpcpLink,
    with (liftInstance (0 : S23) 1) using (pcp_alphabet_lift_spec 0 1 (by decide)),
    with matImage using pcp_reducesto_matMort_spec

open DiagonaLean.PCP.AlphabetLift in
/-- A negative source: the links are composed first. -/
example : ¬ ComputablePred DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from mpcpNeg via mpcpLink,
    with (liftInstance (0 : S23) 1) using (pcp_alphabet_lift_spec 0 1 (by decide)),
    with matImage using pcp_reducesto_matMort_spec

open DiagonaLean.PCP.AlphabetLift in
/-- An inner link given by its two directions. -/
example : HaltReduction DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from DiagonaLean.MPCP.fromHalt via mpcpLink,
    with (liftInstance (0 : S23) 1)
      using (fun h => (pcp_alphabet_lift_spec 0 1 (by decide) _).1 h)
        (fun h => (pcp_alphabet_lift_spec 0 1 (by decide) _).2 h),
    with matImage using pcp_reducesto_matMort_spec

open DiagonaLean.PCP.AlphabetLift in
/-- The last link left open; the computability goal of a named function is `computable_<name>`. -/
example : HaltHard DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from DiagonaLean.MPCP.fromHalt via mpcpLink,
    with (liftInstance (0 : S23) 1) using (pcp_alphabet_lift_spec 0 1 (by decide)),
    with plainF
  case forward => exact matmort_of_pcp hp
  case backward => exact pcp_of_matmort hq
  case computable_plainF => exact matImage_primrec.to_comp

/--
error: hard_reduce_from: the link `with liftL` is not the last of the chain, so its correctness must be given with `using`: the problem it reduces to is read from that proof.
-/
#guard_msgs in
example (liftL : DiagonaLean.PCP.Stack (Ext A) → DiagonaLean.PCP.Stack S23) :
    HaltHard DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from DiagonaLean.MPCP.fromHalt via mpcpLink,
    with liftL,
    with matImage using pcp_reducesto_matMort_spec

/--
error: hard_reduce_from: the chain from `DiagonaLean.MPCP.fromHalt` does not compose to the goal: each link must start from the problem the previous one reduces to.
Application type mismatch: The argument
  matImage
has type
  DiagonaLean.PCP.Stack S23 → Finset (Matrix (Fin 3) (Fin 3) ℤ)
but is expected to have type
  DiagonaLean.PCP.Stack (Ext A) → Finset (Matrix (Fin 3) (Fin 3) ℤ)
in the application
  ComputableReduction.mk matImage
-/
#guard_msgs in
example : HaltHard DiagonaLean.MatMort.DecisionProblem := by
  hard_reduce_from DiagonaLean.MPCP.fromHalt via mpcpLink,
    with matImage using pcp_reducesto_matMort_spec
