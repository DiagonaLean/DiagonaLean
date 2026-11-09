/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.Basic
import DiagonaLean.KleeneAlgebra.MachineEncoding.Halting
import DiagonaLean.Halt.Undecidable
import DiagonaLean.Synthetic.Undecidability

@[expose] public section

/-! # Undecidability of pre-Kleene algebra with commutativity conditions (M7)

The paper reduces a pair of *computably inseparable* sets to the theory, rather than reducing
`HaltProblem`: machines that output `1` give provable inequalities, machines that output `0` give
inequalities that fail in the language model, and nothing is claimed about machines that diverge.
So the result is stated with a separation reduction (decision D1(b)).

## The inseparable pair

`SelfOut b M` holds when `M` halts on its own code with output `[b]`. No Turing machine decides
a set containing `SelfOut true` and disjoint from `SelfOut false` (`selfOut_inseparable`). If it
did, compose it with the bit flip `flipTM` and run the result on its own code.

## The theory

An instance is a pair `(e, f)` of expressions over the doubled alphabet `ℕ ⊕ ℕ`, where left
letters commute with right letters. `Provable (e, f)` is `e ≤ f` in the free pre-Kleene algebra,
and `ModelLe (e, f)` is inclusion in the language model `pl`. Every theory between the two
(`Provable ⊆ S ⊆ ModelLe`) is covered, including Kleene algebra with these commutativity
hypotheses, since the language model is a Kleene algebra in which they hold.

## Main statements

* `selfOut_inseparable`: the pair is not separated by any machine-decidable set.
* `kaRed`: the reduction. It is an ordinary (computable) Lean function of the machine's data:
  the machine's transition table determines the two expressions.
* `sepReduces_of_between`: `kaRed` separates the pair for every `S` between `Provable` and
  `ModelLe`.
* `insepUndecidable_provable`, `insepUndecidable_modelLe`: the synthetic statements.
* `not_machineDecidable_of_between`: no Turing machine decides such an `S`, for any encoding of
  instances under which some Turing machine computes `kaRed`.
* `undecidable_not_modelLe`: `Undecidable (Complement ModelLe)` in the library's sense, through
  the many-one reduction `haltReduces : HaltProblem ⪯ₘ Complement ModelLe`.

The last hypothesis is the usual Church–Turing gap: constructing the Turing machine that
computes `kaRed` from `encodeBoolTM M` is not formalized. This matches how `Undecidable` and
`⪯ₘ` are used elsewhere in the library, which ask that reductions be built from data.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18, §3
-/

open scoped Computability

namespace DiagonaLean.KAComm.Undec

open Cslib.Turing SingleTapeTM DiagonaLean.Halt.Encoding DiagonaLean.Halt.Compositions
  DiagonaLean.Halt.Undecidable DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation
  DiagonaLean.Halt TD FreePreKA

variable {X Y : Type*}

/-! ### Separation reductions -/

/-- `S` separates `A` from `B`. -/
def Separates (A B S : X → Prop) : Prop := (∀ x, A x → S x) ∧ ∀ x, B x → ¬ S x

/-- `f` maps `A` into `p` and `B` into the complement of `p`. As with `ManyOneReduces`, `f` is
meant to be built from the data of `x`, never by inspecting `A`, `B` or `p`. -/
structure SepReduces (A B : X → Prop) (p : Y → Prop) where
  /-- The reduction function. -/
  f : X → Y
  /-- `A` lands in `p`. -/
  pos : ∀ x, A x → p (f x)
  /-- `B` lands outside `p`. -/
  neg : ∀ x, B x → ¬ p (f x)

/-! ### A computably inseparable pair -/

/-- `M` halts on its own code with output `[b]`. -/
def SelfOut (b : Bool) (M : EncodableTM Bool) : Prop :=
  M.toSingleTapeTM.Outputs (encodeBoolTM M) [b]

/-- Flip the bit under the head and halt. -/
def flipTM : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ a :=
    match a with
    | some b => (⟨some (!b), none⟩, none)
    | none => (⟨none, none⟩, none)

theorem flipTM_true : flipTM.Outputs [true] [false] := Relation.ReflTransGen.single rfl

theorem flipTM_false : flipTM.Outputs [false] [true] := Relation.ReflTransGen.single rfl

/-- **The pair `SelfOut true`, `SelfOut false` is computably inseparable.** -/
theorem selfOut_inseparable {S : EncodableTM Bool → Prop}
    (hS : Separates (SelfOut true) (SelfOut false) S) : ¬ MachineDecidable encodeBoolTM S := by
  rintro ⟨D, hD⟩
  let E : EncodableTM Bool := ⟨compComputer D flipTM, Fintype.toEncodable _⟩
  obtain ⟨hpos, hneg⟩ := hD E
  by_cases hE : S E
  · exact hS.2 E (compComputer_seq_outputs (hpos hE) flipTM_true) hE
  · exact hE (hS.1 E (compComputer_seq_outputs (hneg hE) flipTM_false))

/-- `p` is undecidable via the inseparable pair. Like `Undecidable`, the reduction is wrapped in
`Nonempty` to keep this a `Prop`. -/
def InsepUndecidable (p : Y → Prop) : Prop := Nonempty (SepReduces (SelfOut true) (SelfOut false) p)

/-- A separation reduction computed by a Turing machine transfers inseparability: `p` has no
machine decider. -/
theorem not_machineDecidable_of_sepReduces {enc : Y → List Bool} {p : Y → Prop}
    (r : SepReduces (SelfOut true) (SelfOut false) p) {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encodeBoolTM enc r.f) : ¬ MachineDecidable enc p := fun hp =>
  selfOut_inseparable (S := p ∘ r.f) ⟨r.pos, r.neg⟩
    (machineDecidable_of_computes_reduction hR (fun _ => Iff.rfl) hp)

/-! ### The theory -/

/-- `e ≤ f` is provable in pre-Kleene algebra, with left letters commuting with right letters. -/
def Provable (i : Inst) : Prop := (mk i.1 : TD ℕ) ≤ mk i.2

/-- `e ≤ f` holds in the language model. -/
def ModelLe (i : Inst) : Prop := pl (mk i.1 : TD ℕ) ≤ pl (mk i.2)

theorem Provable.modelLe {i : Inst} (h : Provable i) : ModelLe i := pl_mono h

/-- **The reduction.** The inequality `(init)_r R_M∗ ≤ Σ∗ (C_M + T_true)_r + Σ∗ Σ^≠ ρ_M` for `M`
run on its own code, with letters renamed to their codes. -/
def kaRed (M : EncodableTM Bool) : Inst :=
  letI := M.stateEncodable
  letI : DecidableEq M.State := Encodable.decidableEqOfEncodable _
  ((Enc.lhsS M.toSingleTapeTM (encodeBoolTM M)).map (dmap Encodable.encode),
    (Enc.rhsS M.toSingleTapeTM true).map (dmap Encodable.encode))

theorem kaRed_pos {M : EncodableTM Bool} (h : SelfOut true M) : Provable (kaRed M) := by
  let := M.stateEncodable
  let : DecidableEq M.State := Encodable.decidableEqOfEncodable _
  exact le_map _ (Enc.le_of_outputs h)

theorem kaRed_neg {M : EncodableTM Bool} (h : SelfOut false M) : ¬ ModelLe (kaRed M) := by
  let := M.stateEncodable
  let : DecidableEq M.State := Encodable.decidableEqOfEncodable _
  exact fun hle => Enc.not_pl_le_of_outputs h (by decide)
    (pl_le_of_map Encodable.encode_injective hle)

/-- **Separation.** `kaRed` sends machines with output `1` into any theory `S` containing
pre-KA provability, and machines with output `0` outside any `S` sound for the language model. -/
def sepReduces_of_between (S : Inst → Prop) (h₁ : ∀ i, Provable i → S i)
    (h₂ : ∀ i, S i → ModelLe i) : SepReduces (SelfOut true) (SelfOut false) S :=
  ⟨kaRed, fun _ h => h₁ _ (kaRed_pos h), fun _ h hS => kaRed_neg h (h₂ _ hS)⟩

theorem insepUndecidable_of_between (S : Inst → Prop) (h₁ : ∀ i, Provable i → S i)
    (h₂ : ∀ i, S i → ModelLe i) : InsepUndecidable S :=
  ⟨sepReduces_of_between S h₁ h₂⟩

/-- **Pre-Kleene algebra with commutativity conditions is undecidable.** -/
theorem insepUndecidable_provable : InsepUndecidable Provable :=
  insepUndecidable_of_between _ (fun _ h => h) fun _ h => h.modelLe

/-- Inclusion in the language model (with commutativity) is undecidable too. -/
theorem insepUndecidable_modelLe : InsepUndecidable ModelLe :=
  insepUndecidable_of_between _ (fun _ h => h.modelLe) fun _ h => h

/-- **No Turing machine decides any theory between pre-KA provability and the language model**,
for any encoding of instances under which a Turing machine computes `kaRed`. -/
theorem not_machineDecidable_of_between {enc : Inst → List Bool} {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encodeBoolTM enc kaRed) (S : Inst → Prop)
    (h₁ : ∀ i, Provable i → S i) (h₂ : ∀ i, S i → ModelLe i) : ¬ MachineDecidable enc S :=
  not_machineDecidable_of_sepReduces (sepReduces_of_between S h₁ h₂) hR

/-! ### A many-one reduction from `HaltProblem`

Dropping the halting term gives a reduction from `HaltProblem` itself, in the library's sense of
`Undecidable` (`Nonempty (HaltProblem ⪯ₘ p)`). The target is the *failure* of language-model
inclusion: `M` halts on `w` iff `(init w)_r R_M∗ ≤ Σ∗ (C_M)_r + Σ∗ Σ^≠ ρ_M` fails in the model
(`Enc.halts_iff_not_pl_le_syntax`). The same reduction says nothing about pre-KA provability,
because the paper does not determine provability for machines that run forever. -/

/-- **The reduction from `HaltProblem`.** `(M, w) ↦ ((init w)_r R_M∗, Σ∗ (C_M)_r + Σ∗ Σ^≠ ρ_M)`,
with letters renamed to their codes. -/
def haltRed (p : EncodableTM Bool × List Bool) : Inst :=
  letI := p.1.stateEncodable
  letI : DecidableEq p.1.State := Encodable.decidableEqOfEncodable _
  ((Enc.lhsS p.1.toSingleTapeTM p.2).map (dmap Encodable.encode),
    (Enc.rhsHS p.1.toSingleTapeTM).map (dmap Encodable.encode))

/-- `M` halts on `w` iff the instance `haltRed (M, w)` fails in the language model. -/
theorem halt_iff_not_modelLe (p : EncodableTM Bool × List Bool) :
    HaltProblem p ↔ ¬ ModelLe (haltRed p) := by
  obtain ⟨M, w⟩ := p
  let := M.stateEncodable
  let : DecidableEq M.State := Encodable.decidableEqOfEncodable _
  show Halts M.toSingleTapeTM w ↔ _
  rw [Enc.halts_iff_not_pl_le_syntax]
  exact not_congr ⟨pl_map_le_of_le _, pl_le_of_map Encodable.encode_injective⟩

/-- `HaltProblem` many-one reduces to the failure of language-model inclusion. -/
def haltReduces : HaltProblem ⪯ₘ Complement ModelLe := ⟨haltRed, halt_iff_not_modelLe⟩

/-- **Undecidability in the library's sense:** `HaltProblem ⪯ₘ` the complement of language-model
inclusion for KA with commutativity conditions. -/
theorem undecidable_not_modelLe : Undecidable (Complement ModelLe) := ⟨haltReduces⟩

end DiagonaLean.KAComm.Undec
