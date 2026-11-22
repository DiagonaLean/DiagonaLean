/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Codes.Functor
import DiagonaLean.Foundations.Computability.HaltCanon

@[expose] public section

/-! # The lift of a functor on codes, proved computable

`CodeFunctor.lift` is a synthetic reduction from a problem over one alphabet to the same problem
over an alphabet with two distinct letters. With a proof that its function is computable, it is a
proved reduction (`CodeFunctor.computableLift`), so halting-hardness transfers along it
(`CodeFunctor.haltReductionOf`, `CodeFunctor.haltHard_lift`).
-/

namespace DiagonaLean.Foundations.Codes

open DiagonaLean.Foundations.Computability

variable {Good : ∀ {α β : Type}, (α → List β) → Prop} (F : CodeFunctor Good) {α β : Type}

/-- **The lift, proved computable.** -/
def CodeFunctor.computableLift [LiftableCodes Good] [DecidableEq α] [Primcodable (F.Inst α)]
    [Primcodable (F.Inst β)] (b0 b1 : β) (hne : b0 ≠ b1)
    (hmap : Computable (F.liftMap (α := α) b0 b1)) :
    ComputableReduction (@F.Prob α) (@F.Prob β) :=
  .ofSynth (F.lift b0 b1 hne) hmap

/-- A halting reduction to the problem over `α` gives one over any alphabet with two distinct
letters, once the lift's function is computable. -/
def CodeFunctor.haltReductionOf [LiftableCodes Good] [DecidableEq α] [Primcodable (F.Inst α)]
    [Primcodable (F.Inst β)] (h : HaltReduction (@F.Prob α)) (b0 b1 : β) (hne : b0 ≠ b1)
    (hmap : Computable (F.liftMap (α := α) b0 b1)) : HaltReduction (@F.Prob β) :=
  h.trans (F.computableLift b0 b1 hne hmap)

/-- **Halting-hardness transfers to every nontrivial alphabet**, once the lift's function is
computable. -/
theorem CodeFunctor.haltHard_lift [LiftableCodes Good] [Nontrivial β] [Primcodable (F.Inst α)]
    [Primcodable (F.Inst β)]
    (hmap : ∀ [DecidableEq α] (b0 b1 : β), Computable (F.liftMap (α := α) b0 b1))
    (h : HaltHard (@F.Prob α)) : HaltHard (@F.Prob β) := by
  classical
  obtain ⟨b0, b1, hne⟩ := exists_pair_ne β
  obtain ⟨r⟩ := h
  exact ⟨F.haltReductionOf r b0 b1 hne (hmap b0 b1)⟩

end DiagonaLean.Foundations.Codes
