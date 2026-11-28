/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import Mathlib.Computability.StateTransition
import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

@[expose] public section

/-! # Simulations reflect halting

A *forward simulation with progress* of `f₁` by `f₂` relates states by `R` so that whenever
`R a₁ a₂` and `f₁` steps from `a₁` to `b₁`, `f₂` takes at least one step from `a₂` to some `b₂`
with `R b₁ b₂`. Such a simulation reflects halting: if `f₂` halts from `a₂`, then `f₁` halts from
`a₁` (`eval_dom_of_simulation`). If `f₁` ran forever, `f₂` would too, since its steps are a function
and the simulation forces infinitely many of them.

Mathlib's `StateTransition.Respects` gives both directions at once, but it asks `f₂` to stop
exactly when `f₁` does. The translations of the library do some work after the simulated machine
stops (the result check of `PartrecToCslib.lean`, the sweep of `TM0ToCslib.lean`), so they are
forward simulations with progress, and this lemma gives their converse.

A Cslib machine steps by a function (`SingleTapeTM.step`), so these results apply to it:
`SingleTapeTM.eval_dom_iff` says that the evaluation of `step` is defined exactly when the machine
reaches a halting configuration.

## Main statements

* `acc_of_reaches_none`: a run to a stopped state makes the starting state accessible.
* `eval_dom_of_simulation`: a forward simulation with progress reflects halting.
* `SingleTapeTM.eval_dom_iff`: halting of a Cslib machine as termination of its step function.
-/

namespace DiagonaLean.Foundations.Computability

open StateTransition Relation

/-- **A run to a stopped state makes the starting state accessible**: steps are a function, so
the states reachable from `a` form one finite chain. -/
theorem acc_of_reaches_none {σ : Type*} {f : σ → Option σ} {a c : σ} (h : Reaches f a c)
    (hc : f c = none) : Acc (fun y x => y ∈ f x) a := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨_, fun y hy => by simp [hc] at hy⟩
  | head hab _ ih => exact ⟨_, fun y hy => (Option.mem_unique hy hab) ▸ ih⟩

/-- **A forward simulation with progress reflects halting.** If every step of `f₁` from a state
related to `a₂` is matched by at least one step of `f₂` to a related state, and `f₂` halts from
`a₂`, then `f₁` halts from `a₁`. -/
theorem eval_dom_of_simulation {σ₁ σ₂ : Type*} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂}
    {R : σ₁ → σ₂ → Prop}
    (H : ∀ ⦃a₁ a₂ b₁⦄, R a₁ a₂ → b₁ ∈ f₁ a₁ → ∃ b₂, R b₁ b₂ ∧ Reaches₁ f₂ a₂ b₂)
    {a₁ : σ₁} {a₂ : σ₂} (aa : R a₁ a₂) (h : (eval f₂ a₂).Dom) : (eval f₁ a₁).Dom := by
  obtain ⟨c, hc⟩ := Part.dom_iff_mem.1 h
  obtain ⟨hr, h0⟩ := mem_eval.1 hc
  have hacc : Acc (TransGen fun y x => y ∈ f₂ x) a₂ := (acc_of_reaches_none hr h0).transGen
  clear hc hr h h0
  induction hacc generalizing a₁ with
  | intro a₂ _ ih =>
    cases hf : f₁ a₁ with
    | none => exact Part.dom_iff_mem.2 ⟨a₁, mem_eval.2 ⟨.refl, hf⟩⟩
    | some b₁ =>
      obtain ⟨b₂, hb, hab⟩ := H aa hf
      have hd := ih b₂ hab.swap hb
      rwa [reaches_eval (ReflTransGen.single (show b₁ ∈ f₁ a₁ from hf))]

namespace SingleTapeTM

open Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] (tm : SingleTapeTM Symbol)

/-- **Halting of a Cslib machine is termination of its step function**: the evaluation of `step`
from `c` is defined iff the machine reaches a halting configuration from `c`. -/
theorem eval_dom_iff (c : tm.Cfg) :
    (eval tm.step c).Dom ↔
      ∃ t, ReflTransGen tm.TransitionRelation c (⟨none, t⟩ : tm.Cfg) := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := Part.dom_iff_mem.1 h
    obtain ⟨hr, h0⟩ := mem_eval.1 hd
    obtain ⟨_ | q, t⟩ := d
    · exact ⟨t, hr⟩
    · simp [Cslib.Turing.SingleTapeTM.step] at h0
  · rintro ⟨t, hr⟩
    exact Part.dom_iff_mem.2 ⟨_, mem_eval.2 ⟨hr, rfl⟩⟩

end SingleTapeTM

end DiagonaLean.Foundations.Computability
