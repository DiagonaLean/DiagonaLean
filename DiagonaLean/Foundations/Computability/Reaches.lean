/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # Reaching a stopping configuration is recursively enumerable

A machine given by a step function `step : σ → Option σ` reaches `t` from `s` iff `t` is the
configuration after some number `n` of steps (`reflTransGen_iff_iterStep`). If the step function,
the start configuration and the stopping test are primitive recursive in the instance, then
whether the machine reaches a stopping configuration is recursively enumerable: search for `n`
(`REPred.of_reaches`). The halting problems of two-counter machines (`CM2.rePred`) and of list
machines (`ListHalt.rePred`) are instances.

## Main statements

* `reflTransGen_iff_iterStep`: reaching `t` is being the configuration after some number of
  steps.
* `REPred.of_reaches`: reaching a stopping configuration is recursively enumerable.
-/

namespace DiagonaLean.Foundations.Computability

variable {σ : Type*}

/-- The configuration after `n` steps of `step` from `s`, or `none` once a step fails. -/
def iterStep (step : σ → Option σ) (n : ℕ) (s : σ) : Option σ :=
  (fun o => o.bind step)^[n] (some s)

/-- `step` reaches `t` from `s` iff `t` is the configuration after some number of steps. -/
theorem reflTransGen_iff_iterStep {step : σ → Option σ} {s t : σ} :
    Relation.ReflTransGen (fun x y => step x = some y) s t ↔ ∃ n, iterStep step n s = some t := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, by
        simp only [iterStep, Function.iterate_succ_apply'] at hn ⊢
        rw [hn]
        exact hbc⟩
  · rintro ⟨n, hn⟩
    induction n generalizing t with
    | zero => exact (Option.some.inj hn) ▸ .refl
    | succ n ih =>
      simp only [iterStep, Function.iterate_succ_apply', Option.bind_eq_some_iff] at hn
      obtain ⟨b, hb, hbt⟩ := hn
      exact .tail (ih hb) hbt

/-- **Reaching a stopping configuration is recursively enumerable**: if the step function, the
start configuration and the stopping test are primitive recursive in the instance, search for the
number of steps. -/
theorem _root_.REPred.of_reaches {α : Type*} [Primcodable α] [Primcodable σ]
    {step : α → σ → Option σ} {start : α → σ} {stop : α → σ → Prop}
    (hstep : Primrec fun x : α × σ => step x.1 x.2) (hstart : Primrec start)
    (hstop : PrimrecPred fun x : α × σ => stop x.1 x.2) :
    REPred fun a => ∃ t, Relation.ReflTransGen (fun x y => step a x = some y) (start a) t ∧
      stop a t := by
  classical
  have hd : Primrec fun x : α × σ => decide (stop x.1 x.2) := hstop.decide
  have hit : Primrec fun x : α × ℕ => iterStep (step x.1) x.2 (start x.1) :=
    Primrec.nat_iterate .snd (Primrec.option_some.comp (hstart.comp .fst))
      (Primrec.option_bind .snd (hstep.comp ((Primrec.fst.comp (Primrec.fst.comp .fst)).pair
        .snd)).to₂).to₂
  refine REPred.of_exists_primrecPred
    (q := fun a n => (iterStep (step a) n (start a)).elim false (fun t => decide (stop a t)) =
      true) ?_ fun a => ?_
  · refine (Primrec.eq.comp (Primrec.option_casesOn hit (.const false)
      (hd.comp ((Primrec.fst.comp .fst).pair .snd)).to₂) (.const true)).of_eq fun x => ?_
    cases iterStep (step x.1) x.2 (start x.1) <;> rfl
  · simp only [reflTransGen_iff_iterStep]
    constructor
    · rintro ⟨t, ⟨n, hn⟩, ht⟩
      exact ⟨n, by simp [hn, ht]⟩
    · rintro ⟨n, hn⟩
      cases h : iterStep (step a) n (start a) with
      | none => simp [h] at hn
      | some t => exact ⟨t, ⟨n, h⟩, by simpa [h] using hn⟩

end DiagonaLean.Foundations.Computability
