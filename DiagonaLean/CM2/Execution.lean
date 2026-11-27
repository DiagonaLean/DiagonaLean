/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CM2.Basic
import DiagonaLean.Foundations.Computability.PrimrecRec
import Mathlib.Computability.RE

@[expose] public section

/-! # Halting of two-counter machines is semi-decidable

`run p s n` is the configuration after at most `n` steps. The machine halts iff some run leaves
the program (`halting_iff_exists_bound`), so halting is recursively enumerable
(`rePred_halting`).
-/

namespace DiagonaLean.CM2

open DiagonaLean.Foundations.Computability

/-- `execute` is primitive recursive. -/
theorem execute_primrec : Primrec₂ execute := by primrec_rec

/-- `step` is primitive recursive. -/
theorem step_primrec : Primrec₂ step := by
  unfold Primrec₂ step
  exact prim_optionMap (by fun_prop) (execute_primrec.comp (by fun_prop) (by fun_prop))

/-- `step` of a primitive recursive program and configuration is primitive recursive. -/
@[fun_prop] theorem prim_step {α : Type*} [Primcodable α] {p : α → List Instr} {s : α → Config}
    (hp : Primrec p) (hs : Primrec s) : Primrec fun x => step (p x) (s x) :=
  step_primrec.comp hp hs

/-- The configuration after `n` steps, or the last configuration if the machine halts earlier. -/
def run (p : List Instr) (s : Config) : ℕ → Config
  | 0 => s
  | n + 1 => let t := run p s n; (step p t).getD t

/-- `run` is primitive recursive. -/
theorem run_primrec : Primrec₂ (fun (x : List Instr × Config) n => run x.1 x.2 n) := by
  primrec_rec

/-- The machine halts iff after some number of steps the program counter is outside the
program. -/
theorem halting_iff_exists_bound (p : List Instr) (s : Config) :
    Halting (p, s) ↔ ∃ n, p.length ≤ (run p s n).1 := by
  change (StateTransition.eval (step p) s).Dom ↔ _
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨hr, he⟩ := StateTransition.mem_eval.mp ht
    have reachesRun : ∃ n, run p s n = t := by
      clear ht he
      induction hr with
      | refl => exact ⟨0, rfl⟩
      | tail _ h ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, by simp [run, hn, Option.mem_def.mp h]⟩
    obtain ⟨n, rfl⟩ := reachesRun
    exact ⟨n, (step_eq_none_iff p _).mp he⟩
  · rintro ⟨n, hn⟩
    refine ⟨_, StateTransition.mem_eval.mpr ⟨?_, (step_eq_none_iff p _).mpr hn⟩⟩
    clear hn
    induction n with
    | zero => exact .refl
    | succ n ih =>
      cases h : step p (run p s n) with
      | none => simpa [run, h] using ih
      | some t =>
        rw [run, h]
        exact ih.tail h

/-- **Halting of two-counter machines is recursively enumerable.** -/
theorem rePred_halting : REPred Halting := by
  let test (x : List Instr × Config) (n : ℕ) :=
    decide (x.1.length ≤ (run x.1 x.2 n).1)
  have ht : Primrec₂ test := by
    unfold test Primrec₂
    have hr : Primrec fun y : (List Instr × Config) × ℕ => run y.1.1 y.1.2 y.2 := run_primrec
    fun_prop
  have hs := Partrec.rfind (p := fun x n => Part.some (test x n)) ht.to_comp.partrec.to₂
  apply hs.dom_re.of_eq
  intro x
  change (Nat.rfind fun n => Part.some (test x n)).Dom ↔ Halting (x.1, x.2)
  exact (Nat.rfind_dom (p := fun n => Part.some (test x n))).trans (by
    rw [halting_iff_exists_bound]
    simp [test])

end DiagonaLean.CM2
