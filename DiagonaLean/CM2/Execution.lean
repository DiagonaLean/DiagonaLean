/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Mathlib.Computability.RE
import DiagonaLean.CM2.Basic
import DiagonaLean.Foundations.Computability.PrimrecRec

@[expose] public section

/-! # Halting of two-counter machines is semi-decidable

`run p s n` is the configuration after at most `n` steps. The machine halts iff some run leaves
the program (`haltsFrom_iff_exists_bound`), so halting from a configuration is recursively
enumerable (`rePred_haltsFrom`).
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

/-- The machine halts from `s` iff after some number of steps the address is outside the
program. -/
theorem haltsFrom_iff_exists_bound (p : List Instr) (s : Config) :
    HaltsFrom p s ↔ ∃ n, p.length ≤ (run p s n).pc := by
  constructor
  · rintro ⟨t, hr, ht⟩
    have reachesRun : ∃ n, run p s n = t := by
      clear ht
      induction hr with
      | refl => exact ⟨0, rfl⟩
      | tail _ h ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, by simp [run, hn, h]⟩
    obtain ⟨n, rfl⟩ := reachesRun
    exact ⟨n, ht⟩
  · rintro ⟨n, hn⟩
    refine ⟨_, ?_, hn⟩
    clear hn
    induction n with
    | zero => exact .refl
    | succ n ih =>
      cases h : step p (run p s n) with
      | none => simpa [run, h] using ih
      | some t =>
        rw [run, h]
        exact ih.tail h

/-- **Halting of two-counter machines from a configuration is recursively enumerable.** -/
theorem rePred_haltsFrom : REPred fun x : List Instr × Config => HaltsFrom x.1 x.2 := by
  let test (x : List Instr × Config) (n : ℕ) :=
    decide (x.1.length ≤ (run x.1 x.2 n).pc)
  have ht : Primrec₂ test := by
    unfold test Primrec₂
    have hr : Primrec fun y : (List Instr × Config) × ℕ => run y.1.1 y.1.2 y.2 := run_primrec
    fun_prop
  have hs := Partrec.rfind (p := fun x n => Part.some (test x n)) ht.to_comp.partrec.to₂
  apply hs.dom_re.of_eq
  intro x
  exact (Nat.rfind_dom (p := fun n => Part.some (test x n))).trans (by
    rw [haltsFrom_iff_exists_bound]
    simp [test])

end DiagonaLean.CM2
