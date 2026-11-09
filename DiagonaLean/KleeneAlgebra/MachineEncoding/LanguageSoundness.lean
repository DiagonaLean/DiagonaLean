/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.MachineEncoding.TraceCompleteness
import DiagonaLean.KleeneAlgebra.Soundness

@[expose] public section

/-! # Soundness for Turing machines (Theorem 15) and the algebraic core of undecidability

**Theorem 15.** If `M` runs from `d₀` and halts at `dₙ`, and the *language* inequality

`(s₀)_r R_M∗ ≤ Σ∗ (C_M + t)_r + Σ∗ Σ^≠ Σ̈∗`

holds, then `t` is the word of `dₙ`.

Together with Theorem 16 this gives the algebraic core of the undecidability result: for a halting
run there is `ρ` such that the pre-KA inequality `(s₀)_r R_M∗ ≤ Σ∗ (C_M + t)_r + Σ∗ Σ^≠ ρ` holds
**iff** `t` is the halting configuration word. So deciding these inequalities would decide what a
halting machine outputs.

## Main statements

* `Enc.mem_crun`: the strings of `(C_M)_r` are right copies of running configuration words.
* `Enc.wdF_eq_of_pl_le`, `Enc.exists_wdF_of_outputs_of_pl_le`.
* `Enc.le_iff_halting`, `Enc.le_iff_outputs`: the soundness/completeness combination.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 15, 16, 18
-/

open scoped Computability

namespace DiagonaLean.KAComm.Enc

open Cslib.Turing TD FreePreKA

variable {Sym : Type} [Inhabited Sym] [Fintype Sym] {M : SingleTapeTM Sym}

/-! ### The language of `(C_M)_r` -/

theorem mem_Cr_kstar (x : W (Letter Sym M.State)) (hx : SetSemiring.Mem x (pl (Cr M)∗)) :
    ∃ c : List (Option Sym), x = (1, w (cells c)) := by
  rw [pl_kstar, SetSemiring.mem_kstar] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons y l ih =>
    have hy := hl y List.mem_cons_self
    rw [Cr, mem_pl_sum] at hy
    obtain ⟨o, -, hy⟩ := hy
    rw [pl_R, mem_single] at hy
    obtain ⟨c, hc⟩ := ih fun z hz => hl z (List.mem_cons_of_mem _ hz)
    refine ⟨o :: c, ?_⟩
    rw [List.prod_cons, hc, hy]
    rfl

theorem mem_Hr (x : W (Letter Sym M.State)) (hx : SetSemiring.Mem x (pl (Hr M))) :
    ∃ q h, x = (1, FreeMonoid.of (Letter.head (some q) h)) := by
  rw [Hr, mem_pl_sum] at hx
  obtain ⟨⟨q, h⟩, -, hx⟩ := hx
  rw [pl_R, mem_single] at hx
  exact ⟨q, h, hx⟩

/-- Strings of `(C_M)_r` are right copies of running configuration words. -/
theorem mem_crun (x : W (Letter Sym M.State)) (hx : SetSemiring.Mem x (pl (crun M))) :
    ∃ (a : List (Option Sym)) (q : M.State) (h : Option Sym) (b : List (Option Sym)),
      x = (1, w (.lend :: (cells a ++ .head (some q) h :: (cells b ++ [.rend])))) := by
  simp only [crun, pl_mul, SetSemiring.mem_mul, pl_R, mem_single] at hx
  obtain ⟨_, ⟨_, ⟨_, ⟨_, rfl, y, hy, rfl⟩, z, hz, rfl⟩, u, hu, rfl⟩, _, rfl, rfl⟩ := hx
  obtain ⟨a, rfl⟩ := mem_Cr_kstar y hy
  obtain ⟨q, h, rfl⟩ := mem_Hr z hz
  obtain ⟨b, rfl⟩ := mem_Cr_kstar u hu
  refine ⟨a, q, h, b, ?_⟩
  simp only [Prod.mk_mul_mk, mul_one]
  congr 1
  apply FreeMonoid.toList.injective
  simp [w, FreeMonoid.toList_mul, FreeMonoid.toList_of]

theorem fst_eq_one_of_mem_crun_add (t : FreeMonoid (Letter Sym M.State))
    (x : W (Letter Sym M.State)) (hx : SetSemiring.Mem x (pl (crun M + R t))) : x.1 = 1 := by
  rw [pl_add, SetSemiring.mem_add] at hx
  rcases hx with hx | hx
  · obtain ⟨a, q, h, b, rfl⟩ := mem_crun x hx; rfl
  · rw [pl_R, mem_single] at hx; rw [hx]

/-- A halted configuration word is not in `C_M`. -/
theorem not_mem_crun (d : Data M) (hd : ¬ d.Running) :
    ¬ SetSemiring.Mem ((1 : FreeMonoid _), wdF d) (pl (crun M)) := by
  intro hx
  obtain ⟨a, q, h, b, he⟩ := mem_crun _ hx
  have h2 := congrArg FreeMonoid.toList (congrArg Prod.snd he)
  simp only [wdF, wd, w, FreeMonoid.toList_ofList, List.cons.injEq, true_and] at h2
  obtain ⟨-, hq, -⟩ := cells_append_head_inj h2
  exact hd (by simp [Data.Running, hq])

/-! ### Theorem 15 -/

variable [DecidableEq Sym] [DecidableEq M.State]

/-- **Theorem 15** (soundness). If `M` runs for `n` steps from `d₀` and halts, and the language
inequality `(s₀)_r R_M∗ ≤ Σ∗ (C_M + t)_r + Σ∗ Σ^≠ Σ̈∗` holds, then `t` is the halting
configuration word. -/
theorem wdF_eq_of_pl_le (d₀ : Data M) (n : ℕ) (hrun : ∀ i < n, ((dstep M)^[i] d₀).Running)
    (hhalt : ¬ ((dstep M)^[n] d₀).Running) (t : FreeMonoid (Letter Sym M.State))
    (h : pl (R (wdF d₀) * (RM M)∗) ≤ pl (sig∗ * (crun M + R t) + err (sigAll : TD _)∗)) :
    wdF ((dstep M)^[n] d₀) = t := by
  let s : ℕ → FreeMonoid (Letter Sym M.State) := fun i => wdF ((dstep M)^[i] d₀)
  have hstep : ∀ i < n, SetSemiring.Mem (s i, s (i + 1)) (pl (RM M)) := fun i hi =>
    (mem_RM _).2 ⟨_, hrun i hi, by simp only [s, Function.iterate_succ_apply']⟩
  have hn := sound_of_trace (RM M) (crun M + R t) (fst_eq_one_of_mem_crun_add t) n s hstep h
  rw [pl_add, SetSemiring.mem_add] at hn
  rcases hn with hn | hn
  · exact absurd hn (not_mem_crun _ hhalt)
  · rw [pl_R, mem_single] at hn
    exact congrArg Prod.snd hn

/-- **Theorem 15** for Cslib's `Outputs`: the language inequality forces `t` to be the word of a
list-level configuration decoding to `haltCfg output`. -/
theorem exists_wdF_of_outputs_of_pl_le {input output : List Sym} (hout : M.Outputs input output)
    (t : FreeMonoid (Letter Sym M.State))
    (h : pl (R (wdF (initData input : Data M)) * (RM M)∗) ≤
      pl (sig∗ * (crun M + R t) + err (sigAll : TD _)∗)) :
    ∃ d : Data M, t = wdF d ∧ cfgOf d = M.haltCfg output := by
  obtain ⟨m, hlt, hm, hcfg⟩ := exists_halting_trace hout
  exact ⟨_, (wdF_eq_of_pl_le _ m hlt hm t h).symm, hcfg⟩

/-! ### Soundness and completeness together -/

theorem pl_err_le (ρ : TD (Letter Sym M.State)) : pl (err ρ) ≤ pl (err (sigAll : TD _)∗) := by
  simp only [err, pl_mul]
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (pl_le_sigAll_kstar ρ))

/-- **Soundness and completeness.** There is `ρ`, depending only on `M`, such that along any
halting run `d₀ → ⋯ → dₙ`, the pre-KA inequality `(s₀)_r R_M∗ ≤ Σ∗ (C_M + t)_r + Σ∗ Σ^≠ ρ`
holds iff `t` is the word of `dₙ`. It holds in the language model iff it holds in `T Σ̈`. -/
theorem le_iff_halting : ∃ ρ : TD (Letter Sym M.State), ∀ (d₀ : Data M) (n : ℕ),
    (∀ i < n, ((dstep M)^[i] d₀).Running) → ¬ ((dstep M)^[n] d₀).Running →
    ∀ t : FreeMonoid (Letter Sym M.State),
      (R (wdF d₀) * (RM M)∗ ≤ sig∗ * (crun M + R t) + err ρ ↔ wdF ((dstep M)^[n] d₀) = t) ∧
      (pl (R (wdF d₀) * (RM M)∗) ≤ pl (sig∗ * (crun M + R t) + err ρ) ↔
        wdF ((dstep M)^[n] d₀) = t) := by
  obtain ⟨ρ, hρ⟩ := exists_le_err_of_halting_run (M := M)
  refine ⟨ρ, fun d₀ n hrun hhalt t => ?_⟩
  have hsound : pl (R (wdF d₀) * (RM M)∗) ≤ pl (sig∗ * (crun M + R t) + err ρ) →
      wdF ((dstep M)^[n] d₀) = t := fun h =>
    wdF_eq_of_pl_le d₀ n hrun hhalt t (h.trans (by rw [pl_add, pl_add]; exact add_le_add le_rfl (pl_err_le ρ)))
  have hcomp : wdF ((dstep M)^[n] d₀) = t →
      R (wdF d₀) * (RM M)∗ ≤ sig∗ * (crun M + R t) + err ρ := by
    rintro rfl; exact hρ d₀ n hrun hhalt
  exact ⟨⟨fun h => hsound (pl_mono h), hcomp⟩, ⟨hsound, fun h => pl_mono (hcomp h)⟩⟩

/-- **Soundness and completeness** for Cslib's `Outputs`. There is `ρ` such that whenever `M`
outputs `output` on `input`:
* the inequality holds for the word `t` of some configuration decoding to `haltCfg output`;
* whenever it holds for `t`, even only in the language model, `t` is the word of a configuration
  decoding to `haltCfg output`. -/
theorem le_iff_outputs : ∃ ρ : TD (Letter Sym M.State), ∀ input output : List Sym,
    M.Outputs input output →
      (∃ d : Data M, cfgOf d = M.haltCfg output ∧
        R (wdF (initData input : Data M)) * (RM M)∗ ≤ sig∗ * (crun M + R (wdF d)) + err ρ) ∧
      ∀ t : FreeMonoid (Letter Sym M.State),
        pl (R (wdF (initData input : Data M)) * (RM M)∗) ≤ pl (sig∗ * (crun M + R t) + err ρ) →
          ∃ d : Data M, t = wdF d ∧ cfgOf d = M.haltCfg output := by
  obtain ⟨ρ, hρ⟩ := le_iff_halting (M := M)
  refine ⟨ρ, fun input output hout => ?_⟩
  obtain ⟨m, hlt, hm, hcfg⟩ := exists_halting_trace hout
  refine ⟨⟨_, hcfg, ((hρ _ m hlt hm _).1.2 rfl)⟩, fun t ht => ?_⟩
  exact ⟨_, ((hρ _ m hlt hm t).2.1 ht).symm, hcfg⟩

end DiagonaLean.KAComm.Enc
