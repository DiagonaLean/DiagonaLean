/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.TM.Syntax
import DiagonaLean.Halt.Basic

@[expose] public section

/-! # Halting versus the language model

Dropping the halting term `T_a` from the right-hand side gives an inequality that captures
halting exactly, but only in the language model:

`M` halts on `w` **iff** `(init w)_r R_M∗ ≤ Σ∗ (C_M)_r + Σ∗ Σ^≠ ρ` *fails* in the language model.

* If `M` halts, the trace string ending in the halted word is prefix-shaped, so it avoids the error
  term, and its last word is not a running configuration (Theorem 15's argument,
  `TD.sound_of_trace`).
* If `M` runs forever, every string of `(init w)_r R_M∗` is one of two kinds. It may follow the
  actual run, in which case it has the form `(u, u c)` with `c` a running configuration word,
  which lies in `Σ∗ (C_M)_r`. Otherwise it picks a wrong step somewhere, so its left and right
  parts diverge (configuration words are prefix-free), which puts it in `Σ∗ Σ^≠ Σ̈∗`
  (Lemma 33).

This gives a many-one reduction from `HALT` to the complement of language-model inclusion
(`TM/Undecidable.lean`). It does not reach pre-KA *provability*: for a machine that runs forever,
whether the inequality is provable is left open, as in the paper.

## Main statements

* `Enc.halts_iff_exists_not_running`: Cslib halting in terms of `dstep`.
* `Enc.pl_le_of_forall_running`: the divergent case.
* `Enc.halts_iff_not_pl_le`: the equivalence.
* `Enc.halts_iff_not_pl_le_syntax`: the same for the expressions `lhsS`, `rhsHS`.
-/

open scoped Computability

namespace DiagonaLean.KAComm.Enc

open Cslib.Turing TD FreePreKA RExp DiagonaLean.Halt

/-! ### Prefix divergence -/

theorem diverge_append {α : Type*} {a b X Y : List α} (h₁ : ¬ a <+: b) (h₂ : ¬ b <+: a) :
    ¬ (a ++ X) <+: (b ++ Y) ∧ ¬ (b ++ Y) <+: (a ++ X) := by
  obtain ⟨s₀, c, s₁, c', u₁, hne, rfl, rfl⟩ := TD.List.exists_diverge a b h₁ h₂
  constructor <;> intro h <;>
    simp only [List.append_assoc, List.cons_append, List.prefix_append_right_inj,
      List.cons_prefix_cons] at h
  exacts [hne h.1, hne h.1.symm]

/-- A string whose two sides diverge lies in `Σ∗ Σ^≠ Σ̈∗`. -/
theorem mem_err_of_diverge {A : Type*} [Fintype A] [DecidableEq A] (x : W A)
    (h₁ : ¬ x.2.toList <+: x.1.toList) (h₂ : ¬ x.1.toList <+: x.2.toList) :
    SetSemiring.Mem x (pl (err (sigAll : TD A)∗)) := by
  rw [← ofPair_le_iff_mem]
  have hx : ofPair x = R x.2 * L x.1 := (R_mul_L x.2 x.1).symm
  calc ofPair x = R x.2 * L x.1 * 1 := by rw [mul_one, hx]
    _ ≤ R x.2 * L x.1 * sigAll∗ := mul_le_mul' le_rfl (one_le_kstar' _)
    _ ≤ err sigAll∗ := lemma33' _ _ h₁ h₂

variable {Sym : Type} [Inhabited Sym] [Fintype Sym] {M : SingleTapeTM Sym}

/-! ### Halting in terms of `dstep` -/

theorem toList_wdF (d : Data M) : (wdF d).toList = wd d := rfl

theorem reflTransGen_iterate (d : Data M) (n : ℕ) :
    Relation.ReflTransGen M.TransitionRelation (cfgOf d) (cfgOf ((dstep M)^[n] d)) := by
  induction n generalizing d with
  | zero => exact .refl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    by_cases hd : d.Running
    · exact .head (step_cfgOf d hd) (ih _)
    · rw [dstep_halted d hd]; exact ih d

theorem halts_iff_exists_not_running (w : List Sym) :
    Halts M w ↔ ∃ n, ¬ ((dstep M)^[n] (initData w : Data M)).Running := by
  constructor
  · rintro ⟨tape, h⟩
    rw [← cfgOf_initData] at h
    obtain ⟨n, hn⟩ := exists_iterate_of_reflTransGen _ h
    refine ⟨n, fun hr => ?_⟩
    have : ((dstep M)^[n] (initData w : Data M)).state = none := congrArg SingleTapeTM.Cfg.state hn
    simp [Data.Running, this] at hr
  · rintro ⟨n, hn⟩
    have h := reflTransGen_iterate (initData w : Data M) n
    rw [cfgOf_initData] at h
    have hs : ((dstep M)^[n] (initData w : Data M)).state = none := by
      simpa [Data.Running] using hn
    exact ⟨_, by rwa [cfgOf, hs] at h⟩

/-! ### The divergent case -/

/-- Strings of a non-halting run from `d`: they follow the run and end in a running word, or their
two sides diverge. -/
def RunShape (x : W (Letter Sym M.State)) : Prop :=
  (∃ (u : FreeMonoid (Letter Sym M.State)) (d : Data M), d.Running ∧ x = (u, u * wdF d)) ∨
    (¬ x.2.toList <+: x.1.toList ∧ ¬ x.1.toList <+: x.2.toList)

theorem runShape_of_mem (l : List (W (Letter Sym M.State)))
    (hl : ∀ y ∈ l, SetSemiring.Mem y (pl (RM M))) :
    ∀ d : Data M, (∀ i, ((dstep M)^[i] d).Running) → RunShape ((1, wdF d) * l.prod) := by
  induction l with
  | nil =>
    intro d hd
    exact Or.inl ⟨1, d, hd 0, by simp⟩
  | cons y l ih =>
    intro d hd
    obtain ⟨d', -, rfl⟩ := (mem_RM y).1 (hl y List.mem_cons_self)
    have ih' := ih fun z hz => hl z (List.mem_cons_of_mem _ hz)
    rw [List.prod_cons]
    by_cases hdd : d' = d
    · subst hdd
      have hrec := ih' (dstep M d') fun i => by
        simpa only [Function.iterate_succ_apply] using hd (i + 1)
      have hx : ((1, wdF d') : W _) * ((wdF d', wdF (dstep M d')) * l.prod) =
          (wdF d', wdF d') * ((1, wdF (dstep M d')) * l.prod) := by
        refine Prod.ext ?_ ?_ <;> simp
      rw [hx]
      rcases hrec with ⟨u, e, he, hq⟩ | ⟨h1, h2⟩
      · refine Or.inl ⟨wdF d' * u, e, he, ?_⟩
        rw [hq]; refine Prod.ext ?_ ?_ <;> simp [mul_assoc]
      · refine Or.inr ⟨?_, ?_⟩ <;>
          simpa only [Prod.fst_mul, Prod.snd_mul, FreeMonoid.toList_mul,
            List.prefix_append_right_inj]
    · refine Or.inr ?_
      have hp1 : ¬ wd d <+: wd d' := fun h => hdd (prefixFree h).symm
      have hp2 : ¬ wd d' <+: wd d := fun h => hdd (prefixFree h)
      have := diverge_append (X := (wdF (dstep M d') * l.prod.2).toList)
        (Y := l.prod.1.toList) hp1 hp2
      simpa only [Prod.fst_mul, Prod.snd_mul, one_mul, FreeMonoid.toList_mul, toList_wdF,
        mul_assoc] using this

variable [DecidableEq Sym] [DecidableEq M.State]

/-- **The divergent case.** If the run from `d₀` never halts, then in the language model
`(s₀)_r R_M∗ ≤ Σ∗ (C_M)_r + Σ∗ Σ^≠ ρ`, for any `ρ` whose language is everything. -/
theorem pl_le_of_forall_running (d₀ : Data M) (hrun : ∀ i, ((dstep M)^[i] d₀).Running)
    {ρ : TD (Letter Sym M.State)} (hρ : pl (sigAll : TD _)∗ ≤ pl ρ) :
    pl (R (wdF d₀) * (RM M)∗) ≤ pl (sig∗ * crun M + err ρ) := by
  refine (SetSemiring.le_iff _ _).2 fun x hx => ?_
  rw [pl_mul, SetSemiring.mem_mul] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [pl_R, mem_single] at ha
  subst ha
  rw [pl_kstar, SetSemiring.mem_kstar] at hb
  obtain ⟨l, hl, rfl⟩ := hb
  rw [pl_add, SetSemiring.mem_add]
  rcases runShape_of_mem l hl d₀ hrun with ⟨u, d, hd, hx⟩ | ⟨h1, h2⟩
  · refine Or.inl ?_
    rw [hx, pl_mul, SetSemiring.mem_mul]
    refine ⟨(u, u), (mem_sig_kstar _).2 ⟨u, rfl⟩, (1, wdF d), ?_, by simp⟩
    rw [← ofPair_le_iff_mem, ← R_eq_ofPair]
    exact R_wdF_le_crun d hd
  · refine Or.inr ?_
    have hle : pl (err (sigAll : TD (Letter Sym M.State))∗) ≤ pl (err ρ) := by
      simp only [err, pl_mul]
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hρ)
    exact (SetSemiring.le_iff _ _).1 hle _ (mem_err_of_diverge _ h1 h2)

/-- **Halting is the failure of a language-model inequality.** For any `ρ` whose language is
everything, `M` halts on `w` iff `(init w)_r R_M∗ ≤ Σ∗ (C_M)_r + Σ∗ Σ^≠ ρ` fails in the model. -/
theorem halts_iff_not_pl_le (w : List Sym) {ρ : TD (Letter Sym M.State)}
    (hρ : pl (sigAll : TD _)∗ ≤ pl ρ) :
    Halts M w ↔ ¬ pl (R (wdF (initData w : Data M)) * (RM M)∗) ≤ pl (sig∗ * crun M + err ρ) := by
  rw [halts_iff_exists_not_running]
  constructor
  · intro hex hle
    set d₀ : Data M := initData w
    let m := Nat.find hex
    have hm : ¬ ((dstep M)^[m] d₀).Running := Nat.find_spec hex
    have hlt : ∀ i < m, ((dstep M)^[i] d₀).Running := fun i hi => not_not.1 (Nat.find_min hex hi)
    let s : ℕ → FreeMonoid (Letter Sym M.State) := fun i => wdF ((dstep M)^[i] d₀)
    have hstep : ∀ i < m, SetSemiring.Mem (s i, s (i + 1)) (pl (RM M)) := fun i hi =>
      (mem_RM _).2 ⟨_, hlt i hi, by simp only [s, Function.iterate_succ_apply']⟩
    have hX : ∀ x, SetSemiring.Mem x (pl (crun M)) → x.1 = 1 := fun x hx => by
      obtain ⟨_, _, _, _, rfl⟩ := mem_crun x hx; rfl
    have hn := sound_of_trace (RM M) (crun M) hX m s hstep
      (hle.trans (by rw [pl_add, pl_add]; exact add_le_add le_rfl (pl_err_le ρ)))
    exact not_mem_crun _ hm hn
  · intro hle
    by_contra hex
    push Not at hex
    exact hle (pl_le_of_forall_running _ hex hρ)

/-! ### The syntax-level form -/

variable [Encodable Sym] [Encodable M.State]

variable (M) in
/-- The right-hand side without a halting term: `Σ∗ (C_M)_r + Σ∗ Σ^≠ ρ_M`. -/
def rhsHS : Ex M :=
  plus (mul (star (sigS M)) (crunS M)) (mul (star (sigS M)) (mul (sigNeS M) (rhoS M)))

theorem mk_rhsHS : (mk (rhsHS M) : TD _) =
    sig∗ * crun M + err (sigAll∗ * mk (bnd (rmS M)) * (RM M)∗) := by
  simp only [rhsHS, rhoS, err, mk_plus, mk_mul, mk_star, mk_sigS, mk_crunS, mk_sigNeS,
    mk_sigAllS, mk_rmS]

omit [DecidableEq Sym] [DecidableEq M.State] in
/-- The language of `ρ_M` is everything. -/
theorem pl_sigAll_le_rho :
    pl (sigAll : TD (Letter Sym M.State))∗ ≤ pl (sigAll∗ * mk (bnd (rmS M)) * (RM M)∗) := by
  refine (SetSemiring.le_iff _ _).2 fun x hx => ?_
  rw [pl_mul, pl_mul, SetSemiring.mem_mul]
  refine ⟨x, (SetSemiring.mem_mul _ _ _).2 ⟨x, hx, 1, ?_, mul_one x⟩, 1, ?_, mul_one x⟩
  · exact (nullable_mk _).2 (nu_bnd _)
  · rw [pl_kstar, SetSemiring.mem_kstar]; exact ⟨[], by simp, rfl⟩

/-- **Halting, as syntax.** `M` halts on `w` iff `lhsS ≤ rhsHS` fails in the language model. -/
theorem halts_iff_not_pl_le_syntax (w : List Sym) :
    Halts M w ↔ ¬ pl (mk (lhsS M w) : TD _) ≤ pl (mk (rhsHS M)) := by
  rw [mk_lhsS, mk_rhsHS]
  exact halts_iff_not_pl_le w pl_sigAll_le_rho

end DiagonaLean.KAComm.Enc
