/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.KleeneAlgebra.MachineEncoding.Transition
import DiagonaLean.Foundations.KleeneAlgebra.Completeness

@[expose] public section

/-! # Completeness for Turing machines

If the machine halts, then in pre-Kleene algebra `(s₀)_r R_M∗ ≤ Σ∗ (C_M + t)_r + Σ∗ Σ^≠ ρ`,
where `s₀` is the initial configuration word, `t` the halting one, `C_M` the set of running
configuration words, and `ρ` a term depending only on `M`. This is proved both for halting runs
of `dstep` and for Cslib's `SingleTapeTM.Outputs`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 16
-/
open scoped Computability

namespace DiagonaLean.Foundations.KleeneAlgebra.Enc

open Cslib.Turing TD FreePreKA

variable {Sym : Type} [Inhabited Sym] [Fintype Sym] {M : SingleTapeTM Sym}

variable (M) in
/-- The sum of the right copies of all cell letters. -/
noncomputable def Cr : TD (Letter Sym M.State) := ∑ o : Option Sym, R (FreeMonoid.of (Letter.cell o))

variable (M) in
/-- The sum of the right copies of all running head letters. -/
noncomputable def Hr : TD (Letter Sym M.State) :=
  ∑ p : M.State × Option Sym, R (FreeMonoid.of (Letter.head (some p.1) p.2))

variable (M) in
/-- `(C_M)_r`: right copies of running configuration words. -/
noncomputable def crun : TD (Letter Sym M.State) :=
  R (FreeMonoid.of .lend) * (Cr M)∗ * Hr M * (Cr M)∗ * R (FreeMonoid.of .rend)

/-- The right copy of a list of cells lies below `(Cr M)∗`. -/
theorem R_cells_le (a : List (Option Sym)) : R (w (cells a)) ≤ (Cr M)∗ := by
  rw [R, FreeMonoid.lift_apply]
  refine list_prod_le_kstar _ _ fun x hx => ?_
  simp only [FreeMonoid.toList_ofList, cells, List.map_map, List.mem_map, Function.comp] at hx
  obtain ⟨o, -, rfl⟩ := hx
  exact le_sum_of_mem (fun o => R (FreeMonoid.of (Letter.cell o))) (Finset.mem_univ o)

/-- The right copy of a running configuration word lies below `crun M`. -/
theorem R_wdF_le_crun (d : Data M) (hd : d.Running) : R (wdF d) ≤ crun M := by
  obtain ⟨_ | q, l, h, r⟩ := d
  · simp [Data.Running] at hd
  have : wdF (⟨some q, l, h, r⟩ : Data M) = FreeMonoid.of .lend * w (cells l.reverse) *
      FreeMonoid.of (.head (some q) h) * w (cells r) * FreeMonoid.of .rend := by
    apply FreeMonoid.toList.injective
    simp [wdF, wd, w, FreeMonoid.toList_mul, FreeMonoid.toList_of]
  rw [this, map_mul, map_mul, map_mul, map_mul, crun]
  refine mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl (R_cells_le _)) ?_)
    (R_cells_le _)) le_rfl
  exact le_sum_of_mem (fun p : M.State × Option Sym => R (FreeMonoid.of (Letter.head (some p.1) p.2)))
    (Finset.mem_univ (q, h))

variable [DecidableEq Sym] [DecidableEq M.State]

/-- **Theorem 16** (Turing machines), with an explicit residue. If the automaton of `R_M` has its
states below `b`, then with `ρ = Σ̈∗ b R_M∗`: whenever `dstep` runs for `n` steps from `d₀` and
then halts, the configuration word of `d₀` followed by `R_M∗` lies below
`Σ∗ (C_M + t)_r + Σ∗ Σ^≠ ρ`, with `t` the halting configuration word. -/
theorem le_err_of_halting_run {b : TD (Letter Sym M.State)} (hb : FiniteStateLe (RM M) b) :
    ∀ (d₀ : Data M) (n : ℕ),
    (∀ i < n, ((dstep M)^[i] d₀).Running) → ¬ ((dstep M)^[n] d₀).Running →
    R (wdF d₀) * (RM M)∗ ≤
      sig∗ * (crun M + R (wdF ((dstep M)^[n] d₀))) + err (sigAll∗ * b * (RM M)∗) := by
  obtain ⟨hrel, hρ⟩ := rel_RM_le hb
  intro d₀ n hrun hhalt
  let s : ℕ → FreeMonoid (Letter Sym M.State) := fun i => wdF ((dstep M)^[i] d₀)
  have hstep : ∀ i < n, ∀ v, SetSemiring.Mem (s i, v) (pl (RM M)) ↔ v = s (i + 1) := by
    intro i hi v
    rw [mem_RM]
    constructor
    · rintro ⟨d, -, hd⟩
      obtain ⟨h1, rfl⟩ := Prod.mk.inj hd
      have := wdF_injective h1
      subst this
      simp only [s, Function.iterate_succ_apply']
    · rintro rfl
      exact ⟨_, hrun i hi, by simp only [s, Function.iterate_succ_apply']⟩
  have hlast : ∀ v, ¬ SetSemiring.Mem (s n, v) (pl (RM M)) := by
    intro v hv
    obtain ⟨d, hd, he⟩ := (mem_RM _).1 hv
    rw [← wdF_injective (Prod.mk.inj he).1] at hd
    exact hhalt hd
  have := hrel.complete_of_trace_le hρ n s ⟨d₀, rfl⟩ hstep hlast
  refine this.trans (add_le_add (mul_le_mul' le_rfl ?_) le_rfl)
  refine sum_le_of_forall _ _ fun u hu => ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hu
  rcases Nat.lt_or_ge i n with hin | hin
  · exact le_add_right (R_wdF_le_crun _ (hrun i hin))
  · have : i = n := by rw [Finset.mem_range] at hi; omega
    subst this
    exact le_add_left le_rfl

/-- **Theorem 16** (Turing machines). There is `ρ`, depending only on `M`, such that whenever
`dstep` runs for `n` steps from `d₀` and then halts, the configuration word of `d₀` followed by
`R_M∗` lies below `Σ∗ (C_M + t)_r + Σ∗ Σ^≠ ρ`, with `t` the halting configuration word. -/
theorem exists_le_err_of_halting_run : ∃ ρ : TD (Letter Sym M.State), ∀ (d₀ : Data M) (n : ℕ),
    (∀ i < n, ((dstep M)^[i] d₀).Running) → ¬ ((dstep M)^[n] d₀).Running →
    R (wdF d₀) * (RM M)∗ ≤ sig∗ * (crun M + R (wdF ((dstep M)^[n] d₀))) + err ρ := by
  obtain ⟨b, hb⟩ := (finiteState_iff _).1 (finiteState_RM (M := M))
  exact ⟨_, le_err_of_halting_run hb⟩

omit [DecidableEq Sym] [DecidableEq M.State] in
/-- A Cslib run to `haltCfg output` is a `dstep` trace that runs for `m` steps and then halts. -/
theorem exists_halting_trace {input output : List Sym} (hout : M.Outputs input output) :
    ∃ m, (∀ i < m, ((dstep M)^[i] (initData input : Data M)).Running) ∧
      ¬ ((dstep M)^[m] (initData input : Data M)).Running ∧
      cfgOf ((dstep M)^[m] (initData input : Data M)) = M.haltCfg output := by
  set d₀ : Data M := initData input
  have hrun : Relation.ReflTransGen M.TransitionRelation (cfgOf d₀) (M.haltCfg output) := by
    rw [cfgOf_initData]; exact hout
  obtain ⟨n, hn⟩ := exists_iterate_of_reflTransGen d₀ hrun
  have hhn : ¬ ((dstep M)^[n] d₀).Running := by
    intro h
    have : ((dstep M)^[n] d₀).state = none := congrArg SingleTapeTM.Cfg.state hn
    simp [Data.Running, this] at h
  have hex : ∃ m, ¬ ((dstep M)^[m] d₀).Running := ⟨n, hhn⟩
  let m := Nat.find hex
  have hm : ¬ ((dstep M)^[m] d₀).Running := Nat.find_spec hex
  have hmn : m ≤ n := Nat.find_min' hex hhn
  have heq : (dstep M)^[n] d₀ = (dstep M)^[m] d₀ := by
    rw [show n = (n - m) + m by omega, Function.iterate_add_apply, iterate_halted _ hm]
  exact ⟨m, fun i hi => not_not.1 (Nat.find_min hex hi), hm, heq ▸ hn⟩

/-- **Theorem 16** for Cslib's `Outputs`: if `M` outputs `output` on `input`, then for some word
`t` encoding the halting configuration `haltCfg output`,
`(init input)_r R_M∗ ≤ Σ∗ (C_M + t)_r + Σ∗ Σ^≠ ρ`. -/
theorem exists_le_err_of_outputs : ∃ ρ : TD (Letter Sym M.State), ∀ input output : List Sym,
    M.Outputs input output → ∃ d : Data M, cfgOf d = M.haltCfg output ∧
      R (wdF (initData input : Data M)) * (RM M)∗ ≤ sig∗ * (crun M + R (wdF d)) + err ρ := by
  obtain ⟨ρ, hρ⟩ := exists_le_err_of_halting_run (M := M)
  refine ⟨ρ, fun input output hout => ?_⟩
  obtain ⟨m, hlt, hm, hcfg⟩ := exists_halting_trace hout
  exact ⟨_, hcfg, hρ _ m hlt hm⟩

end DiagonaLean.Foundations.KleeneAlgebra.Enc
