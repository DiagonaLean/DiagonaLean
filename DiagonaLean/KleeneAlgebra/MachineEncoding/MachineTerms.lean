/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.MachineEncoding.LanguageSoundness
import DiagonaLean.KleeneAlgebra.Syntax
import Mathlib.Tactic.DeriveEncodable

@[expose] public section

/-! # The reduction terms as syntax

The terms of Theorems 15 and 16, written as expressions (`RExp`) computed from the transition
table of `M`. Every `Finset.univ` sum becomes a `sumL` over `enumL`, and the residue
`ρ_M = Σ̈∗ bnd(R_M) R_M∗` is explicit, using the syntax-directed bound `bnd` of `Syntax.lean`.

Instead of a single halting word `t`, the right-hand side uses `T_a`, the right copies of all
configuration words that decode to `haltCfg [a]`. `T_a` contains `⊢ ␣ⁱ [halt, a] ␣ʲ ⊣` for every
`i` and `j`, since list-level configurations may keep blank cells.

## Main statements

* `Enc.lhsS`, `Enc.rhsS`: the two sides `(init input)_r R_M∗` and
  `Σ∗ (C_M + T_a)_r + Σ∗ Σ^≠ ρ_M`.
* `Enc.le_of_outputs`: if `M` outputs `[a]` on `input`, the inequality is provable in `T Σ̈`.
* `Enc.not_pl_le_of_outputs`: if `M` outputs `[b]` with `b ≠ a`, it fails in the language model.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 15, 16, 18
-/

open scoped Computability

namespace DiagonaLean.KAComm.Enc

open Cslib.Turing TD FreePreKA RExp

deriving instance Encodable for Letter

variable {Sym : Type} [Inhabited Sym] [Fintype Sym] {M : SingleTapeTM Sym}

/-! ### Words as syntax -/

section words

variable {St : Type}

/-- Left copy of a word. -/
def lS (u : List (Letter Sym St)) : RExp (Letter Sym St ⊕ Letter Sym St) :=
  prodL (u.map fun a => sym (.inl a))

/-- Right copy of a word. -/
def rS (v : List (Letter Sym St)) : RExp (Letter Sym St ⊕ Letter Sym St) :=
  prodL (v.map fun a => sym (.inr a))

/-- The string `(u, v)`. -/
def pairS (u v : List (Letter Sym St)) : RExp (Letter Sym St ⊕ Letter Sym St) :=
  mul (lS u) (rS v)

omit [Inhabited Sym] [Fintype Sym] in
@[simp] theorem nu_lS_cons (a : Letter Sym St) (u : List (Letter Sym St)) :
    nu (lS (a :: u)) = false := by simp [lS, prodL, nu]

omit [Inhabited Sym] [Fintype Sym] in
@[simp] theorem guarded_lS (u : List (Letter Sym St)) : guarded (lS u) = true := by
  simp [lS, guarded]

omit [Inhabited Sym] [Fintype Sym] in
@[simp] theorem guarded_rS (u : List (Letter Sym St)) : guarded (rS u) = true := by
  simp [rS, guarded]

omit [Inhabited Sym] [Fintype Sym] in
@[simp] theorem guarded_pairS (u v : List (Letter Sym St)) : guarded (pairS u v) = true := by
  simp [pairS, guarded]

end words

theorem mk_lS (u : List (Letter Sym M.State)) : (mk (lS u) : TD _) = L (w u) := by
  rw [lS, mk_prodL, List.map_map, L, FreeMonoid.lift_apply, FreeMonoid.toList_ofList]; rfl

theorem mk_rS (u : List (Letter Sym M.State)) : (mk (rS u) : TD _) = R (w u) := by
  rw [rS, mk_prodL, List.map_map, R, FreeMonoid.lift_apply, FreeMonoid.toList_ofList]; rfl

theorem mk_pairS (u v : List (Letter Sym M.State)) :
    (mk (pairS u v) : TD _) = ofPair (w u, w v) := by
  rw [pairS, mk_mul, mk_lS, mk_rS]; rfl

theorem w_singleton (a : Letter Sym M.State) : w [a] = FreeMonoid.of a := rfl

/-! ### The halting term `T_a` -/

variable (M) in
/-- `T_a = ⊢ ␣∗ [halt, a] ␣∗ ⊣`, right copies of the words decoding to `haltCfg [a]`. -/
noncomputable def haltT (a : Sym) : TD (Letter Sym M.State) :=
  R (FreeMonoid.of .lend) * (R (FreeMonoid.of (Letter.cell none)))∗ *
    R (FreeMonoid.of (.head none (some a))) * (R (FreeMonoid.of (Letter.cell none)))∗ *
    R (FreeMonoid.of .rend)

theorem mem_blank_kstar (x : W (Letter Sym M.State))
    (hx : SetSemiring.Mem x (pl (R (FreeMonoid.of (Letter.cell none)))∗)) :
    ∃ c : List (Option Sym), x = (1, w (cells c)) := by
  rw [pl_kstar, SetSemiring.mem_kstar] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons y l ih =>
    have hy := hl y List.mem_cons_self
    rw [pl_R, mem_single] at hy
    obtain ⟨c, hc⟩ := ih fun z hz => hl z (List.mem_cons_of_mem _ hz)
    refine ⟨none :: c, ?_⟩
    rw [List.prod_cons, hc, hy]
    rfl

theorem mem_haltT (a : Sym) (x : W (Letter Sym M.State)) (hx : SetSemiring.Mem x (pl (haltT M a))) :
    ∃ c c' : List (Option Sym),
      x = (1, w (.lend :: (cells c ++ .head none (some a) :: (cells c' ++ [.rend])))) := by
  simp only [haltT, pl_mul, SetSemiring.mem_mul, pl_R, mem_single] at hx
  obtain ⟨_, ⟨_, ⟨_, ⟨_, rfl, y, hy, rfl⟩, _, rfl, rfl⟩, u, hu, rfl⟩, _, rfl, rfl⟩ := hx
  obtain ⟨c, rfl⟩ := mem_blank_kstar y (by rwa [pl_kstar])
  obtain ⟨c', rfl⟩ := mem_blank_kstar u (by rwa [pl_kstar])
  refine ⟨c, c', ?_⟩
  simp only [Prod.mk_mul_mk, mul_one]
  congr 1
  apply FreeMonoid.toList.injective
  simp [w, FreeMonoid.toList_mul, FreeMonoid.toList_of]

theorem fst_eq_one_of_mem_crun_haltT (a : Sym) (x : W (Letter Sym M.State))
    (hx : SetSemiring.Mem x (pl (crun M + haltT M a))) : x.1 = 1 := by
  rw [pl_add, SetSemiring.mem_add] at hx
  rcases hx with hx | hx
  · obtain ⟨_, _, _, _, rfl⟩ := mem_crun x hx; rfl
  · obtain ⟨_, _, rfl⟩ := mem_haltT a x hx; rfl

omit [Inhabited Sym] [Fintype Sym] in
theorem stk_eq_nil {l : List (Option Sym)} (h : stk l = StackTape.nil) : ∀ o ∈ l, o = none := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [stk_cons] at h
    rcases x with _ | x
    · rcases hs : stk l with ⟨_ | ⟨hd, tl⟩, hl⟩
      · intro o ho
        rcases List.mem_cons.1 ho with rfl | ho
        · rfl
        · exact ih hs o ho
      · rw [hs] at h
        exact absurd (congrArg StackTape.toList h) (by simp [StackTape.cons, StackTape.nil])
    · exact absurd (congrArg StackTape.toList h) (by simp [StackTape.cons, StackTape.nil])

theorem R_blanks_le {a : List (Option Sym)} (ha : ∀ o ∈ a, o = none) :
    R (w (cells a)) ≤ (R (FreeMonoid.of (Letter.cell none : Letter Sym M.State)))∗ := by
  rw [R, FreeMonoid.lift_apply]
  refine list_prod_le_kstar _ _ fun x hx => ?_
  simp only [FreeMonoid.toList_ofList, cells, List.map_map, List.mem_map, Function.comp] at hx
  obtain ⟨o, ho, rfl⟩ := hx
  rw [ha o ho]
  exact (FreeMonoid.lift_eval_of _ _).symm.le

/-- A configuration word decoding to `haltCfg [a]` lies below `T_a`. -/
theorem R_wdF_le_haltT {a : Sym} {d : Data M} (hd : cfgOf d = M.haltCfg [a]) :
    R (wdF d) ≤ haltT M a := by
  obtain ⟨st, l, h, r⟩ := d
  simp only [cfgOf, SingleTapeTM.haltCfg, BiTape.mk₁, SingleTapeTM.Cfg.mk.injEq,
    BiTape.mk.injEq] at hd
  obtain ⟨rfl, rfl, hl, hr⟩ := hd
  have hl' := stk_eq_nil hl
  have hr' := stk_eq_nil (l := r) hr
  have : wdF (⟨none, l, some a, r⟩ : Data M) = FreeMonoid.of .lend * w (cells l.reverse) *
      FreeMonoid.of (.head none (some a)) * w (cells r) * FreeMonoid.of .rend := by
    apply FreeMonoid.toList.injective
    simp [wdF, wd, w, FreeMonoid.toList_mul, FreeMonoid.toList_of]
  rw [this, map_mul, map_mul, map_mul, map_mul, haltT]
  exact mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl
    (R_blanks_le fun o ho => hl' o (List.mem_reverse.1 ho))) le_rfl) (R_blanks_le hr')) le_rfl

/-! ### The terms as syntax -/

section terms

variable [Encodable Sym] [Encodable M.State]

/-- Expressions over `Σ̈` for the machine `M`. -/
abbrev Ex (M : SingleTapeTM Sym) := RExp (Letter Sym M.State ⊕ Letter Sym M.State)

variable (M) in
/-- `C`, copy one tape cell. -/
def cS : Ex M := sumL ((enumL (Option Sym)).map fun o => pairS [.cell o] [.cell o])

variable (M) in
/-- `⊢ C∗ (u, v) C∗ ⊣`. -/
def ctxS (u v : List (Letter Sym M.State)) : Ex M :=
  mul (mul (mul (mul (pairS [.lend] [.lend]) (star (cS M))) (pairS u v)) (star (cS M)))
    (pairS [.rend] [.rend])

variable (M) in
/-- `⊢ C∗ (u, v)`. -/
def ctxRS (u v : List (Letter Sym M.State)) : Ex M :=
  mul (mul (pairS [.lend] [.lend]) (star (cS M))) (pairS u v)

variable (M) in
/-- `(u, v) C∗ ⊣`. -/
def ctxLS (u v : List (Letter Sym M.State)) : Ex M :=
  mul (mul (pairS u v) (star (cS M))) (pairS [.rend] [.rend])

variable (M) in
/-- The rewriting rule for state `q` and scanned symbol `h`. -/
def ruleS (q : M.State) (h : Option Sym) : Ex M :=
  match M.tr q h with
  | (⟨wr, none⟩, q') => ctxS M [.head (some q) h] [.head q' wr]
  | (⟨wr, some .right⟩, q') =>
    plus (sumL ((enumL (Option Sym)).map fun x =>
        ctxS M [.head (some q) h, .cell x] [.cell wr, .head q' x]))
      (ctxRS M [.head (some q) h, .rend] [.cell wr, .head q' none, .rend])
  | (⟨wr, some .left⟩, q') =>
    plus (sumL ((enumL (Option Sym)).map fun x =>
        ctxS M [.cell x, .head (some q) h] [.head q' x, .cell wr]))
      (ctxLS M [.lend, .head (some q) h] [.lend, .head q' none, .cell wr])

variable (M) in
/-- `R_M` (Definition 13). -/
def rmS : Ex M := sumL ((enumL (M.State × Option Sym)).map fun p => ruleS M p.1 p.2)

variable (M) in
/-- `Σ`, diagonal letters. -/
def sigS : Ex M := sumL ((enumL (Letter Sym M.State)).map fun a => pairS [a] [a])

variable (M) in
/-- `Σ̈`, all symbols. -/
def sigAllS : Ex M := sumL ((enumL (Letter Sym M.State ⊕ Letter Sym M.State)).map sym)

variable (M) in
/-- `Cr`, right copies of cells. -/
def crS : Ex M := sumL ((enumL (Option Sym)).map fun o => rS [.cell o])

variable (M) in
/-- `Hr`, right copies of running head letters. -/
def hrS : Ex M := sumL ((enumL (M.State × Option Sym)).map fun p => rS [.head (some p.1) p.2])

variable (M) in
/-- `(C_M)_r`. -/
def crunS : Ex M :=
  mul (mul (mul (mul (rS [.lend]) (star (crS M))) (hrS M)) (star (crS M))) (rS [.rend])

variable (M) in
/-- `T_a`. -/
def haltS (a : Sym) : Ex M :=
  mul (mul (mul (mul (rS [.lend]) (star (rS [.cell none]))) (rS [.head none (some a)]))
    (star (rS [.cell none]))) (rS [.rend])

variable (M) in
/-- The residue `ρ_M = Σ̈∗ bnd(R_M) R_M∗`. -/
def rhoS : Ex M := mul (mul (star (sigAllS M)) (bnd (rmS M))) (star (rmS M))

variable (M) in
/-- The left-hand side `(init input)_r R_M∗`. -/
def lhsS (input : List Sym) : Ex M := mul (rS (wd (initData input : Data M))) (star (rmS M))

/-! ### Interpretation in `T Σ̈` -/

omit [Encodable M.State] in
theorem mk_cS : (mk (cS M) : TD _) = C M := by
  rw [cS, mk_sumL, List.map_map, sum_enumL]
  simp only [Function.comp_def, mk_pairS, w_singleton]; rfl

omit [Encodable M.State] in
theorem mk_ctxS (u v : List (Letter Sym M.State)) : (mk (ctxS M u v) : TD _) = ctx u v := by
  simp only [ctxS, ctx, mk_mul, mk_star, mk_pairS, mk_cS]

omit [Encodable M.State] in
theorem mk_ctxRS (u v : List (Letter Sym M.State)) : (mk (ctxRS M u v) : TD _) = ctxR u v := by
  simp only [ctxRS, ctxR, mk_mul, mk_star, mk_pairS, mk_cS]

omit [Encodable M.State] in
theorem mk_ctxLS (u v : List (Letter Sym M.State)) : (mk (ctxLS M u v) : TD _) = ctxL u v := by
  simp only [ctxLS, ctxL, mk_mul, mk_star, mk_pairS, mk_cS]

omit [Encodable M.State] in
theorem mk_ruleS (q : M.State) (h : Option Sym) : (mk (ruleS M q h) : TD _) = rule M q h := by
  rcases htr : M.tr q h with ⟨⟨wr, _ | _ | _⟩, q'⟩ <;>
    simp only [ruleS, rule, htr, mk_plus, mk_sumL, List.map_map, sum_enumL, Function.comp_def,
      mk_ctxS, mk_ctxRS, mk_ctxLS]

theorem mk_rmS : (mk (rmS M) : TD _) = RM M := by
  rw [rmS, mk_sumL, List.map_map, sum_enumL]
  simp only [Function.comp_def, mk_ruleS]; rfl

theorem mk_sigS : (mk (sigS M) : TD _) = sig := by
  rw [sigS, mk_sumL, List.map_map, sum_enumL]
  simp only [Function.comp_def, mk_pairS, w_singleton]; rfl

theorem mk_sigAllS : (mk (sigAllS M) : TD _) = sigAll := by
  rw [sigAllS, mk_sumL, List.map_map, sum_enumL]; rfl

omit [Encodable M.State] in
theorem mk_crS : (mk (crS M) : TD _) = Cr M := by
  rw [crS, mk_sumL, List.map_map, sum_enumL]
  simp only [Function.comp_def, mk_rS, w_singleton]; rfl

theorem mk_hrS : (mk (hrS M) : TD _) = Hr M := by
  rw [hrS, mk_sumL, List.map_map, sum_enumL]
  simp only [Function.comp_def, mk_rS, w_singleton]; rfl

theorem mk_crunS : (mk (crunS M) : TD _) = crun M := by
  simp only [crunS, crun, mk_mul, mk_star, mk_rS, mk_crS, mk_hrS, w_singleton]

omit [Encodable Sym] [Encodable M.State] in
theorem mk_haltS (a : Sym) : (mk (haltS M a) : TD _) = haltT M a := by
  simp only [haltS, haltT, mk_mul, mk_star, mk_rS, w_singleton]

theorem mk_lhsS (input : List Sym) :
    (mk (lhsS M input) : TD _) = R (wdF (initData input : Data M)) * (RM M)∗ := by
  rw [lhsS, mk_mul, mk_star, mk_rS, mk_rmS]; rfl

theorem guarded_rmS : guarded (rmS M) = true := by
  have hc : nu (cS M) = false := by simp [cS, pairS, nu]
  have hcg : guarded (cS M) = true := by simp [cS]
  have hctx : ∀ u v, guarded (ctxS M u v) = true := fun u v => by simp [ctxS, guarded, hc, hcg]
  simp only [rmS, guarded_sumL, List.all_map, List.all_eq_true, Function.comp_apply]
  intro p _
  unfold ruleS
  split <;> simp [guarded, hctx, ctxRS, ctxLS, hc, hcg]

theorem finiteStateLe_RM : FiniteStateLe (RM M) (mk (bnd (rmS M))) :=
  mk_rmS (M := M) ▸ finiteStateLe_mk _ guarded_rmS

variable [DecidableEq Sym] [DecidableEq M.State]

variable (M) in
/-- `Σ^≠`. -/
def sigNeS : Ex M :=
  sumL ((enumL (Letter Sym M.State)).map fun a =>
    sumL (((enumL (Letter Sym M.State)).filter (· ≠ a)).map fun b =>
      mul (sym (.inl a)) (sym (.inr b))))

variable (M) in
/-- The right-hand side `Σ∗ (C_M + T_a)_r + Σ∗ Σ^≠ ρ_M`. -/
def rhsS (a : Sym) : Ex M :=
  plus (mul (star (sigS M)) (plus (crunS M) (haltS M a)))
    (mul (star (sigS M)) (mul (sigNeS M) (rhoS M)))

theorem mk_sigNeS : (mk (sigNeS M) : TD _) = sigNe := by
  rw [sigNeS, mk_sumL, List.map_map, sum_enumL]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Function.comp_apply, mk_sumL, List.map_map]
  exact sum_enumL_filter (· ≠ a) _

theorem mk_rhsS (a : Sym) : (mk (rhsS M a) : TD _) =
    sig∗ * (crun M + haltT M a) + err (sigAll∗ * mk (bnd (rmS M)) * (RM M)∗) := by
  simp only [rhsS, rhoS, err, mk_plus, mk_mul, mk_star, mk_sigS, mk_crunS, mk_haltS, mk_sigNeS,
    mk_sigAllS, mk_rmS]

/-! ### The two halves of the reduction -/

/-- If `M` outputs `[a]` on `input`, then `lhs ≤ rhs` is provable in `T Σ̈` (Theorem 16). -/
theorem le_of_outputs {input : List Sym} {a : Sym} (h : M.Outputs input [a]) :
    (mk (lhsS M input) : TD _) ≤ mk (rhsS M a) := by
  rw [mk_lhsS, mk_rhsS]
  obtain ⟨m, hlt, hm, hcfg⟩ := exists_halting_trace h
  exact (le_err_of_halting_run finiteStateLe_RM _ m hlt hm).trans
    (add_le_add (mul_le_mul' le_rfl (add_le_add le_rfl (R_wdF_le_haltT hcfg))) le_rfl)

/-- If `M` outputs `[b]` on `input` with `b ≠ a`, then `lhs ≤ rhs` fails in the language model
(Theorem 15). -/
theorem not_pl_le_of_outputs {input : List Sym} {a b : Sym} (h : M.Outputs input [b])
    (hab : a ≠ b) : ¬ pl (mk (lhsS M input) : TD _) ≤ pl (mk (rhsS M a)) := by
  rw [mk_lhsS, mk_rhsS]
  intro hle
  obtain ⟨m, hlt, hm, hcfg⟩ := exists_halting_trace h
  let s : ℕ → FreeMonoid (Letter Sym M.State) := fun i => wdF ((dstep M)^[i] (initData input))
  have hstep : ∀ i < m, SetSemiring.Mem (s i, s (i + 1)) (pl (RM M)) := fun i hi =>
    (mem_RM _).2 ⟨_, hlt i hi, by simp only [s, Function.iterate_succ_apply']⟩
  have hn := sound_of_trace (RM M) (crun M + haltT M a) (fst_eq_one_of_mem_crun_haltT a) m s hstep
    (hle.trans (by rw [pl_add, pl_add]; exact add_le_add le_rfl (pl_err_le _)))
  rw [pl_add, SetSemiring.mem_add] at hn
  rcases hn with hn | hn
  · exact not_mem_crun _ hm hn
  · obtain ⟨c, c', he⟩ := mem_haltT a _ hn
    have h2 := congrArg FreeMonoid.toList (congrArg Prod.snd he)
    simp only [s, wdF, wd, w, FreeMonoid.toList_ofList, List.cons.injEq, true_and] at h2
    obtain ⟨-, -, ho, -⟩ := cells_append_head_inj h2
    have hb : ((dstep M)^[m] (initData input : Data M)).h = some b :=
      congrArg (fun c : M.Cfg => c.BiTape.head) hcfg
    rw [hb] at ho
    exact hab (Option.some_inj.1 ho).symm

end terms

end DiagonaLean.KAComm.Enc
