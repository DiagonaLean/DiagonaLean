/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.KleeneAlgebra.MachineEncoding.Configurations
import DiagonaLean.Foundations.KleeneAlgebra.Copy
import DiagonaLean.Foundations.KleeneAlgebra.SingleStep

@[expose] public section

/-! # The transition term of a Turing machine

For each state `q` and scanned symbol `h`, the term `rule q h` rewrites the window around the head
according to `tr q h` (adding a blank cell when the head moves past a tape end) and copies the rest
of the word through the context `⊢ C∗ ⋯ C∗ ⊣`, where `C` copies one cell. The transition term
`R_M` is the sum of all rules (Definition 13). Its language relates each running configuration
word to its successor (Lemma 14), and it is a representable relation on configuration words
(Lemma 35).
-/
open scoped Computability

namespace DiagonaLean.Foundations.KleeneAlgebra.Enc

open Cslib.Turing TD FreePreKA

variable {Sym : Type} [Inhabited Sym] [Fintype Sym] {M : SingleTapeTM Sym}

/-- A list of letters as an element of the free monoid. -/
abbrev w (x : List (Letter Sym M.State)) : FreeMonoid (Letter Sym M.State) := FreeMonoid.ofList x

/-- `w` sends concatenation of lists to multiplication. -/
theorem w_mul (x y : List (Letter Sym M.State)) : w x * w y = w (x ++ y) := rfl

variable (M) in
/-- The term copying one tape cell. -/
noncomputable def C : TD (Letter Sym M.State) := cpf fun o : Option Sym => Letter.cell o

/-- The context `⊢ C∗ (u, v) C∗ ⊣`, rewriting `u` to `v` and copying the rest. -/
noncomputable def ctx (u v : List (Letter Sym M.State)) : TD (Letter Sym M.State) :=
  ofPair (w [.lend], w [.lend]) * (C M)∗ * ofPair (w u, w v) * (C M)∗ *
    ofPair (w [.rend], w [.rend])

/-- The context `⊢ C∗ (u, v)`, for a window that contains `⊣`. -/
noncomputable def ctxR (u v : List (Letter Sym M.State)) : TD (Letter Sym M.State) :=
  ofPair (w [.lend], w [.lend]) * (C M)∗ * ofPair (w u, w v)

/-- The context `(u, v) C∗ ⊣`, for a window that contains `⊢`. -/
noncomputable def ctxL (u v : List (Letter Sym M.State)) : TD (Letter Sym M.State) :=
  ofPair (w u, w v) * (C M)∗ * ofPair (w [.rend], w [.rend])

variable (M) in
/-- The rewriting rule for state `q` and scanned symbol `h`. -/
noncomputable def rule (q : M.State) (h : Option Sym) : TD (Letter Sym M.State) :=
  match M.tr q h with
  | (⟨wr, none⟩, q') => ctx [.head (some q) h] [.head q' wr]
  | (⟨wr, some .right⟩, q') =>
    (∑ x : Option Sym, ctx [.head (some q) h, .cell x] [.cell wr, .head q' x]) +
      ctxR [.head (some q) h, .rend] [.cell wr, .head q' none, .rend]
  | (⟨wr, some .left⟩, q') =>
    (∑ x : Option Sym, ctx [.cell x, .head (some q) h] [.head q' x, .cell wr]) +
      ctxL [.lend, .head (some q) h] [.lend, .head q' none, .cell wr]

variable (M) in
/-- **Definition 13.** The transition term `R_M`. -/
noncomputable def RM : TD (Letter Sym M.State) := ∑ p : M.State × Option Sym, rule M p.1 p.2

/-- The language of `ctx u v` consists of the pairs `⊢ a u b ⊣`, `⊢ a v b ⊣` for cell lists
`a`, `b`. -/
theorem mem_ctx (u v : List (Letter Sym M.State)) (s : W (Letter Sym M.State)) :
    SetSemiring.Mem s (pl (ctx u v)) ↔ ∃ a b : List (Option Sym),
      s = (w (.lend :: (cells a ++ u ++ cells b ++ [.rend])),
        w (.lend :: (cells a ++ v ++ cells b ++ [.rend]))) := by
  unfold ctx C
  simp only [mem_mul_ofPair, mem_mul_cpf_star, mem_ofPair]
  constructor
  · rintro ⟨_, ⟨_, b, ⟨_, ⟨_, a, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    refine ⟨a, b, ?_⟩
    simp only [Prod.mk_mul_mk, w_mul, cells, List.cons_append, List.nil_append, List.append_assoc]
  · rintro ⟨a, b, rfl⟩
    refine ⟨_, ⟨_, b, ⟨_, ⟨_, a, rfl, rfl⟩, rfl⟩, rfl⟩, ?_⟩
    simp only [Prod.mk_mul_mk, w_mul, cells, List.cons_append, List.nil_append, List.append_assoc]

/-- The language of `ctxR u v` consists of the pairs `⊢ a u`, `⊢ a v` for cell lists `a`. -/
theorem mem_ctxR (u v : List (Letter Sym M.State)) (s : W (Letter Sym M.State)) :
    SetSemiring.Mem s (pl (ctxR u v)) ↔ ∃ a : List (Option Sym),
      s = (w (.lend :: (cells a ++ u)), w (.lend :: (cells a ++ v))) := by
  unfold ctxR C
  simp only [mem_mul_ofPair, mem_mul_cpf_star, mem_ofPair]
  constructor
  · rintro ⟨_, ⟨_, a, rfl, rfl⟩, rfl⟩
    refine ⟨a, ?_⟩
    simp only [Prod.mk_mul_mk, w_mul, cells, List.cons_append, List.nil_append]
  · rintro ⟨a, rfl⟩
    refine ⟨_, ⟨_, a, rfl, rfl⟩, ?_⟩
    simp only [Prod.mk_mul_mk, w_mul, cells, List.cons_append, List.nil_append]

/-- The language of `ctxL u v` consists of the pairs `u b ⊣`, `v b ⊣` for cell lists `b`. -/
theorem mem_ctxL (u v : List (Letter Sym M.State)) (s : W (Letter Sym M.State)) :
    SetSemiring.Mem s (pl (ctxL u v)) ↔ ∃ b : List (Option Sym),
      s = (w (u ++ cells b ++ [.rend]), w (v ++ cells b ++ [.rend])) := by
  unfold ctxL C
  simp only [mem_mul_ofPair, mem_mul_cpf_star, mem_ofPair]
  constructor
  · rintro ⟨_, ⟨_, b, rfl, rfl⟩, rfl⟩
    refine ⟨b, ?_⟩
    simp only [Prod.mk_mul_mk, w_mul, cells]
  · rintro ⟨b, rfl⟩
    refine ⟨_, ⟨_, b, rfl, rfl⟩, ?_⟩
    simp only [Prod.mk_mul_mk, w_mul, cells]

/-- `wdF d` is the word `wd d` in the free monoid. -/
theorem wdF_eq (d : Data M) : wdF d = w (wd d) := rfl

/-- `rule M q h` relates exactly the words of configurations in state `q` scanning `h` to
the words of their successors. -/
theorem mem_rule (q : M.State) (h : Option Sym) (s : W (Letter Sym M.State)) :
    SetSemiring.Mem s (pl (rule M q h)) ↔ ∃ l r : List (Option Sym),
      s = (wdF (⟨some q, l, h, r⟩ : Data M), wdF (dstep M ⟨some q, l, h, r⟩)) := by
  rcases htr : M.tr q h with ⟨⟨wr, _ | _ | _⟩, q'⟩
  · simp only [rule, htr, mem_ctx, dstep, wdF_eq, wd]
    constructor
    · rintro ⟨a, b, rfl⟩
      exact ⟨a.reverse, b, by simp [cells]⟩
    · rintro ⟨l, r, rfl⟩
      exact ⟨l.reverse, r, by simp [cells]⟩
  · simp only [rule, htr, pl_add, SetSemiring.mem_add, mem_pl_sum, Finset.mem_univ, true_and,
      mem_ctx, mem_ctxL]
    constructor
    · rintro (⟨x, a, b, rfl⟩ | ⟨b, rfl⟩)
      · exact ⟨x :: a.reverse, b, by simp [dstep, htr, wdF_eq, wd, cells]⟩
      · exact ⟨[], b, by simp [dstep, htr, wdF_eq, wd, cells]⟩
    · rintro ⟨l, r, rfl⟩
      cases l with
      | nil => exact Or.inr ⟨r, by simp [dstep, htr, wdF_eq, wd, cells]⟩
      | cons x l => exact Or.inl ⟨x, l.reverse, r, by simp [dstep, htr, wdF_eq, wd, cells]⟩
  · simp only [rule, htr, pl_add, SetSemiring.mem_add, mem_pl_sum, Finset.mem_univ, true_and,
      mem_ctx, mem_ctxR]
    constructor
    · rintro (⟨x, a, b, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨a.reverse, x :: b, by simp [dstep, htr, wdF_eq, wd, cells]⟩
      · exact ⟨a.reverse, [], by simp [dstep, htr, wdF_eq, wd, cells]⟩
    · rintro ⟨l, r, rfl⟩
      cases r with
      | nil => exact Or.inr ⟨l.reverse, by simp [dstep, htr, wdF_eq, wd, cells]⟩
      | cons x r => exact Or.inl ⟨x, l.reverse, r, by simp [dstep, htr, wdF_eq, wd, cells]⟩

/-- **Lemma 14.** `R_M` relates exactly each running configuration word to its successor. -/
theorem mem_RM (s : W (Letter Sym M.State)) :
    SetSemiring.Mem s (pl (RM M)) ↔ ∃ d : Data M, d.Running ∧ s = (wdF d, wdF (dstep M d)) := by
  rw [RM, mem_pl_sum]
  constructor
  · rintro ⟨⟨q, h⟩, -, hs⟩
    obtain ⟨l, r, rfl⟩ := (mem_rule q h s).1 hs
    exact ⟨⟨some q, l, h, r⟩, rfl, rfl⟩
  · rintro ⟨⟨_ | q, l, h, r⟩, hrun, rfl⟩
    · simp [Data.Running] at hrun
    · exact ⟨(q, h), Finset.mem_univ _, (mem_rule q h _).2 ⟨l, r, rfl⟩⟩

/-- Distinct configurations have distinct words in the free monoid. -/
theorem wdF_injective : Function.Injective (wdF : Data M → FreeMonoid (Letter Sym M.State)) :=
  fun _ _ h => wd_injective h

variable (M) in
/-- The set of configuration words. -/
def Lset : Set (FreeMonoid (Letter Sym M.State)) := Set.range wdF

/-- The context `ctx u v` is finite-state. -/
theorem finiteState_ctx (u v : List (Letter Sym M.State)) : FiniteState (ctx (M := M) u v) :=
  ((((FiniteState.ofPair _).mul (FiniteState.cpf_star _)).mul (FiniteState.ofPair _)).mul
    (FiniteState.cpf_star _)).mul (FiniteState.ofPair _)

/-- Each rule is finite-state. -/
theorem finiteState_rule (q : M.State) (h : Option Sym) : FiniteState (rule M q h) := by
  rcases htr : M.tr q h with ⟨⟨wr, _ | _ | _⟩, q'⟩ <;> simp only [rule, htr]
  · exact finiteState_ctx _ _
  · exact (FiniteState.sum _ _ fun _ _ => finiteState_ctx _ _).add
      (((FiniteState.ofPair _).mul (FiniteState.cpf_star _)).mul (FiniteState.ofPair _))
  · exact (FiniteState.sum _ _ fun _ _ => finiteState_ctx _ _).add
      (((FiniteState.ofPair _).mul (FiniteState.cpf_star _)).mul (FiniteState.ofPair _))

variable [DecidableEq Sym] [DecidableEq M.State]

/-- **Lemma 35**, with an explicit residue: if `R_M`'s automaton has its states below `b`, then
`R_M` is a representable relation on configuration words with residue `Σ̈∗ b`. -/
theorem rel_RM_le {b : TD (Letter Sym M.State)} (hb : FiniteStateLe (RM M) b) :
    ∃ h : Rel (Lset M) (RM M), h.ResidBy (sigAll∗ * b) := by
  refine rel_resid_of_finiteStateLe ?_ ?_ ?_ hb ⟨1, ?_⟩
  · rintro _ ⟨d, rfl⟩ _ ⟨d', rfl⟩ h
    exact congrArg wdF (prefixFree h)
  · intro s hs
    obtain ⟨d, -, rfl⟩ := (mem_RM s).1 hs
    exact ⟨d, rfl⟩
  · intro s hs
    obtain ⟨d, -, rfl⟩ := (mem_RM s).1 hs
    exact ⟨dstep M d, rfl⟩
  · intro s hs
    obtain ⟨d, -, rfl⟩ := (mem_RM s).1 hs
    show (wd (dstep M d)).length ≤ ((wd d).length + 1) * 1
    have := length_wd_dstep d
    omega

omit [DecidableEq Sym] [DecidableEq M.State] in
/-- The transition term `R_M` is finite-state. -/
theorem finiteState_RM : FiniteState (RM M) :=
  FiniteState.sum _ _ fun p _ => finiteState_rule p.1 p.2

/-- **Lemma 35.** `R_M` is a representable relation on configuration words. -/
theorem rel_RM : Rel (Lset M) (RM M) := by
  obtain ⟨b, hb⟩ := (finiteState_iff _).1 (finiteState_RM (M := M))
  exact (rel_RM_le hb).1

end DiagonaLean.Foundations.KleeneAlgebra.Enc
