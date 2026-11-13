/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.KleeneAlgebra.ExprCode

@[expose] public section

/-! # Enumerating proofs

A proof is a program for a stack machine whose entries are pairs of expression codes. Every
instruction either pushes a valid equation, using only entries already on the stack, or does
nothing. So every entry of every reachable stack is a provable equation (`run_inv`), with no
parsing of expressions. Conversely, every provable equation has a program
(`exists_prog_equiv`, `exists_prog_ka`).

The flag `ka` switches on the three rules that Kleene algebra adds to pre-Kleene algebra. `Checks`
is the primitive recursive test that a code is a program proving a given equation, and provability
is `∃ k, Checks ..` (`equiv_iff_checks`, `kaEquiv_iff_checks`).
-/

namespace DiagonaLean.Foundations.KleeneAlgebra

open RExp DiagonaLean.Foundations.Computability

/-- The stack machine's stack. -/
abbrev Stk := List (ℕ × ℕ)

/-- Whether two letter codes are on opposite sides. -/
def commC (x y : ℕ) : Prop := x % 2 ≠ y % 2

/-- `commC` is decidable. -/
instance (x y : ℕ) : Decidable (commC x y) := inferInstanceAs (Decidable (_ ≠ _))

/-- The result of each instruction, by its tag. -/
def results (ka : Bool) (arg : ℕ) (s : Stk) : List Stk :=
  let a := s.headI
  let b := s.tail.headI
  let c := s.tail.tail.headI
  let r₁ := s.tail
  let r₂ := s.tail.tail
  let r₃ := s.tail.tail.tail
  [ (cz, cz) :: s,
    (co, co) :: s,
    (cs arg, cs arg) :: s,
    (cp b.1 a.1, cp b.2 a.2) :: r₂,
    (cm b.1 a.1, cm b.2 a.2) :: r₂,
    (ct a.1, ct a.2) :: r₁,
    (a.2, a.1) :: r₁,
    if b.2 = a.1 then (b.1, a.2) :: r₂ else s,
    (cp (cp c.1 b.1) a.1, cp c.1 (cp b.1 a.1)) :: r₃,
    (cp b.1 a.1, cp a.1 b.1) :: r₂,
    (cp cz a.1, a.1) :: r₁,
    (cp a.1 a.1, a.1) :: r₁,
    (cm (cm c.1 b.1) a.1, cm c.1 (cm b.1 a.1)) :: r₃,
    (cm co a.1, a.1) :: r₁,
    (cm a.1 co, a.1) :: r₁,
    (cm cz a.1, cz) :: r₁,
    (cm a.1 cz, cz) :: r₁,
    (cm c.1 (cp b.1 a.1), cp (cm c.1 b.1) (cm c.1 a.1)) :: r₃,
    (cm (cp c.1 b.1) a.1, cp (cm c.1 a.1) (cm b.1 a.1)) :: r₃,
    (ct a.1, cp co (cm a.1 (ct a.1))) :: r₁,
    if commC arg.unpair.1 arg.unpair.2 then
      (cm (cs arg.unpair.1) (cs arg.unpair.2), cm (cs arg.unpair.2) (cs arg.unpair.1)) :: s
    else s,
    if ka then (cp (cm (ct a.1) a.1) (ct a.1), ct a.1) :: r₁ else s,
    if ka then
      (if a.1 = cp (cm c.1 b.1) c.1 ∧ a.2 = c.1 then (cp (cm c.1 (ct b.1)) c.1, c.1) :: r₃ else s)
    else s,
    if ka then
      (if a.1 = cp (cm b.1 c.1) c.1 ∧ a.2 = c.1 then (cp (cm (ct b.1) c.1) c.1, c.1) :: r₃ else s)
    else s ]

/-- One instruction: a tag and an argument. Unknown tags do nothing. -/
def stepS (ka : Bool) (s : Stk) (n : ℕ) : Stk := (results ka n.unpair.2 s).getD n.unpair.1 s

/-- Run a program from a stack. -/
def run (ka : Bool) (p : List ℕ) (s : Stk) : Stk := p.foldl (stepS ka) s

/-- Running `p ++ q` runs `p`, then `q`. -/
theorem run_append (ka : Bool) (p q : List ℕ) (s : Stk) :
    run ka (p ++ q) s = run ka q (run ka p s) := by
  simp [run, List.foldl_append]

/-- The rules of pre-Kleene algebra, for a relation. -/
structure Closed (R : RExp (ℕ ⊕ ℕ) → RExp (ℕ ⊕ ℕ) → Prop) : Prop where
  /-- `R` contains provable equality in pre-Kleene algebra. -/
  ofEquiv {e f} : Equiv DComm e f → R e f
  /-- `R` is symmetric. -/
  symm {e f} : R e f → R f e
  /-- `R` is transitive. -/
  trans {e f g} : R e f → R f g → R e g
  /-- `R` is a congruence for `plus`. -/
  plus {e e' f f'} : R e e' → R f f' → R (plus e f) (plus e' f')
  /-- `R` is a congruence for `mul`. -/
  mul {e e' f f'} : R e e' → R f f' → R (mul e f) (mul e' f')
  /-- `R` is a congruence for `star`. -/
  star {e e'} : R e e' → R (RExp.star e) (RExp.star e')

/-- Provable equality in pre-Kleene algebra satisfies the rules. -/
theorem closed_equiv : Closed (Equiv DComm) :=
  ⟨id, .symm, .trans, .plus, .mul, .star⟩

/-- Provable equality in Kleene algebra satisfies the rules. -/
theorem closed_ka : Closed (KAEquiv DComm) :=
  ⟨.ofEquiv, .symm, .trans, .plus, .mul, .star⟩

/-- The relation for the flag. -/
def Rel (ka : Bool) : RExp (ℕ ⊕ ℕ) → RExp (ℕ ⊕ ℕ) → Prop :=
  if ka then KAEquiv DComm else Equiv DComm

/-- The relation for either flag satisfies the rules. -/
theorem closed_rel (ka : Bool) : Closed (Rel ka) := by
  cases ka
  · exact closed_equiv
  · exact closed_ka

/-- `x` is the code of a provable equation. -/
def Good (ka : Bool) (x : ℕ × ℕ) : Prop := ∃ e f, x = (rc e, rc f) ∧ Rel ka e f

/-- Every entry is good. -/
def Inv (ka : Bool) (s : Stk) : Prop := ∀ x ∈ s, Good ka x

/-- The default entry is good. -/
theorem good_default (ka : Bool) : Good ka (default : ℕ × ℕ) :=
  ⟨zero, zero, rfl, (closed_rel ka).ofEquiv (.refl _)⟩

/-- The head of a good stack is good. -/
theorem Inv.head {ka : Bool} {s : Stk} (h : Inv ka s) : Good ka s.headI := by
  cases s with
  | nil => exact good_default ka
  | cons x s => exact h x List.mem_cons_self

/-- The tail of a good stack is good. -/
theorem Inv.tail {ka : Bool} {s : Stk} (h : Inv ka s) : Inv ka s.tail := by
  cases s with
  | nil => exact h
  | cons x s => exact fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- Pushing a good entry onto a good stack gives a good stack. -/
theorem Inv.cons {ka : Bool} {s : Stk} {x : ℕ × ℕ} (hx : Good ka x) (h : Inv ka s) :
    Inv ka (x :: s) := by
  intro y hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact hx
  · exact h y hy

/-- The code of an equation provable in pre-Kleene algebra is good. -/
theorem good_ax {ka : Bool} {e f : RExp (ℕ ⊕ ℕ)} (h : Equiv DComm e f) :
    Good ka (rc e, rc f) := ⟨e, f, rfl, (closed_rel ka).ofEquiv h⟩

/-- With the flag set, the relation is provable equality in Kleene algebra. -/
theorem rel_true {e f : RExp (ℕ ⊕ ℕ)} : Rel true e f ↔ KAEquiv DComm e f := by simp [Rel]

/-- Letters whose codes are on opposite sides commute. -/
theorem dComm_of_commC {u v : ℕ ⊕ ℕ} (h : commC (symC u) (symC v)) : DComm u v := by
  rcases u with u | u <;> rcases v with v | v <;> simp only [commC, symC] at h
  · omega
  · trivial
  · trivial
  · omega

/-- Every instruction sends a good stack to a good stack. -/
theorem results_inv (ka : Bool) (arg : ℕ) {s : Stk} (hs : Inv ka s) :
    ∀ t ∈ results ka arg s, Inv ka t := by
  have hC := closed_rel ka
  obtain ⟨e₁, f₁, ha, hr₁⟩ := hs.head
  obtain ⟨e₂, f₂, hb, hr₂⟩ := hs.tail.head
  obtain ⟨e₃, f₃, hc, hr₃⟩ := hs.tail.tail.head
  have h₁ := hs.tail
  have h₂ := hs.tail.tail
  have h₃ := hs.tail.tail.tail
  simp only [results, ha, hb, hc]
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  obtain ⟨x, hx⟩ := symC_surjective arg
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Inv.cons (good_ax (.refl zero)) hs
  · exact Inv.cons (good_ax (.refl one)) hs
  · subst hx
    exact Inv.cons (good_ax (.refl (sym x))) hs
  · exact Inv.cons ⟨plus e₂ e₁, plus f₂ f₁, rfl, hC.plus hr₂ hr₁⟩ h₂
  · exact Inv.cons ⟨mul e₂ e₁, mul f₂ f₁, rfl, hC.mul hr₂ hr₁⟩ h₂
  · exact Inv.cons ⟨RExp.star e₁, RExp.star f₁, rfl, hC.star hr₁⟩ h₁
  · exact Inv.cons ⟨f₁, e₁, rfl, hC.symm hr₁⟩ h₁
  · split
    · rename_i h
      obtain rfl := rc_injective h
      exact Inv.cons ⟨e₂, f₁, rfl, hC.trans hr₂ hr₁⟩ h₂
    · exact hs
  · exact Inv.cons (good_ax (.plus_assoc e₃ e₂ e₁)) h₃
  · exact Inv.cons (good_ax (.plus_comm e₂ e₁)) h₂
  · exact Inv.cons (good_ax (.zero_plus e₁)) h₁
  · exact Inv.cons (good_ax (.plus_idem e₁)) h₁
  · exact Inv.cons (good_ax (.mul_assoc e₃ e₂ e₁)) h₃
  · exact Inv.cons (good_ax (.one_mul e₁)) h₁
  · exact Inv.cons (good_ax (.mul_one e₁)) h₁
  · exact Inv.cons (good_ax (.zero_mul e₁)) h₁
  · exact Inv.cons (good_ax (.mul_zero e₁)) h₁
  · exact Inv.cons (good_ax (.left_distrib e₃ e₂ e₁)) h₃
  · exact Inv.cons (good_ax (.right_distrib e₃ e₂ e₁)) h₃
  · exact Inv.cons (good_ax (.unfold e₁)) h₁
  · split
    · rename_i h
      obtain ⟨u, hu⟩ := symC_surjective arg.unpair.1
      obtain ⟨v, hv⟩ := symC_surjective arg.unpair.2
      rw [← hu, ← hv] at h ⊢
      exact Inv.cons (good_ax (.comm (dComm_of_commC h))) hs
    · exact hs
  · cases ka
    · exact hs
    · exact Inv.cons ⟨plus (mul (RExp.star e₁) e₁) (RExp.star e₁), RExp.star e₁, rfl,
        rel_true.2 (.kstar_mul_le e₁)⟩ h₁
  · cases ka
    · exact hs
    · simp only [ite_true]
      split
      · rename_i h
        have he : e₁ = plus (mul e₃ e₂) e₃ := rc_injective h.1
        have hf : f₁ = e₃ := rc_injective h.2
        subst he hf
        exact Inv.cons ⟨plus (mul f₁ (RExp.star e₂)) f₁, f₁, rfl,
          rel_true.2 (.mul_kstar_le_self (rel_true.1 hr₁))⟩ h₃
      · exact hs
  · cases ka
    · exact hs
    · simp only [ite_true]
      split
      · rename_i h
        have he : e₁ = plus (mul e₂ e₃) e₃ := rc_injective h.1
        have hf : f₁ = e₃ := rc_injective h.2
        subst he hf
        exact Inv.cons ⟨plus (mul (RExp.star e₂) f₁) f₁, f₁, rfl,
          rel_true.2 (.kstar_mul_le_self (rel_true.1 hr₁))⟩ h₃
      · exact hs

/-- One instruction sends a good stack to a good stack. -/
theorem stepS_inv {ka : Bool} {s : Stk} (hs : Inv ka s) (n : ℕ) : Inv ka (stepS ka s n) := by
  unfold stepS
  rw [List.getD_eq_getElem?_getD]
  cases h : (results ka n.unpair.2 s)[n.unpair.1]? with
  | none => exact hs
  | some t => exact results_inv ka _ hs t (List.mem_of_getElem? h)

/-- Running a program sends a good stack to a good stack. -/
theorem run_inv (ka : Bool) (p : List ℕ) {s : Stk} (hs : Inv ka s) : Inv ka (run ka p s) := by
  induction p generalizing s with
  | nil => exact hs
  | cons n p ih => exact ih (stepS_inv hs n)

/-- Running a one-instruction program applies that instruction. -/
theorem run_one (ka : Bool) (t a : ℕ) (s : Stk) :
    run ka [Nat.pair t a] s = (results ka a s).getD t s := by
  simp [run, stepS]

/-- `p` pushes the equation `e = f` onto any stack. -/
def Pushes (ka : Bool) (p : List ℕ) (e f : RExp (ℕ ⊕ ℕ)) : Prop :=
  ∀ s, run ka p s = (rc e, rc f) :: s

/-- Some program pushes `e = e`. -/
theorem exists_expr (ka : Bool) (e : RExp (ℕ ⊕ ℕ)) : ∃ p, Pushes ka p e e := by
  induction e with
  | zero => exact ⟨[Nat.pair 0 0], fun s => by rw [run_one]; rfl⟩
  | one => exact ⟨[Nat.pair 1 0], fun s => by rw [run_one]; rfl⟩
  | sym x => exact ⟨[Nat.pair 2 (symC x)], fun s => by rw [run_one]; rfl⟩
  | plus e f ihe ihf =>
    obtain ⟨p, hp⟩ := ihe
    obtain ⟨q, hq⟩ := ihf
    exact ⟨p ++ q ++ [Nat.pair 3 0], fun s => by rw [run_append, run_append, hp, hq, run_one]; rfl⟩
  | mul e f ihe ihf =>
    obtain ⟨p, hp⟩ := ihe
    obtain ⟨q, hq⟩ := ihf
    exact ⟨p ++ q ++ [Nat.pair 4 0], fun s => by rw [run_append, run_append, hp, hq, run_one]; rfl⟩
  | star e ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨p ++ [Nat.pair 5 0], fun s => by rw [run_append, hp, run_one]; rfl⟩

/-- The codes of commuting letters are on opposite sides. -/
theorem commC_of_dComm {u v : ℕ ⊕ ℕ} (h : DComm u v) : commC (symC u) (symC v) := by
  rcases u with u | u <;> rcases v with v | v
  · exact h.elim
  · simp only [commC, symC]; omega
  · simp only [commC, symC]; omega
  · exact h.elim

/-- Every equation provable in pre-Kleene algebra has a program that pushes it, for either flag. -/
theorem exists_prog_equiv (ka : Bool) {e f : RExp (ℕ ⊕ ℕ)} (h : Equiv DComm e f) :
    ∃ p, Pushes ka p e f := by
  have ax₁ : ∀ (t : ℕ) (e x y : RExp (ℕ ⊕ ℕ)),
      (∀ s, (results ka 0 ((rc e, rc e) :: s)).getD t ((rc e, rc e) :: s) = (rc x, rc y) :: s) →
      ∃ p, Pushes ka p x y := fun t e x y h => by
    obtain ⟨p, hp⟩ := exists_expr ka e
    exact ⟨p ++ [Nat.pair t 0], fun s => by rw [run_append, hp, run_one, h]⟩
  have ax₂ : ∀ (t : ℕ) (e f x y : RExp (ℕ ⊕ ℕ)),
      (∀ s, (results ka 0 ((rc f, rc f) :: (rc e, rc e) :: s)).getD t
        ((rc f, rc f) :: (rc e, rc e) :: s) = (rc x, rc y) :: s) →
      ∃ p, Pushes ka p x y := fun t e f x y h => by
    obtain ⟨p, hp⟩ := exists_expr ka e
    obtain ⟨q, hq⟩ := exists_expr ka f
    exact ⟨p ++ q ++ [Nat.pair t 0], fun s => by rw [run_append, run_append, hp, hq, run_one, h]⟩
  have ax₃ : ∀ (t : ℕ) (e f g x y : RExp (ℕ ⊕ ℕ)),
      (∀ s, (results ka 0 ((rc g, rc g) :: (rc f, rc f) :: (rc e, rc e) :: s)).getD t
        ((rc g, rc g) :: (rc f, rc f) :: (rc e, rc e) :: s) = (rc x, rc y) :: s) →
      ∃ p, Pushes ka p x y := fun t e f g x y h => by
    obtain ⟨p, hp⟩ := exists_expr ka e
    obtain ⟨q, hq⟩ := exists_expr ka f
    obtain ⟨r, hr⟩ := exists_expr ka g
    exact ⟨p ++ q ++ r ++ [Nat.pair t 0], fun s => by
      rw [run_append, run_append, run_append, hp, hq, hr, run_one, h]⟩
  induction h with
  | refl e => exact exists_expr ka e
  | symm _ ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨p ++ [Nat.pair 6 0], fun s => by rw [run_append, hp, run_one]; rfl⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨p, hp⟩ := ih₁
    obtain ⟨q, hq⟩ := ih₂
    refine ⟨p ++ q ++ [Nat.pair 7 0], fun s => ?_⟩
    rw [run_append, run_append, hp, hq, run_one]
    simp [results]
  | plus _ _ ih₁ ih₂ =>
    obtain ⟨p, hp⟩ := ih₁
    obtain ⟨q, hq⟩ := ih₂
    exact ⟨p ++ q ++ [Nat.pair 3 0], fun s => by rw [run_append, run_append, hp, hq, run_one]; rfl⟩
  | mul _ _ ih₁ ih₂ =>
    obtain ⟨p, hp⟩ := ih₁
    obtain ⟨q, hq⟩ := ih₂
    exact ⟨p ++ q ++ [Nat.pair 4 0], fun s => by rw [run_append, run_append, hp, hq, run_one]; rfl⟩
  | star _ ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨p ++ [Nat.pair 5 0], fun s => by rw [run_append, hp, run_one]; rfl⟩
  | plus_assoc e f g => exact ax₃ 8 e f g _ _ fun s => rfl
  | plus_comm e f => exact ax₂ 9 e f _ _ fun s => rfl
  | zero_plus e => exact ax₁ 10 e _ _ fun s => rfl
  | plus_idem e => exact ax₁ 11 e _ _ fun s => rfl
  | mul_assoc e f g => exact ax₃ 12 e f g _ _ fun s => rfl
  | one_mul e => exact ax₁ 13 e _ _ fun s => rfl
  | mul_one e => exact ax₁ 14 e _ _ fun s => rfl
  | zero_mul e => exact ax₁ 15 e _ _ fun s => rfl
  | mul_zero e => exact ax₁ 16 e _ _ fun s => rfl
  | left_distrib e f g => exact ax₃ 17 e f g _ _ fun s => rfl
  | right_distrib e f g => exact ax₃ 18 e f g _ _ fun s => rfl
  | unfold e => exact ax₁ 19 e _ _ fun s => rfl
  | @comm x y hxy =>
    refine ⟨[Nat.pair 20 (Nat.pair (symC x) (symC y))], fun s => ?_⟩
    rw [run_one]
    have hc := commC_of_dComm hxy
    simp [results, hc]
    exact ⟨rfl, rfl⟩

/-- Every equation provable in Kleene algebra has a program that pushes it, with the flag set. -/
theorem exists_prog_ka {e f : RExp (ℕ ⊕ ℕ)} (h : KAEquiv DComm e f) :
    ∃ p, Pushes true p e f := by
  induction h with
  | ofEquiv h => exact exists_prog_equiv true h
  | symm _ ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨p ++ [Nat.pair 6 0], fun s => by rw [run_append, hp, run_one]; rfl⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨p, hp⟩ := ih₁
    obtain ⟨q, hq⟩ := ih₂
    refine ⟨p ++ q ++ [Nat.pair 7 0], fun s => ?_⟩
    rw [run_append, run_append, hp, hq, run_one]
    simp [results]
  | plus _ _ ih₁ ih₂ =>
    obtain ⟨p, hp⟩ := ih₁
    obtain ⟨q, hq⟩ := ih₂
    exact ⟨p ++ q ++ [Nat.pair 3 0], fun s => by rw [run_append, run_append, hp, hq, run_one]; rfl⟩
  | mul _ _ ih₁ ih₂ =>
    obtain ⟨p, hp⟩ := ih₁
    obtain ⟨q, hq⟩ := ih₂
    exact ⟨p ++ q ++ [Nat.pair 4 0], fun s => by rw [run_append, run_append, hp, hq, run_one]; rfl⟩
  | star _ ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨p ++ [Nat.pair 5 0], fun s => by rw [run_append, hp, run_one]; rfl⟩
  | kstar_mul_le e =>
    obtain ⟨p, hp⟩ := exists_expr true e
    exact ⟨p ++ [Nat.pair 21 0], fun s => by rw [run_append, hp, run_one]; rfl⟩
  | @mul_kstar_le_self a b _ ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hq⟩ := exists_expr true b
    obtain ⟨r, hr⟩ := exists_expr true a
    refine ⟨q ++ r ++ p ++ [Nat.pair 22 0], fun s => ?_⟩
    rw [run_append, run_append, run_append, hq, hr, hp, run_one]
    simp [results, rc]
  | @kstar_mul_le_self a b _ ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hq⟩ := exists_expr true b
    obtain ⟨r, hr⟩ := exists_expr true a
    refine ⟨q ++ r ++ p ++ [Nat.pair 23 0], fun s => ?_⟩
    rw [run_append, run_append, run_append, hq, hr, hp, run_one]
    simp [results, rc]

/-- The program with code `k` ends with the equation `(a, b)` on top. -/
def Checks (ka : Bool) (k a b : ℕ) : Prop :=
  (run ka (Denumerable.ofNat (List ℕ) k) []).headI = (a, b)

/-- If a program checks the codes of `e` and `f`, then `e` and `f` are related. -/
theorem rel_of_checks {ka : Bool} {k : ℕ} {e f : RExp (ℕ ⊕ ℕ)} (h : Checks ka k (rc e) (rc f)) :
    Rel ka e f := by
  have hi : Inv ka (run ka (Denumerable.ofNat (List ℕ) k) []) :=
    run_inv ka _ (by simp [Inv])
  obtain ⟨e', f', hx, hr⟩ := hi.head
  rw [h] at hx
  obtain ⟨he, hf⟩ := Prod.mk.inj hx
  rwa [rc_injective he, rc_injective hf]

/-- If `p` pushes `e = f`, then some code checks the codes of `e` and `f`. -/
theorem checks_of_pushes {ka : Bool} {p : List ℕ} {e f : RExp (ℕ ⊕ ℕ)} (h : Pushes ka p e f) :
    ∃ k, Checks ka k (rc e) (rc f) :=
  ⟨Encodable.encode p, by simp [Checks, Denumerable.ofNat_encode, h []]⟩

/-- An equation is provable in pre-Kleene algebra iff some program checks its codes. -/
theorem equiv_iff_checks {e f : RExp (ℕ ⊕ ℕ)} :
    Equiv DComm e f ↔ ∃ k, Checks false k (rc e) (rc f) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := exists_prog_equiv false h
    exact checks_of_pushes hp
  · rintro ⟨k, hk⟩
    simpa [Rel] using rel_of_checks hk

/-- An equation is provable in Kleene algebra iff some program checks its codes. -/
theorem kaEquiv_iff_checks {e f : RExp (ℕ ⊕ ℕ)} :
    KAEquiv DComm e f ↔ ∃ k, Checks true k (rc e) (rc f) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := exists_prog_ka h
    exact checks_of_pushes hp
  · rintro ⟨k, hk⟩
    exact rel_true.1 (rel_of_checks hk)

/-- `results ka` is primitive recursive. -/
theorem results_prim (ka : Bool) : Primrec fun y : Stk × ℕ => results ka y.2 y.1 := by
  have hcomm : PrimrecPred fun x : Stk × ℕ => commC x.2.unpair.1 x.2.unpair.2 :=
    pred_ne (by prim) (by prim)
  cases ka <;> simp only [results, Bool.false_eq_true, ite_true, ite_false]
    <;> prim

/-- `stepS ka` is primitive recursive. -/
theorem stepS_prim (ka : Bool) : Primrec fun y : Stk × ℕ => stepS ka y.1 y.2 := by
  have h : Primrec fun y : Stk × ℕ => ((results ka y.2.unpair.2 y.1)[y.2.unpair.1]?).getD y.1 :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp
        ((results_prim ka).comp (prim_pair Primrec.fst (prim_snd (prim_unpair Primrec.snd))))
        (prim_fst (prim_unpair Primrec.snd)))
      Primrec.fst
  exact h.of_eq fun y => (List.getD_eq_getElem?_getD ..).symm

/-- Running the program with code `k` from the empty stack is primitive recursive in `k`. -/
theorem run_prim (ka : Bool) : Primrec fun k : ℕ => run ka (Denumerable.ofNat (List ℕ) k) [] :=
  Primrec.list_foldl (Primrec.ofNat _) (Primrec.const []) ((stepS_prim ka).comp Primrec.snd).to₂

/-- `Checks ka` is a primitive recursive predicate. -/
theorem checks_prim (ka : Bool) : PrimrecPred fun x : ℕ × ℕ × ℕ => Checks ka x.1 x.2.1 x.2.2 := by
  unfold Checks
  exact pred_eq (prim_headI ((run_prim ka).comp Primrec.fst))
    (prim_pair (prim_fst Primrec.snd) (prim_snd Primrec.snd))

end DiagonaLean.Foundations.KleeneAlgebra
