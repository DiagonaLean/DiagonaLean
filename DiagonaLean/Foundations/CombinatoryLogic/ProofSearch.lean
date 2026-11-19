/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Cslib.Languages.CombinatoryLogic.Confluence
import DiagonaLean.Foundations.CombinatoryLogic.Code

@[expose] public section

/-! # Enumerating conversions

Two SKI terms are convertible when they have a common reduct, `Join (ReflTransGen Red)`. A proof
of convertibility is a program for a stack machine whose entries are pairs of term codes. Every
instruction either pushes a valid conversion, using only entries already on the stack, or does
nothing. So every entry of every reachable stack is a conversion (`run_inv`), with no parsing of
terms. Conversely, every conversion has a program (`exists_prog`).

`Checks` is the primitive recursive test that a code is a program proving a given conversion,
and convertibility is `∃ k, Checks ..` (`conv_iff_checks`). The design follows
`KAComm/KleeneAlgebra/ProofSearch.lean`.
-/

namespace DiagonaLean.Foundations.CombinatoryLogic

open Cslib SKI Relation DiagonaLean.Foundations.Computability

/-- Two SKI terms are convertible: they have a common reduct. -/
abbrev Conv (x y : SKI) : Prop := Join (ReflTransGen Red) x y

/-- A reduction is a conversion. -/
theorem conv_of_mRed {x y : SKI} (h : x ↠ y) : Conv x y := ⟨y, h, .refl⟩

/-- Convertibility is a congruence for application. -/
theorem conv_app {x x' y y' : SKI} (hx : Conv x x') (hy : Conv y y') : Conv (x ⬝ y) (x' ⬝ y') :=
  join_mRed_equivalence.trans (join_mRed_head y hx) (join_mRed_tail x' hy)

/-- The stack machine's stack. -/
abbrev Stk := List (ℕ × ℕ)

/-- The result of each instruction, by its tag: push `S`, `K` or `I`, apply, swap, chain, and
the axioms for `S`, `K` and `I`. -/
def results (s : Stk) : List Stk :=
  let a := s.headI
  let b := s.tail.headI
  let c := s.tail.tail.headI
  let r₁ := s.tail
  let r₂ := s.tail.tail
  let r₃ := s.tail.tail.tail
  [ (cS, cS) :: s,
    (cK, cK) :: s,
    (cI, cI) :: s,
    (ca b.1 a.1, ca b.2 a.2) :: r₂,
    (a.2, a.1) :: r₁,
    if b.2 = a.1 then (b.1, a.2) :: r₂ else s,
    (ca (ca (ca cS c.1) b.1) a.1, ca (ca c.1 a.1) (ca b.1 a.1)) :: r₃,
    (ca (ca cK b.1) a.1, b.1) :: r₂,
    (ca cI a.1, a.1) :: r₁ ]

/-- One instruction, by its tag. Unknown tags do nothing. -/
def stepS (s : Stk) (n : ℕ) : Stk := (results s).getD n s

/-- Run a program from a stack. -/
def run (p : List ℕ) (s : Stk) : Stk := p.foldl stepS s

/-- Running `p ++ q` runs `p`, then `q`. -/
theorem run_append (p q : List ℕ) (s : Stk) : run (p ++ q) s = run q (run p s) := by
  simp [run, List.foldl_append]

/-- `x` is the code of a conversion. -/
def Good (x : ℕ × ℕ) : Prop := ∃ t u, x = (skc t, skc u) ∧ Conv t u

/-- Every entry is good. -/
def Inv (s : Stk) : Prop := ∀ x ∈ s, Good x

/-- The default entry is good: it is the code of `S = S`. -/
theorem good_default : Good (default : ℕ × ℕ) := ⟨S, S, rfl, join_mRed_equivalence.refl S⟩

/-- The head of a good stack is good. -/
theorem Inv.head {s : Stk} (h : Inv s) : Good s.headI := by
  cases s with
  | nil => exact good_default
  | cons x s => exact h x List.mem_cons_self

/-- The tail of a good stack is good. -/
theorem Inv.tail {s : Stk} (h : Inv s) : Inv s.tail := by
  cases s with
  | nil => exact h
  | cons x s => exact fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- Pushing a good entry onto a good stack gives a good stack. -/
theorem Inv.cons {s : Stk} {x : ℕ × ℕ} (hx : Good x) (h : Inv s) : Inv (x :: s) := by
  intro y hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact hx
  · exact h y hy

/-- The code of a reduction is good. -/
theorem good_mRed {t u : SKI} (h : t ↠ u) : Good (skc t, skc u) := ⟨t, u, rfl, conv_of_mRed h⟩

/-- Every instruction sends a good stack to a good stack. -/
theorem results_inv {s : Stk} (hs : Inv s) : ∀ t ∈ results s, Inv t := by
  obtain ⟨t₁, u₁, ha, hr₁⟩ := hs.head
  obtain ⟨t₂, u₂, hb, hr₂⟩ := hs.tail.head
  obtain ⟨t₃, u₃, hc, -⟩ := hs.tail.tail.head
  have h₁ := hs.tail
  have h₂ := hs.tail.tail
  have h₃ := hs.tail.tail.tail
  simp only [results, ha, hb, hc]
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Inv.cons (good_mRed (t := S) .refl) hs
  · exact Inv.cons (good_mRed (t := K) .refl) hs
  · exact Inv.cons (good_mRed (t := I) .refl) hs
  · exact Inv.cons ⟨t₂ ⬝ t₁, u₂ ⬝ u₁, rfl, conv_app hr₂ hr₁⟩ h₂
  · exact Inv.cons ⟨u₁, t₁, rfl, join_mRed_equivalence.symm hr₁⟩ h₁
  · split
    · rename_i h
      obtain rfl := skc_injective h
      exact Inv.cons ⟨t₂, u₁, rfl, join_mRed_equivalence.trans hr₂ hr₁⟩ h₂
    · exact hs
  · exact Inv.cons (good_mRed (MRed.S t₃ t₂ t₁)) h₃
  · exact Inv.cons (good_mRed (MRed.K t₂ t₁)) h₂
  · exact Inv.cons (good_mRed (MRed.I t₁)) h₁

/-- One instruction sends a good stack to a good stack. -/
theorem stepS_inv {s : Stk} (hs : Inv s) (n : ℕ) : Inv (stepS s n) := by
  unfold stepS
  rw [List.getD_eq_getElem?_getD]
  cases h : (results s)[n]? with
  | none => exact hs
  | some t => exact results_inv hs t (List.mem_of_getElem? h)

/-- Running a program sends a good stack to a good stack. -/
theorem run_inv (p : List ℕ) {s : Stk} (hs : Inv s) : Inv (run p s) := by
  induction p generalizing s with
  | nil => exact hs
  | cons n p ih => exact ih (stepS_inv hs n)

/-- Running a one-instruction program applies that instruction. -/
theorem run_one (t : ℕ) (s : Stk) : run [t] s = (results s).getD t s := by
  simp [run, stepS]

/-- `p` pushes the conversion `t = u` onto any stack. -/
def Pushes (p : List ℕ) (t u : SKI) : Prop := ∀ s, run p s = (skc t, skc u) :: s

/-- Some program pushes `t = t`. -/
theorem exists_term (t : SKI) : ∃ p, Pushes p t t := by
  induction t with
  | S => exact ⟨[0], fun s => by rw [run_one]; rfl⟩
  | K => exact ⟨[1], fun s => by rw [run_one]; rfl⟩
  | I => exact ⟨[2], fun s => by rw [run_one]; rfl⟩
  | app x y ihx ihy =>
    obtain ⟨p, hp⟩ := ihx
    obtain ⟨q, hq⟩ := ihy
    exact ⟨p ++ q ++ [3], fun s => by rw [run_append, run_append, hp, hq, run_one]; rfl⟩

/-- Every reduction step has a program that pushes it. -/
theorem exists_red {t u : SKI} (h : t ⭢ u) : ∃ p, Pushes p t u := by
  induction h with
  | red_S x y z =>
    obtain ⟨p, hp⟩ := exists_term x
    obtain ⟨q, hq⟩ := exists_term y
    obtain ⟨r, hr⟩ := exists_term z
    exact ⟨p ++ q ++ r ++ [6], fun s => by
      rw [run_append, run_append, run_append, hp, hq, hr, run_one]; rfl⟩
  | red_K x y =>
    obtain ⟨p, hp⟩ := exists_term x
    obtain ⟨q, hq⟩ := exists_term y
    exact ⟨p ++ q ++ [7], fun s => by rw [run_append, run_append, hp, hq, run_one]; rfl⟩
  | red_I x =>
    obtain ⟨p, hp⟩ := exists_term x
    exact ⟨p ++ [8], fun s => by rw [run_append, hp, run_one]; rfl⟩
  | red_head x x' y _ ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hq⟩ := exists_term y
    exact ⟨p ++ q ++ [3], fun s => by rw [run_append, run_append, hp, hq, run_one]; rfl⟩
  | red_tail x y y' _ ih =>
    obtain ⟨p, hp⟩ := exists_term x
    obtain ⟨q, hq⟩ := ih
    exact ⟨p ++ q ++ [3], fun s => by rw [run_append, run_append, hp, hq, run_one]; rfl⟩

/-- If `p` pushes `t = u` and `q` pushes `u = v`, then `p ++ q ++ [5]` pushes `t = v`. -/
theorem pushes_trans {p q : List ℕ} {t u v : SKI} (hp : Pushes p t u) (hq : Pushes q u v) :
    Pushes (p ++ q ++ [5]) t v := fun s => by
  rw [run_append, run_append, hp, hq, run_one]
  simp [results]

/-- Every reduction has a program that pushes it. -/
theorem exists_mRed {t u : SKI} (h : t ↠ u) : ∃ p, Pushes p t u := by
  induction h with
  | refl => exact exists_term t
  | tail _ hs ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hq⟩ := exists_red hs
    exact ⟨_, pushes_trans hp hq⟩

/-- Every conversion has a program that pushes it. -/
theorem exists_prog {t u : SKI} (h : Conv t u) : ∃ p, Pushes p t u := by
  obtain ⟨w, ht, hu⟩ := h
  obtain ⟨p, hp⟩ := exists_mRed ht
  obtain ⟨q, hq⟩ := exists_mRed hu
  have hq' : Pushes (q ++ [4]) w u := fun s => by rw [run_append, hq, run_one]; rfl
  exact ⟨_, pushes_trans hp hq'⟩

/-- The program with code `k` ends with the conversion `(a, b)` on top. -/
def Checks (k a b : ℕ) : Prop := (run (Denumerable.ofNat (List ℕ) k) []).headI = (a, b)

/-- `Checks k a b` is decidable. -/
instance (k a b : ℕ) : Decidable (Checks k a b) := inferInstanceAs (Decidable (_ = _))

/-- If a program checks the codes of `t` and `u`, then `t` and `u` are convertible. -/
theorem conv_of_checks {k : ℕ} {t u : SKI} (h : Checks k (skc t) (skc u)) : Conv t u := by
  have hi : Inv (run (Denumerable.ofNat (List ℕ) k) []) := run_inv _ (by simp [Inv])
  obtain ⟨t', u', hx, hr⟩ := hi.head
  rw [h] at hx
  obtain ⟨ht, hu⟩ := Prod.mk.inj hx
  rwa [skc_injective ht, skc_injective hu]

/-- Two terms are convertible iff some program checks their codes. -/
theorem conv_iff_checks {t u : SKI} : Conv t u ↔ ∃ k, Checks k (skc t) (skc u) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := exists_prog h
    exact ⟨Encodable.encode p, by simp [Checks, Denumerable.ofNat_encode, hp []]⟩
  · rintro ⟨k, hk⟩
    exact conv_of_checks hk

/-- `results` is primitive recursive. -/
theorem results_prim : Primrec results := by
  unfold results
  fun_prop

/-- `stepS` is primitive recursive. -/
theorem stepS_prim : Primrec fun y : Stk × ℕ => stepS y.1 y.2 := by
  have h : Primrec fun y : Stk × ℕ => ((results y.1)[y.2]?).getD y.1 :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (results_prim.comp Primrec.fst) Primrec.snd) Primrec.fst
  exact h.of_eq fun y => (List.getD_eq_getElem?_getD ..).symm

/-- `stepS` applied to primitive recursive functions is primitive recursive. -/
@[fun_prop] theorem prim_stepS {α : Type*} [Primcodable α] {f : α → Stk} {g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun x => stepS (f x) (g x) :=
  stepS_prim.comp (hf.pair hg)

/-- Running the program with code `k` from the empty stack is primitive recursive in `k`. -/
theorem run_prim : Primrec fun k : ℕ => run (Denumerable.ofNat (List ℕ) k) [] := by
  unfold run; fun_prop

/-- `Checks` is a primitive recursive predicate. -/
theorem checks_prim : PrimrecPred fun x : ℕ × ℕ × ℕ => Checks x.1 x.2.1 x.2.2 := by
  unfold Checks
  exact pred_eq (prim_headI (run_prim.comp Primrec.fst))
    (prim_pair (prim_fst Primrec.snd) (prim_snd Primrec.snd))

end DiagonaLean.Foundations.CombinatoryLogic
