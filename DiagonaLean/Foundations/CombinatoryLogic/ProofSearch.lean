/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Foundations.CombinatoryLogic.Conv
import DiagonaLean.Foundations.CombinatoryLogic.Code
import DiagonaLean.Foundations.Computability.StackProof

@[expose] public section

/-! # Enumerating conversions

Two SKI terms are convertible when they have a common reduct, `Join (ReflTransGen Red)`. A proof
of convertibility is a program for a stack machine whose entries are pairs of term codes. Every
instruction either pushes a valid conversion, using only entries already on the stack, or does
nothing. So every entry of every reachable stack is a conversion (`run_inv`), with no parsing of
terms. Conversely, every conversion has a program (`exists_prog`).

The stack machine is an instance of `Computability.StackProof` (`skiSys`), which supplies running
programs, the invariant, `Checks` and its primitive recursion; this file supplies the instructions
(`results`), their soundness (`results_inv`) and completeness (`exists_prog`). `Checks` is the
primitive recursive test that a code is a program proving a given conversion, and convertibility
is `∃ k, Checks ..` (`conv_iff_checks`).
-/

namespace DiagonaLean.Foundations.CombinatoryLogic

open Cslib SKI Relation DiagonaLean.Foundations.Computability

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

/-- The stack machine, as a proof system with no instance data. -/
def skiSys : StackProof.System Unit (ℕ × ℕ) where
  step _ s n := stepS s n
  step_prim := stepS_prim.comp (Primrec.fst.comp Primrec.snd |>.pair (Primrec.snd.comp Primrec.snd))

/-- `x` is the code of a conversion. -/
def Good (x : ℕ × ℕ) : Prop := ∃ t u, x = (skc t, skc u) ∧ Conv t u

/-- The default entry is good: it is the code of `S = S`. -/
theorem good_default : Good (default : ℕ × ℕ) := ⟨S, S, rfl, join_mRed_equivalence.refl S⟩

/-- The code of a reduction is good. -/
theorem good_mRed {t u : SKI} (h : t ↠ u) : Good (skc t, skc u) := ⟨t, u, rfl, conv_of_mRed h⟩

open StackProof in
/-- Every instruction sends a good stack to a good stack. -/
theorem results_inv {s : Stk} (hs : Inv Good s) : ∀ t ∈ results s, Inv Good t := by
  obtain ⟨t₁, u₁, ha, hr₁⟩ := hs.headI good_default
  obtain ⟨t₂, u₂, hb, hr₂⟩ := hs.tail.headI good_default
  obtain ⟨t₃, u₃, hc, -⟩ := hs.tail.tail.headI good_default
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

open StackProof in
/-- One instruction sends a good stack to a good stack. -/
theorem stepS_inv (s : Stk) (hs : Inv Good s) (n : ℕ) : Inv Good (stepS s n) := by
  unfold stepS
  rw [List.getD_eq_getElem?_getD]
  cases h : (results s)[n]? with
  | none => exact hs
  | some t => exact results_inv hs t (List.mem_of_getElem? h)

/-- `p` pushes the conversion `t = u` onto any stack. -/
abbrev Pushes (p : List ℕ) (t u : SKI) : Prop := StackProof.Pushes skiSys () p (skc t, skc u)

open StackProof in
/-- Some program pushes `t = t`. -/
theorem exists_term (t : SKI) : ∃ p, Pushes p t t := by
  induction t with
  | S => exact ⟨_, pushes_one 0 fun _ => rfl⟩
  | K => exact ⟨_, pushes_one 1 fun _ => rfl⟩
  | I => exact ⟨_, pushes_one 2 fun _ => rfl⟩
  | app x y ihx ihy =>
    obtain ⟨p, hp⟩ := ihx
    obtain ⟨q, hq⟩ := ihy
    exact ⟨_, pushes_append₂ 3 hp hq fun _ => rfl⟩

open StackProof in
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
    exact ⟨_, pushes_append₂ 7 hp hq fun _ => rfl⟩
  | red_I x =>
    obtain ⟨p, hp⟩ := exists_term x
    exact ⟨_, pushes_append 8 hp fun _ => rfl⟩
  | red_head x x' y _ ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hq⟩ := exists_term y
    exact ⟨_, pushes_append₂ 3 hp hq fun _ => rfl⟩
  | red_tail x y y' _ ih =>
    obtain ⟨p, hp⟩ := exists_term x
    obtain ⟨q, hq⟩ := ih
    exact ⟨_, pushes_append₂ 3 hp hq fun _ => rfl⟩

open StackProof in
/-- If `p` pushes `t = u` and `q` pushes `u = v`, then `p ++ q ++ [5]` pushes `t = v`. -/
theorem pushes_trans {p q : List ℕ} {t u v : SKI} (hp : Pushes p t u) (hq : Pushes q u v) :
    Pushes (p ++ q ++ [5]) t v :=
  pushes_append₂ 5 hp hq fun _ => by simp [skiSys, stepS, results]

/-- Every reduction has a program that pushes it. -/
theorem exists_mRed {t u : SKI} (h : t ↠ u) : ∃ p, Pushes p t u := by
  induction h with
  | refl => exact exists_term t
  | tail _ hs ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨q, hq⟩ := exists_red hs
    exact ⟨_, pushes_trans hp hq⟩

open StackProof in
/-- Every conversion has a program that pushes it. -/
theorem exists_prog {t u : SKI} (h : Conv t u) : ∃ p, Pushes p t u := by
  obtain ⟨w, ht, hu⟩ := h
  obtain ⟨p, hp⟩ := exists_mRed ht
  obtain ⟨q, hq⟩ := exists_mRed hu
  exact ⟨_, pushes_trans hp (pushes_append 4 hq fun _ => rfl)⟩

/-- The program with code `k` ends with the conversion `(a, b)` on top. -/
abbrev Checks (k a b : ℕ) : Prop := StackProof.Checks skiSys () k (a, b)

/-- Two terms are convertible iff some program checks their codes. -/
theorem conv_iff_checks {t u : SKI} : Conv t u ↔ ∃ k, Checks k (skc t) (skc u) := by
  have := StackProof.good_iff_checks skiSys () good_default (fun s hs n => stepS_inv s hs n)
    (fun j ⟨t, u, hj, h⟩ => hj ▸ exists_prog h) (skc t, skc u)
  rw [← this]
  exact ⟨fun h => ⟨t, u, rfl, h⟩, fun ⟨t', u', hx, h⟩ => by
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj hx
    rwa [skc_injective h₁, skc_injective h₂]⟩

/-- `Checks` is a primitive recursive predicate. -/
theorem checks_prim : PrimrecPred fun x : ℕ × ℕ × ℕ => Checks x.1 x.2.1 x.2.2 :=
  (StackProof.checks_prim skiSys).comp ((Primrec.const ()).pair (Primrec.fst.pair
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd))))

end DiagonaLean.Foundations.CombinatoryLogic
