/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Grammar.ToSRS
import DiagonaLean.Foundations.Rewriting.Primcodable
import DiagonaLean.Foundations.Computability.StackProof

@[expose] public section

/-! # Derivations of string rewriting systems, checked by a stack machine

String rewriting systems are defined in `Foundations/Rewriting/SRS.lean`. Every grammar of the
Chomsky hierarchy is a string rewriting system over its terminals and nonterminals together, with
a start symbol; the classes differ only in the shape of the rules.

`srsSys` is a stack machine that checks derivations, uniformly in the system
(`Computability.StackProof`): its instructions push `[] ⇒ []`, `[a] ⇒ [a]` or a rule of the
system, concatenate the two top derivations, or chain them. So
`Derives R u v ↔ ∃ k, Checks srsSys R k (u, v)` (`derives_iff_checks`), a primitive recursive
predicate of the system, the program code and the two strings (`StackProof.checks_prim`):
derivability in a string rewriting system is recursively enumerable, uniformly in the system.

For a context-free grammar code, Mathlib's derivation relation agrees with that of its rewriting
system (`derives_toCFG_iff`, `Foundations/Grammar/ToSRS.lean`), so membership in the language of a
grammar code is checked the same way (`mem_language_iff_checks`).
-/

namespace DiagonaLean.Foundations.Grammar

open DiagonaLean.Foundations.Computability DiagonaLean.Foundations.Rewriting Relation

variable {T : Type}

/-! ### The stack machine -/

section Machine

variable [Primcodable T] [DecidableEq T]

/-- A judgement: a derivation `u ⇒* v`. -/
abbrev Judgement (T : Type) := List T × List T

/-- One instruction, `n = Nat.pair tag data`: push `[] ⇒ []` (tag `0`), push `[a] ⇒ [a]` for the
letter `a` with code `data` (tag `1`), push the rule numbered `data` (tag `2`), concatenate the two
top derivations (tag `3`), chain them (tag `4`). Anything else does nothing. -/
def srsStep (R : SRS T) (s : List (Judgement T)) (n : ℕ) : List (Judgement T) :=
  if n.unpair.1 = 0 then ([], []) :: s
  else if n.unpair.1 = 1 then
    (Encodable.decode (α := T) n.unpair.2).elim s fun a => ([a], [a]) :: s
  else if n.unpair.1 = 2 then
    ((R.getD n.unpair.2 ⟨[], []⟩).lhs, (R.getD n.unpair.2 ⟨[], []⟩).rhs) :: s
  else if n.unpair.1 = 3 then
    (s.tail.headI.1 ++ s.headI.1, s.tail.headI.2 ++ s.headI.2) :: s.tail.tail
  else if n.unpair.1 = 4 then
    if s.tail.headI.2 = s.headI.1 then (s.tail.headI.1, s.headI.2) :: s.tail.tail else s
  else s

/-- `srsStep` is primitive recursive. -/
theorem srsStep_prim :
    Primrec fun y : SRS T × List (Judgement T) × ℕ => srsStep y.1 y.2.1 y.2.2 := by
  unfold srsStep
  fun_prop

/-- The stack machine checking derivations of string rewriting systems. -/
def srsSys : StackProof.System (SRS T) (Judgement T) := ⟨srsStep, srsStep_prim⟩

open StackProof

/-- Every instruction keeps derivations derivations. -/
theorem srsStep_inv (R : SRS T) (s : List (Judgement T)) (hs : Inv (fun j => j.1 ↠[R] j.2) s)
    (n : ℕ) : Inv (fun j => j.1 ↠[R] j.2) (srsStep R s n) := by
  have hd : (default : Judgement T).1 ↠[R] (default : Judgement T).2 := .refl
  have ha := Inv.headI (Good := fun j : Judgement T => j.1 ↠[R] j.2) hd hs
  have hb := Inv.headI (Good := fun j : Judgement T => j.1 ↠[R] j.2) hd hs.tail
  unfold srsStep
  split_ifs with h0 h1 h2 h3 h4 he
  · exact Inv.cons .refl hs
  · cases Encodable.decode (α := T) n.unpair.2 with
    | none => exact hs
    | some a => exact Inv.cons .refl hs
  · refine Inv.cons ?_ hs
    rw [List.getD_eq_getElem?_getD]
    cases h : R[n.unpair.2]? with
    | none => exact .refl
    | some ρ => exact SRS.Derives.rule (List.mem_of_getElem? h)
  · exact Inv.cons (hb.append ha) hs.tail.tail
  · exact Inv.cons (he ▸ hb |>.trans ha) hs.tail.tail
  · exact hs
  · exact hs

/-- A program pushing `u ⇒ u`, letter by letter. -/
theorem exists_refl (R : SRS T) (u : List T) : ∃ p, Pushes srsSys R p (u, u) := by
  induction u with
  | nil => exact ⟨_, pushes_one (Nat.pair 0 0) fun _ => by simp [srsSys, srsStep]⟩
  | cons a u ih =>
    obtain ⟨p, hp⟩ := ih
    have ha : Pushes srsSys R [Nat.pair 1 (Encodable.encode a)] ([a], [a]) :=
      pushes_one _ fun _ => by simp [srsSys, srsStep]
    exact ⟨_, pushes_append₂ (Nat.pair 3 0) ha hp fun _ => by simp [srsSys, srsStep]⟩

/-- A program pushing `l ⇒ r` for a rule of the system. -/
theorem exists_rule {R : SRS T} {ρ : Rule T} (h : ρ ∈ R) :
    ∃ p, Pushes srsSys R p (ρ.lhs, ρ.rhs) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  exact ⟨_, pushes_one (Nat.pair 2 i) fun _ => by simp [srsSys, srsStep, hi]⟩

/-- Programs pushing `a` and `b` give a program pushing their concatenation. -/
theorem pushes_concat {R : SRS T} {a b : Judgement T} {p q : List ℕ} (hp : Pushes srsSys R p a)
    (hq : Pushes srsSys R q b) :
    Pushes srsSys R (p ++ q ++ [Nat.pair 3 0]) (a.1 ++ b.1, a.2 ++ b.2) :=
  pushes_append₂ _ hp hq fun _ => by simp [srsSys, srsStep]

/-- Programs pushing `u ⇒* v` and `v ⇒* w` give a program pushing `u ⇒* w`. -/
theorem pushes_chain {R : SRS T} {u v w : List T} {p q : List ℕ} (hp : Pushes srsSys R p (u, v))
    (hq : Pushes srsSys R q (v, w)) : Pushes srsSys R (p ++ q ++ [Nat.pair 4 0]) (u, w) :=
  pushes_append₂ _ hp hq fun _ => by simp [srsSys, srsStep]

/-- Every derivation has a program that pushes it. -/
theorem exists_derives {R : SRS T} {u v : List T} (h : u ↠[R] v) :
    ∃ p, Pushes srsSys R p (u, v) := by
  induction h with
  | refl => exact exists_refl R u
  | tail _ hs ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨hlr, a, b⟩ := hs
    obtain ⟨pa, hpa⟩ := exists_refl R a
    obtain ⟨pr, hpr⟩ := exists_rule hlr
    obtain ⟨pb, hpb⟩ := exists_refl R b
    exact ⟨_, pushes_chain hp (pushes_concat (pushes_concat hpa hpr) hpb)⟩

/-- **Derivability is checking**, uniformly in the system: `u ⇒* v` iff some program checks it.
With `StackProof.checks_prim`, derivability in a string rewriting system is recursively
enumerable, uniformly in the system. -/
theorem derives_iff_checks (R : SRS T) (u v : List T) :
    u ↠[R] v ↔ ∃ k, Checks srsSys R k (u, v) :=
  good_iff_checks srsSys R (Good := fun j : Judgement T => j.1 ↠[R] j.2) .refl (srsStep_inv R)
    (fun _ h => exists_derives h) (u, v)

end Machine

/-! ### Context-free grammar codes -/

section CFG

variable [DecidableEq T] [Primcodable T]

open StackProof in
/-- **Membership in the language of a grammar code is checking**, uniformly in the code. -/
theorem mem_language_iff_checks (c : CFGCode T) (w : List T) :
    w ∈ c.toCFG.language ↔ ∃ k, Checks srsSys c.toSRS k ([.inr c.1], w.map .inl) := by
  rw [← derives_iff_checks, ← derives_toCFG_iff]
  simp [ContextFreeGrammar.mem_language_iff, symOf, Function.comp_def]

end CFG

end DiagonaLean.Foundations.Grammar
