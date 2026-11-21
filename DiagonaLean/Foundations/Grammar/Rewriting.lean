/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Grammar.Code
import DiagonaLean.Foundations.Computability.StackProof

@[expose] public section

/-! # String rewriting, and derivations checked by a stack machine

A string rewriting system (semi-Thue system) over `T` is a list of rules `l → r` between strings
(`SRS T`). A step rewrites one occurrence of a left side in context, `p ++ l ++ q ⇒ p ++ r ++ q`,
and `Derives R` is the reflexive–transitive closure. Every grammar of the Chomsky hierarchy is a
string rewriting system over its terminals and nonterminals together, with a start symbol; the
classes differ only in the shape of the rules.

`sys` is a stack machine that checks derivations, uniformly in the system
(`Computability.StackProof`): its instructions push `[] ⇒ []`, `[a] ⇒ [a]` or a rule of the
system, concatenate the two top derivations, or chain them. So
`Derives R u v ↔ ∃ k, Checks sys R k (u, v)` (`derives_iff_checks`), a primitive recursive
predicate of the system, the program code and the two strings (`StackProof.checks_prim`):
derivability in a string rewriting system is recursively enumerable, uniformly in the system.

For a context-free grammar code, a rule `n → rhs` is the rewriting rule `[.inr n] → rhs`
(`CFGCode.toSRS`), and Mathlib's derivation relation agrees with this one (`derives_toCFG_iff`),
so membership in the language of a grammar code is checked the same way (`mem_language_iff_checks`).
-/

namespace DiagonaLean.Foundations.Grammar

open DiagonaLean.Foundations.Computability Relation

variable {T : Type}

/-- A string rewriting system: a list of rules `l → r` between strings. -/
abbrev SRS (T : Type) := List (List T × List T)

/-- One rewriting step: one occurrence of a left side, in context, is replaced by the right
side. -/
def SRS.Step (R : SRS T) (u v : List T) : Prop :=
  ∃ lr ∈ R, ∃ p q, u = p ++ lr.1 ++ q ∧ v = p ++ lr.2 ++ q

/-- Derivability: the reflexive–transitive closure of a step. -/
abbrev SRS.Derives (R : SRS T) : List T → List T → Prop := ReflTransGen R.Step

namespace SRS

variable {R : SRS T}

theorem Step.append_left {u v : List T} (h : R.Step u v) (w : List T) :
    R.Step (w ++ u) (w ++ v) := by
  obtain ⟨lr, hlr, p, q, rfl, rfl⟩ := h
  exact ⟨lr, hlr, w ++ p, q, by simp, by simp⟩

theorem Step.append_right {u v : List T} (h : R.Step u v) (w : List T) :
    R.Step (u ++ w) (v ++ w) := by
  obtain ⟨lr, hlr, p, q, rfl, rfl⟩ := h
  exact ⟨lr, hlr, p, q ++ w, by simp, by simp⟩

theorem Derives.append {u v u' v' : List T} (h : R.Derives u v) (h' : R.Derives u' v') :
    R.Derives (u ++ u') (v ++ v') := by
  have h₁ : R.Derives (u ++ u') (v ++ u') := by
    induction h with
    | refl => exact .refl
    | tail _ hs ih => exact ih.tail (hs.append_right u')
  have h₂ : R.Derives (v ++ u') (v ++ v') := by
    induction h' with
    | refl => exact .refl
    | tail _ hs ih => exact ih.tail (hs.append_left v)
  exact h₁.trans h₂

theorem Derives.rule {lr : List T × List T} (h : lr ∈ R) : R.Derives lr.1 lr.2 :=
  .single ⟨lr, h, [], [], by simp, by simp⟩

end SRS

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
  else if n.unpair.1 = 2 then R.getD n.unpair.2 ([], []) :: s
  else if n.unpair.1 = 3 then
    (s.tail.headI.1 ++ s.headI.1, s.tail.headI.2 ++ s.headI.2) :: s.tail.tail
  else if n.unpair.1 = 4 then
    if s.tail.headI.2 = s.headI.1 then (s.tail.headI.1, s.headI.2) :: s.tail.tail else s
  else s

theorem srsStep_prim :
    Primrec fun y : SRS T × List (Judgement T) × ℕ => srsStep y.1 y.2.1 y.2.2 := by
  unfold srsStep
  fun_prop

/-- The stack machine checking derivations of string rewriting systems. -/
def sys : StackProof.System (SRS T) (Judgement T) := ⟨srsStep, srsStep_prim⟩

open StackProof

/-- Every instruction keeps derivations derivations. -/
theorem srsStep_inv (R : SRS T) (s : List (Judgement T)) (hs : Inv (fun j => R.Derives j.1 j.2) s)
    (n : ℕ) : Inv (fun j => R.Derives j.1 j.2) (srsStep R s n) := by
  have hd : R.Derives (default : Judgement T).1 (default : Judgement T).2 := .refl
  have ha := Inv.headI (Good := fun j : Judgement T => R.Derives j.1 j.2) hd hs
  have hb := Inv.headI (Good := fun j : Judgement T => R.Derives j.1 j.2) hd hs.tail
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
    | some lr => exact SRS.Derives.rule (List.mem_of_getElem? h)
  · exact Inv.cons (hb.append ha) hs.tail.tail
  · exact Inv.cons (he ▸ hb |>.trans ha) hs.tail.tail
  · exact hs
  · exact hs

/-- A program pushing `u ⇒ u`, letter by letter. -/
theorem exists_refl (R : SRS T) (u : List T) : ∃ p, Pushes sys R p (u, u) := by
  induction u with
  | nil => exact ⟨_, pushes_one (Nat.pair 0 0) fun _ => by simp [sys, srsStep]⟩
  | cons a u ih =>
    obtain ⟨p, hp⟩ := ih
    have ha : Pushes sys R [Nat.pair 1 (Encodable.encode a)] ([a], [a]) :=
      pushes_one _ fun _ => by simp [sys, srsStep]
    exact ⟨_, pushes_append₂ (Nat.pair 3 0) ha hp fun _ => by simp [sys, srsStep]⟩

/-- A program pushing `l ⇒ r` for a rule of the system. -/
theorem exists_rule {R : SRS T} {lr : Judgement T} (h : lr ∈ R) : ∃ p, Pushes sys R p lr := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  exact ⟨_, pushes_one (Nat.pair 2 i) fun _ => by simp [sys, srsStep, hi]⟩

theorem exists_concat {R : SRS T} {a b : Judgement T} {p q : List ℕ} (hp : Pushes sys R p a)
    (hq : Pushes sys R q b) : Pushes sys R (p ++ q ++ [Nat.pair 3 0]) (a.1 ++ b.1, a.2 ++ b.2) :=
  pushes_append₂ _ hp hq fun _ => by simp [sys, srsStep]

theorem exists_chain {R : SRS T} {u v w : List T} {p q : List ℕ} (hp : Pushes sys R p (u, v))
    (hq : Pushes sys R q (v, w)) : Pushes sys R (p ++ q ++ [Nat.pair 4 0]) (u, w) :=
  pushes_append₂ _ hp hq fun _ => by simp [sys, srsStep]

/-- Every derivation has a program that pushes it. -/
theorem exists_derives {R : SRS T} {u v : List T} (h : R.Derives u v) :
    ∃ p, Pushes sys R p (u, v) := by
  induction h with
  | refl => exact exists_refl R u
  | tail _ hs ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨lr, hlr, a, b, rfl, rfl⟩ := hs
    obtain ⟨pa, hpa⟩ := exists_refl R a
    obtain ⟨pr, hpr⟩ := exists_rule hlr
    obtain ⟨pb, hpb⟩ := exists_refl R b
    exact ⟨_, exists_chain hp (exists_concat (exists_concat hpa hpr) hpb)⟩

/-- **Derivability is checking**, uniformly in the system: `u ⇒* v` iff some program checks it.
With `StackProof.checks_prim`, derivability in a string rewriting system is recursively
enumerable, uniformly in the system. -/
theorem derives_iff_checks (R : SRS T) (u v : List T) :
    R.Derives u v ↔ ∃ k, Checks sys R k (u, v) :=
  good_iff_checks sys R (Good := fun j : Judgement T => R.Derives j.1 j.2) .refl (srsStep_inv R)
    (fun _ h => exists_derives h) (u, v)

end Machine

/-! ### Context-free grammar codes -/

section CFG

variable [DecidableEq T]

/-- The rewriting system of a context-free grammar code: a rule `n → rhs` rewrites `[.inr n]` to
`rhs`. -/
def CFGCode.toSRS (c : CFGCode T) : SRS (T ⊕ ℕ) := c.2.map fun r => ([.inr r.1], r.2)

omit [DecidableEq T] in
theorem symOf_injective {N : Type} : Function.Injective (symOf : T ⊕ N → Symbol T N) := by
  rintro (a | a) (b | b) h <;> simp_all [symOf]

/-- The inverse of `symOf`. -/
def unSym {N : Type} : Symbol T N → T ⊕ N
  | .terminal t => .inl t
  | .nonterminal n => .inr n

omit [DecidableEq T] in
theorem symOf_unSym {N : Type} (x : Symbol T N) : symOf (unSym x) = x := by
  cases x <;> rfl

omit [DecidableEq T] in
theorem map_symOf_unSym {N : Type} (l : List (Symbol T N)) : (l.map unSym).map symOf = l := by
  simp [List.map_map, Function.comp_def, symOf_unSym]

/-- One step of the grammar is one step of its rewriting system. -/
theorem produces_toCFG_iff (c : CFGCode T) (u v : List (T ⊕ ℕ)) :
    c.toCFG.Produces (u.map symOf) (v.map symOf) ↔ c.toSRS.Step u v := by
  constructor
  · rintro ⟨r, hr, hrw⟩
    obtain ⟨s, hs, rfl⟩ := (mem_rules_toCFG c r).1 hr
    obtain ⟨p', q', hu, hv⟩ := ContextFreeRule.rewrites_iff.1 hrw
    obtain ⟨p, xq, rfl, rfl, hxq⟩ := List.map_eq_append_iff.1 (by simpa using hu)
    obtain ⟨x, q, rfl, hx, rfl⟩ := List.map_eq_cons_iff.1 hxq
    have hx' : x = .inr s.1 :=
      symOf_injective ((by simpa [ruleOf] using hx : symOf x = Symbol.nonterminal s.1).trans rfl)
    subst hx'
    refine ⟨([.inr s.1], s.2), List.mem_map_of_mem hs, p, q, by simp, ?_⟩
    apply List.map_injective_iff.2 symOf_injective
    simpa [ruleOf] using hv
  · rintro ⟨lr, hlr, p, q, rfl, rfl⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hlr
    refine ⟨ruleOf s, (mem_rules_toCFG c _).2 ⟨s, hs, rfl⟩, ?_⟩
    exact ContextFreeRule.rewrites_iff.2 ⟨p.map symOf, q.map symOf, by simp [ruleOf, symOf],
      by simp [ruleOf]⟩

/-- Derivations of the grammar are derivations of its rewriting system. -/
theorem derives_toCFG_iff (c : CFGCode T) (u v : List (T ⊕ ℕ)) :
    c.toCFG.Derives (u.map symOf) (v.map symOf) ↔ c.toSRS.Derives u v := by
  have key : ∀ {v'}, c.toCFG.Derives (u.map symOf) v' →
      ∃ v, v' = v.map symOf ∧ c.toSRS.Derives u v := by
    intro v' h
    induction h with
    | refl => exact ⟨u, rfl, .refl⟩
    | tail _ hs ih =>
      obtain ⟨b, rfl, hb⟩ := ih
      rename_i c' _
      refine ⟨c'.map unSym, (map_symOf_unSym c').symm, hb.tail ?_⟩
      exact (produces_toCFG_iff c b _).1 (by rwa [map_symOf_unSym])
  constructor
  · intro h
    obtain ⟨v', hv, hd⟩ := key h
    rwa [List.map_injective_iff.2 symOf_injective hv]
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.tail ((produces_toCFG_iff c _ _).2 hs)

variable [Primcodable T]

open StackProof in
/-- **Membership in the language of a grammar code is checking**, uniformly in the code. -/
theorem mem_language_iff_checks (c : CFGCode T) (w : List T) :
    w ∈ c.toCFG.language ↔ ∃ k, Checks sys c.toSRS k ([.inr c.1], w.map .inl) := by
  rw [← derives_iff_checks, ← derives_toCFG_iff]
  simp [ContextFreeGrammar.mem_language_iff, symOf, Function.comp_def]

end CFG

end DiagonaLean.Foundations.Grammar
