/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Grammar.Code
import DiagonaLean.Foundations.Rewriting.SRS

@[expose] public section

/-! # Context-free grammar codes as string rewriting systems

A rule `n → rhs` of a context-free grammar code is the rewriting rule `[.inr n] ⟶ rhs`
(`CFGCode.toSRS`), over terminals and numbered nonterminals together (`T ⊕ ℕ`). One step of the
grammar is one step of this system (`produces_toCFG_iff`), and Mathlib's derivation relation of the
grammar agrees with derivability in the system (`derives_toCFG_iff`).

This file needs only the definitions of rewriting systems, so a problem stated through it, such as
membership for grammar codes (`GrammarMem/Basic.lean`), does not import the derivation checker of
`Foundations/Grammar/Rewriting.lean` or the computability machinery it needs.

## Main statements

* `CFGCode.toSRS`, `produces_toCFG_iff`, `derives_toCFG_iff`.
-/

namespace DiagonaLean.Foundations.Grammar

open DiagonaLean.Foundations.Rewriting Relation

variable {T : Type}

section CFG

variable [DecidableEq T]

/-- The rewriting system of a context-free grammar code: a rule `n → rhs` rewrites `[.inr n]` to
`rhs`. -/
def CFGCode.toSRS (c : CFGCode T) : SRS (T ⊕ ℕ) := c.2.map fun r => ⟨[.inr r.1], r.2⟩

omit [DecidableEq T] in
/-- `symOf` is injective. -/
theorem symOf_injective {N : Type} : Function.Injective (symOf : T ⊕ N → Symbol T N) := by
  rintro (a | a) (b | b) h <;> simp_all [symOf]

/-- The inverse of `symOf`. -/
def unSym {N : Type} : Symbol T N → T ⊕ N
  | .terminal t => .inl t
  | .nonterminal n => .inr n

omit [DecidableEq T] in
/-- `unSym` is a right inverse of `symOf`. -/
theorem symOf_unSym {N : Type} (x : Symbol T N) : symOf (unSym x) = x := by
  cases x <;> rfl

omit [DecidableEq T] in
/-- Mapping `unSym`, then `symOf`, over a string gives the string back. -/
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
    refine SRS.step_iff.2 ⟨⟨[.inr s.1], s.2⟩, List.mem_map_of_mem hs, p, q, by simp, ?_⟩
    apply List.map_injective_iff.2 symOf_injective
    simpa [ruleOf] using hv
  · rintro ⟨hlr, p, q⟩
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

end CFG

end DiagonaLean.Foundations.Grammar
