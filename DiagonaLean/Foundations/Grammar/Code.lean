/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.Primrec.List

@[expose] public section

/-! # Grammars presented by lists, and their codes

Mathlib's `ContextFreeGrammar T` has a type of nonterminals as a field and a `Finset` of rules, so
it is not `Primcodable`, and a statement about machines deciding a property of grammars cannot be
made about it. A grammar is presented here by its start symbol and a list of rules `lhs → rhs`, with the
symbols of a right-hand side written `.inl t` for a terminal and `.inr n` for a nonterminal
(`GrammarPres N T`). `GrammarPres.toCFG` is the grammar it presents. With natural numbers as
nonterminals, a presentation is a `CFGCode T`, which is `Primcodable` whenever `T` is.

A construction of grammars is written once as a presentation, polymorphic in the names of its
nonterminals: with the names of the original construction it presents the original grammar, and
with numbers it gives a code. The two are related by renaming nonterminals (`GrammarPres.map`), and
renaming them injectively does not change the language (`language_map_toCFG`).

## Main statements

* `GrammarPres.toCFG`: the grammar of a presentation.
* `CFGCode`: presentations with numbers as nonterminals.
* `mem_language_map_toCFG`, `language_map_toCFG`: an injective renaming of nonterminals keeps the
  language, and renaming terminals renames its words.
-/

namespace DiagonaLean.Foundations.Grammar

open ContextFreeGrammar

variable {T T' N M : Type}

/-- A grammar presented by its start symbol and a list of rules `lhs → rhs`; a symbol of a
right-hand side is `.inl t` for a terminal `t` and `.inr n` for a nonterminal `n`. -/
abbrev GrammarPres (N T : Type) := N × List (N × List (T ⊕ N))

/-- A grammar code: a presentation with natural numbers as nonterminals. -/
abbrev CFGCode (T : Type) := GrammarPres ℕ T

/-- The symbol written `s` in a presentation. -/
def symOf : T ⊕ N → Symbol T N := Sum.elim Symbol.terminal Symbol.nonterminal

/-- The rule written `r` in a presentation. -/
def ruleOf (r : N × List (T ⊕ N)) : ContextFreeRule T N := ⟨r.1, r.2.map symOf⟩

/-- The grammar of a presentation. It is reducible, so that `p.toCFG.NT` is `N` to `rw`, `simp` and
unification. -/
@[reducible] def GrammarPres.toCFG [DecidableEq T] [DecidableEq N] (p : GrammarPres N T) :
    ContextFreeGrammar T where
  NT := N
  initial := p.1
  rules := (p.2.map ruleOf).toFinset

/-- Renaming the terminals by `f` and the nonterminals by `e`. -/
def GrammarPres.map (f : T → T') (e : N → M) (p : GrammarPres N T) : GrammarPres M T' :=
  (e p.1, p.2.map fun r => (e r.1, r.2.map (Sum.map f e)))

/-! ### Renaming symbols -/

/-- Renaming a symbol: terminals by `f`, nonterminals by `e`. -/
def Symbol.mapBoth (f : T → T') (e : N → M) : Symbol T N → Symbol T' M
  | .terminal t => .terminal (f t)
  | .nonterminal n => .nonterminal (e n)

theorem Symbol.mapBoth_injective {f : T → T'} {e : N → M} (hf : Function.Injective f)
    (he : Function.Injective e) : Function.Injective (Symbol.mapBoth f e) := by
  rintro (a | a) (b | b) h <;> simp only [Symbol.mapBoth, Symbol.terminal.injEq,
    Symbol.nonterminal.injEq, reduceCtorEq] at h
  · rw [hf h]
  · rw [he h]

theorem symOf_map (f : T → T') (e : N → M) (s : T ⊕ N) :
    symOf (Sum.map f e s) = Symbol.mapBoth f e (symOf s) := by
  rcases s with s | s <;> rfl

/-- Renaming a rule. -/
def ruleMap (f : T → T') (e : N → M) (r : ContextFreeRule T N) : ContextFreeRule T' M :=
  ⟨e r.input, r.output.map (Symbol.mapBoth f e)⟩

theorem ruleOf_map (f : T → T') (e : N → M) (r : N × List (T ⊕ N)) :
    ruleOf (e r.1, r.2.map (Sum.map f e)) = ruleMap f e (ruleOf r) := by
  simp [ruleOf, ruleMap, List.map_map, Function.comp_def, symOf_map]

theorem mem_rules_toCFG [DecidableEq T] [DecidableEq N] (p : GrammarPres N T)
    (r : ContextFreeRule T N) : r ∈ p.toCFG.rules ↔ ∃ s ∈ p.2, ruleOf s = r := by
  show r ∈ (p.2.map ruleOf).toFinset ↔ _
  rw [List.mem_toFinset, List.mem_map]

theorem mem_rules_map_toCFG [DecidableEq T] [DecidableEq T'] [DecidableEq N] [DecidableEq M]
    (f : T → T') (e : N → M) (p : GrammarPres N T) (r : ContextFreeRule T' M) :
    r ∈ (p.map f e).toCFG.rules ↔ ∃ s ∈ p.toCFG.rules, ruleMap f e s = r := by
  rw [mem_rules_toCFG]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simp only [GrammarPres.map, List.mem_map] at hs
    obtain ⟨s0, hs0, rfl⟩ := hs
    exact ⟨ruleOf s0, (mem_rules_toCFG p _).2 ⟨s0, hs0, rfl⟩, (ruleOf_map f e s0).symm⟩
  · rintro ⟨_, hs, rfl⟩
    obtain ⟨s0, hs0, rfl⟩ := (mem_rules_toCFG p _).1 hs
    exact ⟨_, List.mem_map_of_mem (f := fun r => (e r.1, r.2.map (Sum.map f e))) hs0,
      ruleOf_map f e s0⟩

/-! ### Rewriting commutes with renaming -/

theorem rewrites_map {f : T → T'} {e : N → M} {r : ContextFreeRule T N}
    {u v : List (Symbol T N)} (h : r.Rewrites u v) :
    (ruleMap f e r).Rewrites (u.map (Symbol.mapBoth f e)) (v.map (Symbol.mapBoth f e)) := by
  induction h with
  | head s =>
    simpa [ruleMap, Symbol.mapBoth] using
      ContextFreeRule.Rewrites.head (r := ruleMap f e r) (s.map (Symbol.mapBoth f e))
  | cons x _ ih => simpa using ContextFreeRule.Rewrites.cons (Symbol.mapBoth f e x) ih

/-- A rewrite by a renamed rule of a renamed string is the renaming of a rewrite, when the renaming
of nonterminals is injective. -/
theorem rewrites_of_map {f : T → T'} {e : N → M} (he : Function.Injective e)
    {r : ContextFreeRule T N} {u : List (Symbol T N)} {v' : List (Symbol T' M)}
    (h : (ruleMap f e r).Rewrites (u.map (Symbol.mapBoth f e)) v') :
    ∃ v, v' = v.map (Symbol.mapBoth f e) ∧ r.Rewrites u v := by
  obtain ⟨p', q', hu, rfl⟩ := ContextFreeRule.rewrites_iff.1 h
  rw [List.append_assoc, List.singleton_append] at hu
  obtain ⟨p, xq, rfl, rfl, hxq⟩ := List.map_eq_append_iff.1 hu
  obtain ⟨x, q, rfl, hx, rfl⟩ := List.map_eq_cons_iff.1 hxq
  rcases x with x | x
  · simp [Symbol.mapBoth, ruleMap] at hx
  · simp only [Symbol.mapBoth, ruleMap, Symbol.nonterminal.injEq] at hx
    obtain rfl := he hx
    refine ⟨p ++ r.output ++ q, by simp [ruleMap], ?_⟩
    exact ContextFreeRule.rewrites_iff.2 ⟨p, q, by simp, rfl⟩

/-- A string whose renaming is a word is a word. -/
theorem eq_map_terminal_of_map {f : T → T'} {e : N → M} :
    ∀ {v : List (Symbol T N)} {w' : List T'},
      v.map (Symbol.mapBoth f e) = w'.map Symbol.terminal → ∃ w : List T, v = w.map Symbol.terminal
  | [], _, _ => ⟨[], rfl⟩
  | .terminal t :: v, [], h => by simp at h
  | .terminal t :: v, _ :: w', h => by
    obtain ⟨w, rfl⟩ := eq_map_terminal_of_map (List.cons.inj h).2
    exact ⟨t :: w, rfl⟩
  | .nonterminal n :: v, [], h => by simp at h
  | .nonterminal n :: v, _ :: w', h => by simp [Symbol.mapBoth] at h

/-- Renaming a word is renaming its letters. -/
theorem map_terminal_map_eq {f : T → T'} {e : N → M} :
    ∀ {w : List T} {w' : List T'},
      (w.map Symbol.terminal).map (Symbol.mapBoth f e) = w'.map Symbol.terminal → w.map f = w'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: w, b :: w', h => by
    simp only [List.map_cons, List.cons.injEq, Symbol.mapBoth, Symbol.terminal.injEq] at h
    rw [List.map_cons, h.1, map_terminal_map_eq h.2]

section

variable [DecidableEq T] [DecidableEq T'] [DecidableEq N] [DecidableEq M]
  {f : T → T'} {e : N → M} {p : GrammarPres N T}

theorem derives_map {u v : List (Symbol T N)} (h : p.toCFG.Derives u v) :
    (p.map f e).toCFG.Derives (u.map (Symbol.mapBoth f e)) (v.map (Symbol.mapBoth f e)) := by
  induction h with
  | refl => exact Derives.refl _
  | tail _ hstep ih =>
    obtain ⟨r, hr, hrw⟩ := hstep
    exact ih.trans_produces
      ⟨ruleMap f e r, (mem_rules_map_toCFG f e p _).2 ⟨r, hr, rfl⟩, rewrites_map hrw⟩

theorem derives_of_map (he : Function.Injective e) {u : List (Symbol T N)}
    {v' : List (Symbol T' M)}
    (h : (p.map f e).toCFG.Derives (u.map (Symbol.mapBoth f e)) v') :
    ∃ v, v' = v.map (Symbol.mapBoth f e) ∧ p.toCFG.Derives u v := by
  induction h with
  | refl => exact ⟨u, rfl, Derives.refl _⟩
  | tail _ hstep ih =>
    obtain ⟨v, rfl, hv⟩ := ih
    obtain ⟨r', hr', hrw⟩ := hstep
    obtain ⟨r, hr, rfl⟩ := (mem_rules_map_toCFG f e p r').1 hr'
    obtain ⟨w, rfl, hw⟩ := rewrites_of_map he hrw
    exact ⟨w, rfl, hv.trans_produces ⟨r, hr, hw⟩⟩

/-- **The words of a renamed presentation are the renamed words.** When the renaming `e` of
nonterminals is injective, the words of `p.map f e` are the words of `p` with their letters renamed
by `f`. -/
theorem mem_language_map_toCFG (he : Function.Injective e) (w' : List T') :
    w' ∈ (p.map f e).toCFG.language ↔ ∃ w ∈ p.toCFG.language, w.map f = w' := by
  simp only [mem_language_iff]
  constructor
  · intro h
    have h' : (p.map f e).toCFG.Derives
        ([Symbol.nonterminal p.toCFG.initial].map (Symbol.mapBoth f e)) (w'.map Symbol.terminal) :=
      h
    obtain ⟨v, hv, hd⟩ := derives_of_map he h'
    obtain ⟨w, rfl⟩ := eq_map_terminal_of_map hv.symm
    refine ⟨w, hd, ?_⟩
    exact map_terminal_map_eq hv.symm
  · rintro ⟨w, hw, rfl⟩
    have := derives_map (f := f) (e := e) hw
    simpa [List.map_map, Function.comp_def, Symbol.mapBoth, GrammarPres.map] using this

/-- **An injective renaming of nonterminals keeps the language.** -/
theorem language_map_toCFG (he : Function.Injective e) :
    (p.map id e).toCFG.language = p.toCFG.language := by
  ext w
  rw [mem_language_map_toCFG he]
  simp

end

end DiagonaLean.Foundations.Grammar
