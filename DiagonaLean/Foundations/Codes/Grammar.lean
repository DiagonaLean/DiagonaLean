/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Codes.Basic
import Mathlib.Computability.ContextFreeGrammar
import DiagonaLean.Foundations.Grammar.Code

@[expose] public section

/-! # Changing the terminal alphabet of a context-free grammar

A code `c` on terminals extends to sentential forms by leaving nonterminals alone (`symCode c`).
Encoding the right side of every rule gives a grammar `grammarEncode c hc G` over the code
alphabet. A nonterminal occurs in an encoded sentential form only as the image of a nonterminal
(`split_nonterminal`), so every step from an encoded sentential form is the image of a step, with
no assumption on `c`; the language of `grammarEncode c hc G` is the image of the language of `G`
(`mem_language_encode_iff`). When `c` is a code, words of the two languages correspond one to one,
so non-emptiness of an intersection is preserved and reflected (`intersection_encode_iff`).

Grammar codes (`Foundations.Grammar.GrammarPres`) keep their rules in a list, so encoding them
(`presEncode`) needs no proof, and the grammar of the encoded code is the encoded grammar
(`toCFG_presEncode`): on codes, encoding terminals is a total function, as a reduction needs.

The code is needed already to build `grammarEncode c hc G`: Mathlib keeps the rules in a
`Finset`, and mapping them without decidable equality takes an embedding, so `symCode c` must be a
code (`isCode_symCode`).
-/

namespace DiagonaLean.Foundations.Codes

variable {T β N : Type}

open List

/-- The code of sentential forms: terminals are encoded by `c`, nonterminals stay. -/
def symCode (c : T → List β) : Symbol T N → List (Symbol β N)
  | .terminal t => (c t).map .terminal
  | .nonterminal n => [.nonterminal n]

/-- A word of terminals encodes to the word of terminals of its encoding. -/
@[simp] theorem encode_symCode_map_terminal (c : T → List β) (w : List T) :
    encode (symCode (N := N) c) (w.map .terminal) = (encode c w).map .terminal := by
  induction w <;> simp_all [symCode]

/-- An encoded sentential form without nonterminals comes from one without nonterminals. -/
theorem eq_map_terminal_of_encode {c : T → List β} {v : List (Symbol T N)} {w : List β}
    (h : encode (symCode c) v = w.map .terminal) : ∃ y, v = y.map .terminal ∧ encode c y = w := by
  induction v generalizing w with
  | nil => exact ⟨[], rfl, by simpa using h.symm⟩
  | cons a v ih =>
    rcases a with t | n
    · obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := map_eq_append_iff.1 h.symm
      obtain ⟨y, rfl, rfl⟩ := ih h₂.symm
      exact ⟨t :: y, rfl, by
        simpa [symCode] using (map_injective_iff.2 (fun _ _ h => Symbol.terminal.inj h) h₁).symm⟩
    · rcases w with _ | ⟨b, w⟩ <;> simp [symCode] at h

/-- A nonterminal occurs in an encoded sentential form only as the image of a nonterminal. -/
theorem split_nonterminal {c : T → List β} {u : List (Symbol T N)} {p q : List (Symbol β N)}
    {n : N} (h : encode (symCode c) u = p ++ .nonterminal n :: q) :
    ∃ u₁ u₂, u = u₁ ++ .nonterminal n :: u₂ ∧ p = encode (symCode c) u₁ ∧
      q = encode (symCode c) u₂ := by
  induction u generalizing p with
  | nil => simp at h
  | cons a u ih =>
    rcases a with t | m
    · rw [encode_cons] at h
      rcases append_eq_append_iff.1 h with ⟨p', rfl, h'⟩ | ⟨p', h₁, h₂⟩
      · obtain ⟨u₁, u₂, rfl, rfl, rfl⟩ := ih (p := p') h'
        exact ⟨.terminal t :: u₁, u₂, rfl, rfl, rfl⟩
      · rcases p' with _ | ⟨x, p'⟩
        · obtain ⟨u₁, u₂, rfl, hu₁, rfl⟩ := ih (p := []) h₂.symm
          exact ⟨.terminal t :: u₁, u₂, rfl, by rw [encode_cons, ← hu₁, append_nil, h₁, append_nil],
            rfl⟩
        · obtain ⟨rfl, -⟩ := cons.inj (h₂.trans (cons_append ..))
          have : Symbol.nonterminal n ∈ (c t).map (Symbol.terminal (N := N)) := by
            simp only [symCode] at h₁; rw [h₁]; simp
          simp at this
    · rcases p with _ | ⟨x, p⟩
      · obtain ⟨rfl, rfl⟩ : m = n ∧ encode (symCode c) u = q := by simpa [symCode] using h
        exact ⟨[], u, rfl, rfl, rfl⟩
      · simp only [encode_cons, symCode, cons_append, cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        obtain ⟨u₁, u₂, rfl, rfl, rfl⟩ := ih h
        exact ⟨.nonterminal m :: u₁, u₂, rfl, rfl, rfl⟩

/-- Every sentential form is a word of terminals, possibly followed by a nonterminal and more. -/
theorem terminals_or_split (u : List (Symbol T N)) :
    (∃ x : List T, u = x.map .terminal) ∨
      ∃ (x : List T) (n : N) (u' : List (Symbol T N)),
        u = x.map .terminal ++ .nonterminal n :: u' := by
  induction u with
  | nil => exact .inl ⟨[], rfl⟩
  | cons a u ih =>
    rcases a with t | n
    · rcases ih with ⟨x, rfl⟩ | ⟨x, n, u', rfl⟩
      · exact .inl ⟨t :: x, rfl⟩
      · exact .inr ⟨t :: x, n, u', rfl⟩
    · exact .inr ⟨[], n, u, rfl⟩

/-- A code on terminals gives a code on sentential forms. -/
theorem isCode_symCode {c : T → List β} (hc : IsCode c) : IsCode (symCode (N := N) c) := by
  intro u
  induction h : u.length using Nat.strong_induction_on generalizing u with
  | _ k ih =>
    intro v huv
    rcases terminals_or_split u with ⟨x, rfl⟩ | ⟨x, n, u', rfl⟩
    · obtain ⟨y, rfl, hy⟩ := eq_map_terminal_of_encode (by simpa using huv.symm)
      rw [hc hy]
    · have e : encode (symCode c) v =
          (encode c x).map .terminal ++ .nonterminal n :: encode (symCode c) u' := by
        rw [← huv]; simp [symCode]
      obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := split_nonterminal e
      obtain ⟨y, rfl, hy⟩ := eq_map_terminal_of_encode h₁.symm
      rw [hc hy, ih u'.length (by simp [← h]; omega) rfl h₂]

/-- Encoding the right side of a rule. -/
def ruleEncode (c : T → List β) (r : ContextFreeRule T N) : ContextFreeRule β N :=
  ⟨r.input, encode (symCode c) r.output⟩

/-- If `c` is a code, encoding the right sides of rules is injective. -/
theorem ruleEncode_injective {c : T → List β} (hc : IsCode c) :
    Function.Injective (ruleEncode (N := N) c) := by
  rintro ⟨_, _⟩ ⟨_, _⟩ h
  simp only [ruleEncode, ContextFreeRule.mk.injEq] at h
  rw [h.1, isCode_symCode hc h.2]

/-- The grammar with every terminal encoded by the code `c`. Reducible, so that its nonterminals
are `G.NT` for unification. -/
abbrev grammarEncode (c : T → List β) (hc : IsCode c) (G : ContextFreeGrammar T) :
    ContextFreeGrammar β where
  NT := G.NT
  initial := G.initial
  rules := G.rules.map ⟨ruleEncode c, ruleEncode_injective hc⟩

variable {c : T → List β} {hc : IsCode c} {G : ContextFreeGrammar T}

/-- A step of `G` maps to a step of the encoded grammar between the encoded sentential forms. -/
theorem produces_grammarEncode {u v : List (Symbol T G.NT)} (h : G.Produces u v) :
    (grammarEncode c hc G).Produces (encode (symCode c) u) (encode (symCode c) v) := by
  obtain ⟨r, hr, hrw⟩ := h
  obtain ⟨p, q, rfl, rfl⟩ := hrw.exists_parts
  refine ⟨ruleEncode c r, Finset.mem_map_of_mem _ hr, ?_⟩
  have := (ruleEncode c r).rewrites_of_exists_parts (encode (symCode c) p) (encode (symCode c) q)
  simpa [ruleEncode, symCode] using this

/-- Every step of the encoded grammar from an encoded sentential form is the image of a step of
`G`. -/
theorem produces_grammarEncode_inv {u : List (Symbol T G.NT)} {y : List (Symbol β G.NT)}
    (h : (grammarEncode c hc G).Produces (encode (symCode c) u) y) :
    ∃ v, G.Produces u v ∧ y = encode (symCode c) v := by
  obtain ⟨r', hr', hrw⟩ := h
  obtain ⟨r, hr, rfl⟩ := Finset.mem_map.1 hr'
  obtain ⟨p, q, hu, rfl⟩ := hrw.exists_parts
  obtain ⟨u₁, u₂, rfl, rfl, rfl⟩ := split_nonterminal (by simpa [ruleEncode] using hu)
  refine ⟨u₁ ++ r.output ++ u₂, ⟨r, hr, ?_⟩, by simp [ruleEncode]⟩
  simpa using ContextFreeRule.rewrites_of_exists_parts r u₁ u₂

/-- A derivation in `G` maps to a derivation in the encoded grammar between the encoded sentential
forms. -/
theorem derives_grammarEncode {u v : List (Symbol T G.NT)} (h : G.Derives u v) :
    (grammarEncode c hc G).Derives (encode (symCode c) u) (encode (symCode c) v) := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact ih.trans_produces (produces_grammarEncode hs)

/-- Every sentential form derived in the encoded grammar from an encoded sentential form is the
encoding of one derived in `G`. -/
theorem derives_grammarEncode_inv {u : List (Symbol T G.NT)} {y : List (Symbol β G.NT)}
    (h : (grammarEncode c hc G).Derives (encode (symCode c) u) y) :
    ∃ v, G.Derives u v ∧ y = encode (symCode c) v := by
  induction h with
  | refl => exact ⟨u, .refl _, rfl⟩
  | tail _ hs ih =>
    obtain ⟨v, hv, rfl⟩ := ih
    obtain ⟨v', hv', rfl⟩ := produces_grammarEncode_inv hs
    exact ⟨v', hv.trans_produces hv', rfl⟩

/-- The language of the encoded grammar is the image of the language. -/
theorem mem_language_encode_iff {w : List β} :
    w ∈ (grammarEncode c hc G).language ↔ ∃ v ∈ G.language, encode c v = w := by
  simp only [ContextFreeGrammar.mem_language_iff]
  constructor
  · intro h
    obtain ⟨v, hv, hw⟩ := derives_grammarEncode_inv (u := [.nonterminal G.initial])
      (by simpa [symCode] using h)
    obtain ⟨y, rfl, rfl⟩ := eq_map_terminal_of_encode hw.symm
    exact ⟨y, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    simpa [symCode] using derives_grammarEncode (hc := hc) hv

/-- **A code preserves and reflects non-emptiness of the intersection of two languages.** -/
theorem intersection_encode_iff (G₁ G₂ : ContextFreeGrammar T) :
    (∃ w, w ∈ (grammarEncode c hc G₁).language ∧ w ∈ (grammarEncode c hc G₂).language) ↔
      ∃ w, w ∈ G₁.language ∧ w ∈ G₂.language := by
  simp only [mem_language_encode_iff]
  constructor
  · rintro ⟨_, ⟨v₁, h₁, rfl⟩, ⟨v₂, h₂, he⟩⟩
    exact ⟨v₁, h₁, hc he ▸ h₂⟩
  · rintro ⟨v, h₁, h₂⟩
    exact ⟨_, ⟨v, h₁, rfl⟩, ⟨v, h₂, rfl⟩⟩

/-! ### Grammar codes -/

open DiagonaLean.Foundations.Grammar

/-- The code of the symbols of a grammar code: terminals are encoded by `c`, nonterminals stay. -/
def sumCode (c : T → List β) : T ⊕ N → List (β ⊕ N) :=
  Sum.elim (fun t => (c t).map Sum.inl) fun n => [Sum.inr n]

/-- Encoding the terminals of a grammar code. -/
def presEncode (c : T → List β) (p : GrammarPres N T) : GrammarPres N β :=
  (p.1, p.2.map fun r => (r.1, encode (sumCode c) r.2))

/-- The terminals of a grammar code. -/
def presTerminals (p : GrammarPres N T) : List T :=
  p.2.flatMap fun r => r.2.flatMap (Sum.elim (fun t => [t]) fun _ => [])

/-- Codes that agree on the terminals of a grammar code encode it alike. -/
theorem presEncode_congr {c c' : T → List β} {p : GrammarPres N T}
    (h : ∀ t ∈ presTerminals p, c t = c' t) : presEncode c p = presEncode c' p := by
  refine Prod.ext rfl (List.map_congr_left fun r hr => Prod.ext rfl
    (Codes.encode_congr fun s hs => ?_))
  cases s with
  | inl t =>
    simp only [sumCode, Sum.elim_inl]
    rw [h t (List.mem_flatMap.2 ⟨r, hr, List.mem_flatMap.2 ⟨.inl t, hs, by simp⟩⟩)]
  | inr n => rfl

/-- Encoding the symbols of a grammar code by `sumCode c` and then reading them as symbols is
reading them as symbols and then encoding by `symCode c`. -/
theorem map_symOf_encode (c : T → List β) (w : List (T ⊕ N)) :
    (encode (sumCode c) w).map symOf = encode (symCode c) (w.map symOf) := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    simp only [encode_cons, List.map_cons, List.map_append, ih]
    rcases s with t | n <;> simp [sumCode, symCode, symOf, Function.comp_def]

/-- `sumCode` of the identity code encodes every word as itself. -/
theorem encode_sumCode_unit (w : List (T ⊕ N)) : encode (sumCode (unit (α := T))) w = w := by
  induction w with
  | nil => rfl
  | cons s w ih => rcases s with t | n <;> simp_all [sumCode, unit]

/-- A word of terminals encodes by `sumCode c` to the word of terminals of its encoding by `c`. -/
theorem encode_sumCode_map_inl (c : T → List β) (l : List T) :
    encode (sumCode (N := N) c) (l.map Sum.inl) = (encode c l).map Sum.inl := by
  induction l <;> simp_all [sumCode]

/-- Encoding by `sumCode c₁`, then by `sumCode c₂`, is encoding by `sumCode (kcomp c₂ c₁)`. -/
theorem encode_sumCode_kcomp {γ : Type} (c₁ : T → List β) (c₂ : β → List γ) (w : List (T ⊕ N)) :
    encode (sumCode c₂) (encode (sumCode c₁) w) = encode (sumCode (kcomp c₂ c₁)) w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    rw [encode_cons, encode_append, ih, encode_cons]
    congr 1
    rcases s with t | n
    · exact encode_sumCode_map_inl c₂ (c₁ t)
    · rfl

/-- The identity code encodes every grammar code as itself. -/
@[simp] theorem presEncode_unit (p : GrammarPres N T) : presEncode unit p = p := by
  simp [presEncode, encode_sumCode_unit]

/-- Encoding a grammar code by `c₁`, then by `c₂`, is encoding it by `kcomp c₂ c₁`. -/
theorem presEncode_kcomp {γ : Type} (c₁ : T → List β) (c₂ : β → List γ) (p : GrammarPres N T) :
    presEncode c₂ (presEncode c₁ p) = presEncode (kcomp c₂ c₁) p := by
  simp only [presEncode, List.map_map, Function.comp_def, encode_sumCode_kcomp]

/-- **The grammar of the encoded code is the encoded grammar.** -/
theorem toCFG_presEncode [DecidableEq T] [DecidableEq β] [DecidableEq N] (hc : IsCode c)
    (p : GrammarPres N T) : (presEncode c p).toCFG = grammarEncode c hc p.toCFG := by
  show ContextFreeGrammar.mk N p.1 _ = ContextFreeGrammar.mk N p.1 _
  congr 1
  ext r
  simp only [presEncode, List.map_map, List.mem_toFinset, List.mem_map, Function.comp_def,
    Finset.mem_map, Function.Embedding.coeFn_mk]
  have e (x : N × List (T ⊕ N)) :
      ruleOf (x.1, encode (sumCode c) x.2) = ruleEncode c (ruleOf x) := by
    simp [ruleOf, ruleEncode, map_symOf_encode]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, (e x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, e x⟩

end DiagonaLean.Foundations.Codes
