/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Grammar.ToSRS

@[expose] public section

/-! # Membership for unrestricted grammars

An unrestricted (type 0) grammar over terminals `T` is a string rewriting system over terminals and
nonterminals together, with a start symbol. A grammar code (`GrammarCode T`) numbers the
nonterminals: a start symbol and a list of rules over `T ⊕ ℕ`. Its language is the set of terminal
words that the start symbol rewrites to (`GrammarCode.language`). `IsType0` is Chomsky's condition
that every left side contains a nonterminal; every context-free grammar code is a grammar code with
the same language (`language_toGrammarCode`).

The membership problem asks whether a word belongs to the language (`DecisionProblem`);
`EmptyWordProblem` is the special case of the empty word.

To audit the definition, read `GrammarCode.language` and `decisionProblem_mk` (membership
`w ∈ g.language`), which is pinned in `scripts/HeadlineTest.lean`.

## References

* N. Chomsky, *On certain formal properties of grammars* (1959)
* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

namespace DiagonaLean.GrammarMem

open DiagonaLean.Foundations.Grammar DiagonaLean.Foundations.Rewriting

variable {T : Type}

/-- A grammar code: a start symbol and rewriting rules over terminals `T` and numbered
nonterminals. -/
abbrev GrammarCode (T : Type) := ℕ × SRS (T ⊕ ℕ)

/-- The language of a grammar code: the terminal words that the start symbol rewrites to. -/
def GrammarCode.language (g : GrammarCode T) : Language T :=
  { w | g.2.Derives [.inr g.1] (w.map .inl) }

/-- Chomsky's condition for type 0, as a test: every left side contains a nonterminal. -/
def isType0 (g : GrammarCode T) : Bool :=
  g.2.all fun lr => lr.lhs.any fun s => Sum.elim (fun _ => false) (fun _ => true) s

/-- Chomsky's condition for type 0: every left side contains a nonterminal. -/
def IsType0 (g : GrammarCode T) : Prop := isType0 g = true

/-- A grammar code is of type 0 iff every left side contains a nonterminal. -/
theorem isType0_iff (g : GrammarCode T) :
    IsType0 g ↔ ∀ lr ∈ g.2, ∃ n, (.inr n : T ⊕ ℕ) ∈ lr.lhs := by
  simp only [IsType0, isType0, List.all_eq_true, List.any_eq_true]
  refine forall₂_congr fun lr _ => ⟨fun ⟨s, hs, h⟩ => ?_, fun ⟨n, hn⟩ => ⟨_, hn, rfl⟩⟩
  rcases s with s | n
  · simp at h
  · exact ⟨n, hs⟩

/-- `IsType0` is decidable. -/
instance : DecidablePred (IsType0 (T := T)) := fun _ => inferInstanceAs (Decidable (_ = _))

/-! ### The problem on instances, for the reductions and the computability statements -/

/-- **The membership problem on an instance `(g, w)`**, for the reductions and the computability
statements: is `w` in the language of `g`? Read it curried, `decisionProblem_mk`. -/
def DecisionProblem (x : GrammarCode T × List T) : Prop := x.2 ∈ x.1.language

/-- The problem on an instance `(g, w)` is membership of `w` in the language of `g`. -/
@[simp] theorem decisionProblem_mk (g : GrammarCode T) (w : List T) :
    DecisionProblem (g, w) ↔ w ∈ g.language := Iff.rfl

/-- Is the empty word in the language of the grammar? -/
def EmptyWordProblem (g : GrammarCode T) : Prop := [] ∈ g.language

/-! ### Context-free grammar codes as grammar codes -/

/-- A context-free grammar code as a grammar code. -/
def toGrammarCode (c : CFGCode T) : GrammarCode T := (c.1, c.toSRS)

/-- **A context-free grammar code and its grammar code have the same language.** -/
theorem language_toGrammarCode [DecidableEq T] (c : CFGCode T) :
    (toGrammarCode c).language = c.toCFG.language := by
  ext w
  change c.toSRS.Derives [.inr c.1] (w.map .inl) ↔ w ∈ c.toCFG.language
  rw [ContextFreeGrammar.mem_language_iff, ← derives_toCFG_iff]
  simp [symOf, Function.comp_def]

/-- A context-free grammar code is of type 0. -/
theorem isType0_toGrammarCode (c : CFGCode T) : IsType0 (toGrammarCode c) := by
  rw [isType0_iff]
  intro lr hlr
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hlr
  exact ⟨r.1, List.mem_singleton.2 rfl⟩

end DiagonaLean.GrammarMem
