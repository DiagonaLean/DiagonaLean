/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Grammar.Rewriting

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

## References

* N. Chomsky, *On certain formal properties of grammars* (1959)
* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

namespace DiagonaLean.GrammarMem

open DiagonaLean.Foundations.Grammar

variable {T : Type}

/-- A grammar code: a start symbol and rewriting rules over terminals `T` and numbered
nonterminals. -/
abbrev GrammarCode (T : Type) := ℕ × SRS (T ⊕ ℕ)

/-- The language of a grammar code: the terminal words that the start symbol rewrites to. -/
def GrammarCode.language (g : GrammarCode T) : Language T :=
  { w | g.2.Derives [.inr g.1] (w.map .inl) }

/-- Chomsky's condition for type 0, as a test: every left side contains a nonterminal. -/
def isType0 (g : GrammarCode T) : Bool :=
  g.2.all fun lr => lr.1.any fun s => Sum.elim (fun _ => false) (fun _ => true) s

/-- Chomsky's condition for type 0: every left side contains a nonterminal. -/
def IsType0 (g : GrammarCode T) : Prop := isType0 g = true

theorem isType0_iff (g : GrammarCode T) : IsType0 g ↔ ∀ lr ∈ g.2, ∃ n, (.inr n : T ⊕ ℕ) ∈ lr.1 := by
  simp only [IsType0, isType0, List.all_eq_true, List.any_eq_true]
  refine forall₂_congr fun lr _ => ⟨fun ⟨s, hs, h⟩ => ?_, fun ⟨n, hn⟩ => ⟨_, hn, rfl⟩⟩
  rcases s with s | n
  · simp at h
  · exact ⟨n, hs⟩

instance : DecidablePred (IsType0 (T := T)) := fun _ => inferInstanceAs (Decidable (_ = _))

/-- The membership problem: is the word in the language of the grammar? -/
def DecisionProblem (x : GrammarCode T × List T) : Prop := x.2 ∈ x.1.language

/-- Is the empty word in the language of the grammar? -/
def EmptyWordProblem (g : GrammarCode T) : Prop := [] ∈ g.language

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

/-! ### A fresh start symbol -/

namespace Start

variable {R : SRS T} {S : T}

theorem derives_mono {R' : SRS T} (h : ∀ lr ∈ R, lr ∈ R') {u v : List T} (hd : R.Derives u v) :
    SRS.Derives R' u v := by
  induction hd with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨lr, hlr, p, q, rfl, rfl⟩ := hs
    exact ih.tail ⟨lr, h lr hlr, p, q, rfl, rfl⟩

/-- **A fresh start symbol.** If `S` occurs in no rule of `R`, and every left side of `R` is
non-empty, then `[S]` rewrites under `[S] → rhs` and `R` to a string without `S` iff `rhs` rewrites
to it under `R`. -/
theorem derives_start (hS : ∀ lr ∈ R, S ∉ lr.1 ∧ S ∉ lr.2) (hne : ∀ lr ∈ R, lr.1 ≠ [])
    {rhs : List T} (hrhs : S ∉ rhs) {v : List T} (hv : S ∉ v) :
    SRS.Derives (([S], rhs) :: R) [S] v ↔ R.Derives rhs v := by
  constructor
  · intro h
    -- away from `S`, a step of the larger system is a step of `R`
    have inv : ∀ {u u'}, S ∉ u → SRS.Step (([S], rhs) :: R) u u' → R.Step u u' ∧ S ∉ u' := by
      intro u u' hu hs
      obtain ⟨lr, hlr, p, q, rfl, rfl⟩ := hs
      rcases List.mem_cons.1 hlr with rfl | hlr
      · simp at hu
      · refine ⟨⟨lr, hlr, p, q, rfl, rfl⟩, ?_⟩
        simp only [List.mem_append, not_or] at hu ⊢
        exact ⟨⟨hu.1.1, (hS lr hlr).2⟩, hu.2⟩
    have run : ∀ {u}, S ∉ u → SRS.Derives (([S], rhs) :: R) u v → R.Derives u v := by
      intro u hu hd
      induction hd using Relation.ReflTransGen.head_induction_on with
      | refl => exact .refl
      | head hstep _ ih =>
        obtain ⟨hR, hc⟩ := inv hu hstep
        exact (ih hc).head hR
    rcases h.cases_head with heq | ⟨s₁, ⟨lr, hlr, p, q, h₁, rfl⟩, hrest⟩
    · exact absurd (heq ▸ List.mem_singleton_self S) hv
    · rcases List.mem_cons.1 hlr with rfl | hlr
      · have : p = [] ∧ q = [] := by
          have hl := congrArg List.length h₁
          simp only [List.length_append, List.length_singleton] at hl
          exact ⟨List.length_eq_zero_iff.1 (by omega), List.length_eq_zero_iff.1 (by omega)⟩
        obtain ⟨rfl, rfl⟩ := this
        exact run hrhs (by simpa using hrest)
      · exfalso
        have hl := congrArg List.length h₁
        simp only [List.length_append, List.length_singleton] at hl
        have hp : p = [] := List.length_eq_zero_iff.1 (by
          have := List.length_pos_of_ne_nil (hne lr hlr); omega)
        have hq : q = [] := List.length_eq_zero_iff.1 (by
          have := List.length_pos_of_ne_nil (hne lr hlr); omega)
        subst hp hq
        simp only [List.nil_append, List.append_nil] at h₁
        exact (hS lr hlr).1 (h₁ ▸ List.mem_singleton_self S)
  · intro h
    exact (derives_mono (fun lr hlr => List.mem_cons_of_mem _ hlr) h).head
      ⟨([S], rhs), List.mem_cons_self, [], [], by simp, by simp⟩

end Start

end DiagonaLean.GrammarMem
