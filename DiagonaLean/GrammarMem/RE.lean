/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.GrammarMem.Basic
import DiagonaLean.GrammarMem.Reductions.SemiThue_to_GrammarMem
import DiagonaLean.SemiThue.RE

@[expose] public section

/-! # Membership in the language of a grammar is recursively enumerable

A word `w` is in the language of a grammar code `(s, R)` iff the start symbol `s` rewrites to `w` in
`R`, an instance of the word problem for string rewriting systems, and the instance `(R, [s], w)` is
a primitive recursive function of `(s, R)` and `w`. The word problem is recursively enumerable
(`SemiThue.rePred`), so membership is (`GrammarMem.rePred`), and so is the special case of the empty
word for grammars of type 0 (`GrammarMem.EmptyWord.rePred`). With `GrammarMem.haltHard` and
`GrammarMem.EmptyWord.haltHard` both are as hard as the halting problem and no harder.

## Main statements

* `GrammarMem.rePred`: membership in the language of a grammar is recursively enumerable.
* `GrammarMem.EmptyWord.rePred`: whether a grammar of type 0 generates the empty word is
  recursively enumerable.
-/

namespace DiagonaLean.GrammarMem

variable {T : Type} [Primcodable T]

/-- **Membership in the language of a grammar is recursively enumerable**: it is the word problem
on `(R, [s], w)`. -/
theorem rePred : REPred (@DecisionProblem T) := by
  classical
  exact REPred.of_manyOneReducible (q := SemiThue.DecisionProblem)
    ⟨fun x : GrammarCode T × List T => (x.1.2, [Sum.inr x.1.1], x.2.map Sum.inl),
      Primrec.to_comp (by fun_prop), fun _ => Iff.rfl⟩ SemiThue.rePred

/-- **Whether a grammar of type 0 generates the empty word is recursively enumerable**: it is the
word problem on `(R, [s], [])`. -/
theorem EmptyWord.rePred :
    REPred fun g : { g : GrammarCode T // IsType0 g } => EmptyWordProblem g.1 := by
  classical
  exact REPred.of_manyOneReducible (q := SemiThue.DecisionProblem)
    ⟨fun g : { g : GrammarCode T // IsType0 g } => (g.1.2, [Sum.inr g.1.1], ([] : List (T ⊕ ℕ))),
      Primrec.to_comp (by fun_prop), fun _ => Iff.rfl⟩ SemiThue.rePred

end DiagonaLean.GrammarMem
