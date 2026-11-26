/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import Mathlib.Computability.ContextFreeGrammar

@[expose] public section

/-! # Ambiguity of CFGs

Parse trees (`ParseTree`) and forests (`Forest`) for a context-free grammar from Mathlib, the
terminal `yield` of a parse tree, and `DecisionProblem`, the property of a grammar of being
ambiguous: some word has two distinct parse trees from the start symbol. Its former alias
`AmbigCFGProblem` is deprecated.

This is one of the standard problems shown undecidable by reduction from PCP
(see [HopcroftMotwaniUllman2006] Theorem 9.20).

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

namespace DiagonaLean.AmbigCFG

universe u

variable {T : Type u}

mutual
  /-- A parse tree for the grammar `G` rooted at the nonterminal `n`. -/
  inductive ParseTree (G : ContextFreeGrammar T) : G.NT → Type u
    | node (r : ContextFreeRule T G.NT) (hr : r ∈ G.rules) (children : Forest G r.output) :
        ParseTree G r.input

  /-- A sequence of subtrees corresponding to the symbol list `ss`. Terminals are stored
    directly. -/
  inductive Forest (G : ContextFreeGrammar T) : List (Symbol T G.NT) → Type u
    | nil : Forest G []
    | consT (t : T) (rest : Forest G ss) : Forest G (Symbol.terminal t :: ss)
    | consN {n : G.NT} (tree : ParseTree G n) (rest : Forest G ss) :
        Forest G (Symbol.nonterminal n :: ss)
end

mutual
  /-- The terminal word read sequentially off the leaves of the parse tree. -/
  def ParseTree.yield {G : ContextFreeGrammar T} {n : G.NT} : ParseTree G n → List T
    | .node _ _ children => children.yield

  /-- The sequentially concatenated yield of a forest of subtrees. -/
  def Forest.yield {G : ContextFreeGrammar T} {ss : List (Symbol T G.NT)} : Forest G ss → List T
    | .nil           => []
    | .consT t rest  => t :: rest.yield
    | .consN tr rest => tr.yield ++ rest.yield
end

/-- A grammar is ambiguous if a terminal word has at least two distinct parse trees generated from
  the start symbol. -/
def DecisionProblem (G : ContextFreeGrammar T) : Prop :=
  ∃ (t1 t2 : ParseTree G G.initial), t1 ≠ t2 ∧ t1.yield = t2.yield

/-- The former alias of `DecisionProblem`. -/
@[deprecated DecisionProblem (since := "2026-11-23")]
abbrev AmbigCFGProblem : ContextFreeGrammar T → Prop := DecisionProblem

end DiagonaLean.AmbigCFG
