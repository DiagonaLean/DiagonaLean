/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.EmpCFG.Basic
import DiagonaLean.GrammarMem.Basic
import DiagonaLean.SemiThue.RE
import DiagonaLean.Foundations.Computability.DerivePrimrec

@[expose] public section

/-! # Non-empty intersection of context-free languages is recursively enumerable

A word `w` is in the language of a context-free grammar code `c` iff the start symbol rewrites to
`w` in the rewriting system `c.toSRS` (`GrammarMem.language_toGrammarCode`), which holds iff some
program of the stack machine `srsSys` checks the derivation (`derives_iff_checks`). So the
languages of two codes meet iff some word `w` and two programs `k₁`, `k₂` pass a primitive
recursive check, and the problem on codes is recursively enumerable (`EmpCFG.code_rePred`). With
`EmpCFG.Code.haltHard` it is as hard as the halting problem and no harder.

## Main statements

* `EmpCFG.code_rePred`: whether the languages of two context-free grammar codes meet is
  recursively enumerable.
-/

namespace DiagonaLean.EmpCFG

open Foundations.Grammar Foundations.Computability

variable {α : Type} [Primcodable α] [DecidableEq α]

derive_primrec CFGCode.toSRS [Primcodable T]

/-- The program `k` of `srsSys` checks that the start symbol of `c` rewrites to `w` in
`c.toSRS`. -/
def ChecksWord (c : CFGCode α) (k : ℕ) (w : List α) : Prop :=
  StackProof.Checks srsSys c.toSRS k ([.inr c.1], w.map .inl)

/-- A word is in the language of a context-free grammar code `c` iff some program checks that the
start symbol rewrites to it. -/
theorem mem_language_iff_checksWord (c : CFGCode α) (w : List α) :
    w ∈ c.toCFG.language ↔ ∃ k, ChecksWord c k w :=
  (Iff.of_eq (congrArg (w ∈ ·) (GrammarMem.language_toGrammarCode c))).symm.trans
    (derives_iff_checks _ _ _)

/-- **Whether the languages of two context-free grammar codes meet is recursively enumerable**:
search for a word and the two derivations of it. -/
theorem code_rePred :
    REPred fun c : CFGCode α × CFGCode α => IntersectionNonempty c.1.toCFG c.2.toCFG :=
  REPred.of_exists_primrecPred_witness
    (q := fun (c : CFGCode α × CFGCode α) (x : List α × ℕ × ℕ) =>
      ChecksWord c.1 x.2.1 x.1 ∧ ChecksWord c.2 x.2.2 x.1)
    (PrimrecPred.and
      ((StackProof.checks_prim srsSys).comp (f := fun x : (CFGCode α × CFGCode α) ×
        (List α × ℕ × ℕ) => (x.1.1.toSRS, x.2.2.1, ([Sum.inr x.1.1.1], x.2.1.map Sum.inl)))
        (by fun_prop))
      ((StackProof.checks_prim srsSys).comp (f := fun x : (CFGCode α × CFGCode α) ×
        (List α × ℕ × ℕ) => (x.1.2.toSRS, x.2.2.2, ([Sum.inr x.1.2.1], x.2.1.map Sum.inl)))
        (by fun_prop)))
    fun c => by
      constructor
      · rintro ⟨w, h₁, h₂⟩
        obtain ⟨k₁, h₁⟩ := (mem_language_iff_checksWord c.1 w).1 h₁
        obtain ⟨k₂, h₂⟩ := (mem_language_iff_checksWord c.2 w).1 h₂
        exact ⟨(w, k₁, k₂), h₁, h₂⟩
      · rintro ⟨⟨w, k₁, k₂⟩, h₁, h₂⟩
        exact ⟨w, (mem_language_iff_checksWord c.1 w).2 ⟨k₁, h₁⟩,
          (mem_language_iff_checksWord c.2 w).2 ⟨k₂, h₂⟩⟩

end DiagonaLean.EmpCFG
