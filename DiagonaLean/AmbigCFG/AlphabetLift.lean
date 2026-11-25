/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.AmbigCFG.Encode
import DiagonaLean.AmbigCFG.MachineLevel
import DiagonaLean.Foundations.Codes.Tactic
import DiagonaLean.Foundations.Computability.HaltResults

@[expose] public section

/-! # Ambiguity of grammar codes over every alphabet with two letters

Encoding the terminals of a grammar by a code keeps and reflects ambiguity
(`decisionProblem_grammarEncode_iff`), so on grammar codes ambiguity is a functor on codes
(`ambCodeFunctor`), and the lifting of `Foundations.Codes.Functor` moves the results over the
terminals `Bool ⊕ ℕ` (`AmbigCFG.codeFromHaltSum`, through `ambCode`) to grammar codes over any
alphabet with two distinct letters: the classical statement, with a finite terminal alphabet.

## Main statements

* `AmbigCFG.synthCodeFromHaltOver`: `SynthHaltReduction` over any alphabet with two distinct
  letters.
* `AmbigCFG.codeFromHaltOver`: a halting reduction, proved computable, over any alphabet with two
  distinct letters.
* `AmbigCFG.Code.haltHard`, `AmbigCFG.Code.not_computablePred`, `AmbigCFG.Code.not_machineDecidable`
  (`halt_results`): over every nontrivial `Primcodable` alphabet.
* `ambigCFGCode_manyOneEquiv`: many-one equivalent over any two such alphabets.
-/

namespace DiagonaLean.AmbigCFG.MachineLevel

open DiagonaLean.Foundations.Grammar DiagonaLean.Foundations.Codes
  DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions

variable {T α : Type}

open Classical in
/-- Ambiguity of a grammar code, with classical decidable equality of terminals, so that it is
defined over every alphabet (the grammar does not depend on the instance, `codeProblem_iff`). -/
def CodeProblem (p : CFGCode T) : Prop := AmbigCFG.DecisionProblem p.toCFG

theorem codeProblem_iff [DecidableEq T] (p : CFGCode T) :
    CodeProblem p ↔ AmbigCFG.DecisionProblem p.toCFG := by
  unfold CodeProblem
  convert Iff.rfl

theorem codeProblem_eq [DecidableEq T] :
    @CodeProblem T = fun p => AmbigCFG.DecisionProblem p.toCFG :=
  funext fun p => propext (codeProblem_iff p)

/-- **Ambiguity of grammar codes, as a functor on codes.** -/
abbrev ambCodeFunctor : CodeFunctor IsCode where
  Inst T := CFGCode T
  map c p := presEncode c p
  Prob p := CodeProblem p
  map_unit p := presEncode_unit p
  map_kcomp c₁ c₂ p := presEncode_kcomp c₁ c₂ p
  natural {T β} c hc p := by
    classical
    rw [codeProblem_iff, codeProblem_iff, toCFG_presEncode hc]
    exact decisionProblem_grammarEncode_iff hc
  supp := presTerminals
  map_congr _ h := presEncode_congr h

/-- The two forms of the problem reduce to each other by the identity. -/
def codeProblemReduces [DecidableEq T] :
    (fun p : CFGCode T => AmbigCFG.DecisionProblem p.toCFG) ⪯_s @CodeProblem T :=
  ⟨id, fun p => (codeProblem_iff p).symm⟩

/-- The two forms of the problem reduce to each other by the identity. -/
def codeProblemReduces' [DecidableEq T] :
    @CodeProblem T ⪯_s fun p : CFGCode T => AmbigCFG.DecisionProblem p.toCFG :=
  ⟨id, fun p => codeProblem_iff p⟩

/-- **Ambiguity of grammar codes is synthetically halting-hard over any alphabet `α` with two
distinct letters
`b0`, `b1`**: from PCP over `Bool` to codes over `Bool ⊕ ℕ`, then the lifting. -/
def _root_.DiagonaLean.AmbigCFG.synthCodeFromHaltOver [DecidableEq α] (b0 b1 : α) (hne : b0 ≠ b1) :
    SynthHaltReduction fun c : CFGCode α => AmbigCFG.DecisionProblem c.toCFG :=
  have u₀ : SynthHaltReduction fun c : CFGCode (Bool ⊕ ℕ) => AmbigCFG.DecisionProblem c.toCFG := by
    synth_reduce_from (PCP.synthFromHaltOver false true Bool.false_ne_true) with ambCode
      using pcp_reducesto_ambigCFGCode_spec
  have u : SynthHaltReduction (@CodeProblem (Bool ⊕ ℕ)) :=
    SynthHaltReduction.comp u₀ codeProblemReduces
  have u' : SynthHaltReduction (@CodeProblem α) := by code_lift ambCodeFunctor from u
  SynthHaltReduction.comp u' codeProblemReduces'

/-- The former name of `AmbigCFG.synthCodeFromHaltOver`. -/
@[deprecated DiagonaLean.AmbigCFG.synthCodeFromHaltOver (since := "2026-11-23")]
abbrev undecidableAmbigCFGCodeOf := @DiagonaLean.AmbigCFG.synthCodeFromHaltOver

/-- **Alphabet invariance of ambiguity on grammar codes**: over any two nontrivial `Primcodable`
alphabets, ambiguity of grammar codes is many-one equivalent. -/
theorem ambigCFGCode_manyOneEquiv {β : Type} [Primcodable α] [Primcodable β] [Nontrivial α]
    [Nontrivial β] [DecidableEq α] [DecidableEq β] :
    ManyOneEquiv (fun c : CFGCode α => AmbigCFG.DecisionProblem c.toCFG)
      fun c : CFGCode β => AmbigCFG.DecisionProblem c.toCFG := by
  have h : ManyOneEquiv (@CodeProblem α) (@CodeProblem β) := by code_lift ambCodeFunctor
  rwa [codeProblem_eq, codeProblem_eq] at h

end DiagonaLean.AmbigCFG.MachineLevel

namespace DiagonaLean.AmbigCFG

open DiagonaLean.AmbigCFG.MachineLevel DiagonaLean.Foundations.Codes
  DiagonaLean.Foundations.Computability DiagonaLean.Foundations.Grammar

variable {α : Type} [Primcodable α] [DecidableEq α]

/-- **Ambiguity of grammar codes is halting-hard over any alphabet with two distinct letters**:
`codeFromHaltSum` over `Bool ⊕ ℕ`, then the lifting along `ambCodeFunctor`, proved computable. -/
def codeFromHaltOver (b0 b1 : α) (hne : b0 ≠ b1) :
    HaltReduction fun c : CFGCode α => AmbigCFG.DecisionProblem c.toCFG := by
  have h : HaltReduction (@CodeProblem (Bool ⊕ ℕ)) := by
    rw [codeProblem_eq]
    exact codeFromHaltSum false true Bool.false_ne_true
  rw [← codeProblem_eq]
  code_lift ambCodeFunctor from h

section
variable [Nontrivial α]

halt_results Code for (fun c : CFGCode α => AmbigCFG.DecisionProblem c.toCFG)
  over_letters from codeFromHaltOver

end

end DiagonaLean.AmbigCFG
