/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.PCP.Primrec
import DiagonaLean.EmpCFG.MachineLevel
import DiagonaLean.Foundations.Codes.Grammar
import DiagonaLean.Foundations.Codes.Tactic

@[expose] public section

/-! # Non-emptiness of CFG intersection over two letters

`undecidableEmpCFG` holds over the terminals `Term α = α ⊕ Tile α`, which include the tiles of the
PCP instance. Encoding the terminals of both grammars by a code preserves and reflects non-emptiness
of the intersection (`Foundations.Codes.intersection_encode_iff`), and `Term Bool` is countable,
so `Foundations.Codes.bitCode` moves the problem to any alphabet with two distinct letters
(`empCFGAlphabetLift`). `Undecidable.lean` uses it for `undecidableEmpCFGOf` and
`undecidableEmpCFGBool`.

Mathlib's grammars keep their rules in a `Finset`, so encoding them needs the proof that the code
is a code, and is not the action of a functor. Grammar codes keep their rules in a list: on pairs
of grammar codes the problem is a functor on codes (`empCodeFunctor`), and the lifting of
`Foundations.Codes.Functor` gives the machine-level statements over every nontrivial alphabet
(`not_computablePred_empCFGCodeOf`, `not_machineDecidable_empCFGCodeOf`).
-/

open DiagonaLean.Synthetic.Definitions DiagonaLean.Foundations.Codes

namespace DiagonaLean.EmpCFG.Reduction

variable {T α : Type}

/-- **The reduction.** Both grammars with their terminals encoded by `bitCode b0 b1`. -/
def empCFGLift [Encodable T] (b0 b1 : α) (hne : b0 ≠ b1)
    (G : ContextFreeGrammar T × ContextFreeGrammar T) :
    ContextFreeGrammar α × ContextFreeGrammar α :=
  (grammarEncode (bitCode b0 b1) (isSync_bitCode hne).isCode G.1,
    grammarEncode (bitCode b0 b1) (isSync_bitCode hne).isCode G.2)

/-- `empCFGLift b0 b1 hne` witnesses the reduction from non-emptiness of CFG intersection over a
countable alphabet to it over `α`. -/
theorem empCFGLift_spec [Encodable T] (b0 b1 : α) (hne : b0 ≠ b1) :
    @DecisionProblem T ⪯_s[empCFGLift b0 b1 hne] @DecisionProblem α := fun G =>
  (intersection_encode_iff (hc := (isSync_bitCode hne).isCode) G.1 G.2).symm

/-- Non-emptiness of CFG intersection over a countable alphabet many-one reduces to it over any
alphabet with two distinct letters, by encoding the terminals of both grammars with `bitCode`. -/
def empCFGAlphabetLift [Encodable T] (b0 b1 : α) (hne : b0 ≠ b1) :
    @DecisionProblem T ⪯_s @DecisionProblem α :=
  ⟨empCFGLift b0 b1 hne, empCFGLift_spec b0 b1 hne⟩

end DiagonaLean.EmpCFG.Reduction

namespace DiagonaLean.EmpCFG.MachineLevel

open DiagonaLean.Foundations.Grammar DiagonaLean.Foundations.Computability
  DiagonaLean.Synthetic.Definitions

variable {T α : Type}

open Classical in
/-- Non-emptiness of the intersection of the languages of two grammar codes, with classical
decidable equality of terminals, so that it is defined over every alphabet (the languages do not
depend on the instance, `codeProblem_iff`). -/
def CodeProblem (x : CFGCode T × CFGCode T) : Prop := IntersectionNonempty x.1.toCFG x.2.toCFG

/-- With any decidable equality of terminals, `CodeProblem x` is non-emptiness of the
intersection of the languages of the two grammar codes. -/
theorem codeProblem_iff [DecidableEq T] (x : CFGCode T × CFGCode T) :
    CodeProblem x ↔ IntersectionNonempty x.1.toCFG x.2.toCFG := by
  unfold CodeProblem
  convert Iff.rfl

/-- With any decidable equality of terminals, `CodeProblem` is non-emptiness of the intersection
of the languages of the two grammar codes. -/
theorem codeProblem_eq [DecidableEq T] :
    @CodeProblem T = fun x => IntersectionNonempty x.1.toCFG x.2.toCFG :=
  funext fun x => propext (codeProblem_iff x)

/-- **Non-emptiness of the intersection of two grammar codes, as a functor on codes.** -/
abbrev empCodeFunctor : CodeFunctor IsCode where
  Inst T := CFGCode T × CFGCode T
  map c x := (presEncode c x.1, presEncode c x.2)
  Prob x := CodeProblem x
  map_unit x := by simp
  map_kcomp c₁ c₂ x := by simp [presEncode_kcomp]
  natural hc x := by
    classical
    rw [codeProblem_iff, codeProblem_iff]
    simp only [IntersectionNonempty, toCFG_presEncode hc]
    exact intersection_encode_iff (hc := hc) _ _
  supp x := presTerminals x.1 ++ presTerminals x.2
  map_congr x h := Prod.ext (presEncode_congr fun t ht => h t (List.mem_append_left _ ht))
    (presEncode_congr fun t ht => h t (List.mem_append_right _ ht))

/-- **Non-emptiness of the intersection of two grammar codes is not a computable predicate over
any nontrivial alphabet**: the lifting of `not_computablePred_empCFGCode` from `Term Bool`. -/
theorem not_computablePred_empCFGCodeOf [Primcodable α] [Nontrivial α] [DecidableEq α] :
    ¬ ComputablePred fun c : CFGCode α × CFGCode α => IntersectionNonempty c.1.toCFG c.2.toCFG := by
  have h₀ : ¬ ComputablePred (@CodeProblem (Reduction.Term Bool)) := by
    rw [codeProblem_eq]
    exact not_computablePred_empCFGCode (α := Bool)
  have h : ¬ ComputablePred (@CodeProblem α) := by code_lift empCodeFunctor from h₀
  rwa [codeProblem_eq] at h

/-- **No Turing machine decides non-emptiness of the intersection of two grammar codes over any
nontrivial alphabet**, under any computable encoding. -/
theorem not_machineDecidable_empCFGCodeOf [Primcodable α] [Nontrivial α] [DecidableEq α]
    {enc : CFGCode α × CFGCode α → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc fun c => IntersectionNonempty c.1.toCFG c.2.toCFG :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_empCFGCodeOf

/-- **Alphabet invariance of CFG intersection on grammar codes**: over any two nontrivial
`Primcodable` alphabets, non-emptiness of the intersection is many-one equivalent. -/
theorem empCFGCode_manyOneEquiv {β : Type} [Primcodable α] [Primcodable β] [Nontrivial α]
    [Nontrivial β] [DecidableEq α] [DecidableEq β] :
    ManyOneEquiv (fun c : CFGCode α × CFGCode α => IntersectionNonempty c.1.toCFG c.2.toCFG)
      fun c : CFGCode β × CFGCode β => IntersectionNonempty c.1.toCFG c.2.toCFG := by
  have h : ManyOneEquiv (@CodeProblem α) (@CodeProblem β) := by code_lift empCodeFunctor
  rwa [codeProblem_eq, codeProblem_eq] at h

end DiagonaLean.EmpCFG.MachineLevel
