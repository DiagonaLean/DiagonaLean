/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.EmpCFG.Undecidable
import DiagonaLean.PCP.Primrec
import DiagonaLean.Foundations.Codes.Grammar
import DiagonaLean.Foundations.Codes.Unary

@[expose] public section

/-! # Non-emptiness of CFG intersection over two letters

`undecidableEmpCFG` holds over the terminals `Term α = α ⊕ Tile α`, which include the tiles of the
PCP instance. Encoding the terminals of both grammars by a code preserves and reflects non-emptiness
of the intersection (`Foundations.Codes.intersection_encode_iff`), and `Term Bool` is countable,
so `Foundations.Codes.bitCode` moves the problem to any alphabet with two distinct letters
(`undecidableEmpCFGOf`), for instance to `Bool` (`undecidableEmpCFGBool`).
-/

open DiagonaLean.Synthetic.Notation DiagonaLean.Foundations.Codes

namespace DiagonaLean.EmpCFG.Reduction

variable {T α : Type}

/-- Non-emptiness of CFG intersection over a countable alphabet many-one reduces to it over any
alphabet with two distinct letters, by encoding the terminals of both grammars with `bitCode`. -/
def empCFGAlphabetLift [Encodable T] (b0 b1 : α) (hne : b0 ≠ b1) :
    @DecisionProblem T ⪯ₘ @DecisionProblem α :=
  ⟨fun G => (grammarEncode (bitCode b0 b1) (isSync_bitCode hne).isCode G.1,
      grammarEncode (bitCode b0 b1) (isSync_bitCode hne).isCode G.2),
    fun G => (intersection_encode_iff (hc := (isSync_bitCode hne).isCode) G.1 G.2).symm⟩

/-- **Non-emptiness of the intersection of two context-free grammars is `Undecidable` over any
alphabet `α` with two distinct letters `b0`, `b1`.** -/
def undecidableEmpCFGOf (b0 b1 : α) (hne : b0 ≠ b1) : Undecidable (@DecisionProblem α) :=
  undecidabilityFromReducibility (undecidableEmpCFG false true Bool.false_ne_true)
    (empCFGAlphabetLift b0 b1 hne)

/-- **Non-emptiness of the intersection of two context-free grammars over `Bool` is
`Undecidable`.** -/
def undecidableEmpCFGBool : Undecidable (@DecisionProblem Bool) :=
  undecidableEmpCFGOf false true Bool.false_ne_true

end DiagonaLean.EmpCFG.Reduction
