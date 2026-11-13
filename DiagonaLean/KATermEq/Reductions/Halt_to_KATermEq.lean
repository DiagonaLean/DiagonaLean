/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KATermEq.Basic
import DiagonaLean.Foundations.KleeneAlgebra.Race
import DiagonaLean.Foundations.KleeneAlgebra.Separation

@[expose] public section

/-! # `HaltProblem ⪯ₘ` equality on `K Σ̈`

`reduction B C` sends a `HaltProblem` instance `p` to the instance of the race program of `p` over
`ℕ`, and `reductionB B C` to its substitution over `{0, 1}`. By Smullyan's argument, `p` halts iff
the two sides are provably equal in Kleene algebra with commutativity (`halt_iff_rel`,
`halt_iff_qb`). The constants `B` and `C` are the interpreter's table and the race program from the
recursion theorem.

`haltReducesKATermEqOfFamily` is the conditional form of Theorem 19: given a `SmullyanFamily`,
`eqRed ∘ N` is a reduction.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorems 18 and 19
-/

open scoped Computability

namespace DiagonaLean.KATermEq.Reduction

open DiagonaLean.Foundations.KleeneAlgebra

open Cslib.Turing RExp TD FreePreKA Nat.Partrec DiagonaLean.Foundations.Computability
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation

/-- `reduction B C` reduces `HaltProblem` to provable equality in Kleene algebra with
commutativity. -/
theorem halt_reducesto_kaTermEq_spec {B : Base} {C : Code} (hB : B.Good) (hC : RaceProg true B C) :
    HaltProblem ⪯ₘ[reduction B C] @KATermEq.DecisionProblem ℕ :=
  fun p => by
    simpa [Foundations.KleeneAlgebra.Rel, KATermEq.DecisionProblem] using halt_iff_rel hB hC p

/-- `HaltProblem` many-one reduces to provable equality in Kleene algebra with commutativity. -/
def haltReducesKATermEq (B : Base) (C : Code) (hB : B.Good) (hC : RaceProg true B C) :
    HaltProblem ⪯ₘ @KATermEq.DecisionProblem ℕ :=
  ⟨reduction B C, halt_reducesto_kaTermEq_spec hB hC⟩

/-- `reductionB B C` reduces `HaltProblem` to provable equality in Kleene algebra over `{0, 1}`. -/
theorem halt_reducesto_kaTermEq_bool_spec {B : Base} {C : Code} (hB : B.Good)
    (hC : RaceProgB true B C) :
    HaltProblem ⪯ₘ[reductionB B C] KATermEqProblem := fun p =>
  (halt_iff_qb hB hC p).trans (by
    simpa [QB, Foundations.KleeneAlgebra.Rel, reductionB, KATermEq.DecisionProblem]
      using kaEquiv_iff_map)

/-- `HaltProblem` many-one reduces to provable equality in Kleene algebra over `{0, 1}`. -/
def haltReducesKATermEqBool (B : Base) (C : Code) (hB : B.Good) (hC : RaceProgB true B C) :
    HaltProblem ⪯ₘ KATermEqProblem :=
  ⟨reductionB B C, halt_reducesto_kaTermEq_bool_spec hB hC⟩

/-- `HaltProblem` many-one reduces to provable equality in Kleene algebra with commutativity,
through `eqRed ∘ N`, given a Smullyan family for `K Σ̈`. -/
def haltReducesKATermEqOfFamily (fam : SmullyanFamily (SelfEq factorK)) :
    HaltProblem ⪯ₘ @KATermEq.DecisionProblem ℕ :=
  ⟨eqRed ∘ fam.N, fun p => (halt_iff_selfEq factorK fam p).trans (eqVia_factorK _)⟩

end DiagonaLean.KATermEq.Reduction
