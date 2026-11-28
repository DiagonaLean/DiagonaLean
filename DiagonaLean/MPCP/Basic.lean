/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import DiagonaLean.PCP.Basic

@[expose] public section

/-! # Modified Post Correspondence Problem

The solvability predicate `DecisionProblem` for the Modified Post Correspondence Problem.
MPCP is PCP with a designated start tile: every solution must begin with it.
MPCP serves as the intermediate step in the reduction chain `Halt ⪯_s MPCP ⪯_s PCP`.

The problem is `Solvable c P`, curried; `DecisionProblem` is the same problem on an instance
`(c, P)`. To audit the definition, read `Solvable` and `decisionProblem_mk`, which is pinned in
`scripts/HeadlineTest.lean`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

namespace DiagonaLean.MPCP

open DiagonaLean.PCP

variable {α : Type}

/-- `Solvable c P` holds iff there exists a stack `A` drawn from `c :: P` such that
`c.top ++ τ1 A = c.bot ++ τ2 A`. The full solution is `c :: A`; `c` is the forced start tile.
Proofs use this curried form; the problem itself is `DecisionProblem`, on the pair. -/
def Solvable (c : Tile α) (P : Stack α) : Prop :=
  ∃ A : Stack α, (∀ t ∈ A, t ∈ c :: P) ∧
    c.top ++ τ1 A = c.bot ++ τ2 A

/-! ### The problem on instances, for the reductions and the computability statements -/

/-- **The problem on an instance `(c, P)`**, for the reductions and the computability statements:
`Solvable c P`. Read it curried, `decisionProblem_mk`. -/
def DecisionProblem (x : Tile α × Stack α) : Prop := Solvable x.1 x.2

/-- The problem on an instance `(c, P)` is the curried problem. -/
@[simp] theorem decisionProblem_mk (c : Tile α) (P : Stack α) :
    DecisionProblem (c, P) ↔ Solvable c P := Iff.rfl

/-- The problem on an instance, by projections. -/
theorem decisionProblem_iff (x : Tile α × Stack α) : DecisionProblem x ↔ Solvable x.1 x.2 :=
  Iff.rfl

/-- Solvability of MPCP depends only on the set of tiles. -/
theorem mpcp_congr (c : Tile α) {P P' : Stack α} (h : ∀ t, t ∈ P ↔ t ∈ P') :
    Solvable c P ↔ Solvable c P' := by
  unfold Solvable
  simp only [List.mem_cons, h]

/-- The MPCP decision problem over `Bool`. -/
abbrev MPCProblem : Tile Bool × Stack Bool → Prop := DecisionProblem

end DiagonaLean.MPCP
