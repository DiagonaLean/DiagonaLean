/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.TeamGame.Coding
import DiagonaLean.TeamGame.Finite
import DiagonaLean.TeamGame.Winning
import DiagonaLean.Foundations.Computability.Normalize.Normalize
import DiagonaLean.Synthetic.HaltReduction
import DiagonaLean.Synthetic.Tactics.ReductionPath

@[expose] public section

/-! # Halting reduces to team games

A single-tape machine that never writes a blank and never moves left at the left end of its tape
halts on `w` iff its list machine halts from the initial configuration
(`Foundations.Computability.ListMachine.halts_iff`). The reduction `haltToTeamGame v` normalises
the machine and its input (`Foundations.Computability.Normalize`), takes the game of variant `v` of
the normalised list machine, and codes its positions and actions as natural numbers (`codeGame`).
The target of the reachability variant is the passed check; the bad positions of the safety
variant are the failed check and the halting head.

By `winReach_iff_halts`, the reachability variant reduces the halting problem to team reachability
games (`halt_reducesto_teamReach_spec`). By `winSafety_iff_not_halts`,
the safety variant reduces the halting problem to the complement of team safety games
(`halt_reducesto_not_teamSafety_spec`). The packaged reductions are in `SynthHardness.lean`.

## References

* [G. L. Peterson, J. H. Reif, *Multiple-person alternation*][PetersonReif1979]
* [A. Pnueli, R. Rosner, *Distributed reactive systems are hard to synthesize*][PnueliRosner1990]
* D. Berwanger, Ł. Kaiser, *Information tracking in distributed games*, talk at ACTS 2010 (slides)
-/

namespace DiagonaLean.TeamGame.Reduction

open Cslib.Turing DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Foundations.Computability.ListMachine DiagonaLean.Foundations.Computability.Normalize
  DiagonaLean.Synthetic.Definitions

/-- The goal of a variant: the passed check for reachability, the failed check and the halting
head for safety. -/
def goalOf {Q Γ : Type} : Variant → List (Pos Q Γ)
  | .reach => [.ok]
  | .safety => [.err, .hlt]

/-- **The reduction.** For a variant, a machine and an input: the game of that variant of the
normalised list machine from the initial configuration, with positions and actions coded as
natural numbers. -/
def haltToTeamGame (var : Variant) (p : EncodableTM Bool × List Bool) : Game ℕ × ℕ :=
  letI := (normEnc p.1).stateEncodable
  letI := (normEnc p.1).stateFintype
  letI : DecidableEq (normEnc p.1).State := Encodable.decidableEqOfEncodable _
  let tm := (normEnc p.1).toSingleTapeTM
  let c₀ := cells (cfgOf tm tm.q₀ (BiTape.mk₁ (encInput p.2)))
  (codeGame Encodable.encode Encodable.encode .start (succs (tmAct tm) none c₀ var) observe
    (allPos (enumAll tm.State) (enumAll (Option Sym2)) c₀.length)
    (allMoves (enumAll tm.State) (enumAll (Option Sym2))) (goalOf var), 0)

/-- The reachability variant of `haltToTeamGame`. -/
def haltToTeamReach : EncodableTM Bool × List Bool → Game ℕ × ℕ := haltToTeamGame .reach

/-- The safety variant of `haltToTeamGame`. -/
def haltToTeamSafety : EncodableTM Bool × List Bool → Game ℕ × ℕ := haltToTeamGame .safety

/-- `haltToTeamReach` witnesses the reduction from the halting problem to team reachability
games. -/
theorem halt_reducesto_teamReach_spec : HaltProblem ⪯_s[haltToTeamReach] DecisionProblem := by
  rintro ⟨M, w⟩
  show Halts M.toSingleTapeTM w ↔ _
  let := (normEnc M).stateEncodable
  let := (normEnc M).stateFintype
  let : DecidableEq (normEnc M).State := Encodable.decidableEqOfEncodable _
  have hqs : ∀ q : (normEnc M).State, q ∈ enumAll (normEnc M).State := mem_enumAll
  have hcs : ∀ c : Option Sym2, c ∈ enumAll (Option Sym2) := mem_enumAll
  rw [halts_normTM_iff, halts_iff (normTM_noBlankWrites _) (normTM_noLeftBoundary _ _),
    ← winReach_iff_halts]
  simp only [haltToTeamReach, haltToTeamGame]
  rw [reachProblem_codeGame_iff Encodable.encode_injective Encodable.encode_injective
    ((mem_allPos hqs hcs Pos.start).2 trivial) (succs_closed hqs hcs _ _ _ _)
    (mem_allMoves hqs hcs)]
  simp only [goalOf, List.mem_singleton]
  rfl

/-- `haltToTeamSafety` witnesses the reduction from the halting problem to the complement of team
safety games. -/
theorem halt_reducesto_not_teamSafety_spec :
    HaltProblem ⪯_s[haltToTeamSafety] Complement DecisionProblemSafety := by
  rintro ⟨M, w⟩
  show Halts M.toSingleTapeTM w ↔ _
  let := (normEnc M).stateEncodable
  let := (normEnc M).stateFintype
  let : DecidableEq (normEnc M).State := Encodable.decidableEqOfEncodable _
  have hqs : ∀ q : (normEnc M).State, q ∈ enumAll (normEnc M).State := mem_enumAll
  have hcs : ∀ c : Option Sym2, c ∈ enumAll (Option Sym2) := mem_enumAll
  rw [halts_normTM_iff, halts_iff (normTM_noBlankWrites _) (normTM_noLeftBoundary _ _),
    ← not_iff_not, ← winSafety_iff_not_halts]
  simp only [haltToTeamSafety, haltToTeamGame, Synthetic.Definitions.Complement, not_not]
  rw [safetyProblem_codeGame_iff Encodable.encode_injective Encodable.encode_injective
    ((mem_allPos hqs hcs Pos.start).2 trivial) (succs_closed hqs hcs _ _ _ _)
    (mem_allMoves hqs hcs)]
  simp only [goalOf, List.mem_cons, List.not_mem_nil, or_false, not_or]
  rfl

/-- Team reachability games are displayed as "Team reachability game". -/
instance : Synthetic.ReductionChain.ProblemName (@DecisionProblem ℕ _) :=
  ⟨"Team reachability game"⟩

end DiagonaLean.TeamGame.Reduction
