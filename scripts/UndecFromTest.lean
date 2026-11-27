import DiagonaLean.MPCP.SynthHardness
import DiagonaLean.EmpCFG.SynthHardness
import DiagonaLean.SemiThue.SynthHardness
import DiagonaLean.MatMort.SynthHardness
import DiagonaLean.EmpCFG.Undecidable
import DiagonaLean.SemiThue.Undecidable
import DiagonaLean.MatMort.Undecidable
import DiagonaLean.MatrixGame.Undecidable
import DiagonaLean.MatrixGame.MachineLevel
import DiagonaLean.Rabin.FixedGame
import DiagonaLean.Rabin.MachineLevel

/-! Regression tests for discovery, composition, and the manual tactic interface. -/

open DiagonaLean DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation

-- Imported registrations work across namespaces and predicate abbreviations.
example : SynthHaltReduction MatMort.DecisionProblem := by undec from PCP.PCProblem

/--
info: Try this:
  [apply] exact MPCP.synthFromHaltBool
-/
#guard_msgs (whitespace := lax) in
example : SynthHaltReduction MPCP.MPCProblem := by undec?

-- Passing through halting adds no identity function to the generated witness.
/--
info: Try this:
  [apply] exact MPCP.synthFromHaltBool
-/
#guard_msgs (whitespace := lax) in
example : SynthHaltReduction MPCP.MPCProblem := by show_term undec from Halt.HaltProblem

-- The public suggestion includes the mathematical route followed by a replayable proof.
/--
info: Halting → Binary PCP → PCP over Paterson’s alphabet → 3×3 matrix mortality
---
info: Try this:
  [apply] reduce_from PCP.synthFromHaltBool
    via MatMort.synthS23FromPCP,
    via MatMort.synthFromPCP
-/
#guard_msgs (whitespace := lax) in
example : SynthHaltReduction MatMort.DecisionProblem := by undec? from PCP.PCProblem

-- The suggestion replays with `reduce_from`.
example : SynthHaltReduction MatMort.DecisionProblem := by
  reduce_from PCP.synthFromHaltBool via MatMort.synthS23FromPCP, via MatMort.synthFromPCP

-- Library results are discoverable from halting.
example : SynthHaltReduction MPCP.MPCProblem := by undec from Halt.HaltProblem
example : SynthHaltReduction (@SemiThue.DecisionProblem Bool) := by undec from Halt.HaltProblem
example : SynthHaltReduction (@EmpCFG.DecisionProblem Bool) := by undec from Halt.HaltProblem

-- Every function along the PCP-to-mortality route has computability evidence.
example {enc : Finset (Matrix (Fin 3) (Fin 3) ℤ) → List Bool} (he : Computable enc) :
    ¬ MachineDecidable enc MatMort.DecisionProblem := by
  undec from PCP.PCProblem

/-- info: Binary PCP → PCP over Paterson’s alphabet → 3×3 matrix mortality -/
#guard_msgs in
set_option undec.showRoute true in
example : ¬ ComputablePred MatMort.DecisionProblem := by undec from PCP.PCProblem

-- An uncertified shortcut and a cycle must not prevent discovery of the certified route.
/-- info: P → Q → R -/
#guard_msgs in
set_option undec.showRoute true in
example (P Q R : ℕ → Prop) (_shortcut : P ⪯_s R) (pq : P ⪯_s Q) (_back : Q ⪯_s P)
    (qr : Q ⪯_s R) (h : ¬ ComputablePred P) (hpq : Computable pq.f) (hqr : Computable qr.f) :
    ¬ ComputablePred R := by undec from P

-- Local reductions can extend the graph, including one whose target is a local predicate.
example (P Q : ℕ → Prop) (h : SynthHaltReduction P) (r : P ⪯_s Q) : SynthHaltReduction Q := by
  undec from P

-- A compiled witness alone cannot discharge computability. Both obligations remain visible.
example (P Q : ℕ → Prop) (r : P ⪯_s Q) (enc : ℕ → List Bool) (h : ¬ ComputablePred P)
    (certs : Computable r.f ∧ Computable enc) : ¬ MachineDecidable enc Q := by
  undec from h
  · exact certs.1
  · exact certs.2

/--
info: P → Q
---
info: P → Q needs Computable r.f
---
info: The encoding needs Computable enc
-/
#guard_msgs (whitespace := lax) in
set_option undec.showRoute true in
example (P Q : ℕ → Prop) (r : P ⪯_s Q) (enc : ℕ → List Bool) (h : ¬ ComputablePred P)
    (certs : Computable r.f ∧ Computable enc) : ¬ MachineDecidable enc Q := by
  undec from P
  · exact certs.1
  · exact certs.2

/--
error: missing hardness theorem for P. Supply a proof of ¬ComputablePred P
or register one with @[undecHardness].
-/
#guard_msgs (whitespace := lax) in
example (P : ℕ → Prop) : ¬ ComputablePred P := by undec from P

-- An explicitly specialized witness can seed the search.
example : SynthHaltReduction MatMort.DecisionProblem := by
  undec from (PCP.synthFromHaltOver (0 : MatMort.Reduction.S23) 1 (by decide)) via?

-- The original spelling with a witness still leaves the reduction goal for the caller.
example : SynthHaltReduction MatMort.DecisionProblem := by
  undec from (PCP.synthFromHaltOver (0 : MatMort.Reduction.S23) 1 (by decide))
  exact MatMort.synthFromPCP

-- A cycle, a second route, and a missing path in a local registry.
private def AtValue (k n : ℕ) := n = k

private def translateValue (a b : ℕ) : AtValue a ⪯_s AtValue b :=
  ⟨fun n => if n = a then b else b + 1, fun n => by by_cases h : n = a <;> simp [AtValue, h]⟩

@[local undecReduction] private def zeroOne : AtValue 0 ⪯_s AtValue 1 := translateValue 0 1
@[local undecReduction] private def oneZero : AtValue 1 ⪯_s AtValue 0 := translateValue 1 0
@[local undecReduction] private def oneTwo : AtValue 1 ⪯_s AtValue 2 := translateValue 1 2

-- A shorter untagged edge is available, but the registered route is preferred.
private def untaggedShortcut : AtValue 0 ⪯_s AtValue 2 :=
  ⟨(· + 2), fun n => by simp [AtValue]⟩

private def indirect : AtValue 0 ⪯_s AtValue 2 := by reduction_path
example : indirect.f 10 = 3 := rfl

/--
error: no reduction path found from AtValue 0 to AtValue 9
Import a concrete reduction definition or supply a specialized witness locally.
-/
#guard_msgs (whitespace := lax) in
example : AtValue 0 ⪯_s AtValue 9 := by reduction_path

@[local undecReduction] private def direct : AtValue 0 ⪯_s AtValue 2 :=
  ⟨(· + 2), fun n => by simp [AtValue]⟩

private def shortest : AtValue 0 ⪯_s AtValue 2 := by reduction_path
example : shortest.f 10 = 12 := rfl

-- A requested intermediate problem still counts when a direct edge is available.
private def throughOne : AtValue 0 ⪯_s AtValue 2 := by reduction_path via AtValue 1
example : throughOne.f 10 = 3 := rfl

private def identityPath : AtValue 2 ⪯_s AtValue 2 := by reduction_path
example : identityPath.f 10 = 10 := rfl

-- Untagged witnesses from imported modules, including a certified reduction.
open DiagonaLean.Foundations.Computability in
example : SynthHaltReduction HaltCanon := by undec from Halt.HaltProblem

/--
info: Try this:
  [apply] exact not_computablePred_of_reduces (ComputableReduction.toSynth PCP.fromHaltBool)
    PCP.fromHaltBool.computable
    not_computablePred_haltCanon
-/
#guard_msgs (whitespace := lax) in
open DiagonaLean.Foundations.Computability in
example : ¬ ComputablePred PCP.PCProblem := by show_term undec from not_computablePred_haltCanon

-- An uncertified shortcut still allows fallback to a tagged edge and a private untagged edge.
private def twoThree : AtValue 2 ⪯_s AtValue 3 := translateValue 2 3

example (_shortcut : AtValue 1 ⪯_s AtValue 3) (h : ¬ ComputablePred (AtValue 1))
    (h12 : Computable oneTwo.f) (h23 : Computable twoThree.f) : ¬ ComputablePred (AtValue 3) := by
  undec from AtValue 1

-- A specialized proved reduction supplied locally carries its own certificate.
open DiagonaLean.Foundations.Computability in
example (P Q : ℕ → Prop) (r : P ⪯ Q) (h : ¬ ComputablePred P) : ¬ ComputablePred Q := by
  undec from P

-- The suggested scripts replay without search.
example : SynthHaltReduction MatMort.DecisionProblem := by
  undec from PCP.synthFromHaltBool via MatMort.synthS23FromPCP, MatMort.synthFromPCP

/--
info: Binary PCP → PCP over Paterson’s alphabet → 3×3 matrix mortality
---
info: Try this:
  [apply] reduce_from PCP.not_computablePred via MatMort.synthS23FromPCP, via MatMort.synthFromPCP
-/
#guard_msgs (whitespace := lax) in
example {enc : Finset (Matrix (Fin 3) (Fin 3) ℤ) → List Bool} (he : Computable enc) :
    ¬ MachineDecidable enc MatMort.DecisionProblem := by
  undec? from PCP.PCProblem

example {enc : Finset (Matrix (Fin 3) (Fin 3) ℤ) → List Bool} (he : Computable enc) :
    ¬ MachineDecidable enc MatMort.DecisionProblem := by
  reduce_from PCP.not_computablePred via MatMort.synthS23FromPCP, via MatMort.synthFromPCP

example {enc : Finset (Matrix (Fin 3) (Fin 3) ℤ) → List Bool} (he : Computable enc) :
    ¬ MachineDecidable enc MatMort.DecisionProblem := by
  undec from PCP.not_computablePred via MatMort.synthS23FromPCP,
    MatMort.synthFromPCP

-- A source with an error is reported once.
/-- error: Unknown identifier `MPCP.synthFromHaltBoool` -/
#guard_msgs in
example : SynthHaltReduction MPCP.MPCProblem := by undec from MPCP.synthFromHaltBoool

-- An unsupported goal names the goals that `undec from` proves.
/--
error: undec from proves goals of the form `SynthHaltReduction Q`, and, with
`DiagonaLean.Foundations.Computability.UndecTransfer` imported, `¬ ComputablePred Q` and
`¬ MachineDecidable enc Q`
The goal is
  ComputablePred P
-/
#guard_msgs (whitespace := lax) in
example (P : ℕ → Prop) : ComputablePred P := by undec from P

-- A negation written as an implication is recognized, in a hypothesis and in the goal.
example (P Q : ℕ → Prop) (r : P ⪯_s Q) (hr : Computable r.f) (h : ComputablePred P → False) :
    ¬ ComputablePred Q := by undec from h

example (P Q : ℕ → Prop) (r : P ⪯_s Q) (hr : Computable r.f) (h : ¬ ComputablePred P) :
    ComputablePred Q → False := by undec from h

-- A `via` list is checked step by step.
/--
error: this reduction starts at
  @PCP.DecisionProblem MatMort.Reduction.S23
but the previous step ends at
  PCP.PCProblem
-/
#guard_msgs (whitespace := lax) in
example : SynthHaltReduction MatMort.DecisionProblem := by
  undec from PCP.synthFromHaltBool via MatMort.synthFromPCP

-- An ill-formed tag is skipped by the search and named when no path is found.
@[local undecReduction] private def badTag : ℕ := 0

example : SynthHaltReduction MPCP.MPCProblem := by undec from Halt.HaltProblem

/--
error: no reduction path found from AtValue 0 to AtValue 9
Import a concrete reduction definition or supply a specialized witness locally.
Skipped @[undecReduction] declarations:
badTag has type ℕ, not a closed reduction P ⪯_s Q; specialize it
-/
#guard_msgs (whitespace := lax) in
example : AtValue 0 ⪯_s AtValue 9 := by reduction_path

-- Suggestions name the identity reduction without hygiene, and hidden hypotheses by their type.
/--
info: Try this:
  [apply] exact DiagonaLean.Synthetic.Definitions.SynthReduction.refl _
-/
#guard_msgs (whitespace := lax) in
example : SynthHaltReduction Halt.HaltProblem := by undec?

/--
info: Try this:
  [apply] reduce_from ‹SynthHaltReduction P› via ‹P ⪯_s Q›
-/
#guard_msgs (whitespace := lax) in
example (P Q : ℕ → Prop) : (SynthHaltReduction P) → (P ⪯_s Q) → SynthHaltReduction Q := by
  intro _ _
  undec?

example (P Q : ℕ → Prop) : (SynthHaltReduction P) → (P ⪯_s Q) → SynthHaltReduction Q := by
  intro _ _
  undec from ‹SynthHaltReduction P› via ‹P ⪯_s Q›

example (P Q : ℕ → Prop) : (SynthHaltReduction P) → (P ⪯_s Q) → SynthHaltReduction Q := by
  intro _ _
  reduce_from ‹SynthHaltReduction P› via ‹P ⪯_s Q›

/--
info: Halting → P → Q
---
info: Try this:
  [apply] reduce_from h via ‹P ⪯_s Q›
-/
#guard_msgs (whitespace := lax) in
example (P Q R : ℕ → Prop) (h : SynthHaltReduction P) (r : P ⪯_s Q) (r' : Q ⪯_s R) :
    SynthHaltReduction Q := by
  have r := r'
  undec? from h

-- A term that does not elaborate again gives no script.
/--
info: Halting → PCP over Paterson’s alphabet → 3×3 matrix mortality
---
info: a step of this route has no term that elaborates again, so there is no script to suggest;
name it in a `via` list
-/
#guard_msgs (whitespace := lax) in
example : SynthHaltReduction MatMort.DecisionProblem := by
  undec? from (PCP.synthFromHaltOver (0 : MatMort.Reduction.S23) 1 (by decide))

-- `undec?` with no source does not search for a hardness theorem.
/--
error: on a goal
  ¬ComputablePred MatMort.DecisionProblem
name a source problem: `undec? from P`
-/
#guard_msgs (whitespace := lax) in
example : ¬ ComputablePred MatMort.DecisionProblem := by undec?

-- A proved reduction in a `via` list supplies its certificate; a tactic block can be the source.
open DiagonaLean.Foundations.Computability in
example (P Q : ℕ → Prop) (r : P ⪯ Q) (h : ¬ ComputablePred P) : ¬ ComputablePred Q := by
  undec from (by exact h) via r

-- Game reductions registered in their own modules.
example : SynthHaltReduction Rabin.DecisionProblem := by undec from Halt.HaltProblem
example : SynthHaltReduction MatrixGame.DecisionProblem := by undec from PCP.PCProblem

/--
info: Halting → Rabin game winner
---
info: Try this:
  [apply] exact Rabin.synthFromHalt
-/
#guard_msgs (whitespace := lax) in
example : SynthHaltReduction Rabin.DecisionProblem := by undec? from Halt.HaltProblem

-- Every function along the PCP-to-matrix-game route has computability evidence.
example {enc : MatrixGame.Arena → List Bool} (he : Computable enc) :
    ¬ MachineDecidable enc MatrixGame.DecisionProblem := by
  undec from PCP.PCProblem

/-- info: Binary PCP → PCP over Paterson’s alphabet → 3×3 matrix mortality → Matrix-game winner -/
#guard_msgs in
set_option undec.showRoute true in
example : ¬ ComputablePred MatrixGame.DecisionProblem := by undec from PCP.PCProblem

-- The original spelling with a witness still leaves the reduction goal for the caller.
example : SynthHaltReduction MatrixGame.DecisionProblem := by
  undec from MatMort.synthFromHalt
  exact MatrixGame.synthFromMatMort

-- The suggested script for the matrix game replays without search.
example {enc : MatrixGame.Arena → List Bool} (he : Computable enc) :
    ¬ MachineDecidable enc MatrixGame.DecisionProblem := by
  undec from PCP.not_computablePred via MatMort.synthS23FromPCP,
    MatMort.synthFromPCP, MatrixGame.synthFromMatMort
