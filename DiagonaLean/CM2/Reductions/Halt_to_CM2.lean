/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CM2.Simulation
import DiagonaLean.Foundations.Computability.Normalize.Normalize
import DiagonaLean.Synthetic.HaltReduction
import DiagonaLean.Synthetic.Tactics.ReductionPath

@[expose] public section

/-! # Halting reduces to halting of two-counter machines

A single-tape machine that never writes a blank and never moves left at the left end of its tape
halts on `w` iff its list machine halts from the initial configuration
(`Foundations.Computability.ListMachine.halts_iff`). The reduction `haltToCM2` normalises the
machine and its input (`Foundations.Computability.Normalize`) and takes the two-counter program
of the list machine of the normalised machine for its initial configuration. The program starts
from zero counters. By `halting_program_iff` it is a reduction from `HaltProblem`
(`halt_reducesto_cm2_spec`, `CM2.synthFromHalt`).

## References

* [M. L. Minsky, *Computation: Finite and Infinite Machines*][Minsky1967], Section 14.1
-/

namespace DiagonaLean.CM2.Reduction

open Cslib.Turing DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Foundations.Computability.ListMachine
  DiagonaLean.Foundations.Computability.Normalize

/-- **The reduction.** For a machine and an input: the two-counter program of the list machine of
the normalised machine, for its initial configuration. -/
def haltToCM2 (p : EncodableTM Bool × List Bool) : List Instr :=
  letI := (normEnc p.1).stateEncodable
  letI := (normEnc p.1).stateFintype
  letI : DecidableEq (normEnc p.1).State := Encodable.decidableEqOfEncodable _
  let tm := (normEnc p.1).toSingleTapeTM
  link (program (tmAct tm) none (enumAll tm.State) (enumAll (Option Sym2))
    (cfgOf tm tm.q₀ (BiTape.mk₁ (encInput p.2))))

/-- `haltToCM2` witnesses the reduction from the halting problem to halting of two-counter
machines. -/
theorem halt_reducesto_cm2_spec : HaltProblem ⪯_s[haltToCM2] DecisionProblem := by
  rintro ⟨M, w⟩
  show Halts M.toSingleTapeTM w ↔ _
  let := (normEnc M).stateEncodable
  let := (normEnc M).stateFintype
  let : DecidableEq (normEnc M).State := Encodable.decidableEqOfEncodable _
  rw [halts_normTM_iff, halts_iff (normTM_noBlankWrites _) (normTM_noLeftBoundary _ _)]
  exact (halting_program_iff mem_enumAll (fun _ _ _ _ => mem_enumAll _) (mem_enumAll _)
    (by simp only [cfgOf, BiTape.mk₁]; cases encInput w <;> rfl)).symm

/-- Halting of two-counter machines is displayed as "Two-counter machine halting". -/
instance : Synthetic.ReductionChain.ProblemName DecisionProblem :=
  ⟨"Two-counter machine halting"⟩

/-- **The reduction.** The halting problem many-one reduces to halting of two-counter machines,
through `haltToCM2`. -/
@[undecReduction] def _root_.DiagonaLean.CM2.synthFromHalt : HaltProblem ⪯_s DecisionProblem :=
  ⟨haltToCM2, halt_reducesto_cm2_spec⟩

end DiagonaLean.CM2.Reduction
