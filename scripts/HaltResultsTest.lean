import DiagonaLean

/-! Tests of `halt_results` on the library's halting reductions: the statements of the three
theorems, every form of the command, and the sources it must reject. Run by CI as
`lake env lean scripts/HaltResultsTest.lean`. -/

open DiagonaLean DiagonaLean.PCP DiagonaLean.Foundations.Computability
  DiagonaLean.Foundations.Grammar DiagonaLean.GrammarMem DiagonaLean.Synthetic.Definitions

/-! ## A fixed instance type -/

namespace MatMortResults

halt_results MatMort.DecisionProblem from MatMort.fromHalt

/-- info: MatMortResults.haltHard : HaltHard MatMort.DecisionProblem -/
#guard_msgs in
#check haltHard

/-- info: MatMortResults.not_computablePred : ¬ComputablePred MatMort.DecisionProblem -/
#guard_msgs in
#check not_computablePred

example {enc : Finset (Matrix (Fin 3) (Fin 3) ℤ) → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc MatMort.DecisionProblem :=
  not_machineDecidable henc

/-- info: 'MatMortResults.not_machineDecidable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_machineDecidable

end MatMortResults

/-! ## Over every nontrivial alphabet -/

namespace MPCPResults

variable {α : Type} [Primcodable α] [Nontrivial α]

halt_results (@MPCP.DecisionProblem α) over_letters from MPCP.fromHaltOver

example : HaltHard (@MPCP.DecisionProblem Bool) := haltHard

example : ¬ ComputablePred (@MPCP.DecisionProblem α) := not_computablePred

example {enc : Tile α × Stack α → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc (@MPCP.DecisionProblem α) :=
  not_machineDecidable henc

/-- info: 'MPCPResults.haltHard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms haltHard

end MPCPResults

/-! ## Several problems in one namespace -/

namespace SemiThueResults

variable {α : Type} [Primcodable α] [Nontrivial α]

halt_results (@SemiThue.DecisionProblem α) over_letters from SemiThue.fromHaltOver

halt_results Pos for (@SemiThue.DecisionProblemPos α) over_letters from SemiThue.posFromHaltOver

halt_results OverBool for (@SemiThue.DecisionProblem Bool) from SemiThue.fromHaltBool

example : ¬ ComputablePred (@SemiThue.DecisionProblem α) := not_computablePred

example : ¬ ComputablePred (@SemiThue.DecisionProblemPos α) := Pos.not_computablePred

example : ¬ ComputablePred (@SemiThue.DecisionProblem Bool) := OverBool.not_computablePred

end SemiThueResults

/-! ## A problem written as a lambda, and section variables -/

namespace GrammarResults

variable {T : Type} [Primcodable T]

halt_results (fun g : { g : GrammarCode T // IsType0 g } => GrammarMem.EmptyWordProblem g.1)
  from GrammarMem.emptyWordFromHalt

variable {α : Type} [DecidableEq α] [Primcodable α] [Nontrivial α]

halt_results Ambig for (fun c : CFGCode (α ⊕ ℕ) => AmbigCFG.DecisionProblem c.toCFG)
  over_letters from AmbigCFG.codeFromHaltSum

example : ¬ ComputablePred fun c : CFGCode (α ⊕ ℕ) => AmbigCFG.DecisionProblem c.toCFG :=
  Ambig.not_computablePred

end GrammarResults

/-! ## From a proof of hardness

When the reduction needs constants that exist only classically, the source is `HaltHard P`
itself, as in `SKIConv/Hardness.lean`. -/

namespace FromHard

halt_results MatMort.DecisionProblem from (⟨MatMort.fromHalt⟩ : HaltHard MatMort.DecisionProblem)

/-- info: FromHard.not_computablePred : ¬ComputablePred MatMort.DecisionProblem -/
#guard_msgs in
#check not_computablePred

-- the library's uses state the same theorems as by hand
example : ¬ ComputablePred SKIConv.SKIConvProblem := SKIConv.not_computablePred

example {enc : KAComm.KleeneAlgebra.InstB → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc KAComm.TermEqBool.TermEqBoolProblem :=
  KAComm.TermEqBool.not_machineDecidable henc

end FromHard

/-! ## Rejected sources

Each of the three theorems reports the error, so `substring` matches one telling line. -/

namespace Rejected

namespace Synthetic

-- A synthetic halting reduction proves none of the three.
/-- error: Application type mismatch: The argument
  MatMort.synthFromHalt -/
#guard_msgs (substring := true) in
halt_results MatMort.DecisionProblem from MatMort.synthFromHalt

end Synthetic

namespace WrongProblem

-- The reduction must be to the problem stated.
/-- error: Application type mismatch: The argument
  MatMort.fromHalt -/
#guard_msgs (substring := true) in
halt_results (@PCP.DecisionProblem Bool) from MatMort.fromHalt

end WrongProblem

namespace WrongHard

-- A proof of hardness must be for the problem stated.
/-- error: Application type mismatch: The argument
  MatMort.haltHard -/
#guard_msgs (substring := true) in
halt_results (@PCP.DecisionProblem Bool) from MatMort.haltHard

end WrongHard

namespace NoLetters

-- `over_letters` takes a reduction for each pair of letters, not a single reduction.
/-- error: Application type mismatch: The argument
  MPCP.fromHaltBool -/
#guard_msgs (substring := true) in
halt_results (@MPCP.DecisionProblem Bool) over_letters from MPCP.fromHaltBool

end NoLetters

namespace TrivialAlphabet

variable {α : Type} [Primcodable α]

-- `over_letters` needs two letters.
/-- error: failed to synthesize instance of type class
  Nontrivial α -/
#guard_msgs (substring := true) in
halt_results (@MPCP.DecisionProblem α) over_letters from MPCP.fromHaltOver

end TrivialAlphabet

end Rejected
