/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.MPCP.Undecidable
import DiagonaLean.MPCP.RE
import DiagonaLean.PCP.Undecidable
import DiagonaLean.PCP.RE
import DiagonaLean.SemiThue.Undecidable
import DiagonaLean.SemiThue.RE
import DiagonaLean.SKIConv.Undecidable
import DiagonaLean.SKIConv.RE
import DiagonaLean.BetaConv.Undecidable
import DiagonaLean.BetaConv.RE
import DiagonaLean.MatMort.Undecidable
import DiagonaLean.MatMort.RE
import DiagonaLean.KAComm.TermEq.Undecidable
import DiagonaLean.KAComm.TermEq.RE
import DiagonaLean.KAComm.KATermEq.Undecidable
import DiagonaLean.KAComm.KATermEq.RE
import DiagonaLean.KAComm.TermEqBool.Undecidable
import DiagonaLean.KAComm.TermEqBool.RE
import DiagonaLean.KAComm.KATermEqBool.Undecidable
import DiagonaLean.KAComm.KATermEqBool.RE
import DiagonaLean.GrammarMem.Undecidable
import DiagonaLean.GrammarMem.RE
import DiagonaLean.EmpCFG.Undecidable
import DiagonaLean.EmpCFG.RE
import DiagonaLean.CM2.Undecidable
import DiagonaLean.CM2.RE
import DiagonaLean.Foundations.Computability.ListHaltRE

@[expose] public section

/-! # Problems complete for the recursively enumerable problems

Each problem below is halting-hard (`X.haltHard`, by `halt_results`) and recursively enumerable
(`X.rePred`). The halting problem is complete for the recursively enumerable problems
(`manyOneReducible_haltCanon_of_rePred`), so each of them is: `re_results` states `X.complete`, and
registers the problem so that any two of them are many-one equivalent by
`manyOneEquiv_of_complete`.

## Main statements

* `MPCP.complete`, `PCP.complete`, `SemiThue.complete`, `SKIConv.complete`, `BetaConv.complete`,
  `MatMort.complete`: PCP, MPCP, string rewriting, SKI convertibility, β-conversion and matrix
  mortality.
* `KAComm.TermEq.complete`, `KAComm.KATermEq.complete` and their `Bool` forms.
* `GrammarMem.complete`, `GrammarMem.EmptyWord.complete`, `EmpCFG.Code.complete`.
* `CM2.complete`, `ListHalt.complete`: halting of two-counter machines and of list machines.

## References

* H. Rogers, *Theory of Recursive Functions and Effective Computability* (1967), Section 7.2
-/

namespace DiagonaLean

open Foundations.Computability Foundations.Grammar

namespace MPCP

variable {α : Type} [Primcodable α] [Nontrivial α]

re_results (@DecisionProblem α) from rePred

end MPCP

namespace PCP

variable {α : Type} [Primcodable α] [Nontrivial α]

re_results (@DecisionProblem α) from rePred

end PCP

namespace SemiThue

variable {α : Type} [Primcodable α] [Nontrivial α]

re_results (@DecisionProblem α) from (by classical exact rePred)

end SemiThue

namespace SKIConv

re_results DecisionProblem from rePred

end SKIConv

namespace BetaConv

re_results DecisionProblem from rePred

end BetaConv

namespace MatMort

re_results DecisionProblem from rePred

end MatMort

namespace KAComm.TermEq

re_results DecisionProblem from rePred

end KAComm.TermEq

namespace KAComm.KATermEq

re_results DecisionProblem from rePred

end KAComm.KATermEq

namespace KAComm.TermEqBool

re_results DecisionProblem from rePred

end KAComm.TermEqBool

namespace KAComm.KATermEqBool

re_results DecisionProblem from rePred

end KAComm.KATermEqBool

namespace GrammarMem

variable {T : Type} [Primcodable T]

re_results (@DecisionProblem T) from rePred

re_results EmptyWord for (fun g : { g : GrammarCode T // IsType0 g } => EmptyWordProblem g.1)
  from EmptyWord.rePred

end GrammarMem

namespace EmpCFG

variable {α : Type} [Primcodable α] [DecidableEq α] [Nontrivial α]

re_results Code for (fun c : CFGCode α × CFGCode α => IntersectionNonempty c.1.toCFG c.2.toCFG)
  from Code.rePred

end EmpCFG

namespace CM2

re_results DecisionProblem from rePred

end CM2

namespace Foundations.Computability.ListHalt

re_results (DecisionProblem (none : Option Normalize.Sym2)) from rePred none

end Foundations.Computability.ListHalt

end DiagonaLean
