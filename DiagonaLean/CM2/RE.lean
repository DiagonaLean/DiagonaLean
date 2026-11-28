/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CM2.Basic
import DiagonaLean.Foundations.Computability.Reaches
import DiagonaLean.Foundations.Computability.DerivePrimrec
import DiagonaLean.Foundations.Computability.PrimrecRec

@[expose] public section

/-! # Halting of two-counter machines is recursively enumerable

One step of a two-counter machine is primitive recursive in the program and the configuration
(`execute_prim`, `step_prim`), and so is the test that the address is outside the program. So
whether the machine halts is recursively enumerable (`CM2.rePred`): search for the number of
steps (`REPred.of_reaches`). With `CM2.haltHard` it is as hard as the halting problem and no
harder.

## Main statements

* `CM2.rePred`: halting of two-counter machines is recursively enumerable.
-/

namespace DiagonaLean.CM2

open Foundations.Computability

/-- Executing an instruction is primitive recursive in the configuration and the instruction. -/
@[fun_prop] theorem execute_prim : Primrec fun x : Config × Instr => execute x.1 x.2 :=
  (by primrec_rec : Primrec₂ execute)

derive_primrec step

/-- **Halting of two-counter machines is recursively enumerable**: search for the number of
steps. -/
theorem rePred : REPred DecisionProblem :=
  REPred.of_reaches (step := step) (start := fun _ => ⟨0, 0, 0⟩)
    (stop := fun p t => p.length ≤ t.pc) (by fun_prop) (.const _) (by fun_prop)

end DiagonaLean.CM2
