/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.PCP.Reductions.Halt_to_PCP
import DiagonaLean.Halt.Helpers

/-! # Evaluation fixture (not wired into `DiagonaLean.lean`)

Runs the computable reduction `haltToPcp : EncodableTM Bool × List Bool → Stack _` on a concrete
halting instance, to demonstrate that the HALT → PCP witness is an executable program and not
just a proof object. Kept out of the main build because evaluation in the interpreter takes
several minutes. Run with `lake env lean DiagonaLean/Synthetic/EvalExample.lean`. -/

open DiagonaLean.Halt.Encoding DiagonaLean.Halt.Helpers DiagonaLean.PCP.Reduction

/-- `haltTM` (halts immediately on every input) bundled with its `Encodable` state instance. -/
def haltEnc : EncodableTM Bool := ⟨haltTM, inferInstance⟩

-- The PCP instance produced from `(haltEnc, [true])` has 635 tiles.
#eval (haltToPcp (haltEnc, [true])).length
