/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CM2.Reductions.Halt_to_CM2

@[expose] public section

/-! # Undecidability of halting for two-counter machines

`CM2.synthFromHalt` (`Reductions/Halt_to_CM2.lean`) many-one reduces the halting problem to
halting of a two-counter machine from address 0 with both counters zero, so that problem is
synthetically halting-hard. This is Minsky's theorem that two counters suffice. The machine-level
statements are in `MachineLevel.lean`.

## References

* [M. L. Minsky, *Computation: Finite and Infinite Machines*][Minsky1967], Section 14.1
-/
