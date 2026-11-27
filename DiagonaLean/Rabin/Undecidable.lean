/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Rabin.Reductions.Halt_to_Rabin

@[expose] public section

/-! # Undecidability of winner determination in Rabin's game

`Rabin.synthFromHalt` (`Reductions/Halt_to_Rabin.lean`) many-one reduces the halting problem to
winner determination for finite payoff programs, so winner determination is synthetically
halting-hard. The machine-level statements are in `MachineLevel.lean`.

## References

* [M. O. Rabin, *Effective computability of winning strategies*][Rabin1957]
-/
