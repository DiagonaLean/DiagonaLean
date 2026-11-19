```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
```
# `UTMHalt`: The Universal Turing Machine Halting Problem
## Problem Statement
Given an encoding `instanceEncoding M w` of a TM `M` and input `w`, does `U`, a Turing Machine satisfying `IsUniversal`, halt on `instanceEncoding M w`?

## Layout
* `Basic.lean`: the problem.
* `Reductions/Halt_to_UTMHalt.lean`: `M` halts on `w` exactly when a (weakly) universal machine halts on the encoded instance (`halt_iff_weakutmhalt`, `halt_iff_utmhalt`), so a halting decider for that machine decides `HaltProblem` (`isHaltDecider_of_isHaltDeciderFor`).
* `Undecidable.lean`: no Turing machine decides the halting problem of a weakly universal machine (`not_exists_haltDeciderFor_of_isWeaklyUniversal`). No universal machine is constructed, so this is a statement about machines, not a many-one reduction.
* `UniversalTuringMachine/`: universal machines (`Basic.lean`), and the proof that universality does not depend on how a machine and its input are packaged into one string, as long as a Turing machine translates one packaging into the other (`Translation.lean`).
