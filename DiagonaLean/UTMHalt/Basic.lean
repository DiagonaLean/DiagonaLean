/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Akhilesh Balaji
-/

import DiagonaLean.UTMHalt.UniversalTuringMachine.Basic

@[expose] public section

/-! # The UTM halting problem

The central notions used in the proof that the UTM halting problem is undecidable: a machine
deciding the halting problem of a fixed machine (`IsHaltDeciderFor`), halting of a (weakly)
universal machine on an encoded instance (`WeakUTMHalts`, `UTMHalts`), and the decision problems
`WeakUTMHaltProblem` and `UTMHaltProblem`.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
-/

namespace DiagonaLean.UTMHalt

open Cslib.Turing SingleTapeTM DiagonaLean.Halt DiagonaLean.Halt.Encoding
     DiagonaLean.Halt.Helpers DiagonaLean.UTMHalt.UniversalTuringMachine

/-- `D` decides the halting problem of the fixed machine `U` if, on every input string
  `x`, it outputs `[true]` when `U` halts on `x` and `[false]` when it does not. -/
def IsHaltDeciderFor (U D : SingleTapeTM Bool) : Prop :=
  ∀ x : List Bool, (Halts U x → D.Outputs x [true]) ∧ (¬ Halts U x → D.Outputs x [false])

/-- `WeakUTMHalts U hU M w` holds when the weakly universal machine `U` halts on
`instanceEncoding M w`. -/
def WeakUTMHalts (U : SingleTapeTM Bool) (_hU : IsWeaklyUniversal U) (M : EncodableTM Bool)
  (w : List Bool) := Halts U (instanceEncoding M w)

/-- `UTMHalts U hU M w` holds when the universal machine `U` halts on `instanceEncoding M w`. -/
def UTMHalts (U : SingleTapeTM Bool) (_hU : IsUniversal U) (M : EncodableTM Bool)
  (w : List Bool) := Halts U (instanceEncoding M w)

/-- The halting problem of the fixed Weak UTM `U`. -/
abbrev WeakUTMHaltProblem : ({U : SingleTapeTM Bool // IsWeaklyUniversal U} ×
    EncodableTM Bool × List Bool) → Prop :=
  fun ⟨⟨U, hU⟩, ⟨M, w⟩⟩ ↦ WeakUTMHalts U hU M w

/-- The halting problem of the fixed UTM `U`. -/
abbrev UTMHaltProblem : ({U : SingleTapeTM Bool // IsUniversal U} ×
    EncodableTM Bool × List Bool) → Prop :=
  fun ⟨⟨U, hU⟩, ⟨M, w⟩⟩ ↦ UTMHalts U hU M w

end DiagonaLean.UTMHalt
