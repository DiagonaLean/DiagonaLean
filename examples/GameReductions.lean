/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Rabin.FixedGame
import DiagonaLean.Rabin.Undecidable
import DiagonaLean.Rabin.SynthHardness
import DiagonaLean.MatrixGame.Undecidable
import DiagonaLean.MatrixGame.SynthHardness

/-! # Two game reductions

Run `lake env lean examples/GameReductions.lean` to see the routes and proof terms.
The last command runs a bounded search on a concrete winning arena.
-/

open DiagonaLean DiagonaLean.Synthetic.Definitions

-- In the fixed Rabin game II can win, but every computable reply strategy can be defeated.
#check Rabin.rabin_game

-- When the payoff program is the input, deciding whether I wins is halting-hard.
example : SynthHaltReduction Rabin.DecisionProblem := by
  undec? from Halt.HaltProblem

-- Starting at binary PCP exposes the intermediate alphabet change and matrix mortality.
example {enc : MatrixGame.Arena → List Bool} (he : Computable enc) :
    ¬ MachineDecidable enc MatrixGame.DecisionProblem := by
  undec? from PCP.PCProblem

-- The shift matrix has a nonzero square and zero cube. Adam can only change its sign.
private def shift : MatrixGame.Position := !![0, 1, 0; 0, 0, 1; 0, 0, 0]
#eval (MatrixGame.winsWithin (MatrixGame.Reduction.signGame {shift}) 2 1,
       MatrixGame.winsWithin (MatrixGame.Reduction.signGame {shift}) 3 1)
