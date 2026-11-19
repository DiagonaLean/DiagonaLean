/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kshitij Salunke, Aalok Thakkar, Claude Opus
-/

import Mathlib.Computability.PartrecCode

@[expose] public section

/-! # Rice's problem

An instance is a program `c : Nat.Partrec.Code`. For a set `C` of partial functions `ℕ →. ℕ`,
`DecisionProblem C` asks whether the function that `c` computes (`c.eval`) is in `C`. The answer
depends only on `c.eval`, so programs that compute the same function get the same answer.
`RiceProblem C` names it. `C` is non-trivial (`IsNontrivial`) if some program computes a function
in `C` and some program computes a function not in `C`; equivalently, `C` contains a partial
recursive function and misses one (`isNontrivial_iff`).

## References

* H. G. Rice, *Classes of recursively enumerable sets and their decision problems* (1953)
-/

namespace DiagonaLean.Rice

open Nat.Partrec

/-- `DecisionProblem C c` holds iff the function computed by `c` is in `C`. -/
def DecisionProblem (C : Set (ℕ →. ℕ)) (c : Code) : Prop := c.eval ∈ C

/-- Rice's problem for `C`: does a program compute a function in `C`? -/
abbrev RiceProblem (C : Set (ℕ →. ℕ)) : Code → Prop := DecisionProblem C

/-- `C` is non-trivial if some program computes a function in `C` and some program computes a
function not in `C`. -/
def IsNontrivial (C : Set (ℕ →. ℕ)) : Prop := (∃ c : Code, c.eval ∈ C) ∧ ∃ c : Code, c.eval ∉ C

/-- `C` is non-trivial iff it contains a partial recursive function and misses one, the
hypotheses of Mathlib's `ComputablePred.rice`. -/
theorem isNontrivial_iff {C : Set (ℕ →. ℕ)} :
    IsNontrivial C ↔ (∃ f, Nat.Partrec f ∧ f ∈ C) ∧ ∃ g, Nat.Partrec g ∧ g ∉ C := by
  constructor
  · rintro ⟨⟨c, hc⟩, d, hd⟩
    exact ⟨⟨_, Code.exists_code.2 ⟨c, rfl⟩, hc⟩, _, Code.exists_code.2 ⟨d, rfl⟩, hd⟩
  · rintro ⟨⟨f, hf, hfC⟩, g, hg, hgC⟩
    obtain ⟨c, rfl⟩ := Code.exists_code.1 hf
    obtain ⟨d, rfl⟩ := Code.exists_code.1 hg
    exact ⟨⟨c, hfC⟩, d, hgC⟩

end DiagonaLean.Rice
