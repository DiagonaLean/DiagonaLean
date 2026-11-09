/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.Free

@[expose] public section

/-! # Equality in Kleene algebra with commutativity, as a decision problem

An instance is a pair of expressions over a doubled alphabet. The questions are whether the two
sides are provably equal in pre-Kleene algebra (`Equiv DComm`), provably equal in Kleene algebra
(`KAEquiv DComm`), or have the same language.

`Undec.Inst` uses the alphabet `ℕ`. `Reduction.InstB` uses `Bool`, the paper's `Σ = {0, 1}`.
-/

namespace DiagonaLean.KAComm

/-- An instance: two expressions over the doubled alphabet `ℕ ⊕ ℕ`. -/
abbrev Undec.Inst := RExp (ℕ ⊕ ℕ) × RExp (ℕ ⊕ ℕ)

/-- A two-letter instance: two expressions over the doubled alphabet `Bool ⊕ Bool`. -/
abbrev Reduction.InstB := RExp (Bool ⊕ Bool) × RExp (Bool ⊕ Bool)

end DiagonaLean.KAComm
