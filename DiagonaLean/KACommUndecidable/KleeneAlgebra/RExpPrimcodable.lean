/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KACommUndecidable.KleeneAlgebra.ExprCode
import DiagonaLean.Foundations.Computability.DerivePrimcodable
import DiagonaLean.Foundations.Computability.TaggedCode

@[expose] public section

/-! # Regular expressions are `Primcodable`

`derive_primcodable` makes `RExp X` `Primcodable` for any `Primcodable X`, through its trees
(Theorem A), with `fun_prop` lemmas for the constructors (`RExp.prim_plus` and so on) and
structural recursion (`RExp.primrec_of_eqns`, Theorem B), which `primrec_rec` uses.

The hand-made code `rc` of `ExprCode.lean` is a correct encoding: it is primitive recursive
(`rc_primrec`, by `primrec_rec`), it has a primitive recursive decoder (`rcDec_primrec`,
`rcDec_rc`), and so primitive recursion through `rc` is primitive recursion (`primrec_iff_rc`).
-/

derive_primcodable DiagonaLean.KACommUndecidable.KleeneAlgebra.RExp

namespace DiagonaLean.KACommUndecidable.KleeneAlgebra

open DiagonaLean.Foundations.Computability

namespace RExp

/-! ### The hand-made code `rc` is primitive recursive -/

/-- `symC` is primitive recursive. -/
@[fun_prop] theorem symC_primrec : Primrec symC := by
  have h : Primrec fun x : ℕ ⊕ ℕ => x.elim (fun a => 2 * a) (fun a => 2 * a + 1) := by fun_prop
  exact h.of_eq fun x => by cases x <;> rfl

/-- **The hand-made code `rc` is primitive recursive** with respect to the `Primcodable` encoding
of expressions. -/
theorem rc_primrec : Primrec rc := by primrec_rec

/-! ### Decoding `rc` codes -/

/-- The letter with code `p`: the inverse of `symC`. -/
def symDec (p : ℕ) : ℕ ⊕ ℕ := if p % 2 = 0 then .inl (p / 2) else .inr (p / 2)

theorem symDec_symC (x : ℕ ⊕ ℕ) : symDec (symC x) = x := by
  cases x <;> simp [symDec, symC]; omega

theorem symDec_primrec : Primrec symDec := by unfold symDec; fun_prop

/-- The child codes packed into an `rc` code. -/
def rcKids (n : ℕ) : List ℕ :=
  if n.unpair.1 = 3 ∨ n.unpair.1 = 4 then [n.unpair.2.unpair.1, n.unpair.2.unpair.2]
  else if n.unpair.1 = 5 then [n.unpair.2] else []

theorem rcKids_lt (n : ℕ) : ∀ m ∈ rcKids n, m < n := by
  intro m hm
  unfold rcKids at hm
  split_ifs at hm with h₁ h₂
  · have h : n.unpair.1 ≠ 0 := by omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact (Nat.unpair_left_le _).trans_lt (TaggedCode.unpair_snd_lt h)
    · exact (Nat.unpair_right_le _).trans_lt (TaggedCode.unpair_snd_lt h)
  · simp only [List.mem_singleton] at hm
    exact hm ▸ TaggedCode.unpair_snd_lt (by omega)
  · simp at hm

/-- One decoding step of `rc`: the node of code `n`, from its decoded children `ts`. -/
def rcBuild (n : ℕ) (ts : List (RExp (ℕ ⊕ ℕ))) : Option (RExp (ℕ ⊕ ℕ)) :=
  if n.unpair.1 = 0 then (if n.unpair.2 = 0 then some zero else none)
  else if n.unpair.1 = 1 then (if n.unpair.2 = 0 then some one else none)
  else if n.unpair.1 = 2 then some (sym (symDec n.unpair.2))
  else if n.unpair.1 = 3 then ts[0]?.elim none fun e => ts[1]?.elim none fun f => some (plus e f)
  else if n.unpair.1 = 4 then ts[0]?.elim none fun e => ts[1]?.elim none fun f => some (mul e f)
  else if n.unpair.1 = 5 then ts[0]?.elim none fun e => some (star e)
  else none

/-- `rc` decodes in one step from its children. -/
theorem rc_spec (e : RExp (ℕ ⊕ ℕ)) :
    ∃ ts, rcKids (rc e) = ts.map rc ∧ rcBuild (rc e) ts = some e := by
  cases e with
  | zero => exact ⟨[], by simp [rcKids, rc, cz], by simp [rcBuild, rc, cz]⟩
  | one => exact ⟨[], by simp [rcKids, rc, co], by simp [rcBuild, rc, co]⟩
  | sym x => exact ⟨[], by simp [rcKids, rc, cs], by simp [rcBuild, rc, cs, symDec_symC]⟩
  | plus e f => exact ⟨[e, f], by simp [rcKids, rc, cp], by simp [rcBuild, rc, cp, Option.elim]⟩
  | mul e f => exact ⟨[e, f], by simp [rcKids, rc, cm], by simp [rcBuild, rc, cm, Option.elim]⟩
  | star e => exact ⟨[e], by simp [rcKids, rc, ct], by simp [rcBuild, rc, ct, Option.elim]⟩

theorem rcKids_primrec : Primrec rcKids := by unfold rcKids; fun_prop

theorem rcBuild_primrec : Primrec fun q : ℕ × List (RExp (ℕ ⊕ ℕ)) => rcBuild q.1 q.2 := by
  have := symDec_primrec
  unfold rcBuild
  fun_prop

/-- The decoder of `rc`, from `TaggedCode`. -/
abbrev rcDec : ℕ → Option (RExp (ℕ ⊕ ℕ)) := TaggedCode.decode rcKids rcKids_lt rcBuild

/-- **`rcDec` decodes `rc`.** -/
theorem rcDec_rc (e : RExp (ℕ ⊕ ℕ)) : rcDec (rc e) = some e :=
  TaggedCode.decode_code rcKids rcKids_lt rcBuild rc_spec e

/-- **The decoder of `rc` is primitive recursive.** -/
theorem rcDec_primrec : Primrec rcDec :=
  TaggedCode.decode_primrec rcKids rcKids_lt rcBuild rcKids_primrec rcBuild_primrec

/-- **`rc` is a correct encoding.** A function into expressions is primitive recursive exactly
when it is so through `rc`: the hand-made code and the `Primcodable` encoding are primitive
recursively isomorphic. -/
theorem primrec_iff_rc {β : Type} [Primcodable β] {f : β → RExp (ℕ ⊕ ℕ)} :
    Primrec f ↔ Primrec fun b => rc (f b) :=
  TaggedCode.primrec_iff rcKids rcKids_lt rcBuild rc_spec rc_primrec rcKids_primrec rcBuild_primrec

end RExp

end DiagonaLean.KACommUndecidable.KleeneAlgebra
