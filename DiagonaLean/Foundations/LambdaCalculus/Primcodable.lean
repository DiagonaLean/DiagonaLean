/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.LambdaCalculus.Code
import DiagonaLean.Foundations.Computability.DerivePrimcodable
import DiagonaLean.Foundations.Computability.TaggedCode

@[expose] public section

/-! # λ-terms are `Primcodable`, and `tc` is a correct encoding

`derive_primcodable` makes Cslib's locally nameless λ-terms `Term Var` `Primcodable` for any
`Primcodable Var`, through their trees (Theorem A), with `fun_prop` lemmas for the constructors
(`Term.prim_abs` and so on) and structural recursion (`Term.primrec_of_eqns`, Theorem B), which
`primrec_rec` uses.

The hand-made code `tc` is primitive recursive (`tc_primrec`, by `primrec_rec`) and decodes in one
step from its children, so it is a correct encoding (`primrec_iff_tc`, by `TaggedCode.primrec_iff`).
-/

derive_primcodable Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

namespace DiagonaLean.Foundations.LambdaCalculus

open Cslib LambdaCalculus.LocallyNameless.Untyped DiagonaLean.Foundations.Computability

/-! ### `tc` is a correct encoding -/

/-- **`tc` is primitive recursive.** -/
theorem tc_primrec : Primrec tc := by primrec_rec

/-- The child codes packed into a `tc` code. -/
def tcKids (n : ℕ) : List ℕ :=
  if n.unpair.1 = 2 then [n.unpair.2]
  else if n.unpair.1 = 3 then [n.unpair.2.unpair.1, n.unpair.2.unpair.2] else []

theorem tcKids_lt (n : ℕ) : ∀ m ∈ tcKids n, m < n := by
  intro m hm
  unfold tcKids at hm
  split_ifs at hm with h₁ h₂
  · simp only [List.mem_singleton] at hm
    exact hm ▸ TaggedCode.unpair_snd_lt (by omega)
  · have h : n.unpair.1 ≠ 0 := by omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact (Nat.unpair_left_le _).trans_lt (TaggedCode.unpair_snd_lt h)
    · exact (Nat.unpair_right_le _).trans_lt (TaggedCode.unpair_snd_lt h)
  · simp at hm

/-- One decoding step of `tc`. -/
def tcBuild (n : ℕ) (ts : List (Term ℕ)) : Option (Term ℕ) :=
  if n.unpair.1 = 0 then some (.bvar n.unpair.2)
  else if n.unpair.1 = 1 then some (.fvar n.unpair.2)
  else if n.unpair.1 = 2 then ts[0]?.elim none fun M => some (.abs M)
  else if n.unpair.1 = 3 then ts[0]?.elim none fun M => ts[1]?.elim none fun N => some (.app M N)
  else none

theorem tc_spec (M : Term ℕ) :
    ∃ ts, tcKids (tc M) = ts.map tc ∧ tcBuild (tc M) ts = some M := by
  cases M with
  | bvar i => exact ⟨[], by simp [tcKids, tc, cb], by simp [tcBuild, tc, cb]⟩
  | fvar x => exact ⟨[], by simp [tcKids, tc, cf], by simp [tcBuild, tc, cf]⟩
  | abs M => exact ⟨[M], by simp [tcKids, tc, cl], by simp [tcBuild, tc, cl, Option.elim]⟩
  | app M N => exact ⟨[M, N], by simp [tcKids, tc, cp], by simp [tcBuild, tc, cp, Option.elim]⟩

theorem tcKids_primrec : Primrec tcKids := by unfold tcKids; fun_prop

theorem tcBuild_primrec : Primrec fun q : ℕ × List (Term ℕ) => tcBuild q.1 q.2 := by
  unfold tcBuild; fun_prop

/-- **`tc` is a correct encoding.** A function into λ-terms is primitive recursive exactly when it
is so through `tc`. -/
theorem primrec_iff_tc {β : Type} [Primcodable β] {f : β → Term ℕ} :
    Primrec f ↔ Primrec fun b => tc (f b) :=
  TaggedCode.primrec_iff tcKids tcKids_lt tcBuild tc_spec tc_primrec tcKids_primrec
    tcBuild_primrec

end DiagonaLean.Foundations.LambdaCalculus
