/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.CombinatoryLogic.Code
import DiagonaLean.Foundations.Computability.DerivePrimcodable
import DiagonaLean.Foundations.Computability.PrimrecRec
import DiagonaLean.Foundations.Computability.TaggedCode

@[expose] public section

/-! # SKI terms are `Primcodable`, and `skc` is a correct encoding

`derive_primcodable Cslib.SKI` makes SKI terms `Primcodable` through their trees, with primitive
recursive constructors (`Cslib.SKI.prim_app`) and `Cslib.SKI.primrec_of_eqns`, so `primrec_rec`
proves structural recursions on SKI terms primitive recursive. The hand-made code `skc` is one
(`skc_primrec`), and decodes in one step from its children, so it is a correct encoding
(`primrec_iff_skc`, by `TaggedCode.primrec_iff`).
-/

derive_primcodable Cslib.SKI

namespace DiagonaLean.Foundations.CombinatoryLogic

open Cslib SKI DiagonaLean.Foundations.Computability

/-! ### `skc` is a correct encoding -/

/-- **`skc` is primitive recursive.** -/
theorem skc_primrec : Primrec skc := by primrec_rec

/-- The child codes packed into an `skc` code. -/
def skcKids (n : ℕ) : List ℕ :=
  if n.unpair.1 = 3 then [n.unpair.2.unpair.1, n.unpair.2.unpair.2] else []

theorem skcKids_lt (n : ℕ) : ∀ m ∈ skcKids n, m < n := by
  intro m hm
  unfold skcKids at hm
  split_ifs at hm with h
  · have h' : n.unpair.1 ≠ 0 := by omega
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact (Nat.unpair_left_le _).trans_lt (TaggedCode.unpair_snd_lt h')
    · exact (Nat.unpair_right_le _).trans_lt (TaggedCode.unpair_snd_lt h')
  · simp at hm

/-- One decoding step of `skc`. -/
def skcBuild (n : ℕ) (ts : List SKI) : Option SKI :=
  if n = cS then some S else if n = cK then some K else if n = cI then some I
  else if n.unpair.1 = 3 then ts[0]?.elim none fun x => ts[1]?.elim none fun y => some (app x y)
  else none

theorem skc_spec (x : SKI) : ∃ ts, skcKids (skc x) = ts.map skc ∧ skcBuild (skc x) ts = some x := by
  cases x with
  | S => exact ⟨[], by simp [skcKids, skc, cS], by simp [skcBuild, skc]⟩
  | K => exact ⟨[], by simp [skcKids, skc, cK], by simp [skcBuild, skc, cS, cK]⟩
  | I => exact ⟨[], by simp [skcKids, skc, cI], by simp [skcBuild, skc, cS, cK, cI]⟩
  | app x y => exact ⟨[x, y], by simp [skcKids, skc, ca],
      by simp [skcBuild, skc, ca, cS, cK, cI, Option.elim]⟩

theorem skcKids_primrec : Primrec skcKids := by unfold skcKids; fun_prop

theorem skcBuild_primrec : Primrec fun q : ℕ × List SKI => skcBuild q.1 q.2 := by
  unfold skcBuild; fun_prop

/-- **`skc` is a correct encoding.** A function into SKI terms is primitive recursive exactly when it
is so through `skc`. -/
theorem primrec_iff_skc {β : Type} [Primcodable β] {f : β → SKI} :
    Primrec f ↔ Primrec fun b => skc (f b) :=
  TaggedCode.primrec_iff skcKids skcKids_lt skcBuild skc_spec skc_primrec skcKids_primrec
    skcBuild_primrec

end DiagonaLean.Foundations.CombinatoryLogic
