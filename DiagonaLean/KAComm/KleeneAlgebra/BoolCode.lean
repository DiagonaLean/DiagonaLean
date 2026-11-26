/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.KAComm.KleeneAlgebra.Race
import DiagonaLean.KAComm.KleeneAlgebra.RExpPrimcodable
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # The code of an expression over `Bool ⊕ Bool` has a primitive recursive decoder

`encBool` writes an instance over `Bool ⊕ Bool` as the binary digits of the pair of codes
`rc (toNat e)`: the letters `false`, `true` become `0`, `1` of `ℕ` (`toNat`), then `rc` codes the
expression. Decoding is `rcDec`, then the letters back (`fromNat`, by `natBool`), kept only when
coding the result again gives the same expression (`rcbDec`). Both directions are primitive
recursive, so `not_computablePred_of_bitsPair` turns the machine-level results for `encBool` into
`¬ ComputablePred` (`TermEqBool`, `KATermEqBool`, `LangEqBool`, `ModelLeBool`).
-/

namespace DiagonaLean.KAComm.KleeneAlgebra

open DiagonaLean.Foundations.Computability TD

/-- Back from the letters `0`, `1` of `ℕ` to `Bool`: `natBool` on both sides. -/
def fromNat (e : RExp (ℕ ⊕ ℕ)) : RExp (Bool ⊕ Bool) := e.map (dmap natBool)

/-- `fromNat` is a left inverse of `toNat`. -/
theorem fromNat_toNat (e : RExp (Bool ⊕ Bool)) : fromNat (toNat e) = e := by
  induction e with
  | sym x => exact congrArg RExp.sym (congrFun dmap_natBool_comp x)
  | _ => simp_all [fromNat, toNat, RExp.map]

/-- The code of an expression over `Bool ⊕ Bool`, as `encBool` writes it. -/
theorem rcb_prim : Primrec fun e : RExp (Bool ⊕ Bool) => rc (toNat e) := by
  have := RExp.rc_primrec
  unfold toNat boolNat
  fun_prop

/-- **The decoder of `rc ∘ toNat`.** -/
def rcbDec (n : ℕ) : Option (RExp (Bool ⊕ Bool)) :=
  (RExp.rcDec n).bind fun e => if toNat (fromNat e) = e then some (fromNat e) else none

theorem rcbDec_rc (e : RExp (Bool ⊕ Bool)) : rcbDec (rc (toNat e)) = some e := by
  simp [rcbDec, RExp.rcDec_rc, fromNat_toNat]

theorem rcbDec_prim : Primrec rcbDec := by
  have := RExp.rcDec_primrec
  unfold rcbDec fromNat toNat natBool boolNat
  fun_prop

end DiagonaLean.KAComm.KleeneAlgebra
