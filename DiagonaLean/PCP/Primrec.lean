/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.PCP.AlphabetLift
import DiagonaLean.PCP.Reductions.MPCP_to_PCP
import DiagonaLean.Foundations.Computability.DerivePrimcodable

@[expose] public section

/-! # The PCP reductions are primitive recursive

Tiles and the extended alphabet `Ext α` are `Primcodable` (`derive_primcodable`), and so are PCP and
MPCP instances (lists and pairs of tiles). With these encodings:

* the reduction from MPCP to PCP is primitive recursive (`mpcpToPcp_primrec`);
* the change of alphabet behind `pcpUndecidable` is primitive recursive (`liftInstance_primrec`).

This is a statement about the functions themselves, stronger than `#check_reductions`, which only
checks that they compile.
-/

derive_primcodable DiagonaLean.PCP.Tile
derive_primcodable DiagonaLean.PCP.Reduction.Ext

namespace DiagonaLean.PCP

open DiagonaLean.Foundations.Computability

namespace Reduction

variable {α : Type}

theorem hashL_eq (x : List α) : hashL x = x.flatMap fun a => [⋕, ↟a] := by
  induction x <;> simp_all [hashL]

theorem hashR_eq (x : List α) : hashR x = x.flatMap fun a => [↟a, ⋕] := by
  induction x <;> simp_all [hashR]

variable [Primcodable α]

@[fun_prop] theorem prim_hashL {β : Type} [Primcodable β] {f : β → List α} (hf : Primrec f) :
    Primrec fun x => hashL (f x) := by
  simp only [hashL_eq]; fun_prop

@[fun_prop] theorem prim_hashR {β : Type} [Primcodable β] {f : β → List α} (hf : Primrec f) :
    Primrec fun x => hashR (f x) := by
  simp only [hashR_eq]; fun_prop

/-- **The reduction from MPCP to PCP is primitive recursive.** -/
theorem mpcpToPcp_primrec : Primrec₂ (mpcpToPcp (α := α)) := by
  show Primrec fun q : Tile α × Stack α => mpcpToPcp q.1 q.2
  unfold mpcpToPcp tileStart tileReg tileEnd
  fun_prop

end Reduction

namespace AlphabetLift

theorem natToBits_eq (len n : ℕ) :
    natToBits len n = (List.range len).map fun i => decide (n / 2 ^ i % 2 = 1) := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih =>
    rw [natToBits, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · simp
    · refine List.map_congr_left fun i _ => ?_
      simp [Function.comp, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

variable {γ₁ γ₂ : Type} [DecidableEq γ₁] [Primcodable γ₁] [Primcodable γ₂]

/-- **The change of alphabet is primitive recursive**, for fixed target letters `b0`, `b1`. -/
theorem liftInstance_primrec (b0 b1 : γ₂) :
    Primrec (liftInstance (γ₁ := γ₁) b0 b1) := by
  unfold liftInstance liftTile liftWord symbolWord symbolBits widthFor symbolsUsed bitTo
  simp only [natToBits_eq]
  fun_prop

/-- The function of the reduction `PCPAlphabetLift` is primitive recursive. -/
theorem pcpAlphabetLift_primrec {b0 b1 : γ₂} (hne : b0 ≠ b1) :
    Primrec (PCPAlphabetLift (γ₁ := γ₁) b0 b1 hne).f :=
  liftInstance_primrec b0 b1

end AlphabetLift

end DiagonaLean.PCP
