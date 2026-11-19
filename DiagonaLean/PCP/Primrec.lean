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
* the change of alphabet behind `undecidablePCP` is primitive recursive (`liftInstance_primrec`).

This is a statement about the functions themselves, stronger than `#check_reductions`, which only
checks that they compile.
-/

derive_primcodable DiagonaLean.PCP.Tile
derive_primcodable DiagonaLean.PCP.Reduction.Ext

namespace DiagonaLean.PCP

open DiagonaLean.Foundations.Computability

namespace Reduction

variable {α : Type} [Primcodable α]

@[fun_prop] theorem hashL_primrec : Primrec (hashL (α := α)) := by primrec_rec

@[fun_prop] theorem hashR_primrec : Primrec (hashR (α := α)) := by primrec_rec

/-- **The reduction from MPCP to PCP is primitive recursive.** -/
theorem mpcpToPcp_primrec : Primrec₂ (mpcpToPcp (α := α)) := by
  show Primrec fun q : Tile α × Stack α => mpcpToPcp q.1 q.2
  unfold mpcpToPcp tileStart tileReg tileEnd
  fun_prop

end Reduction

namespace AlphabetLift

theorem natToBits_primrec : Primrec₂ natToBits := by primrec_rec

@[fun_prop] theorem prim_natToBits {β : Type} [Primcodable β] {f g : β → ℕ} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => natToBits (f x) (g x) := natToBits_primrec.comp hf hg

variable {γ₁ γ₂ : Type} [DecidableEq γ₁] [Primcodable γ₁] [Primcodable γ₂]

/-- **The change of alphabet is primitive recursive**, for fixed target letters `b0`, `b1`. -/
theorem liftInstance_primrec (b0 b1 : γ₂) :
    Primrec (liftInstance (γ₁ := γ₁) b0 b1) := by
  unfold liftInstance liftTile liftWord symbolWord symbolBits widthFor symbolsUsed bitTo
  fun_prop

/-- The function of the reduction `pcpAlphabetLift` is primitive recursive. -/
theorem pcpAlphabetLift_primrec {b0 b1 : γ₂} (hne : b0 ≠ b1) :
    Primrec (pcpAlphabetLift (γ₁ := γ₁) b0 b1 hne).f :=
  liftInstance_primrec b0 b1

end AlphabetLift

end DiagonaLean.PCP
