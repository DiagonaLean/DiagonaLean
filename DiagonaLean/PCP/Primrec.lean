/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.PCP.AlphabetLift
import DiagonaLean.PCP.Reductions.MPCP_to_PCP
import DiagonaLean.Foundations.Computability.DerivePrimcodable
import DiagonaLean.Foundations.Codes.Functor

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

section Codes

variable {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ] {c : α → List β}

/-- Encoding a tile is primitive recursive in it, for a primitive recursive code. -/
@[fun_prop] theorem prim_tileEncode (hc : Primrec c) {f : γ → Tile α} (hf : Primrec f) :
    Primrec fun x => (f x).encode c := by
  unfold Tile.encode
  fun_prop

/-- Encoding a stack is primitive recursive in it, for a primitive recursive code. -/
@[fun_prop] theorem prim_stackEncode (hc : Primrec c) {f : γ → Stack α} (hf : Primrec f) :
    Primrec fun x => (f x).encode c := by
  unfold Stack.encode
  have : Primrec (Tile.encode c) := prim_tileEncode hc Primrec.id
  fun_prop

end Codes

namespace AlphabetLift

variable {γ₁ γ₂ : Type} [DecidableEq γ₁] [Primcodable γ₁] [Primcodable γ₂]

/-- **The change of alphabet is primitive recursive**, for fixed target letters `b0`, `b1`. -/
theorem liftInstance_primrec (b0 b1 : γ₂) :
    Primrec (liftInstance (γ₁ := γ₁) b0 b1) := by
  have := Foundations.Codes.unary_primrec
  unfold liftInstance Stack.encode Tile.encode Foundations.Codes.localCode Foundations.Codes.bitCode
    Foundations.Codes.ofEncodable Foundations.Codes.bit Foundations.Codes.encode Stack.letters
  fun_prop

/-- The function of the reduction `pcpAlphabetLift` is primitive recursive. -/
theorem pcpAlphabetLift_primrec {b0 b1 : γ₂} (hne : b0 ≠ b1) :
    Primrec (pcpAlphabetLift (γ₁ := γ₁) b0 b1 hne).f :=
  liftInstance_primrec b0 b1

end AlphabetLift

end DiagonaLean.PCP
