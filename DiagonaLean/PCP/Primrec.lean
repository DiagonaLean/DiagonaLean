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
* the change of alphabet behind `PCP.synthFromHaltOver` is primitive recursive
  (`liftInstance_primrec`).

This is a statement about the functions themselves, stronger than `#check_reductions`, which only
checks that they compile.
-/

derive_primcodable DiagonaLean.PCP.Tile
derive_primcodable DiagonaLean.PCP.Reduction.Ext

namespace DiagonaLean.PCP

open DiagonaLean.Foundations.Computability

namespace Reduction

variable {α : Type} [Primcodable α]

/-- `hashL` is primitive recursive. -/
@[fun_prop] theorem hashL_primrec : Primrec (hashL (α := α)) := by primrec_rec

/-- `hashR` is primitive recursive. -/
@[fun_prop] theorem hashR_primrec : Primrec (hashR (α := α)) := by primrec_rec

end Reduction

/- The tiles of the reduction from MPCP to PCP, and the reduction itself, are primitive recursive;
`derive_primrec` registers each lemma with `fun_prop`, so a link built on `mpcpToPcp` is upgraded
to a proved one by `reduce_from` with no goal left. -/
derive_primrec Reduction.tileStart [Primcodable α]
derive_primrec Reduction.tileReg [Primcodable α]
derive_primrec Reduction.mpcpToPcp [Primcodable α]

namespace Reduction

variable {α : Type} [Primcodable α]

/-- **The reduction from MPCP to PCP is primitive recursive.** -/
theorem mpcpToPcp_primrec : Primrec₂ (mpcpToPcp (α := α)) := mpcpToPcp_prim

end Reduction

/- Encoding tiles and stacks is primitive recursive, for a code that may depend on the input. -/
derive_primrec Tile.encode [Primcodable α] [Primcodable β]
derive_primrec Stack.encode [Primcodable α] [Primcodable β]
derive_primrec Tile.toPair [Primcodable α]
derive_primrec Stack.letters [Primcodable α]

namespace AlphabetLift

variable {γ₁ γ₂ : Type} [DecidableEq γ₁] [Primcodable γ₁] [Primcodable γ₂]

/-- **The change of alphabet is primitive recursive**, for fixed target letters `b0`, `b1`. -/
@[fun_prop] theorem liftInstance_primrec (b0 b1 : γ₂) :
    Primrec (liftInstance (γ₁ := γ₁) b0 b1) := by
  unfold liftInstance
  fun_prop

/-- The change of alphabet, as the lift map of `pcpFunctor`, is primitive recursive; registered
with `fun_prop`, so `reduce_from` upgrades `PCP.synthAlphabetLift` with no goal left. -/
@[fun_prop] theorem liftMap_primrec (b0 b1 : γ₂) :
    Primrec (pcpFunctor.liftMap (α := γ₁) b0 b1) :=
  liftInstance_primrec b0 b1

/-- The function of the reduction `PCP.synthAlphabetLift` is primitive recursive. -/
theorem synthAlphabetLift_primrec {b0 b1 : γ₂} (hne : b0 ≠ b1) :
    Primrec (PCP.synthAlphabetLift (γ₁ := γ₁) b0 b1 hne).f :=
  liftInstance_primrec b0 b1

end AlphabetLift

end DiagonaLean.PCP
