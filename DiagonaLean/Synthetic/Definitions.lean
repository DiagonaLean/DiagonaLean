/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import DiagonaLean.Halt.Basic

@[expose] public section

/-! # Core synthetic computability definitions

The basic notions of synthetic computability: Boolean deciders (`Decider`, `SDecidable`),
Turing machine deciders (`TMDeciderFor`, `MachineDecidable`), enumerators (`Enumerator`,
`SEnumerable`), semi-deciders (`SemiDecider`, `SemiDecidable`), many-one reductions by a fixed
function (`Reduction`, notation `p ⪯ₘ[f] q`) and many-one reducibility as data
(`ManyOneReduces`, notation `p ⪯ₘ q`).

## References

* [Y. Forster, D. Larchey-Wendling, A. Dudenhefner, et al.,
    *A Coq Library of Undecidable Problems*][ForsterEtAl2020]
-/

namespace DiagonaLean.Synthetic.Definitions
open DiagonaLean.Halt Cslib.Turing

variable {X Y Z : Type*}

/-- `Complement P` is the complement decision problem. -/
def Complement (P : X → Prop) : X → Prop := fun x => ¬P x

/-- `Reflects b p` means provability of `p` coincides with `b = true`. -/
def Reflects (b : Bool) (p : Prop) : Prop := p ↔ b = true

/-- `Decider f P` means `f` pointwise reflects `P` through `Reflects`. -/
def Decider (f : X → Bool) (P : X → Prop) : Prop :=
  ∀ x, Reflects (f x) (P x)

/-- `SDecidable P` means there exists a total Boolean decider for `P`. -/
def SDecidable (P : X → Prop) : Prop :=
  ∃ f : X → Bool, Decider f P

/-- `D` is a Turing-machine decider for `P` under the encoding `enc : X → List Bool`: it halts
on `enc x` with output `[true]` when `P x` holds, and `[false]` when it does not. -/
def TMDeciderFor (D : SingleTapeTM Bool) (enc : X → List Bool) (P : X → Prop) : Prop :=
  ∀ x, (P x → SingleTapeTM.Outputs D (enc x) [true]) ∧
       (¬ P x → SingleTapeTM.Outputs D (enc x) [false])

/-- `P` is machine-decidable under `enc` if some `SingleTapeTM Bool` decides it via
`TMDeciderFor`. Unlike `SDecidable`, the witness here is an actual Turing machine, so this
predicate is not classically vacuous: `SDecidable P` holds for every `P` (through
`Classical.propDecidable`), but `MachineDecidable enc P` requires `P` to be algorithmically
decidable. -/
def MachineDecidable (enc : X → List Bool) (P : X → Prop) : Prop :=
  ∃ D : SingleTapeTM Bool, TMDeciderFor D enc P

/-- `Enumerator f P` means `f` surjects onto the positive instances of `P`. -/
def Enumerator (f : ℕ → Option X) (P : X → Prop) : Prop :=
  ∀ x, P x ↔ ∃ n, f n = some x

/-- `SEnumerable P` means there exists an enumerator for `P`. -/
def SEnumerable (P : X → Prop) : Prop :=
  ∃ f : ℕ → Option X, Enumerator f P

/-- `SemiDecider f P` means `f` semi-decides `P` via Boolean sequences. -/
def SemiDecider (f : X → ℕ → Bool) (P : X → Prop) : Prop :=
  ∀ x, P x ↔ ∃ n, f x n = true

/-- `SemiDecidable P` means there exists a semi-decider for `P`. -/
def SemiDecidable (P : X → Prop) : Prop :=
  ∃ f : X → ℕ → Bool, SemiDecider f P

/-- `Reduction f P Q` means `f` many-one reduces `P` to `Q`. Unlike `ManyOneReduces`, `f` is a
plain parameter here rather than existentially/structurally packaged: `Reduction f P Q` is a
`Prop` (for a *fixed*, already-in-hand `f`), whereas `P ⪯ₘ Q` bundles the choice of `f` itself. -/
def Reduction (f : X → Y) (P : X → Prop) (Q : Y → Prop) : Prop :=
  ∀ x, P x ↔ Q (f x)

/-- If `f` many-one reduces `p` to `q` then we write `p ⪯ₘ[f] q`. -/
notation:50 p " ⪯ₘ[" f "] " q => Reduction f p q

/-- Many-one reducibility: `f` witnesses `p ⪯ₘ q` when `p x ↔ q (f x)` for every `x`. Packaged
as a structure (rather than `∃ f, ...`) so a reduction is data: `.f` projects out the witness
function directly, without going through `Classical.choose`.

**Convention, checked by `#check_reductions`.** Lean's logic is classical, so a term of this
structure exists for almost any non-trivial `p` and `q`: the case split `if p x then a else b`,
with `q a` and `¬ q b`, is a valid `f` with no algorithmic content. To keep `⪯ₘ` meaningful, every
reduction is built by a definition that Lean compiles: not `noncomputable`, and without
`implemented_by`, `extern` or `unsafe`. Lean refuses to compile a case split on an undecided `p x`,
since the `Decidable (p x)` instance can only come from classical choice. The definition may read
data carried by its input, such as a machine's `stateEncodable` field (see
`PCP.Reduction.haltToPcp`).

Proofs are never compiled, so a reduction is never stated as a proposition: an undecidability
result is a definition whose value is the reduction (`Undecidable` is a type), and composing
results composes their functions. A theorem may take reductions as hypotheses, but may not conclude
that one exists, as `Nonempty (p ⪯ₘ q)` would.

`#check_reductions` (`Synthetic/ReductionCheck.lean`), run in CI by `scripts/CheckReductions.lean`,
checks these rules over the library. A reduction that passes runs as a Lean program; that is not a
proof that a Turing machine computes it on encoded inputs, which is the `ComputesReduction`
hypothesis of `not_machineDecidable_of_halt_reduces`. -/
structure ManyOneReduces (p : X → Prop) (q : Y → Prop) where
  /-- The reduction function. -/
  f : X → Y
  /-- `f` witnesses the reduction: `p ⪯ₘ[f] q`, i.e. `p x ↔ q (f x)` for every `x`. -/
  hf : p ⪯ₘ[f] q

/-- If `p` many-one reduces to `q` then we write `p ⪯ₘ q`. -/
notation:50 p " ⪯ₘ " q => ManyOneReduces p q

end DiagonaLean.Synthetic.Definitions
