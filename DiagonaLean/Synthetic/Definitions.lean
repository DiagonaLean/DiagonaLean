/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.Halt.Basic

/-! # Core synthetic computability definitions

## References

* [Y. Forster, D. Larchey-Wendling, A. Dudenhefner, et al.,
    *A Coq Library of Undecidable Problems*][ForsterEtAl2020]
-/

@[expose] public section

namespace DiagonaLean.Synthetic.Definitions
open DiagonaLean.Halt Cslib.Turing

variable {X Y Z : Type*}

/-- `Complement P` is the complement decision problem. -/
def Complement (P : X → Prop) : X → Prop := fun x => ¬P x

/-- `Reflects b p` means provability of `p` coincides with `b = true`. -/
def Reflects (b : Bool) (p : Prop) : Prop := p ↔ b = true

/-- `Decider f P` means `f` pointwise reflects `P` via `reflects`. -/
def Decider (f : X → Bool) (P : X → Prop) : Prop :=
  ∀ x, Reflects (f x) (P x)

/-- `decidable P` means there exists a total Boolean decider for `P`. -/
def SDecidable (P : X → Prop) : Prop :=
  ∃ f : X → Bool, Decider f P

/-- `D` is a Turing-machine decider for `P` under the encoding `enc : X → List Bool`: it halts
on `enc x` with output `[true]` when `P x` holds, and `[false]` when it does not. -/
def TMDeciderFor (D : SingleTapeTM Bool) (enc : X → List Bool) (P : X → Prop) : Prop :=
  ∀ x, (P x → SingleTapeTM.Outputs D (enc x) [true]) ∧
       (¬ P x → SingleTapeTM.Outputs D (enc x) [false])

/-- `P` is machine-decidable under `enc` if some `SingleTapeTM Bool` decides it via
`TMDeciderFor`. Unlike `SDecidable`, the witness here is an actual Turing machine, so this
predicate is not classically vacuous: `SDecidable P` holds for every `P` (via
`Classical.propDecidable`), but `MachineDecidable enc P` genuinely requires `P` to be
algorithmically decidable. -/
def MachineDecidable (enc : X → List Bool) (P : X → Prop) : Prop :=
  ∃ D : SingleTapeTM Bool, TMDeciderFor D enc P

/-- `enumerator f P` means `f` surjects onto the positive instances of `P`. -/
def Enumerator (f : ℕ → Option X) (P : X → Prop) : Prop :=
  ∀ x, P x ↔ ∃ n, f n = some x

/-- `enumerable P` means there exists an enumerator for `P`. -/
def SEnumerable (P : X → Prop) : Prop :=
  ∃ f : ℕ → Option X, Enumerator f P

/-- `semi_decider f P` means `f` semi-decides `P` via Boolean sequences. -/
def SemiDecider (f : X → ℕ → Bool) (P : X → Prop) : Prop :=
  ∀ x, P x ↔ ∃ n, f x n = true

/-- `semi_decidable P` means there exists a semi-decider for `P`. -/
def SemiDecidable (P : X → Prop) : Prop :=
  ∃ f : X → ℕ → Bool, SemiDecider f P

/-- `reduction f P Q` means `f` many-one reduces `P` to `Q`. Unlike `ManyOneReduces`, `f` is a
plain parameter here rather than existentially/structurally packaged: `Reduction f P Q` is a
`Prop` (for a *fixed*, already-in-hand `f`), whereas `P ⪯ₘ Q` bundles the choice of `f` itself. -/
def Reduction (f : X → Y) (P : X → Prop) (Q : Y → Prop) : Prop :=
  ∀ x, P x ↔ Q (f x)

/-- If `f` many-one reduces `p` to `q` then we write `p ⪯ₘ[f] q`. -/
notation:50 p " ⪯ₘ[" f "] " q => Reduction f p q

/-- Many-one reducibility: `f` witnesses `p ⪯ₘ q` when `p x ↔ q (f x)` for every `x`. Packaged
as a structure (rather than `∃ f, ...`) so a reduction is data: `.f` projects out the witness
function directly, without going through `Classical.choose`.

**Convention (not enforced by the type above).** Lean's logic is classical, so a term of this
structure is still satisfiable by excluded-middle-style case splits on `p x` itself: pick a
positive witness of `q` when `p x` holds and a negative one otherwise, producing an `f` with no
algorithmic content that "reduces" almost any non-trivial `p` to almost any non-trivial `q`.
Bundling `f` into a structure does not by itself rule this out -- the case split can still live
inside the `f` field. To keep `⪯ₘ` meaningful, every witness function must be a named `def` that
is not tagged `noncomputable` and does not use `implemented_by`, `extern` or `unsafe`. It may
read data carried by its input, such as a machine's `stateEncodable` field (see
`PCP.Reduction.haltToPcp`). Lean's compiler then rejects a case split on `p x`, because the
`Decidable (p x)` instance can only come from `Classical.propDecidable`, which is
`noncomputable`; `Synthetic/VacuousExample.lean` shows the tagged form this rules out.

Since `Undecidable` is a `Prop` and proofs are not compiled, the same case split raises no error
when it is written inline in a `theorem`. So an undecidability proof must obtain its reduction
from such a `def`, not construct the function in the proof.

The `def` may also take parameters, and a closed undecidability proof may obtain their values
classically, but only if each is a *finite constant* that does not vary with the input: a letter,
a number, a program code (see `PCP.Reduction.pcp_undecidable`). One constant cannot hide infinitely
many answers. A parameter that is a function of the input can: a classically obtained `f` passed
to an untagged `def` is the same case split in another place. A theorem that takes such a parameter
as a hypothesis (`KAComm.Undec.undecidable_termEq_of_family` and its `SmullyanFamily`) is therefore
only conditional, and its hypothesis must itself be discharged by a `def` that follows this
convention.

This convention is evidence of computability, not a proof of it: a witness that follows it runs
as a Lean program, but that does not show a Turing machine computes it on encoded inputs. That
stronger statement is the `ComputesReduction` hypothesis of
`not_machineDecidable_of_halt_reduces`. `scripts/check-classical-reductions.sh` gives a
best-effort textual check for the most direct form of the case split (see its header for what it
does and does not catch); it does not check this convention as a whole. -/
structure ManyOneReduces (p : X → Prop) (q : Y → Prop) where
  /-- The reduction function. -/
  f : X → Y
  /-- `f` witnesses the reduction: `p ⪯ₘ[f] q`, i.e. `p x ↔ q (f x)` for every `x`. -/
  hf : p ⪯ₘ[f] q

/-- If `p` many-one reduces to `q` then we write `p ⪯ₘ q`. -/
notation:50 p " ⪯ₘ " q => ManyOneReduces p q

end DiagonaLean.Synthetic.Definitions
