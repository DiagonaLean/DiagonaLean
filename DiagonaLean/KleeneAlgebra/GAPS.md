# KA with commutativity: gaps and possible extensions

Status as of 2026-11-02: everything the paper proves (arXiv:2411.15979) is formalized, M0–M7 in
`TODO.md`. This file lists what goes beyond the paper or is left as a hypothesis. The final
theorems are in `Reductions/SelfOut_to_ModelLe.lean` (`insepUndecidable_provable`,
`insepUndecidable_of_between`, `not_machineDecidable_of_between`).

## Status: no machine decides equality on `T Σ̈` and `K Σ̈` (2026-11-09)

`Reductions/SelfHalt_to_TermEq.lean` proves `not_machineDecidable_termEq_bool`,
`not_machineDecidable_kaTermEq_bool` and the `_nat` versions, with no hypotheses. The encodings are
injective, and `not_machineDecidable_of_conv` extends them to any encoding a machine can compute
from these. This goes around items 0 and 1, by reducing from self-halting and reading only the code.
Still open at machine level: `L Σ̈`, and the exact reductions `kaRed`, `eqRed`, `haltRed`, `reduction`.

## 0. `encodeBoolTM` is not faithful (found 2026-11-09; blocks item 1 and M8b)

**What:** `toBoolMachineData` (`Halt/Encoding.lean`) records only transitions with a successor
state, so a machine's write on its halting step is not in its code. Take the one-state machine
that erases its input moving right, then writes `b` on the first blank and halts. For `b = true`
and `b = false` the two machines have the same code (`rfl`), and they output `[true]` and `[false]`
on every input. This was checked in Lean, with no `sorry`, in a scratch file not yet in the repo.

**Consequences, all proved from that pair:**
- No machine computes `eqRed` (or `kaRed`) from the code under an injective `enc`, since
  `eqRed` differs on the pair. So `hR` in `not_machineDecidable_eqVia_of_computes` can't be met as stated, and
  `not_machineDecidable_of_between` has the same problem.
- `selfOut_inseparable` holds by the collision alone, with no diagonal argument. So
  `not_machineDecidable_selfEq`, `not_machineDecidable_termEq` and
  `not_machineDecidable_kaTermEq` currently say nothing about the difficulty of the problem: the
  input doesn't determine the answer.
- The output clause of `IsUniversalWrt` (`Foundations/UniversalTuringMachine/Basic.lean`) can't be
  met by any machine under any pairing. `IsWeaklyUniversalWrt`, which only mentions halting, is not
  affected by this argument.

**Fix to make:** record every `(state, symbol)` row in the code, including the written symbol,
the movement and an optional successor. That should also expose states that never appear as
successors, which `enumL` in `rmS` depends on. Not done yet: see `TODO.md`, M8b.

## 1. A Turing machine computing `kaRed` (the one open hypothesis)

**Where:** `not_machineDecidable_of_between` takes
`hR : ComputesReduction R encodeBoolTM enc kaRed`.

**What it means:** the theorem says no TM decides any theory between `Provable` and `ModelLe`,
*provided* some TM `R` turns `encodeBoolTM M` into `enc (kaRed M)`. Without it, the result is the
synthetic statement `insepUndecidable_provable`, in the same style as the repo's `Undecidable`.

**Evidence it holds:** `kaRed` is an ordinary computable Lean function. `#eval` runs it, and the
one-state bit-flip machine gives expressions of 258 and 1743 nodes.

**What discharging it needs:**
- A concrete `enc : Inst → List Bool`. For example, derive `Encodable (RExp (ℕ ⊕ ℕ))` and write
  the code in binary.
- A `SingleTapeTM Bool` that decodes `encodeBoolTM M`, enumerates states and symbols, and prints
  the expressions `lhsS` and `rhsS` (`MachineEncoding/MachineTerms.lean`), including `bnd (rmS M)`.
- Correctness proofs at the level of tape traces, as in `Halt/Compositions.lean`
  (`pairSelfTM`). That machine alone is about 450 lines; this one would be much larger.

**Cheaper alternative:** show that `kaRed` is `Computable` in Mathlib's sense (via `Primrec`), and
use a bridge from `Computable` to `SingleTapeTM`, if one is ever added to the repo or Cslib.

## 1a. The alphabet: `ℕ`, and now also `{0, 1}`

**Where:** `Inst` is over `ℕ ⊕ ℕ`, and `kaRed` and `rInst` rename letters to numbers. The paper fixes
`Σ = {0, 1}` and encodes the letters of `Σ_M` as binary strings.

**Done for `Undecidable` (2026-11-09):** `Reductions/Halt_to_TermEqBool.lean` proves `undecidable_termEq_bool`,
`undecidable_kaTermEq_bool` and `undecidable_not_langEq_bool` over `Bool ⊕ Bool`, by substituting
each letter `n` with the prefix code `1ⁿ0`.

**Still over `ℕ`:** the older statements (`termEq_separated`, `not_machineDecidable_eqOn_of_computes`, and so on). No
theorem states that the `{0, 1}` result implies the `ℕ` one; they are proved separately. The map on
`T Σ̈` is not proved injective, as the paper claims, because the argument doesn't need it.

## 2. `HaltProblem ⪯ₘ Provable`, Σ⁰₁-completeness, decision D1(a)

**Equality is done (2026-11-09):** `Reductions/Halt_to_TermEq.lean` proves `undecidable_termEq` and
`undecidable_kaTermEq` with no hypotheses. The reduction `Reduction.reduction` is an untagged `def`
whose only classically obtained inputs are finite constants (`Base`, and the code `C`), as the
`ManyOneReduces` convention requires. Three limits remain:

- `ComputesReduction` is not proved for `reduction` itself, which reads halting transitions through
  `rowsE`, so it is not a function of `haltInputEncoding` (item 0). The machine-level theorems in
  `Reductions/SelfHalt_to_TermEq.lean` use a variant that reads only the code.
- It is computable but infeasible to run: `Code.const n` nests `n` terms and `n` is the code of the
  instance's data. The pieces run on small inputs; the composite overflows the stack.
- `HaltProblem ⪯ₘ Provable` (the inequality) is not stated separately. `provable_iff_equiv` relates the
  two forms, and `rInst` already has the shape `(e + f, f)`.

The notes below predate this.

**Partly done:** `Undecidable (Complement ModelLe)` holds (`Reductions/SelfOut_to_ModelLe.lean`,
`undecidable_not_modelLe`): `M` halts on `w` iff the inequality *fails* in the language model. In
equality form, `undecidable_not_langEq` and `undecidable_not_eqVia` are in `Reductions/SelfOut_to_Eq.lean`.

For `T Σ̈` and `K Σ̈`, `Reductions/SelfOut_to_Eq.lean` proves `selfEq_reduces` and
`not_machineDecidable_selfEq`: the problem on machine codes reduces to equality, and no machine
decides it. That is not `Undecidable`, which needs a reduction from `HaltProblem`.

**Which direction is possible:** language equality is co-r.e., so only its complement can receive
a computable reduction from `HaltProblem`. Provable equality in `T Σ̈` and `K Σ̈` is r.e., so there the
target is the predicate itself. These two remarks are not formalized.

**Logical core done:** `Reductions/Sigma1.lean` proves `Undecidable` for equality on `T Σ̈` and `K Σ̈`
from a `SmullyanFamily` (paper's Theorem 19). What remains is building that family from data:
`TODO.md`, M8b–d and decision D4.

**Do not close this classically:** a term of `HaltProblem ⪯ₘ Equiv` is easy to write by case split on
`HaltProblem p`, picking a true or a false instance. That breaks the convention on `ManyOneReduces`. The
same applies to any function from `(M, w)` to machines that is chosen by such a case split.

**What remains:** a reduction `HaltProblem ⪯ₘ Provable`, giving `Undecidable Provable` as the repo defines
it.

**Why it's not done:** the paper doesn't prove it, and the model-level reduction doesn't transfer.
For a machine that runs forever, the inequality *holds* in the language model
(`Enc.pl_le_of_forall_running`), but whether pre-KA can prove it is open: the completeness proof
(Theorem 16) needs a terminating run.

A route is Smullyan's theorem: an r.e. set separating effectively inseparable sets is creative,
hence Σ⁰₁-complete. `Provable` is r.e. and separates the pair (`sepReduces_of_between`). This
needs the recursion theorem (Mathlib's `Nat.Partrec.Code.fixed_point`), an enumeration of pre-KA
proofs, and the same computability bridge as item 1.

## 3. General commutation relations

**What:** a language model `T X → trace languages` for an arbitrary commutation relation `C`.

**Current state:** `FreePreKA.lang` needs `C = Eq` (`Free.lean`), and the doubled alphabet has its
own model `TD.pl` (`Doubled.lean`). The undecidability proof only needs the doubled case. The
general case would need Mazurkiewicz trace monoids (the old M1 milestone).

## 4. Uniqueness of `FreePreKA.lift`

**What:** two pre-KA morphisms `FreePreKA X C → α` that agree on generators are equal, so `T X` is
actually free. It is a short induction with `FreePreKA.ind`. Nothing uses it yet.

## 5. Restating the Theorem 6 repair for `C = Eq`

`FiniteLangExpansion.lean` proves the guarded-term repair for `T Σ̈` with the language model `pl`, the
setting where the paper uses it. The counterexample file states Theorem 6 for `C = Eq` with
`lang`. The same proof should carry over to that setting.

## 6. Paper errata write-up

These are recorded in `TODO.md` under "Paper issues found":
- Theorem 6, Corollary 7 and Theorem 9 fail at `1∗`; repaired for guarded terms.
- Corollary 8's proof goes through the false Corollary 7; it is reproved directly.
- Definition 20 needs the residue bound only for `Λ ⊆ L`.
- Lemma 34's proof simplifies, and Lemma 33 needs its right context.
- Typos in Theorem 16 and in Lemma 34 step (5).

These could become a short note for the authors or an appendix.
