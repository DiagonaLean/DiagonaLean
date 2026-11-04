# KA with commutativity: gaps and possible extensions

Status as of 2026-11-02: everything the paper proves (arXiv:2411.15979) is formalized, M0–M7 in
`TODO.md`. This file lists what goes beyond the paper or is left as a hypothesis. The final
theorems are in `TM/Undecidable.lean` (`insepUndecidable_provable`,
`insepUndecidable_of_between`, `not_machineDecidable_of_between`).

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
  the expressions `lhsS` and `rhsS` (`TM/Syntax.lean`), including `bnd (rmS M)`.
- Correctness proofs at the level of tape traces, as in `Halt/Compositions.lean`
  (`pairSelfTM`). That machine alone is about 450 lines; this one would be much larger.

**Cheaper alternative:** show that `kaRed` is `Computable` in Mathlib's sense (via `Primrec`), and
use a bridge from `Computable` to `SingleTapeTM`, if one is ever added to the repo or Cslib.

## 2. `HALT ⪯ₘ Provable`, Σ⁰₁-completeness, decision D1(a)

**Partly done:** `Undecidable (Complement ModelLe)` holds (`TM/Undecidable.lean`,
`undecidable_not_modelLe`): `M` halts on `w` iff the inequality *fails* in the language model.

**What remains:** a reduction `HALT ⪯ₘ Provable`, giving `Undecidable Provable` as the repo defines
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

`Theorem6Repair.lean` proves the guarded-term repair for `T Σ̈` with the language model `pl`, the
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
