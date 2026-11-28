/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.Foundations.Computability.HaltCanon
import DiagonaLean.Foundations.Computability.ProofRace

@[expose] public section

/-! # The proof race on canonical machines

`ProofRace.halt_iff` gives Smullyan's argument for `HaltProblem`, whose instances bundle a type of
states and cannot be numbered computably. On canonical machines (`HaltCanon`) the same argument
gives reductions that are computable: the data of an instance in the simulator's format,
`dataCanon x`, is primitive recursive in `x` (`dataCanon_prim`), and the halting search on it
succeeds exactly when the machine halts (`haltCanon_iff_test`), since the simulator reads a table
only through `lookup` and `c.table` looks up like the table of `c.toTM`.

So a race program `C` for an instance family `G` gives `HaltCanon x ↔ Q (encode (dataCanon x))`
(`ProofRace.haltCanon_iff`): a proved halting reduction once `x ↦ encode (dataCanon x)` is composed
with a computable map to instances. The race programs are only known to exist (the recursion
theorem), so the reductions take them as arguments, and halting-hardness, a proposition, obtains
them inside its proof.

## Main declarations

* `dataCanon`, `dataCanon_prim`: the data of a canonical instance.
* `haltCanon_iff_test`: `HaltCanon` is the halting search on that data.
* `ProofRace.haltCanon_iff`: Smullyan's argument on canonical instances.
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing Nat.Partrec DiagonaLean.Halt DiagonaLean.Halt.Encoding

/-- The data of a canonical instance in the simulator's format: the table of the machine, and the
initial configuration on the input, with the start state's code `start + 1` and the symbol codes
`b.toNat + 1` of the input, as `absD (initData w)` has them (`absD_initData`). -/
def dataCanon (x : CanonTM × List Bool) : List (ℕ × ℕ) × SC :=
  (x.1.table, (x.1.start + 1, [], (x.2.head?.map fun b => b.toNat + 1).getD 0,
    x.2.tail.map fun b => b.toNat + 1))

/-- **`HaltCanon` is the halting search on `dataCanon`.** -/
theorem haltCanon_iff_test (x : CanonTM × List Bool) :
    HaltCanon x ↔ ∃ k, Test (dataCanon x) k := by
  have hs : sstep (rowsE x.1.toTM) = sstep x.1.table := by
    funext s; simp only [sstep, CanonTM.lookup_rowsE_toTM, CanonTM.lookup_table]
  have h := halt_iff_test (x.1.toTM, x.2)
  simp only [dataOf, Test, absD_initData, hs] at h
  exact h

/-- `dataCanon` is primitive recursive. -/
theorem dataCanon_prim : Primrec dataCanon := by
  unfold dataCanon; fun_prop

/-- **Smullyan's argument, on canonical instances.** Under the hypotheses of
`ProofRace.race_iff`, a canonical instance `x` halts iff `Q` holds of the code of `dataCanon x`. -/
theorem ProofRace.haltCanon_iff {chk : ℕ → ℕ × ℕ → Bool} {G : Code → ℕ → ℕ × ℕ} {C : Code}
    (hC : ProofRace.RaceOn chk G C) {Q : ℕ → Prop} (hQ : ∀ n, Q n ↔ ∃ k, chk k (G C n) = true)
    (pos : ∀ n, 1 ∈ C.eval n → Q n) (neg : ∀ n, 0 ∈ C.eval n → ¬ Q n)
    (x : CanonTM × List Bool) : HaltCanon x ↔ Q (Encodable.encode (dataCanon x)) :=
  ProofRace.race_iff hC hQ pos neg (dataCanon x) (haltCanon_iff_test x)

end DiagonaLean.Foundations.Computability
