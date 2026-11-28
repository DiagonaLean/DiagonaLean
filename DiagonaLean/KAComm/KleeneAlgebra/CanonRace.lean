/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.KAComm.KleeneAlgebra.BoolCode
import DiagonaLean.Foundations.Computability.CanonRace

@[expose] public section

/-! # The race on canonical machines, for Kleene algebra with commutativity

The race of `Race.lean`, run on the data of a canonical instance (`dataCanon`) instead of a
`HaltProblem` instance. The tape of the race program on that data (`canonTape`) is primitive
recursive in the instance, and so are the instances built from it, over `ℕ` (`rInst_prim`) and over
`{0, 1}` (`sbI_rInst_prim`), through their codes `rc`. So the reductions from `HaltCanon`,
`canonReduction B C` and `canonReductionB B C`, are proved computable for each choice of the
interpreter constants `B` and the race program `C`, which exist only classically.

Smullyan's argument carries over unchanged (`haltCanon_iff_rel`, `haltCanon_iff_qb`): `race_iff`
takes any data whose halting search is the proposition, and `haltCanon_iff_test` is that for
`dataCanon`.

## Main declarations

* `canonTape`, `canonTape_prim`: the tape of the race program on canonical data.
* `rInst_prim`, `sbI_rInst_prim`: the instances are primitive recursive in the tape.
* `canonReduction`, `canonReductionB`: the reductions from `HaltCanon`, and their `Primrec` lemmas.
* `haltCanon_iff_rel`, `haltCanon_iff_qb`: Smullyan's argument on canonical instances.
-/

namespace DiagonaLean.KAComm.KleeneAlgebra

open Cslib.Turing RExp Nat.Partrec DiagonaLean.Foundations.Computability DiagonaLean.Halt

/-- The tape of the race program `C` on the data of the canonical instance `x`. -/
def canonTape (B : Base) (C : Code) (x : CanonTM × List Bool) : List Bool :=
  tapeOf B (Encodable.encode (C.curry (Encodable.encode (dataCanon x))))

/-- `canonTape B C` is primitive recursive. -/
theorem canonTape_prim (B : Base) (C : Code) : Primrec (canonTape B C) :=
  (tapeOf_prim B).comp (Primrec.encode.comp
    (Code.primrec₂_curry.comp (Primrec.const C) (Primrec.encode.comp dataCanon_prim)))

/-- **Smullyan's argument on canonical instances, for any instance family.** -/
theorem haltCanon_iff_of_family {ka : Bool} {B : Base} {G : List Bool → ℕ × ℕ} {C : Code}
    (hB : B.Good) (hC : RaceOn ka B G C) {Q : List Bool → Prop}
    (hQ : ∀ l, Q l ↔ ∃ k, Checks ka k (G l).1 (G l).2)
    (pos : ∀ l, (NM B.K l).Outputs [] [true] → Q l)
    (neg : ∀ l, (NM B.K l).Outputs [] [false] → ¬ Q l)
    (x : CanonTM × List Bool) : HaltCanon x ↔ Q (canonTape B C x) :=
  race_iff hB hC hQ pos neg (dataCanon x) (haltCanon_iff_test x)

/-- The instance over `ℕ` is primitive recursive in the tape: its codes are `instCode`
(`instCode_eq`), and `rc` is a correct encoding (`primrec_iff_rc`). -/
theorem rInst_prim (K : UConst) : Primrec (rInst K) := by
  have h₁ : Primrec fun l => (rInst K l).1 := primrec_iff_rc.2 <|
    (prim_fst (instCode_prim K)).of_eq fun l => by rw [← instCode_eq]
  have h₂ : Primrec fun l => (rInst K l).2 := primrec_iff_rc.2 <|
    (prim_snd (instCode_prim K)).of_eq fun l => by rw [← instCode_eq]
  exact h₁.pair h₂

/-- The instance over `{0, 1}` is primitive recursive in the tape: each side is the decoding by
`rcbDec` of its code in `instCodeB` (`instCodeB_eq`, `rcbDec_rc`). -/
theorem sbI_rInst_prim (K : UConst) : Primrec fun l => sbI (rInst K l) := by
  have h₁ : Primrec fun l => (rcbDec (instCodeB K l).1).getD RExp.zero :=
    Primrec.option_getD.comp (rcbDec_prim.comp (prim_fst (instCodeB_prim K))) (Primrec.const _)
  have h₂ : Primrec fun l => (rcbDec (instCodeB K l).2).getD RExp.zero :=
    Primrec.option_getD.comp (rcbDec_prim.comp (prim_snd (instCodeB_prim K))) (Primrec.const _)
  exact (h₁.pair h₂).of_eq fun l => by simp only [instCodeB_eq, rcbDec_rc, Option.getD_some]

/-- **The reduction from canonical instances, over `ℕ`.** -/
def canonReduction (B : Base) (C : Code) (x : CanonTM × List Bool) : Inst :=
  rInst B.K (canonTape B C x)

/-- `canonReduction B C` is primitive recursive. -/
theorem canonReduction_prim (B : Base) (C : Code) : Primrec (canonReduction B C) :=
  (rInst_prim B.K).comp (canonTape_prim B C)

/-- **The reduction from canonical instances, over `{0, 1}`.** -/
def canonReductionB (B : Base) (C : Code) (x : CanonTM × List Bool) : InstB :=
  sbI (rInst B.K (canonTape B C x))

/-- `canonReductionB B C` is primitive recursive. -/
theorem canonReductionB_prim (B : Base) (C : Code) : Primrec (canonReductionB B C) :=
  (sbI_rInst_prim B.K).comp (canonTape_prim B C)

/-- **Smullyan's argument on canonical instances, over `ℕ`.** -/
theorem haltCanon_iff_rel {ka : Bool} {B : Base} {C : Code} (hB : B.Good) (hC : RaceProg ka B C)
    (x : CanonTM × List Bool) :
    HaltCanon x ↔ Rel ka (canonReduction B C x).1 (canonReduction B C x).2 :=
  haltCanon_iff_of_family (Q := fun l => Rel ka (rInst B.K l).1 (rInst B.K l).2) hB hC
    (fun l => by
      rw [rel_iff_checks]
      have hi := instCode_eq B.K l
      rw [← hi])
    (fun _ h => rel_pos h) (fun _ h => rel_neg h) x

/-- **Smullyan's argument on canonical instances, over `{0, 1}`.** -/
theorem haltCanon_iff_qb {ka : Bool} {B : Base} {C : Code} (hB : B.Good) (hC : RaceProgB ka B C)
    (x : CanonTM × List Bool) : HaltCanon x ↔ QB ka B.K (canonTape B C x) :=
  haltCanon_iff_of_family (Q := QB ka B.K) hB hC
    (fun l => by
      rw [QB, rel_iff_checks, instCodeB_eq])
    (fun _ h => qb_pos h) (fun _ h => qb_neg h) x

end DiagonaLean.KAComm.KleeneAlgebra
