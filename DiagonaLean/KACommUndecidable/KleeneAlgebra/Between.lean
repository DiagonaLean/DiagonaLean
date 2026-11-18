/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.OutputSearch
import DiagonaLean.KACommUndecidable.KleeneAlgebra.Race
import DiagonaLean.KACommUndecidable.KleeneAlgebra.Separation

@[expose] public section

/-! # Theorem 18 for every theory between pre-Kleene algebra and the language model

No Turing machine decides any predicate `S` on pairs of expressions that contains provability in
pre-Kleene algebra and is contained in the language model: for inequalities
(`not_machineDecidable_between`) and for equations (`not_machineDecidable_eq_between`). `S` need not
be recursively enumerable, so the race program of Theorem 19 does not apply.

The argument separates the computably inseparable pair `SelfOut true`, `SelfOut false`
(`Halt/Inseparable.lean`), as the paper does with its map `η`. Instead of compiling the paper's
instance of a machine `M`, it uses the instance of the interpreter running a program that simulates
`M` on its own code and returns the bit `M` outputs (`readOut`). The code of that instance is a
primitive recursive function of the code of `M` (`instCode_prim`), so a machine computes the
reduction (`exists_computes`), with no hypothesis.

For equality on any `X` through which the language map factors (`LangFactor`), no machine decides
`EqVia F` (`not_machineDecidable_eqVia`), and no machine decides equality on `X` itself given a
machine that computes `l'` on the codes of expressions (`not_machineDecidable_eqOn`), which is the
paper's hypothesis that `l'` is computable.

Each statement over `encNat` has an `_of_conv` version for an arbitrary encoding `enc`, given a
machine that converts `encNat i` into `enc i` (`not_machineDecidable_of_conv`). Some condition of
this kind is needed: an injective encoding that records whether `S i` holds in its first bit makes
`S` decidable. `encNat` is the reference encoding the proofs use, not part of the result.

The `_bool` statements give the same results over the paper's alphabet `{0, 1}` under `encBool`,
through the substitution `sbB` that writes the letter `n` as the word `1ⁿ0`.

## References

* [A. Azevedo de Amorim, C. Zhang, M. Gaboardi][AmorimZhangGaboardi2024], Theorem 18
-/

open scoped Computability

namespace DiagonaLean.KACommUndecidable.KleeneAlgebra

open Cslib.Turing SingleTapeTM Enc RExp FreePreKA TD Nat.Partrec
  DiagonaLean.Foundations.Computability DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Halt.Undecidable DiagonaLean.Halt.Inseparable DiagonaLean.Synthetic.Definitions

variable {X : Type*}

-- the instance codes are `Nat.pair`s of literals; unfolding them makes elaboration time out
attribute [local irreducible] Nat.pair

/-- A program that, on `⟨d, m⟩`, returns the output bit of the run with numeric data `d`. -/
theorem exists_outProg :
    ∃ C : Code, C.eval = fun n => readOut (Denumerable.ofNat HD n.unpair.1) := by
  have h : Partrec fun n : ℕ => readOut (Denumerable.ofNat HD n.unpair.1) :=
    readOut_part.comp ((Primrec.ofNat HD).comp (Primrec.fst.comp Primrec.unpair)).to_comp
  exact Code.exists_code.1 (Partrec.nat_iff.1 h)

/-- **No machine decides a predicate with a suitable family of interpreter instances.** For each
constant `K`, `G K` is a primitive recursive family of codes, and `inst K l` an instance with those
codes under `enc`. If the predicate holds when `NM K l` outputs `1` and fails when it outputs `0`,
no machine decides it. Unlike `not_machineDecidable_of_family`, the predicate need not be
recursively enumerable. -/
theorem not_machineDecidable_of_interp {Y : Type*} {enc : Y → List Bool} {P : Y → Prop}
    (G : UConst → List Bool → ℕ × ℕ) (hG : ∀ K, Primrec (G K)) (inst : UConst → List Bool → Y)
    (henc : ∀ K l, enc (inst K l) = bitsPair (G K l).1 (G K l).2)
    (pos : ∀ K l, (NM K l).Outputs [] [true] → P (inst K l))
    (neg : ∀ K l, (NM K l).Outputs [] [false] → ¬ P (inst K l)) :
    ¬ MachineDecidable enc P := by
  obtain ⟨B, hB⟩ := exists_base
  obtain ⟨C, hC⟩ := exists_outProg
  -- the tape of the program that reads the output bit of the machine with code `w` on `w`
  let tape : List Bool → List Bool := fun w =>
    tapeOf B (Encodable.encode (C.curry (Encodable.encode (dataC w))))
  have htape : Primrec tape := (tapeOf_prim B).comp (Primrec.encode.comp
    (Code.primrec₂_curry.comp (Primrec.const C) (Primrec.encode.comp dataC_prim)))
  have hF : Primrec fun w => bitsPair (G B.K (tape w)).1 (G B.K (tape w)).2 := by
    have h := (hG B.K).comp htape
    exact bitsOf_prim.comp (prim_natPair (prim_fst h) (prim_snd h))
  have hout : ∀ {b : Bool} {M : EncodableTM Bool}, SelfOut b M →
      (NM B.K (tape (encodeBoolTM M))).Outputs [] [b] := by
    intro b M h
    have heval : (C.curry (Encodable.encode (dataC (encodeBoolTM M)))).eval 0 =
        readOut (dataC (encodeBoolTM M)) := by
      simp only [Code.eval_curry, hC, Nat.unpair_pair, Denumerable.ofNat_encode]
    have hm := hB _ _ (heval ▸ selfOut_mem h)
    cases b <;> simpa using hm
  obtain ⟨R, hR⟩ := exists_computes (enc₁ := encodeBoolTM) (enc₂ := enc)
    (f := fun M => inst B.K (tape (encodeBoolTM M))) _ hF.to_comp fun M => (henc _ _).symm
  exact not_machineDecidable_of_separation (fun _ h => pos _ _ (hout h))
    (fun _ h => neg _ _ (hout h)) hR

/-- The codes of the inequality `redA K l ≤ redB K l` are primitive recursive in `l`. -/
theorem instAB_prim (K : UConst) : Primrec fun l : List Bool => (instA K l, instB K l) := by
  fun_prop

/-- **Theorem 18 for inequalities.** No machine decides any predicate on pairs of expressions that
contains provable inequality in pre-Kleene algebra and is contained in inclusion of languages. -/
theorem not_machineDecidable_between (S : Inst → Prop) (h₁ : ∀ i, Provable i → S i)
    (h₂ : ∀ i, S i → ModelLe i) : ¬ MachineDecidable encNat S :=
  not_machineDecidable_of_interp (fun K l => (instA K l, instB K l)) instAB_prim
    (fun K l => (redA K l, redB K l)) (fun K l => by simp only [encNat, rc_redA, rc_redB])
    (fun _ _ h => h₁ _ ((provable_iff_equiv _).2 (rInst_pos h)))
    (fun _ _ h hS => not_modelLe h (h₂ _ hS))

/-- **Theorem 18 for inequalities, under any encoding** that a machine computes from `encNat`. -/
theorem not_machineDecidable_between_of_conv (S : Inst → Prop) (h₁ : ∀ i, Provable i → S i)
    (h₂ : ∀ i, S i → ModelLe i) {enc : Inst → List Bool} {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encNat enc id) : ¬ MachineDecidable enc S :=
  not_machineDecidable_of_conv (not_machineDecidable_between S h₁ h₂) hR

/-- **Theorem 18 for equations.** No machine decides any predicate on pairs of expressions that
contains provable equality in pre-Kleene algebra and is contained in equality of languages. -/
theorem not_machineDecidable_eq_between (S : Inst → Prop) (h₁ : ∀ i, Equiv DComm i.1 i.2 → S i)
    (h₂ : ∀ i, S i → pl (mk i.1 : TD ℕ) = pl (mk i.2)) : ¬ MachineDecidable encNat S :=
  not_machineDecidable_of_interp instCode instCode_prim rInst enc_nat
    (fun _ _ h => h₁ _ (rInst_pos h))
    (fun K l h hS => not_modelLe h (by
      have hl := h₂ _ hS
      rwa [show (rInst K l).1 = plus (redA K l) (redB K l) from rfl,
        show (rInst K l).2 = redB K l from rfl, mk_plus, pl_add, add_eq_right_iff_le] at hl))

/-- **Theorem 18 for equations, under any encoding** that a machine computes from `encNat`. -/
theorem not_machineDecidable_eq_between_of_conv (S : Inst → Prop)
    (h₁ : ∀ i, Equiv DComm i.1 i.2 → S i) (h₂ : ∀ i, S i → pl (mk i.1 : TD ℕ) = pl (mk i.2))
    {enc : Inst → List Bool} {R : SingleTapeTM Bool} (hR : ComputesReduction R encNat enc id) :
    ¬ MachineDecidable enc S :=
  not_machineDecidable_of_conv (not_machineDecidable_eq_between S h₁ h₂) hR

/-- **Theorem 18 on syntax.** For any `X` through which the language map factors, no machine
decides whether two expressions denote the same element of `X`. -/
theorem not_machineDecidable_eqVia (F : LangFactor X) : ¬ MachineDecidable encNat (EqVia F) :=
  not_machineDecidable_eq_between _ (fun _ h => congrArg F.l' (mk_eq_mk.2 h))
    (fun _ h => by simpa only [F.fac] using congrArg F.g h)

/-- **Theorem 18 on syntax, under any encoding** that a machine computes from `encNat`. -/
theorem not_machineDecidable_eqVia_of_conv (F : LangFactor X) {enc : Inst → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encNat enc id) :
    ¬ MachineDecidable enc (EqVia F) :=
  not_machineDecidable_of_conv (not_machineDecidable_eqVia F) hR

/-! ### Over `{0, 1}`

The same statements over the paper's alphabet `Σ = {0, 1}`, under `encBool`. The instances are the
images under `sbB`, which writes the letter `n` as the word `1ⁿ0`; this substitution preserves
provability (`Equiv.sb`) and reflects language inclusion (`pl_le_of_sb`). -/

/-- An instance over `{0, 1}` whose inequality fails in the language model maps back to one over
`ℕ`: `sbB` reflects inclusion. -/
theorem modelLe_of_sbB {e f : RExp (ℕ ⊕ ℕ)}
    (h : pl (mk (sbB e) : TD Bool) ≤ pl (mk (sbB f))) : ModelLe (e, f) :=
  pl_le_of_sb cd_injective h

/-- **Theorem 18 for inequalities over `{0, 1}`.** No machine decides any predicate on pairs of
expressions over `{0, 1}` that contains provable inequality in pre-Kleene algebra and is contained
in inclusion of languages. -/
theorem not_machineDecidable_between_bool (S : InstB → Prop)
    (h₁ : ∀ i : InstB, (mk i.1 : TD Bool) ≤ mk i.2 → S i)
    (h₂ : ∀ i : InstB, S i → pl (mk i.1 : TD Bool) ≤ pl (mk i.2)) :
    ¬ MachineDecidable encBool S :=
  not_machineDecidable_of_interp (fun K l => (subC (instA K l), subC (instB K l)))
    (fun _ => by fun_prop) (fun K l => (sbB (redA K l), sbB (redB K l)))
    (fun K l => by rw [← rc_redA, ← rc_redB, subC_rc, subC_rc, encBool])
    (fun _ _ h => h₁ _ (mk_le_mk.2 (Equiv.sb wordOf
      ((provable_iff_equiv (redA _ _, redB _ _)).1 ((provable_iff_equiv _).2 (rInst_pos h))))))
    (fun _ _ h hS => not_modelLe h (modelLe_of_sbB (h₂ _ hS)))

/-- **Theorem 18 for inequalities over `{0, 1}`, under any encoding** that a machine computes from
`encBool`. -/
theorem not_machineDecidable_between_bool_of_conv (S : InstB → Prop)
    (h₁ : ∀ i : InstB, (mk i.1 : TD Bool) ≤ mk i.2 → S i)
    (h₂ : ∀ i : InstB, S i → pl (mk i.1 : TD Bool) ≤ pl (mk i.2)) {enc : InstB → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encBool enc id) :
    ¬ MachineDecidable enc S :=
  not_machineDecidable_of_conv (not_machineDecidable_between_bool S h₁ h₂) hR

/-- **Theorem 18 for equations over `{0, 1}`.** No machine decides any predicate on pairs of
expressions over `{0, 1}` that contains provable equality in pre-Kleene algebra and is contained in
equality of languages. -/
theorem not_machineDecidable_eq_between_bool (S : InstB → Prop)
    (h₁ : ∀ i : InstB, Equiv DComm i.1 i.2 → S i)
    (h₂ : ∀ i : InstB, S i → pl (mk i.1 : TD Bool) = pl (mk i.2)) :
    ¬ MachineDecidable encBool S :=
  not_machineDecidable_of_interp instCodeB instCodeB_prim (fun K l => sbI (rInst K l)) enc_bool
    (fun _ _ h => h₁ _ (pos_bool h))
    (fun K l h hS => not_modelLe h (modelLe_of_sbB (by
      have hl := h₂ _ hS
      rwa [show (sbI (rInst K l)).1 = plus (sbB (redA K l)) (sbB (redB K l)) from rfl,
        show (sbI (rInst K l)).2 = sbB (redB K l) from rfl, mk_plus, pl_add,
        add_eq_right_iff_le] at hl)))

/-- **Theorem 18 for equations over `{0, 1}`, under any encoding** that a machine computes from
`encBool`. -/
theorem not_machineDecidable_eq_between_bool_of_conv (S : InstB → Prop)
    (h₁ : ∀ i : InstB, Equiv DComm i.1 i.2 → S i)
    (h₂ : ∀ i : InstB, S i → pl (mk i.1 : TD Bool) = pl (mk i.2)) {enc : InstB → List Bool}
    {R : SingleTapeTM Bool} (hR : ComputesReduction R encBool enc id) :
    ¬ MachineDecidable enc S :=
  not_machineDecidable_of_conv (not_machineDecidable_eq_between_bool S h₁ h₂) hR

/-- **Theorem 18.** If a machine computes `l'` on the codes of expressions, no machine decides
equality on `X`, under any encoding of `X × X`. -/
theorem not_machineDecidable_eqOn (F : LangFactor X) {enc : X × X → List Bool}
    {R : SingleTapeTM Bool}
    (hR : ComputesReduction R encNat enc fun i => (F.l' (mk i.1), F.l' (mk i.2))) :
    ¬ MachineDecidable enc (EqOn X) := fun hd =>
  not_machineDecidable_eqVia F (machineDecidable_of_computes_reduction hR (fun _ => Iff.rfl) hd)

end DiagonaLean.KACommUndecidable.KleeneAlgebra
