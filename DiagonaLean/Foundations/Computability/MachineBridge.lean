/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.OutputSearch
import DiagonaLean.Foundations.Computability.Computer
import Mathlib.Computability.RE

@[expose] public section

/-! # Machine decidability is Mathlib's `ComputablePred`

`MachineDecidable enc P` asks for a `SingleTapeTM Bool` that decides `P` on the bit strings
`enc x`. Mathlib's `ComputablePred P` asks for a computable indicator function. For an encoding
that is computable and has a computable decoder, the two agree (`machineDecidable_iff`).

* **Machine to function.** A decider's answer on `enc x` is `readOut` of the data of the run
  (`OutputSearch.lean`): a search for the first halting step of the primitive recursive simulator
  of `HaltSearch.lean`, followed by reading the head symbol. That is partial recursive in `x`, and
  total because the decider always halts. This direction needs only that
  `enc` is computable (`computablePred_of_machineDecidable`).
* **Function to machine.** Decode, decide, and write the answer; `exists_computer` turns that
  computable function on bit strings into a machine (`machineDecidable_of_computablePred`).

So every `¬ ComputablePred` result of Mathlib, such as `ComputablePred.rice` or
`ComputablePred.halting_problem`, gives a `¬ MachineDecidable` result
(`not_machineDecidable_of_not_computablePred`).

## Main statements

* `computablePred_of_machineDecidable`, `machineDecidable_of_computablePred`.
* `machineDecidable_iff`: the equivalence.
* `not_machineDecidable_of_not_computablePred`: the form used for undecidability.
* `encUnary`, `machineDecidable_unary_iff`: an encoding of any `Primcodable` type that satisfies
  the hypotheses.
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions

/-! ### The data of a machine on an input -/

section

variable {M : EncodableTM Bool}

attribute [local instance] EncodableTM.stateEncodable

/-- The numeric start configuration, in closed form. -/
theorem absD_initData (w : List Bool) :
    absD (initData w : Data M.toSingleTapeTM) =
      (qc (some M.q₀), [], (w.head?.map fun b => b.toNat + 1).getD 0,
        w.tail.map fun b => b.toNat + 1) := by
  have hb : ∀ b : Bool, hc (some b) = b.toNat + 1 := by decide
  cases w with
  | nil => rfl
  | cons a t =>
    simp only [absD, initData, List.map_map, List.head?_cons, Option.map_some, Option.getD_some,
      List.tail_cons, List.map_nil, hb]
    rw [show (hc ∘ some) = fun b : Bool => b.toNat + 1 from funext hb]

variable (M) in
/-- For a fixed machine, the data of a run is primitive recursive in the input. -/
theorem dataOf_prim : Primrec fun w : List Bool => dataOf (M, w) := by
  have h : (fun w : List Bool => dataOf (M, w)) = fun w =>
      (rowsE M, (qc (some M.q₀), ([] : List ℕ), (w.head?.map fun b => b.toNat + 1).getD 0,
        w.tail.map fun b => b.toNat + 1)) := by
    funext w
    simp only [dataOf, absD_initData]
  rw [h]
  have hb : Primrec fun b : Bool => b.toNat + 1 :=
    Primrec.succ.comp (Primrec.dom_bool _)
  exact (Primrec.const _).pair ((Primrec.const _).pair ((Primrec.const _).pair
    ((Primrec.option_getD.comp (Primrec.option_map Primrec.list_head?
      (hb.comp Primrec.snd).to₂) (Primrec.const 0)).pair
    (Primrec.list_map Primrec.list_tail (hb.comp Primrec.snd).to₂))))

end

/-! ### Machine to function -/

/-- A Cslib machine, with some encoding of its finitely many states. -/
noncomputable def toEncodableTM (D : SingleTapeTM Bool) : EncodableTM Bool :=
  { toSingleTapeTM := D
    stateEncodable := by
      classical
      let := D.stateFintype
      exact (Fintype.truncEncodable D.State).out }

/-- **A machine decider gives a computable predicate.** The decider's answer on `enc x` is
`readOut` of the data of the run, which is partial recursive (`readOut_part`) and correct
(`mem_readOut`). Only the encoding needs to be computable. -/
theorem computablePred_of_machineDecidable {X : Type*} [Primcodable X] {enc : X → List Bool}
    (henc : Computable enc) {P : X → Prop} (h : MachineDecidable enc P) : ComputablePred P := by
  classical
  obtain ⟨D, hD⟩ := h
  have hr : Partrec fun x => readOut (dataOf (toEncodableTM D, enc x)) :=
    readOut_part.comp ((dataOf_prim _).to_comp.comp henc)
  have hbit : Computable fun x => if P x then 1 else 0 :=
    Partrec.of_eq_tot hr fun x => by
      by_cases hx : P x
      · simpa [hx] using mem_readOut (M := toEncodableTM D) ((hD x).1 hx)
      · simpa [hx] using mem_readOut (M := toEncodableTM D) ((hD x).2 hx)
  refine ⟨inferInstance, ?_⟩
  refine (Primrec.beq.to_comp.comp hbit (Computable.const 1)).of_eq fun x => ?_
  by_cases hx : P x <;> simp [hx]

/-! ### Function to machine -/

/-- **A computable predicate is machine-decidable** under an encoding with a computable
decoder. -/
theorem machineDecidable_of_computablePred {X : Type*} [Primcodable X] {enc : X → List Bool}
    {dec : List Bool → Option X} (hdec : Computable dec) (hde : ∀ x, dec (enc x) = some x)
    {P : X → Prop} (h : ComputablePred P) : MachineDecidable enc P := by
  obtain ⟨_, hP⟩ := h
  obtain ⟨R, hR⟩ := exists_computer (fun l => ((dec l).map fun x => [decide (P x)]).getD [])
    (Computable.option_getD (Computable.option_map hdec
      ((Computable.list_cons.comp hP (Computable.const []) |>.comp Computable.snd).to₂))
      (Computable.const []))
  refine ⟨R, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · simpa [hde, hx] using hR (enc x)
  · simpa [hde, hx] using hR (enc x)

/-! ### The equivalence -/

/-- **`MachineDecidable` is `ComputablePred`**, for a computable encoding with a computable
decoder. -/
theorem machineDecidable_iff {X : Type*} [Primcodable X] {enc : X → List Bool}
    {dec : List Bool → Option X} (henc : Computable enc) (hdec : Computable dec)
    (hde : ∀ x, dec (enc x) = some x) {P : X → Prop} :
    MachineDecidable enc P ↔ ComputablePred P :=
  ⟨computablePred_of_machineDecidable henc, machineDecidable_of_computablePred hdec hde⟩

/-- **Undecidability transfers from Mathlib.** If `P` is not a computable predicate, no machine
decides it under any computable encoding. -/
theorem not_machineDecidable_of_not_computablePred {X : Type*} [Primcodable X]
    {enc : X → List Bool} (henc : Computable enc) {P : X → Prop} (h : ¬ ComputablePred P) :
    ¬ MachineDecidable enc P :=
  fun hm => h (computablePred_of_machineDecidable henc hm)

/-! ### A canonical encoding -/

/-- The unary encoding of a `Primcodable` value: `encode x` copies of `false`. -/
def encUnary {X : Type*} [Primcodable X] (x : X) : List Bool :=
  (List.range (Encodable.encode x)).map fun _ => false

/-- The decoder of `encUnary`. -/
def decUnary {X : Type*} [Primcodable X] (l : List Bool) : Option X :=
  Encodable.decode l.length

theorem encUnary_prim {X : Type*} [Primcodable X] : Primrec (encUnary : X → List Bool) :=
  Primrec.list_map (Primrec.list_range.comp Primrec.encode) (Primrec.const false).to₂

theorem decUnary_prim {X : Type*} [Primcodable X] : Primrec (decUnary : List Bool → Option X) :=
  Primrec.decode.comp Primrec.list_length

@[simp] theorem decUnary_encUnary {X : Type*} [Primcodable X] (x : X) :
    decUnary (encUnary x) = some x := by
  simp [decUnary, encUnary]

/-- Under the unary encoding, `MachineDecidable` is `ComputablePred`. -/
theorem machineDecidable_unary_iff {X : Type*} [Primcodable X] {P : X → Prop} :
    MachineDecidable encUnary P ↔ ComputablePred P :=
  machineDecidable_iff encUnary_prim.to_comp decUnary_prim.to_comp decUnary_encUnary

end DiagonaLean.Foundations.Computability
