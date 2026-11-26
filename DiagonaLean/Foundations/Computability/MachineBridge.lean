/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.OutputSearch
import DiagonaLean.Foundations.Computability.Computer
import Mathlib.Computability.RE
import Mathlib.Computability.Reduce

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
* `not_computablePred_of_reduces`: `¬ ComputablePred` transfers along a reduction with a computable
  function; `REPred.of_reduces`, `REPred.of_manyOneReducible`: recursive enumerability transfers
  back along one.
* `not_computablePred_of_selfHalt`: a predicate that a computable map of machine codes reduces
  self-halting to is not computable.
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

/-- **From synthetic to Mathlib's reductions.** A reduction `r : p ⪯_s q` (data) whose function is
computable gives Mathlib's `ManyOneReducible p q`. Unlike a bare `⪯_s`, which exists classically for
almost any `p` and `q`, `ManyOneReducible` asks for a computable function, so the proposition has
content and may be stated as a conclusion. -/
theorem _root_.DiagonaLean.Synthetic.Definitions.SynthReduction.toManyOneReducible
    {X Y : Type*} [Primcodable X] [Primcodable Y] {p : X → Prop} {q : Y → Prop} (r : p ⪯_s q)
    (hr : Computable r.f) : ManyOneReducible p q :=
  ⟨r.f, hr, r.hf⟩

/-- The former name of `SynthReduction.toManyOneReducible`. Its parameter is typed with the former
name `ManyOneReduces`, so that field notation finds it on terms whose type uses that name. -/
@[deprecated SynthReduction.toManyOneReducible (since := "2026-11-22")]
theorem _root_.DiagonaLean.Synthetic.Definitions.ManyOneReduces.toManyOneReducible
    {X Y : Type*} [Primcodable X] [Primcodable Y] {p : X → Prop} {q : Y → Prop}
    (r : DiagonaLean.Synthetic.Definitions.ManyOneReduces p q)
    (hr : Computable r.f) : ManyOneReducible p q :=
  DiagonaLean.Synthetic.Definitions.SynthReduction.toManyOneReducible r hr

/-- **Not being a computable predicate transfers along a computable reduction.** If `p` is not a
computable predicate and `r : p ⪯_s q` has a computable function, then `q` is not one either. -/
theorem not_computablePred_of_reduces {X Y : Type*} [Primcodable X] [Primcodable Y]
    {p : X → Prop} {q : Y → Prop} (r : p ⪯_s q) (hr : Computable r.f) (hp : ¬ ComputablePred p) :
    ¬ ComputablePred q :=
  fun hq => hp (ComputablePred.computable_of_manyOneReducible (r.toManyOneReducible hr) hq)

/-- Recursive enumerability transfers back along a reduction (`⪯_s`) with a computable function. -/
theorem _root_.REPred.of_reduces {X Y : Type*} [Primcodable X] [Primcodable Y] {p : X → Prop}
    {q : Y → Prop} (r : p ⪯_s q) (hr : Computable r.f) (hq : REPred q) : REPred p :=
  REPred.of_eq (hq.comp hr) fun x => (r.hf x).symm

/-- Recursive enumerability transfers back along a computable many-one reduction. -/
theorem _root_.REPred.of_manyOneReducible {X Y : Type*} [Primcodable X] [Primcodable Y]
    {p : X → Prop} {q : Y → Prop} (h : ManyOneReducible p q) (hq : REPred q) : REPred p := by
  obtain ⟨f, hf, hpq⟩ := h
  exact REPred.of_reduces (q := q) ⟨f, hpq⟩ hf hq

/-! ### From self-halting on codes -/

/-- **A predicate that a computable map of codes reduces self-halting to is not computable.**
If `code` is computable and a machine halts on its own code `encodeBoolTM M` iff
`P (code (encodeBoolTM M))`, then a computable decision procedure for `P`, composed with `code`,
would give a machine deciding self-halting (`machineDecidable_of_computablePred` on bit strings),
which `self_halt_undecidable` rules out. This is the last step of every machine-level result that
reads its instance off a machine code. -/
theorem not_computablePred_of_selfHalt {X : Type*} [Primcodable X] {P : X → Prop}
    {code : List Bool → X} (hcode : Computable code)
    (hspec : ∀ M : EncodableTM Bool,
      Halts M.toSingleTapeTM (encodeBoolTM M) ↔ P (code (encodeBoolTM M))) :
    ¬ ComputablePred P := by
  intro h
  have h' : ComputablePred fun w => P (code w) :=
    ComputablePred.computable_of_manyOneReducible (ManyOneReducible.mk P hcode) h
  obtain ⟨D, hD⟩ := machineDecidable_of_computablePred (enc := id) (dec := some)
    Computable.option_some (fun _ => rfl) h'
  refine Halt.Undecidable.self_halt_undecidable ⟨D, fun M => ?_⟩
  simpa only [id, ← hspec] using hD (encodeBoolTM M)

/-! ### A canonical encoding -/

/-- The unary encoding of a `Primcodable` value: `encode x` copies of `false`. -/
def encUnary {X : Type*} [Primcodable X] (x : X) : List Bool :=
  (List.range (Encodable.encode x)).map fun _ => false

/-- The decoder of `encUnary`. -/
def decUnary {X : Type*} [Primcodable X] (l : List Bool) : Option X :=
  Encodable.decode l.length

/-- `encUnary` is primitive recursive. -/
theorem encUnary_prim {X : Type*} [Primcodable X] : Primrec (encUnary : X → List Bool) :=
  Primrec.list_map (Primrec.list_range.comp Primrec.encode) (Primrec.const false).to₂

/-- `decUnary` is primitive recursive. -/
theorem decUnary_prim {X : Type*} [Primcodable X] : Primrec (decUnary : List Bool → Option X) :=
  Primrec.decode.comp Primrec.list_length

/-- `decUnary` inverts `encUnary`. -/
@[simp] theorem decUnary_encUnary {X : Type*} [Primcodable X] (x : X) :
    decUnary (encUnary x) = some x := by
  simp [decUnary, encUnary]

/-- Under the unary encoding, `MachineDecidable` is `ComputablePred`. -/
theorem machineDecidable_unary_iff {X : Type*} [Primcodable X] {P : X → Prop} :
    MachineDecidable encUnary P ↔ ComputablePred P :=
  machineDecidable_iff encUnary_prim.to_comp decUnary_prim.to_comp decUnary_encUnary

/-! ### Binary encodings of pairs of codes

Several problems are encoded as the binary digits of the pair of the codes of two terms
(`bitsPair (c a) (c b)`: `encSKI`, `encBeta`, KAComm's `encNat`), and their machine-level results
are proved for that encoding. With a primitive recursive decoder of the code, the encoding has a
computable decoder, so those results give `¬ ComputablePred`, and with it `¬ MachineDecidable`
under every computable encoding. -/

/-- The number whose binary digits, least significant first, are `l`: the inverse of `bitsOf`. -/
def valBits (l : List Bool) : ℕ := l.foldr (fun b acc => 2 * acc + b.toNat) 0

theorem valBits_eq_valG (l : List Bool) : valBits l = valG (l.map bitG) := by
  induction l with
  | nil => rfl
  | cons b t ih => cases b <;> simp [valBits, valG, bitG] at ih ⊢ <;> omega

/-- **`valBits` inverts `bitsOf`.** -/
theorem valBits_bitsOf (n : ℕ) : valBits (bitsOf n) = n := by
  rw [valBits_eq_valG, bitsOf_map, valG_trNat]

@[fun_prop] theorem valBits_prim : Primrec valBits := by
  unfold valBits
  fun_prop

/-- The decoder of `bitsPair (c a) (c b)`, from a decoder `d` of the code `c`. -/
def unbitsPair {T : Type*} (d : ℕ → Option T) (l : List Bool) : Option (T × T) :=
  (d (valBits l).unpair.1).bind fun a => (d (valBits l).unpair.2).map fun b => (a, b)

theorem unbitsPair_bitsPair {T : Type*} {c : T → ℕ} {d : ℕ → Option T}
    (hd : ∀ t, d (c t) = some t) (a b : T) : unbitsPair d (bitsPair (c a) (c b)) = some (a, b) := by
  simp [unbitsPair, bitsPair, valBits_bitsOf, hd]

theorem unbitsPair_prim {T : Type*} [Primcodable T] {d : ℕ → Option T} (hd : Primrec d) :
    Primrec (unbitsPair d) := by
  unfold unbitsPair
  fun_prop

/-- **From one binary encoding of pairs to every computable encoding.** If no machine decides `P`
under the encoding of a pair of terms as the binary digits of the pair of their codes, and the
code has a primitive recursive decoder, then `P` is not a computable predicate. -/
theorem not_computablePred_of_bitsPair {T : Type*} [Primcodable T] {c : T → ℕ}
    {d : ℕ → Option T} (hc : Primrec c) (hd : Primrec d) (hdc : ∀ t, d (c t) = some t)
    {P : T × T → Prop} (h : ¬ MachineDecidable (fun i => bitsPair (c i.1) (c i.2)) P) :
    ¬ ComputablePred P := fun hP =>
  h ((machineDecidable_iff (prim_bitsPair (hc.comp Primrec.fst) (hc.comp Primrec.snd)).to_comp
    (unbitsPair_prim hd).to_comp (fun i => unbitsPair_bitsPair hdc i.1 i.2)).2 hP)

end DiagonaLean.Foundations.Computability
