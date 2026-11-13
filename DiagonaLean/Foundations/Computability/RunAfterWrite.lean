/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.PartrecToCslib
import DiagonaLean.Foundations.Computability.Prim

@[expose] public section

/-! # The race machine as an explicit, untagged function of its input tape

`NM K l` is a Cslib machine that, started on the empty tape, writes `l`, returns to its first cell,
and then runs a constant machine `W`. The transition table of `W` is the finite constant
`K : UConst`, obtained classically once (`exists_uconst`). The rest of the machine depends on `l`
through the plain arithmetic of `rowFn`.

`NM` is not tagged `noncomputable`, so it is usable in a reduction under the convention on
`ManyOneReduces`: the only classical choice is the finite constant `K`. `rowFn` is primitive
recursive in `l` (`prim_rowFn`).

## Main statements

* `rowFn`: the transition table, as arithmetic on row codes.
* `NM`: the machine.
* `exists_uconst`: any machine `W` has a constant `K` with `W.Outputs l [b] → (NM K l).Outputs [] [b]`.
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing Turing

/-! ### Row codes -/

/-- Decode a symbol. -/
def optOf : ℕ → Option Bool
  | 0 => none
  | 1 => some false
  | _ => some true

/-- Encode a symbol. -/
def hc : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

@[simp] theorem optOf_hc (o : Option Bool) : optOf (hc o) = o := by
  rcases o with _ | _ | _ <;> rfl

theorem hc_lt (o : Option Bool) : hc o < 3 := by
  rcases o with _ | _ | _ <;> decide

/-- Decode a movement. -/
def mvOf : ℕ → Option Dir
  | 0 => none
  | 1 => some .left
  | _ => some .right

/-- Encode a movement. -/
def mvc : Option Dir → ℕ
  | none => 0
  | some .left => 1
  | some .right => 2

@[simp] theorem mvOf_mvc (o : Option Dir) : mvOf (mvc o) = o := by
  rcases o with _ | _ | _ <;> rfl

/-- The next state from its code: `0` halts, and `j + 1` goes to state `j`. -/
def nxOf (N : ℕ) : ℕ → Option (Fin (N + 1))
  | 0 => none
  | j + 1 => some (Fin.ofNat (N + 1) j)

/-- A row: symbol, movement, next state. -/
def mkRow (a m x : ℕ) : ℕ := Nat.pair a (Nat.pair m x)

/-- The symbol of a row. -/
def rowA (r : ℕ) : ℕ := r.unpair.1
/-- The movement of a row. -/
def rowM (r : ℕ) : ℕ := r.unpair.2.unpair.1
/-- The next-state code of a row. -/
def rowX (r : ℕ) : ℕ := r.unpair.2.unpair.2

@[simp] theorem rowA_mkRow (a m x : ℕ) : rowA (mkRow a m x) = a := by simp [rowA, mkRow]
@[simp] theorem rowM_mkRow (a m x : ℕ) : rowM (mkRow a m x) = m := by simp [rowM, mkRow]
@[simp] theorem rowX_mkRow (a m x : ℕ) : rowX (mkRow a m x) = x := by simp [rowX, mkRow]

/-- Add `off` to the next state of a row, keeping `0` (halt). -/
def shift (off r : ℕ) : ℕ :=
  mkRow (rowA r) (rowM r) (if rowX r = 0 then 0 else rowX r + off)

/-- The finite constant: a table for the machine `W`. -/
structure UConst where
  /-- `W` has `k + 1` states. -/
  k : ℕ
  /-- The rows of `W`, three per state. -/
  rows : List ℕ
  /-- The initial state of `W`. -/
  w0 : ℕ

/-- The code of a Boolean symbol being written. -/
def bitCode (b : Bool) : ℕ := if b then 2 else 1

variable (K : UConst) (l : List Bool)

/-- The row for state `q` and symbol code `h`. States below `|l|` write `l`, state `|l|` steps back
onto the last cell, state `|l| + 1` sweeps left to the first blank, and the rest run `W`. -/
def rowFn (q h : ℕ) : ℕ :=
  if q < l.length then mkRow (bitCode (l.getD q false)) 2 (q + 2)
  else if q = l.length then mkRow h 1 (l.length + 2)
  else if q = l.length + 1 then
    (if h = 0 then mkRow 0 2 (l.length + 2 + K.w0 + 1) else mkRow h 1 (l.length + 2))
  else shift (l.length + 2) (K.rows.getD (3 * (q - (l.length + 2)) + h) 0)

/-- The largest state of `NM K l`. -/
def NN : ℕ := l.length + 2 + K.k

/-- The machine that writes `l` and then runs `W`. -/
def NM : SingleTapeTM Bool where
  State := Fin (NN K l + 1)
  q₀ := 0
  tr q h :=
    let r := rowFn K l q.val (hc h)
    (⟨optOf (rowA r), mvOf (rowM r)⟩, nxOf (NN K l) (rowX r))

instance : Encodable (NM K l).State := inferInstanceAs (Encodable (Fin (NN K l + 1)))
instance : DecidableEq (NM K l).State := inferInstanceAs (DecidableEq (Fin (NN K l + 1)))

/-! ### Running it -/

/-- A running configuration at state number `j`. -/
def cf (j : ℕ) (t : BiTape Bool) : (NM K l).Cfg := ⟨some (Fin.ofNat (NN K l + 1) j), t⟩

variable {K l}

theorem nm_step (q : Fin (NN K l + 1)) (t : BiTape Bool) :
    (NM K l).step (⟨some q, t⟩ : (NM K l).Cfg) =
      some (⟨nxOf (NN K l) (rowX (rowFn K l q.val (hc t.head))),
        (t.write (optOf (rowA (rowFn K l q.val (hc t.head))))).optionMove
          (mvOf (rowM (rowFn K l q.val (hc t.head))))⟩ : (NM K l).Cfg) := rfl

theorem cf_step {j a m x : ℕ} {t : BiTape Bool} (hj : j < NN K l + 1)
    (hr : rowFn K l j (hc t.head) = mkRow a m (x + 1)) :
    (NM K l).TransitionRelation (cf K l j t)
      (cf K l x ((t.write (optOf a)).optionMove (mvOf m))) := by
  have hv : (Fin.ofNat (NN K l + 1) j).val = j := by simp [Fin.ofNat, Nat.mod_eq_of_lt hj]
  have h := nm_step (K := K) (l := l) (Fin.ofNat (NN K l + 1) j) t
  rw [hv, hr, rowA_mkRow, rowM_mkRow, rowX_mkRow] at h
  exact h

theorem tp_left_none (h : Option Bool) (L : List Bool) :
    ((tp h L []).write none).optionMove (some .left) = tp L.head? L.tail [] := by
  simp only [tp, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft, mapSome_head,
    mapSome_tail, cons_none_mapSome_nil]

theorem writer_run (suf pre : List Bool) (hl : pre ++ suf = l) :
    Relation.ReflTransGen (NM K l).TransitionRelation
      (cf K l pre.length (tp none pre.reverse []))
      (cf K l l.length (tp none l.reverse [])) := by
  induction suf generalizing pre with
  | nil =>
    obtain rfl : pre = l := by simpa using hl
    exact .refl
  | cons a suf ih =>
    have hlen : pre.length < l.length := by rw [← hl]; simp
    have hget : l.getD pre.length false = a := by
      rw [← hl, List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    have hr : rowFn K l pre.length (hc (tp none pre.reverse []).head) =
        mkRow (bitCode a) 2 (pre.length + 1 + 1) := by
      simp only [rowFn, ite_eq_left hlen, hget]
    have hs := cf_step (K := K) (hj := by simp only [NN]; omega) hr
    have htape : (((tp none pre.reverse []).write (optOf (bitCode a))).optionMove (mvOf 2)) =
        tp none (pre ++ [a]).reverse [] := by
      have : optOf (bitCode a) = some a := by cases a <;> rfl
      rw [this, show mvOf 2 = some .right from rfl, tp_move_right]
      simp
    rw [htape] at hs
    refine .head hs ?_
    have := ih (pre ++ [a]) (by rw [← hl]; simp)
    simpa using this

theorem sweep_nm (A R : List Bool) :
    Relation.ReflTransGen (NM K l).TransitionRelation
      (cf K l (l.length + 1) (tp A.head? A.tail R))
      (cf K l (l.length + 2 + K.w0) (BiTape.mk₁ (A.reverse ++ R))) := by
  have hj : l.length + 1 < NN K l + 1 := by simp only [NN]; omega
  induction A generalizing R with
  | nil =>
    have hr : rowFn K l (l.length + 1) (hc (tp ([] : List Bool).head? [] R).head) =
        mkRow 0 2 (l.length + 2 + K.w0 + 1) := by
      simp [rowFn, tp, hc]
    have hs := cf_step hj hr
    rw [show optOf 0 = none from rfl, show mvOf 2 = some .right from rfl, tp_erase] at hs
    refine .single ?_
    simpa [tp_mk₁] using hs
  | cons x A ih =>
    have hne : hc (some x) ≠ 0 := by cases x <;> decide
    have hr : rowFn K l (l.length + 1) (hc (tp (x :: A).head? (x :: A).tail R).head) =
        mkRow (hc (some x)) 1 (l.length + 1 + 1) := by
      simp [rowFn, tp, hne]
    have hs := cf_step hj hr
    rw [optOf_hc, show mvOf 1 = some .left from rfl] at hs
    have ht : ((tp (x :: A).head? (x :: A).tail R).write (some x)).optionMove (some .left) =
        tp A.head? A.tail (x :: R) := tp_move_left _ x A R
    rw [ht] at hs
    refine .head hs ?_
    simpa using ih (x :: R)

/-- `NM` writes `l` and arrives at `W`'s initial state with `l` on the tape. -/
theorem nm_start :
    Relation.ReflTransGen (NM K l).TransitionRelation
      ((NM K l).initCfg []) (cf K l (l.length + 2 + K.w0) (BiTape.mk₁ l)) := by
  have h₀ : (NM K l).initCfg [] = cf K l ([] : List Bool).length (tp none ([] : List Bool).reverse []) :=
    rfl
  rw [h₀]
  refine (writer_run l [] rfl).trans ?_
  have hj : l.length < NN K l + 1 := by simp only [NN]; omega
  have hr : rowFn K l l.length (hc (tp none l.reverse []).head) = mkRow 0 1 (l.length + 1 + 1) := by
    simp [rowFn, tp, hc]
  have hs := cf_step hj hr
  rw [show optOf 0 = none from rfl, show mvOf 1 = some .left from rfl, tp_left_none] at hs
  refine .head hs ?_
  have := sweep_nm (K := K) (l := l) l.reverse []
  simpa using this

/-! ### The constant for a given machine -/

section Const

variable (W : SingleTapeTM Bool) {k : ℕ} (e : W.State ≃ Fin (k + 1))

/-- The row of a transition of `W`. -/
def rowEnc (x : SingleTapeTM.Stmt Bool × Option W.State) : ℕ :=
  mkRow (hc x.1.symbol) (mvc x.1.movement)
    (match x.2 with
      | none => 0
      | some q => (e q).val + 1)

/-- The table of `W`. -/
def rowsOf : List ℕ :=
  (List.range (3 * (k + 1))).map fun idx =>
    rowEnc W e (W.tr (e.symm (Fin.ofNat (k + 1) (idx / 3))) (optOf (idx % 3)))

theorem rowsOf_get (i : Fin (k + 1)) (h : Option Bool) :
    (rowsOf W e).getD (3 * i.val + hc h) 0 = rowEnc W e (W.tr (e.symm i) h) := by
  have hlt := hc_lt h
  have hidx : 3 * i.val + hc h < 3 * (k + 1) := by have := i.2; omega
  have h3 : (3 * i.val + hc h) / 3 = i.val := by omega
  have h3' : (3 * i.val + hc h) % 3 = hc h := by omega
  simp [rowsOf, List.getD_eq_getElem?_getD, hidx, h3, h3']

/-- The constant of `W`. -/
def constOf : UConst := ⟨k, rowsOf W e, (e W.q₀).val⟩

end Const

/-- **Running a constant machine inside `NM`.** -/
theorem exists_uconst (W : SingleTapeTM Bool) :
    ∃ K : UConst, ∀ (l : List Bool) (b : Bool), W.Outputs l [b] → (NM K l).Outputs [] [b] := by
  classical
  let := W.stateFintype
  have hcard : 0 < Fintype.card W.State := Fintype.card_pos_iff.2 ⟨W.q₀⟩
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card W.State = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hcard).symm⟩
  let e : W.State ≃ Fin (k + 1) := (Fintype.equivFinOfCardEq hk)
  refine ⟨constOf W e, fun l b hout => ?_⟩
  let K := constOf W e
  let off := l.length + 2
  let φ : W.State → (NM K l).State := fun q => Fin.ofNat (NN K l + 1) (off + (e q).val)
  let ψ : W.Cfg → (NM K l).Cfg := fun c => ⟨c.state.map φ, c.BiTape⟩
  have hstep : ∀ c c', W.TransitionRelation c c' → (NM K l).TransitionRelation (ψ c) (ψ c') := by
    rintro ⟨_ | q, t⟩ c' h
    · exact absurd h (by simp [SingleTapeTM.TransitionRelation])
    · have hc' : c' = ⟨(W.tr q t.head).2,
          (t.write (W.tr q t.head).1.symbol).optionMove (W.tr q t.head).1.movement⟩ := by
        have : W.step ⟨some q, t⟩ = some ⟨(W.tr q t.head).2,
            (t.write (W.tr q t.head).1.symbol).optionMove (W.tr q t.head).1.movement⟩ := rfl
        exact (Option.some.inj (this.symm.trans h)).symm
      subst hc'
      have hlt : off + (e q).val < NN K l + 1 := by
        have := (e q).2
        simp only [NN, off, K, constOf]
        omega
      have hv : (φ q).val = off + (e q).val := by
        simp [φ, Fin.ofNat, Nat.mod_eq_of_lt hlt]
      have hrow : rowFn K l (off + (e q).val) (hc t.head) =
          shift off (rowEnc W e (W.tr q t.head)) := by
        have h1 : ¬ off + (e q).val < l.length := by simp only [off]; omega
        have h2 : off + (e q).val ≠ l.length := by simp only [off]; omega
        have h3 : off + (e q).val ≠ l.length + 1 := by simp only [off]; omega
        simp only [rowFn, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
        have hsub : off + (e q).val - (l.length + 2) = (e q).val := by simp only [off]; omega
        rw [hsub]
        have := rowsOf_get W e (e q) t.head
        rw [Equiv.symm_apply_apply] at this
        exact congrArg (shift off) this
      have hn := nm_step (K := K) (l := l) (φ q) t
      rw [hv, hrow] at hn
      refine hn.trans ?_
      rcases hx : W.tr q t.head with ⟨⟨wr, mv⟩, _ | q'⟩
      · simp [ψ, shift, rowEnc, nxOf]
        rfl
      · have hadd : (e q').val + 1 + off = (off + (e q').val) + 1 := by omega
        simp [ψ, shift, rowEnc, nxOf, hadd]
        rfl
  have hgen : ∀ c c', Relation.ReflTransGen W.TransitionRelation c c' →
      Relation.ReflTransGen (NM K l).TransitionRelation (ψ c) (ψ c') := fun c c' h => by
    induction h with
    | refl => exact .refl
    | tail _ h ih => exact ih.tail (hstep _ _ h)
  have hlift := hgen _ _ hout
  have hend : ψ (W.haltCfg [b]) = (NM K l).haltCfg [b] := rfl
  have hbeg : ψ (W.initCfg l) = cf K l (l.length + 2 + K.w0) (BiTape.mk₁ l) := rfl
  rw [hend, hbeg] at hlift
  exact nm_start.trans hlift

/-! ### Codes used by simulators -/

section codes

variable {St : Type} [Encodable St]

/-- The code of an optional state. -/
def qc : Option St → ℕ
  | none => 0
  | some q => Encodable.encode q + 1

theorem qc_injective : Function.Injective (qc : Option St → ℕ) := by
  rintro (_ | a) (_ | b) h <;> simp_all [qc]

end codes

theorem hc_injective : Function.Injective hc := by
  intro a b h
  simpa using congrArg optOf h

/-- The tape symbols. -/
def syms : List (Option Bool) := [none, some false, some true]

theorem mem_syms (o : Option Bool) : o ∈ syms := by
  rcases o with _ | _ | _ <;> simp [syms]

/-! ### Primitive recursiveness -/

section Prim

variable {α : Type*} [Primcodable α]

theorem prim_rowA {f : α → ℕ} (hf : Primrec f) : Primrec fun x => rowA (f x) := by
  unfold rowA
  prim

theorem prim_rowM {f : α → ℕ} (hf : Primrec f) : Primrec fun x => rowM (f x) := by
  unfold rowM
  prim

theorem prim_rowX {f : α → ℕ} (hf : Primrec f) : Primrec fun x => rowX (f x) := by
  unfold rowX
  prim

theorem prim_mkRow {a m r : α → ℕ} (ha : Primrec a) (hm : Primrec m) (hr : Primrec r) :
    Primrec fun x => mkRow (a x) (m x) (r x) := by
  unfold mkRow
  prim

theorem prim_bitCode {f : α → Bool} (hf : Primrec f) : Primrec fun x => bitCode (f x) := by
  unfold bitCode
  exact prim_ite (pred_eq hf (Primrec.const true)) (Primrec.const _) (Primrec.const _)

end Prim

macro_rules
  | `(tactic| prim_step) => `(tactic| with_reducible first
    | apply prim_rowA
    | apply prim_rowM
    | apply prim_rowX
    | apply prim_mkRow
    | apply prim_bitCode)

section Prim

variable {α : Type*} [Primcodable α]

theorem prim_rowFn (K : UConst) {l : α → List Bool} {q h : α → ℕ} (hl : Primrec l)
    (hq : Primrec q) (hh : Primrec h) : Primrec fun x => rowFn K (l x) (q x) (h x) := by
  unfold rowFn shift
  prim

theorem prim_NN (K : UConst) {l : α → List Bool} (hl : Primrec l) :
    Primrec fun x => NN K (l x) := by
  unfold NN
  prim

end Prim

macro_rules
  | `(tactic| prim_step) => `(tactic| with_reducible first
    | apply prim_rowFn
    | apply prim_NN)

end DiagonaLean.Foundations.Computability
