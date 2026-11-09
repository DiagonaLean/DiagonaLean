/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import Mathlib.Computability.TuringMachine.ToPartrec
import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

@[expose] public section

/-! # From a finitely supported Mathlib `TM0` machine to a Cslib machine with a clean output

A `TM0` machine over `Bool` has `false` as its blank, and stops with an arbitrary tape. A Cslib
machine `Outputs` a list only when the final tape is exactly that list, with the head on its first
cell. `wrap` closes the gap.

* While simulating, every visited cell is written as `some _`, so the non-blank cells stay
  contiguous and a blank is read as `false`.
* When the `TM0` machine stops in state `q`, `wrap` sweeps left to the first blank, erases rightward
  up to the next blank, writes the single bit `bit q`, and halts.

Only forward simulation is proved, because that is all the reduction needs.

## Main statements

* `wrap`: the Cslib machine.
* `wrap_outputs`: if `M` stops in `c` on input `l`, then `wrap` outputs `[bit c.q]` on `l`.
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing Turing StateTransition

variable {Λ : Type} [Inhabited Λ] (M : TM0.Machine Bool Λ) (S : Finset Λ)
  (hS : TM0.Supports M (S : Set Λ))
  {Stop : Type} [Fintype Stop] (enter : Λ → Stop)
  (stopTr : Stop → Option Bool → SingleTapeTM.Stmt Bool × Option Stop)

/-- The states: simulation in the support, then a cleanup stage. -/
abbrev WState (Stop : Type) := {q // q ∈ S} ⊕ Stop

variable {M S}

theorem next_mem (hS : TM0.Supports M (S : Set Λ)) {q : Λ} (hq : q ∈ S) {a : Bool} {q' : Λ}
    {s : TM0.Stmt Bool} (hm : M q a = some (q', s)) : q' ∈ S := by
  obtain ⟨-, h⟩ := hS
  exact Finset.mem_coe.1 (h (show (q', s) ∈ M q a from hm) (Finset.mem_coe.2 hq))

variable (M S)

/-- The transition function: simulate `M`, and when it stops, enter the cleanup stage. -/
def wrapTrG : WState S Stop → Option Bool → SingleTapeTM.Stmt Bool × Option (WState S Stop)
  | .inl q, h =>
    match hm : M q.1 (h.getD false) with
    | none => (⟨some (h.getD false), none⟩, some (.inr (enter q.1)))
    | some (q', .write x) => (⟨some x, none⟩, some (.inl ⟨q', next_mem hS q.2 hm⟩))
    | some (q', .move d) => (⟨some (h.getD false), some d⟩, some (.inl ⟨q', next_mem hS q.2 hm⟩))
  | .inr t, h => ((stopTr t h).1, (stopTr t h).2.map .inr)

/-- The Cslib machine simulating `M`, followed by a cleanup stage. -/
def wrapG : SingleTapeTM Bool where
  State := WState S Stop
  q₀ := .inl ⟨default, Finset.mem_coe.1 hS.1⟩
  tr := wrapTrG M S hS enter stopTr

/-! ### Tapes whose non-blank cells are contiguous -/

/-- A Cslib tape with all-`some` sides. -/
def tp (h : Option Bool) (L R : List Bool) : BiTape Bool :=
  ⟨h, StackTape.mapSome L, StackTape.mapSome R⟩

/-- The `TM0` tape it represents. -/
def ab (h : Option Bool) (L R : List Bool) : Tape Bool :=
  ⟨h.getD false, ListBlank.mk L, ListBlank.mk R⟩

theorem mapSome_head (R : List Bool) : (StackTape.mapSome R).head = R.head? := by
  cases R <;> rfl

theorem mapSome_tail (R : List Bool) : (StackTape.mapSome R).tail = StackTape.mapSome R.tail := by
  cases R <;> rfl

theorem cons_some_mapSome (a : Bool) (L : List Bool) :
    StackTape.cons (some a) (StackTape.mapSome L) = StackTape.mapSome (a :: L) := rfl

theorem cons_none_mapSome_nil :
    StackTape.cons none (StackTape.mapSome ([] : List Bool)) = StackTape.mapSome [] := rfl

theorem headI_getD (R : List Bool) : R.head?.getD false = R.headI := by
  cases R <;> rfl

theorem tp_move_right (h : Option Bool) (a : Bool) (L R : List Bool) :
    ((tp h L R).write (some a)).optionMove (some .right) = tp R.head? (a :: L) R.tail := by
  simp only [tp, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveRight, mapSome_head,
    mapSome_tail, cons_some_mapSome]

theorem tp_move_left (h : Option Bool) (a : Bool) (L R : List Bool) :
    ((tp h L R).write (some a)).optionMove (some .left) = tp L.head? L.tail (a :: R) := by
  simp only [tp, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft, mapSome_head,
    mapSome_tail, cons_some_mapSome]

theorem ab_move_right (h : Option Bool) (L R : List Bool) :
    (ab h L R).move .right = ab R.head? (h.getD false :: L) R.tail := by
  simp only [ab, Tape.move, ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk, headI_getD]

theorem ab_move_left (h : Option Bool) (L R : List Bool) :
    (ab h L R).move .left = ab L.head? L.tail (h.getD false :: R) := by
  simp only [ab, Tape.move, ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk, headI_getD]

theorem ab_write (h : Option Bool) (x : Bool) (L R : List Bool) :
    (ab h L R).write x = ab (some x) L R := rfl

theorem ab_mk₁ (l : List Bool) : (Tape.mk₁ l : Tape Bool) = ab l.head? [] l.tail := by
  simp only [Tape.mk₁, Tape.mk₂, Tape.mk', ab, ListBlank.head_mk, ListBlank.tail_mk, headI_getD]

theorem tp_mk₁ (l : List Bool) : BiTape.mk₁ l = tp l.head? [] l.tail := by
  cases l <;> rfl

/-! ### Simulation -/

/-- `w` represents the `TM0` configuration `a`. -/
def WRel (a : TM0.Cfg Bool Λ) (w : (wrapG M S hS enter stopTr).Cfg) : Prop :=
  ∃ (hq : a.q ∈ S) (h : Option Bool) (L R : List Bool),
    w = ⟨some (.inl ⟨a.q, hq⟩), tp h L R⟩ ∧ a.Tape = ab h L R

variable {M S hS enter stopTr}

/-- One step of `wrap`, from its transition table. -/
theorem wrap_step {q : WState S Stop} {t : BiTape Bool} {stmt : SingleTapeTM.Stmt Bool}
    {q' : Option (WState S Stop)} (h : wrapTrG M S hS enter stopTr q t.head = (stmt, q'))
    {w' : (wrapG M S hS enter stopTr).Cfg} (hw : w' = (⟨q', (t.write stmt.symbol).optionMove stmt.movement⟩ : (wrapG M S hS enter stopTr).Cfg)) :
    (wrapG M S hS enter stopTr).TransitionRelation (⟨some q, t⟩ : (wrapG M S hS enter stopTr).Cfg) w' := by
  subst hw
  show (match wrapTrG M S hS enter stopTr q t.head with
    | (⟨wr, dir⟩, q'') =>
      some (⟨q'', (t.write wr).optionMove dir⟩ : (wrapG M S hS enter stopTr).Cfg)) = _
  rw [h]

theorem rel_step {a b : TM0.Cfg Bool Λ} {w : (wrapG M S hS enter stopTr).Cfg} (hr : WRel M S hS enter stopTr a w)
    (hb : b ∈ TM0.step M a) :
    ∃ w', WRel M S hS enter stopTr b w' ∧ (wrapG M S hS enter stopTr).TransitionRelation w w' := by
  obtain ⟨hq, h, L, R, rfl, hT⟩ := hr
  obtain ⟨q, T⟩ := a
  obtain rfl : T = ab h L R := hT
  obtain ⟨⟨q', s⟩, hm, rfl⟩ := Option.map_eq_some_iff.1 hb
  have hm' : M q (h.getD false) = some (q', s) := hm
  have hq' : q' ∈ S := next_mem hS hq hm'
  let st : WState S Stop := .inl ⟨q', hq'⟩
  cases s with
  | write x =>
    have htr : wrapTrG M S hS enter stopTr (.inl ⟨q, hq⟩) (tp h L R).head = (⟨some x, none⟩, some st) := by
      simp only [wrapTrG, tp]
      split <;> simp_all [st]
    exact ⟨⟨some st, tp (some x) L R⟩, ⟨hq', _, L, R, rfl, ab_write h x L R⟩, wrap_step htr rfl⟩
  | move d =>
    have htr : wrapTrG M S hS enter stopTr (.inl ⟨q, hq⟩) (tp h L R).head =
        (⟨some (h.getD false), some d⟩, some st) := by
      simp only [wrapTrG, tp]
      split <;> simp_all [st]
    cases d with
    | right =>
      exact ⟨⟨some st, tp R.head? (h.getD false :: L) R.tail⟩,
        ⟨hq', _, _, _, rfl, ab_move_right h L R⟩, wrap_step htr (by rw [tp_move_right]; rfl)⟩
    | left =>
      exact ⟨⟨some st, tp L.head? L.tail (h.getD false :: R)⟩,
        ⟨hq', _, _, _, rfl, ab_move_left h L R⟩, wrap_step htr (by rw [tp_move_left]; rfl)⟩

theorem rel_reaches {a b : TM0.Cfg Bool Λ} {w : (wrapG M S hS enter stopTr).Cfg} (hr : WRel M S hS enter stopTr a w)
    (hab : Reaches (TM0.step M) a b) :
    ∃ w', WRel M S hS enter stopTr b w' ∧
      Relation.ReflTransGen (wrapG M S hS enter stopTr).TransitionRelation w w' := by
  induction hab with
  | refl => exact ⟨w, hr, .refl⟩
  | tail _ hstep ih =>
    obtain ⟨w₁, hr₁, hw₁⟩ := ih
    obtain ⟨w₂, hr₂, hw₂⟩ := rel_step hr₁ hstep
    exact ⟨w₂, hr₂, hw₁.tail hw₂⟩

variable (M S hS enter stopTr) in
/-- `M` stopping in `c` means the cleanup stage starts on a tape representing `c`. -/
theorem wrapG_reach {l : List Bool} {c : TM0.Cfg Bool Λ}
    (hc : c ∈ StateTransition.eval (TM0.step M) (TM0.init l)) :
    ∃ (h : Option Bool) (L R : List Bool),
      Relation.ReflTransGen (wrapG M S hS enter stopTr).TransitionRelation
        ((wrapG M S hS enter stopTr).initCfg l)
        (⟨some (.inr (enter c.q)), tp (some (h.getD false)) L R⟩ :
          (wrapG M S hS enter stopTr).Cfg) ∧ c.Tape = ab h L R := by
  obtain ⟨hr, hstop⟩ := mem_eval.1 hc
  have h₀ : WRel M S hS enter stopTr (TM0.init l) ((wrapG M S hS enter stopTr).initCfg l) :=
    ⟨Finset.mem_coe.1 hS.1, l.head?, [], l.tail,
      by simp only [SingleTapeTM.initCfg, tp_mk₁]; rfl, ab_mk₁ l⟩
  obtain ⟨w, ⟨hq, h, L, R, rfl, hT⟩, hw⟩ := rel_reaches h₀ hr
  obtain ⟨q, T⟩ := c
  obtain rfl : T = ab h L R := hT
  have hn : M q (h.getD false) = none := by
    simpa [TM0.step, ab] using hstop
  have htr : wrapTrG M S hS enter stopTr (.inl ⟨q, hq⟩) (tp h L R).head =
      (⟨some (h.getD false), none⟩, some (.inr (enter q))) := by
    simp only [wrapTrG, tp]
    split <;> simp_all
  exact ⟨h, L, R, hw.tail (wrap_step htr rfl), rfl⟩

/-! ### Cleaning up by sweeping -/

section sweep

variable (M S hS) (bit : Λ → Bool)

/-- The cleanup stage of `wrap`: sweep left to a blank, then erase rightward and write the bit. -/
def sweepTr : Bool ⊕ Bool → Option Bool → SingleTapeTM.Stmt Bool × Option (Bool ⊕ Bool)
  | .inl b, some x => (⟨some x, some .left⟩, some (.inl b))
  | .inl b, none => (⟨none, some .right⟩, some (.inr b))
  | .inr b, some _ => (⟨none, some .right⟩, some (.inr b))
  | .inr b, none => (⟨some b, none⟩, none)

/-- The Cslib machine simulating `M`, and then cleaning the tape to the single bit `bit q`. -/
abbrev wrap : SingleTapeTM Bool := wrapG M S hS (fun q => .inl (bit q)) sweepTr

variable {M S hS bit}


theorem tp_erase (h : Option Bool) (R : List Bool) :
    ((tp h [] R).write none).optionMove (some .right) = tp R.head? [] R.tail := by
  simp only [tp, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveRight, mapSome_head,
    mapSome_tail, cons_none_mapSome_nil]

theorem erase_run (b : Bool) (R : List Bool) :
    Relation.ReflTransGen (wrap M S hS bit).TransitionRelation
      (⟨some (.inr (.inr b)), tp R.head? [] R.tail⟩ : (wrap M S hS bit).Cfg)
      ((wrap M S hS bit).haltCfg [b]) := by
  induction R with
  | nil => exact .single (wrap_step (stmt := ⟨some b, none⟩) (q' := none) rfl rfl)
  | cons x R ih =>
    exact .head (wrap_step (stmt := ⟨none, some .right⟩) (q' := some (.inr (.inr b))) rfl
      (by rw [List.head?_cons, List.tail_cons]; exact (congrArg _ (tp_erase _ R)).symm)) ih

theorem sweep_run (b : Bool) (L : List Bool) (x : Bool) (R : List Bool) :
    Relation.ReflTransGen (wrap M S hS bit).TransitionRelation
      (⟨some (.inr (.inl b)), tp (some x) L R⟩ : (wrap M S hS bit).Cfg)
      ((wrap M S hS bit).haltCfg [b]) := by
  induction L generalizing x R with
  | nil =>
    refine .head (wrap_step (stmt := ⟨some x, some .left⟩) (q' := some (.inr (.inl b))) rfl
      (w' := ⟨some (.inr (.inl b)), tp none [] (x :: R)⟩) (congrArg _ (tp_move_left _ x [] R).symm)) ?_
    exact .head (wrap_step (stmt := ⟨none, some .right⟩) (q' := some (.inr (.inr b))) rfl
      (congrArg _ (tp_erase _ (x :: R)).symm)) (erase_run b (x :: R))
  | cons y L ih =>
    exact .head (wrap_step (stmt := ⟨some x, some .left⟩) (q' := some (.inr (.inl b))) rfl
      (w' := ⟨some (.inr (.inl b)), tp (some y) L (x :: R)⟩)
      (congrArg _ (tp_move_left _ x (y :: L) R).symm)) (ih y (x :: R))

variable (M S hS bit) in
/-- **Correctness of `wrap`.** If `M` stops in `c` on `l`, then `wrap` outputs `[bit c.q]` on `l`. -/
theorem wrap_outputs {l : List Bool} {c : TM0.Cfg Bool Λ}
    (hc : c ∈ StateTransition.eval (TM0.step M) (TM0.init l)) :
    (wrap M S hS bit).Outputs l [bit c.q] := by
  obtain ⟨h, L, R, hr, -⟩ := wrapG_reach M S hS (fun q => .inl (bit q)) sweepTr hc
  exact hr.trans (sweep_run _ L _ R)

end sweep

end DiagonaLean.Foundations.Computability
