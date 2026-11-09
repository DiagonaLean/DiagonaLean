/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.Foundations.Computability.ListConfig
import Mathlib.Tactic.DeriveFintype

@[expose] public section

/-! # A block transducer on one tape

`queueTM s a M w P` reads its input in blocks of `a` cells. The first cell of a block is a bit `b`,
and the block is replaced by the word `w b`, except that the first `s` blocks are dropped. The word
`P` comes first in the output.

The machine works like a queue. Input and output are kept on the tape separated by one blank. It
erases a block from the left end of the input, walks to the right end of the output, appends the
word, and walks back.

Run with `a = 1`, it expands bits into blocks. Run with `w b = [b]`, it contracts blocks into bits.

## Main statements

* `queueTM`: the machine.
* `queue_outputs`: its output, on an input made of blocks of length `a`.
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing Turing

/-- What is being written. -/
inductive Src where
  | pre
  | drop
  | bit (b : Bool)
  deriving DecidableEq, Fintype

/-- The states of the machine. -/
inductive QS (s a M : ℕ) where
  | toEnd
  | wr (src : Src) (c : Fin (s + 1)) (i : Fin (M + 1))
  | backOut (c : Fin (s + 1))
  | stepIn (c : Fin (s + 1))
  | backIn (c : Fin (s + 1))
  | rd (c : Fin (s + 1))
  | rest (src : Src) (c : Fin (s + 1)) (i : Fin (a + 1))
  | toGap (src : Src) (c : Fin (s + 1))
  | toOut (src : Src) (c : Fin (s + 1))
  | fin₁
  | fin₂
  deriving DecidableEq, Fintype

/-- Clamp a number into `Fin (n + 1)`. -/
def cl (n x : ℕ) : Fin (n + 1) := Fin.ofNat (n + 1) x

theorem cl_val {n x : ℕ} (h : x ≤ n) : (cl n x).val = x := by
  simp [cl, Fin.ofNat, Nat.mod_eq_of_lt (Nat.lt_succ_of_le h)]

variable (s a M : ℕ) (w : Bool → List Bool) (P : List Bool)

/-- The word for a source. -/
def srcW : Src → List Bool
  | .pre => P
  | .drop => []
  | .bit b => w b

/-- The transition table. -/
def qtr : QS s a M → Option Bool → SingleTapeTM.Stmt Bool × Option (QS s a M)
  | .toEnd, some x => (⟨some x, some .right⟩, some .toEnd)
  | .toEnd, none => (⟨none, some .right⟩, some (.wr .pre (cl s s) (cl M 0)))
  | .wr src c i, _ =>
    if i.val < (srcW w P src).length then
      (⟨some ((srcW w P src).getD i.val false), some .right⟩, some (.wr src c (cl M (i.val + 1))))
    else (⟨none, some .left⟩, some (.backOut c))
  | .backOut c, some x => (⟨some x, some .left⟩, some (.backOut c))
  | .backOut c, none => (⟨none, some .left⟩, some (.stepIn c))
  | .stepIn c, some x => (⟨some x, none⟩, some (.backIn c))
  | .stepIn _, none => (⟨none, some .right⟩, some .fin₁)
  | .backIn c, some x => (⟨some x, some .left⟩, some (.backIn c))
  | .backIn c, none => (⟨none, some .right⟩, some (.rd c))
  | .rd c, some b =>
    (⟨none, some .right⟩, some (.rest (if c.val = 0 then .bit b else .drop) c (cl a 1)))
  | .rd _, none => (⟨none, none⟩, none)
  | .rest src c i, h =>
    if i.val < a then (⟨none, some .right⟩, some (.rest src c (cl a (i.val + 1))))
    else (⟨h, none⟩, some (.toGap src (cl s (c.val - 1))))
  | .toGap src c, some x => (⟨some x, some .right⟩, some (.toGap src c))
  | .toGap src c, none => (⟨none, some .right⟩, some (.toOut src c))
  | .toOut src c, some x => (⟨some x, some .right⟩, some (.toOut src c))
  | .toOut src c, none => (⟨none, none⟩, some (.wr src c (cl M 0)))
  | .fin₁, _ => (⟨none, some .right⟩, some .fin₂)
  | .fin₂, h => (⟨h, none⟩, none)

/-- The machine. -/
def queueTM : SingleTapeTM Bool where
  State := QS s a M
  q₀ := .toEnd
  tr := qtr s a M w P

/-! ### Tapes -/

/-- A tape from list-level contents: `L` to the left, nearest first, and `C` from the head on. -/
def tq (L C : List (Option Bool)) : BiTape Bool :=
  ⟨C.headD none, stk L, stk C.tail⟩

theorem stk_head (X : List (Option Bool)) : (stk X).head = X.headD none := by
  cases X with
  | nil => rfl
  | cons x X => exact StackTape.head_cons _ _

theorem stk_tail (X : List (Option Bool)) : (stk X).tail = stk X.tail := by
  cases X with
  | nil => rfl
  | cons x X => exact StackTape.tail_cons _ _

theorem tq_right (L C : List (Option Bool)) (x : Option Bool) :
    ((tq L C).write x).optionMove (some .right) = tq (x :: L) C.tail := by
  simp only [tq, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveRight, stk_head, stk_tail,
    stk_cons]

theorem tq_left (L C : List (Option Bool)) (x : Option Bool) :
    ((tq L C).write x).optionMove (some .left) = tq L.tail (L.headD none :: x :: C.tail) := by
  simp only [tq, BiTape.write, BiTape.optionMove, BiTape.move, BiTape.moveLeft, stk_head, stk_tail,
    stk_cons, List.headD_cons, List.tail_cons]

theorem tq_stay (L C : List (Option Bool)) (x : Option Bool) :
    ((tq L C).write x).optionMove none = tq L (x :: C.tail) := rfl

/-- Cells holding bits. -/
abbrev sm (X : List Bool) : List (Option Bool) := X.map some

variable {s a M w P}

theorem q_step {q : QS s a M} {t : BiTape Bool} {stmt : SingleTapeTM.Stmt Bool}
    {q' : Option (QS s a M)} (h : qtr s a M w P q t.head = (stmt, q'))
    {c' : (queueTM s a M w P).Cfg}
    (hc : c' = (⟨q', (t.write stmt.symbol).optionMove stmt.movement⟩ : (queueTM s a M w P).Cfg)) :
    (queueTM s a M w P).TransitionRelation
      (⟨some q, t⟩ : (queueTM s a M w P).Cfg) c' := by
  subst hc
  show (match qtr s a M w P q t.head with
    | (⟨wr, dir⟩, q'') =>
      some (⟨q'', (t.write wr).optionMove dir⟩ : (queueTM s a M w P).Cfg)) = _
  rw [h]

/-- Reachability in the machine. -/
abbrev QR (s a M : ℕ) (w : Bool → List Bool) (P : List Bool) (x y : (queueTM s a M w P).Cfg) : Prop :=
  Relation.ReflTransGen (queueTM s a M w P).TransitionRelation x y

/-- A running configuration. -/
abbrev qcf (s a M : ℕ) (w : Bool → List Bool) (P : List Bool) (q : QS s a M) (L C : List (Option Bool)) :
    (queueTM s a M w P).Cfg :=
  (⟨some q, tq L C⟩ : (queueTM s a M w P).Cfg)

theorem st_right {q : QS s a M} {q' : Option (QS s a M)} {L C : List (Option Bool)}
    {x : Option Bool} (h : qtr s a M w P q (C.headD none) = (⟨x, some .right⟩, q')) :
    (queueTM s a M w P).TransitionRelation (qcf s a M w P q L C)
      (⟨q', tq (x :: L) C.tail⟩ : (queueTM s a M w P).Cfg) := by
  refine q_step h ?_
  show _ = (⟨q', ((tq L C).write x).optionMove (some .right)⟩ : (queueTM s a M w P).Cfg)
  rw [tq_right]

theorem st_left {q : QS s a M} {q' : Option (QS s a M)} {L C : List (Option Bool)}
    {x : Option Bool} (h : qtr s a M w P q (C.headD none) = (⟨x, some .left⟩, q')) :
    (queueTM s a M w P).TransitionRelation (qcf s a M w P q L C)
      (⟨q', tq L.tail (L.headD none :: x :: C.tail)⟩ : (queueTM s a M w P).Cfg) := by
  refine q_step h ?_
  show _ = (⟨q', ((tq L C).write x).optionMove (some .left)⟩ : (queueTM s a M w P).Cfg)
  rw [tq_left]

theorem st_stay {q : QS s a M} {q' : Option (QS s a M)} {L C : List (Option Bool)}
    {x : Option Bool} (h : qtr s a M w P q (C.headD none) = (⟨x, none⟩, q')) :
    (queueTM s a M w P).TransitionRelation (qcf s a M w P q L C)
      (⟨q', tq L (x :: C.tail)⟩ : (queueTM s a M w P).Cfg) := by
  refine q_step h ?_
  rfl

/-! ### Walking -/

theorem walk_right {q : QS s a M}
    (h : ∀ x, qtr s a M w P q (some x) = (⟨some x, some .right⟩, some q))
    (X : List Bool) (L C : List (Option Bool)) :
    QR s a M w P (qcf s a M w P q L (sm X ++ C)) (qcf s a M w P q (sm X.reverse ++ L) C) := by
  induction X generalizing L with
  | nil => exact .refl
  | cons x X ih =>
    refine .head (st_right (x := some x) (q' := some q) (h x)) ?_
    have e : sm (x :: X).reverse ++ L = sm X.reverse ++ some x :: L := by simp
    rw [e]
    exact ih (some x :: L)

theorem walk_left {q : QS s a M}
    (h : ∀ x, qtr s a M w P q (some x) = (⟨some x, some .left⟩, some q))
    (X : List Bool) (y : Bool) (L C : List (Option Bool)) :
    QR s a M w P (qcf s a M w P q (sm X ++ none :: L) (some y :: C))
      (qcf s a M w P q L (none :: sm (X.reverse ++ [y]) ++ C)) := by
  induction X generalizing y C with
  | nil => exact .single (st_left (x := some y) (q' := some q) (h y))
  | cons x X ih =>
    refine .head (st_left (x := some y) (q' := some q) (h y)) ?_
    have e : none :: sm ((x :: X).reverse ++ [y]) ++ C =
        none :: sm (X.reverse ++ [x]) ++ some y :: C := by simp
    rw [e]
    exact ih x (some y :: C)

/-! ### Writing a word -/

theorem wr_run {src : Src} {c : Fin (s + 1)} (hM : (srcW w P src).length ≤ M) (D A : List Bool)
    (hAD : A ++ D = srcW w P src) (L C : List (Option Bool)) (hC : C.tail = []) :
    ∃ C', C'.tail = [] ∧ QR s a M w P (qcf s a M w P (.wr src c (cl M A.length)) L C)
      (qcf s a M w P (.wr src c (cl M (srcW w P src).length)) (sm D.reverse ++ L) C') := by
  induction D generalizing A L C with
  | nil =>
    refine ⟨C, hC, ?_⟩
    have : A = srcW w P src := by simpa using hAD
    rw [this]
    exact .refl
  | cons d D ih =>
    have hlen : A.length < (srcW w P src).length := by rw [← hAD]; simp
    have hv : (cl M A.length).val = A.length := cl_val (by omega)
    have hget : (srcW w P src).getD A.length false = d := by
      rw [← hAD, List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    have hget₂ : (srcW w P src)[A.length] = d := by
      have := hget
      rwa [List.getD_eq_getElem _ _ hlen] at this
    have hs : (queueTM s a M w P).TransitionRelation (qcf s a M w P (.wr src c (cl M A.length)) L C)
        (qcf s a M w P (.wr src c (cl M (A.length + 1))) (some d :: L) []) := by
      have := st_right (s := s) (a := a) (M := M) (w := w) (P := P) (q := .wr src c (cl M A.length))
        (q' := some (.wr src c (cl M (A.length + 1)))) (L := L) (C := C) (x := some d)
        (by simp [qtr, hv, hlen, hget₂])
      rwa [hC] at this
    obtain ⟨C', hC', hr⟩ := ih (A ++ [d]) (by simpa using hAD) (some d :: L) [] rfl
    have hl : (A ++ [d]).length = A.length + 1 := by simp
    rw [hl] at hr
    refine ⟨C', hC', .head hs ?_⟩
    have e : sm (d :: D).reverse ++ L = sm D.reverse ++ some d :: L := by simp
    rw [e]
    exact hr

/-- After writing, walk back to the gap. -/
theorem back_to_gap {src : Src} {c : Fin (s + 1)} (hM : (srcW w P src).length ≤ M)
    (OW : List Bool) (L C : List (Option Bool)) (hC : C.tail = []) :
    QR s a M w P (qcf s a M w P (.wr src c (cl M (srcW w P src).length)) (sm OW.reverse ++ none :: L) C)
      (qcf s a M w P (.backOut c) L (none :: sm OW ++ [none])) := by
  have hv : (cl M (srcW w P src).length).val = (srcW w P src).length := cl_val hM
  have hq : qtr s a M w P (.wr src c (cl M (srcW w P src).length)) (C.headD none) =
      (⟨none, some .left⟩, some (.backOut c)) := by
    simp [qtr, hv]
  have hs := st_left (s := s) (a := a) (M := M) (w := w) (P := P) (L := sm OW.reverse ++ none :: L) hq
  rw [hC] at hs
  refine .head hs ?_
  rcases hrev : OW.reverse with _ | ⟨z, Z⟩
  · have : OW = [] := by simpa using hrev
    subst this
    exact .refl
  · have hO : OW = Z.reverse ++ [z] := by
      have := congrArg List.reverse hrev
      simpa using this
    subst hO
    exact walk_left (q := .backOut c) (fun x => rfl) Z z L [none]

/-! ### Reading a block -/

theorem rest_run {src : Src} {c : Fin (s + 1)} (r : List Bool) (i : ℕ) (hi : i + r.length = a)
    (L C : List (Option Bool)) :
    QR s a M w P (qcf s a M w P (.rest src c (cl a i)) L (sm r ++ C))
      (qcf s a M w P (.rest src c (cl a a)) (List.replicate r.length none ++ L) C) := by
  induction r generalizing i L with
  | nil =>
    have : i = a := by simpa using hi
    subst this
    exact .refl
  | cons x r ih =>
    have hlt : i < a := by simp at hi; omega
    have hv : (cl a i).val = i := cl_val hlt.le
    refine .head (st_right (x := none) (q' := some (.rest src c (cl a (i + 1)))) (L := L)
      (by simp [qtr, hv, hlt])) ?_
    have e : List.replicate (x :: r).length none ++ L =
        List.replicate r.length none ++ none :: L := by
      simp [List.replicate_succ']
    rw [e]
    exact ih (i + 1) (by simp at hi; omega) (none :: L)

theorem stk_append_none (X : List (Option Bool)) : stk (X ++ [none]) = stk X := by
  induction X with
  | nil => rfl
  | cons x X ih => simp only [List.cons_append, stk_cons, ih]

theorem stk_nones {L : List (Option Bool)} (h : ∀ x ∈ L, x = none) : stk L = StackTape.nil := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    obtain rfl := h x List.mem_cons_self
    rw [stk_cons, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

/-- One round of the queue. -/
theorem round {c : ℕ} (hs : c ≤ s) {O' : List Bool} (b : Bool) (r I' : List Bool)
    (hr : r.length + 1 = a) (hM : ∀ src, (srcW w P src).length ≤ M) (L₀ : List (Option Bool)) :
    QR s a M w P
      (qcf s a M w P (.backOut (cl s c)) (sm ((b :: r) ++ I').reverse ++ none :: L₀) (none :: sm O' ++ [none]))
      (qcf s a M w P (.backOut (cl s (c - 1))) (sm I'.reverse ++
          (List.replicate r.length none ++ [none, none] ++ L₀))
        (none :: sm (O' ++ srcW w P (if c = 0 then .bit b else .drop)) ++ [none])) := by
  have hcv : (cl s c).val = c := cl_val hs
  set I := (b :: r) ++ I' with hI
  obtain ⟨z, Z, hzZ⟩ : ∃ z Z, I.reverse = z :: Z := by
    rcases h : I.reverse with _ | ⟨z, Z⟩
    · simp [hI] at h
    · exact ⟨z, Z, rfl⟩
  have hIZ : I = Z.reverse ++ [z] := by
    have := congrArg List.reverse hzZ
    simpa using this
  rw [hzZ]
  -- step off the gap
  refine .head (st_left (x := none) (q' := some (.stepIn (cl s c))) rfl) ?_
  refine .head (st_stay (x := some z) (q' := some (.backIn (cl s c))) rfl) ?_
  have hwalk := walk_left (s := s) (a := a) (M := M) (w := w) (P := P) (q := .backIn (cl s c)) (fun x => rfl) Z z L₀
    (none :: sm O' ++ [none])
  refine Relation.ReflTransGen.trans hwalk ?_
  rw [← hIZ]
  refine .head (st_right (x := none) (q' := some (.rd (cl s c))) rfl) ?_
  rw [hI]
  set src : Src := if c = 0 then .bit b else .drop with hsrc
  have hsrc' : (if (cl s c).val = 0 then Src.bit b else Src.drop) = src := by rw [hcv]
  have hq : qtr s a M w P (.rd (cl s c)) (some b) =
      (⟨none, some .right⟩, some (.rest src (cl s c) (cl a 1))) := by
    show ((⟨none, some .right⟩, some (QS.rest (if (cl s c).val = 0 then Src.bit b else Src.drop)
      (cl s c) (cl a 1))) : SingleTapeTM.Stmt Bool × Option (QS s a M)) = _
    rw [hsrc']
  refine .head (st_right (x := none) hq) ?_
  have hrest := rest_run (s := s) (a := a) (M := M) (w := w) (P := P) (src := src) (c := cl s c) r 1
    (by omega) (none :: none :: L₀) (sm I' ++ none :: sm O' ++ [none])
  have hshape : (none :: sm (b :: r ++ I') ++ (none :: sm O' ++ [none])).tail.tail =
      sm r ++ (sm I' ++ none :: sm O' ++ [none]) := by
    simp [List.map_append]
  rw [hshape]
  refine Relation.ReflTransGen.trans hrest ?_
  have ha : ¬ (cl a a).val < a := by rw [cl_val le_rfl]; omega
  set L₁ := List.replicate r.length none ++ none :: none :: L₀ with hL₁
  -- the block is gone
  set C₁ : List (Option Bool) := sm I' ++ none :: sm O' ++ [none] with hC₁
  have hC₁e : C₁.headD none :: C₁.tail = C₁ := by
    rw [hC₁]
    cases I' <;> rfl
  have hstay := st_stay (s := s) (a := a) (M := M) (w := w) (P := P) (q := .rest src (cl s c) (cl a a))
    (q' := some (.toGap src (cl s ((cl s c).val - 1)))) (L := L₁) (C := C₁) (x := C₁.headD none)
    (by simp [qtr, ha])
  rw [hC₁e] at hstay
  refine .head hstay ?_
  rw [hcv]
  have hw₁ := walk_right (s := s) (a := a) (M := M) (w := w) (P := P) (q := .toGap src (cl s (c - 1))) (fun x => rfl) I' L₁
    (none :: sm O' ++ [none])
  have heC : C₁ = sm I' ++ (none :: sm O' ++ [none]) := by simp [hC₁]
  rw [heC]
  refine Relation.ReflTransGen.trans hw₁ ?_
  refine .head (st_right (x := none) (q' := some (.toOut src (cl s (c - 1)))) rfl) ?_
  have hw₂ := walk_right (s := s) (a := a) (M := M) (w := w) (P := P) (q := .toOut src (cl s (c - 1))) (fun x => rfl) O'
    (none :: (sm I'.reverse ++ L₁)) [none]
  refine Relation.ReflTransGen.trans hw₂ ?_
  refine .head (st_stay (x := none) (q' := some (.wr src (cl s (c - 1)) (cl M 0))) rfl) ?_
  obtain ⟨C', hC', hwr⟩ := wr_run (s := s) (a := a) (M := M) (w := w) (P := P) (src := src) (c := cl s (c - 1)) (hM src)
    (srcW w P src) [] rfl (sm O'.reverse ++ none :: (sm I'.reverse ++ L₁)) [none] rfl
  refine Relation.ReflTransGen.trans hwr ?_
  have hb := back_to_gap (s := s) (a := a) (M := M) (w := w) (P := P) (src := src) (c := cl s (c - 1)) (hM src)
    (O' ++ srcW w P src) (sm I'.reverse ++ L₁) C' hC'
  have he : sm (O' ++ srcW w P src).reverse ++ none :: (sm I'.reverse ++ L₁) =
      sm (srcW w P src).reverse ++ (sm O'.reverse ++ none :: (sm I'.reverse ++ L₁)) := by
    simp [List.map_append]
  rw [he] at hb
  have hL : sm I'.reverse ++ (List.replicate r.length none ++ [none, none] ++ L₀) =
      sm I'.reverse ++ L₁ := by
    simp [hL₁]
  rw [hL]
  exact hb

/-! ### The whole run -/

/-- The cells of a list of blocks. -/
def flat (bs : List (Bool × List Bool)) : List Bool := bs.flatMap fun x => x.1 :: x.2

theorem tq_final {L : List (Option Bool)} (hL : ∀ x ∈ L, x = none) (O : List Bool) :
    tq L (sm O ++ [none]) = BiTape.mk₁ O := by
  cases O with
  | nil => simp only [tq, stk_nones hL]; rfl
  | cons o O =>
    simp only [tq, stk_nones hL, List.map_cons, List.cons_append, List.headD_cons, List.tail_cons,
      stk_append_none, stk_map_some]
    rfl

/-- The queue empties, and the machine stops with the output alone on the tape. -/
theorem loop (hM : ∀ src, (srcW w P src).length ≤ M) (bs : List (Bool × List Bool))
    (hbs : ∀ x ∈ bs, x.2.length + 1 = a) (c : ℕ) (hc : c ≤ s) (O : List Bool)
    (L₀ : List (Option Bool)) (hL : ∀ x ∈ L₀, x = none) :
    QR s a M w P
      (qcf s a M w P (.backOut (cl s c)) (sm (flat bs).reverse ++ none :: L₀)
        (none :: sm O ++ [none]))
      ((queueTM s a M w P).haltCfg (O ++ (bs.drop c).flatMap fun x => w x.1)) := by
  induction bs generalizing c O L₀ with
  | nil =>
    refine .head (st_left (x := none) (q' := some (.stepIn (cl s c))) rfl) ?_
    refine .head (st_right (x := none) (q' := some .fin₁) rfl) ?_
    refine .head (st_right (x := none) (q' := some .fin₂) rfl) ?_
    have hhalt := st_stay (s := s) (a := a) (M := M) (w := w) (P := P) (q := .fin₂)
      (q' := none) (L := none :: none :: L₀) (C := sm O ++ [none])
      (x := (sm O ++ [none]).headD none) rfl
    have hC : (sm O ++ [none]).headD none :: (sm O ++ [none]).tail = sm O ++ [none] := by
      cases O <;> rfl
    rw [hC] at hhalt
    have hL' : ∀ x ∈ none :: none :: L₀, x = none := by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · rfl
      · rfl
      · exact hL x hx
    rw [tq_final hL'] at hhalt
    have e : O ++ (([] : List (Bool × List Bool)).drop c).flatMap (fun x => w x.1) = O := by simp
    rw [e]
    exact .single hhalt
  | cons x bs ih =>
    obtain ⟨b, r⟩ := x
    have hr : r.length + 1 = a := hbs _ List.mem_cons_self
    have hflat : flat ((b, r) :: bs) = (b :: r) ++ flat bs := by simp [flat]
    rw [hflat]
    have hround := round (s := s) (a := a) (M := M) (w := w) (P := P) (c := c) hc (O' := O)
      b r (flat bs) hr hM L₀
    refine hround.trans ?_
    have hL₁ : List.replicate r.length none ++ [none, none] ++ L₀ =
        none :: (List.replicate r.length none ++ none :: L₀) := by
      simp only [List.append_assoc]
      rw [show (none : Option Bool) :: (List.replicate r.length none ++ none :: L₀) =
        (List.replicate (r.length + 1) none) ++ none :: L₀ from rfl, List.replicate_succ']
      simp
    rw [hL₁]
    have hL₂ : ∀ x ∈ List.replicate r.length none ++ none :: L₀, x = none := by
      intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact List.eq_of_mem_replicate h
      · rcases List.mem_cons.1 h with rfl | h
        · rfl
        · exact hL x h
    have := ih (fun y hy => hbs y (List.mem_cons_of_mem _ hy)) (c - 1) (by omega)
      (O ++ srcW w P (if c = 0 then .bit b else .drop)) _ hL₂
    refine this.trans ?_
    have heq : srcW w P (if c = 0 then .bit b else .drop) ++
        (List.drop (c - 1) bs).flatMap (fun x => w x.1) =
        (((b, r) :: bs).drop c).flatMap fun x => w x.1 := by
      rcases c with _ | c
      · simp [srcW]
      · simp [srcW]
    rw [List.append_assoc, heq]

/-- **Correctness of the queue.** -/
theorem queue_outputs (hM : ∀ src, (srcW w P src).length ≤ M) (bs : List (Bool × List Bool))
    (hbs : ∀ x ∈ bs, x.2.length + 1 = a) :
    (queueTM s a M w P).Outputs (flat bs) (P ++ (bs.drop s).flatMap fun x => w x.1) := by
  have hinit : (queueTM s a M w P).initCfg (flat bs) =
      qcf s a M w P .toEnd [] (sm (flat bs) ++ []) := by
    have : BiTape.mk₁ (flat bs) = tq [] (sm (flat bs) ++ []) := by
      cases flat bs with
      | nil => rfl
      | cons o O =>
        simp only [tq, List.map_cons, List.cons_append, List.nil_append, List.append_nil,
          List.headD_cons, List.tail_cons, stk_map_some, BiTape.mk₁]
        rfl
    simp only [SingleTapeTM.initCfg, this]
    rfl
  show Relation.ReflTransGen _ _ _
  rw [hinit]
  have h₁ := walk_right (s := s) (a := a) (M := M) (w := w) (P := P) (q := .toEnd) (fun x => rfl)
    (flat bs) [] []
  refine h₁.trans ?_
  refine .head (st_right (x := none) (q' := some (.wr .pre (cl s s) (cl M 0))) rfl) ?_
  obtain ⟨C', hC', hwr⟩ := wr_run (s := s) (a := a) (M := M) (w := w) (P := P) (src := .pre)
    (c := cl s s) (hM _) P [] rfl (none :: (sm (flat bs).reverse ++ [])) [] rfl
  refine hwr.trans ?_
  have hb := back_to_gap (s := s) (a := a) (M := M) (w := w) (P := P) (src := .pre) (c := cl s s)
    (hM _) P (sm (flat bs).reverse ++ []) C' hC'
  refine Relation.ReflTransGen.trans (by exact hb) ?_
  have hnorm : tq (sm (flat bs).reverse ++ []) (none :: sm P ++ [none]) =
      tq (sm (flat bs).reverse ++ none :: []) (none :: sm P ++ [none]) := by
    simp only [tq, List.append_nil, stk_append_none]
  show Relation.ReflTransGen _ (⟨some (.backOut (cl s s)), _⟩ : (queueTM s a M w P).Cfg) _
  rw [hnorm]
  exact loop hM bs hbs s le_rfl P [] (by simp)

end DiagonaLean.Foundations.Computability
