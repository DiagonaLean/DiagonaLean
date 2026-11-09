/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.Foundations.Computability.PartrecToCslib
import DiagonaLean.Foundations.Computability.Queue

@[expose] public section

/-! # A partial recursive function, as a machine with a full output

`exists_compiled` strengthens `exists_machine`: on the tape of `n`, the machine stops with exactly
the tape of `m`, for every `m ∈ g n`.

Mathlib's final TM2 configuration for output `m` has the same stacks as its initial configuration
for `m`, so its final tape is the initial tape of `m`, up to blanks (inside `exists_compiled`). The
cleanup stage `cleanTr` removes the stray `some false` cells on both sides. That is possible
because every block ends in `true` (`exists_blockEnc`), so the end of the data can be found.
-/

namespace DiagonaLean.Foundations.Computability

/-- The states of the cleanup stage. -/
inductive CS where
  | s0 | lft | toD | toR | trim | home
  deriving DecidableEq

instance : Fintype CS :=
  ⟨{.s0, .lft, .toD, .toR, .trim, .home}, by intro x; cases x <;> simp⟩

open Turing PartrecToTM2 ToPartrec StateTransition Function

/-! ### Steps on `tq` tapes, for any machine -/

section steps

open Cslib.Turing

variable {T : SingleTapeTM Bool}

theorem g_step {q : T.State} {t : BiTape Bool} {stmt : SingleTapeTM.Stmt Bool}
    {q' : Option T.State} (h : T.tr q t.head = (stmt, q')) {c' : T.Cfg}
    (hc : c' = (⟨q', (t.write stmt.symbol).optionMove stmt.movement⟩ : T.Cfg)) :
    T.TransitionRelation (⟨some q, t⟩ : T.Cfg) c' := by
  subst hc
  show (match T.tr q t.head with
    | (⟨wr, dir⟩, q'') => some (⟨q'', (t.write wr).optionMove dir⟩ : T.Cfg)) = _
  rw [h]

theorem g_right {q : T.State} {q' : Option T.State} {L C : List (Option Bool)} {x : Option Bool}
    (h : T.tr q (C.headD none) = (⟨x, some .right⟩, q')) :
    T.TransitionRelation (⟨some q, tq L C⟩ : T.Cfg) (⟨q', tq (x :: L) C.tail⟩ : T.Cfg) := by
  refine g_step h ?_
  show _ = (⟨q', ((tq L C).write x).optionMove (some .right)⟩ : T.Cfg)
  rw [tq_right]

theorem g_left {q : T.State} {q' : Option T.State} {L C : List (Option Bool)} {x : Option Bool}
    (h : T.tr q (C.headD none) = (⟨x, some .left⟩, q')) :
    T.TransitionRelation (⟨some q, tq L C⟩ : T.Cfg)
      (⟨q', tq L.tail (L.headD none :: x :: C.tail)⟩ : T.Cfg) := by
  refine g_step h ?_
  show _ = (⟨q', ((tq L C).write x).optionMove (some .left)⟩ : T.Cfg)
  rw [tq_left]

theorem g_stay {q : T.State} {q' : Option T.State} {L C : List (Option Bool)} {x : Option Bool}
    (h : T.tr q (C.headD none) = (⟨x, none⟩, q')) :
    T.TransitionRelation (⟨some q, tq L C⟩ : T.Cfg) (⟨q', tq L (x :: C.tail)⟩ : T.Cfg) :=
  g_step h rfl

theorem g_walk_right {q : T.State} (h : ∀ x, T.tr q (some x) = (⟨some x, some .right⟩, some q))
    (X : List Bool) (L C : List (Option Bool)) :
    Relation.ReflTransGen T.TransitionRelation (⟨some q, tq L (sm X ++ C)⟩ : T.Cfg)
      (⟨some q, tq (sm X.reverse ++ L) C⟩ : T.Cfg) := by
  induction X generalizing L with
  | nil => exact .refl
  | cons x X ih =>
    refine .head (g_right (x := some x) (q' := some q) (h x)) ?_
    have e : sm (x :: X).reverse ++ L = sm X.reverse ++ some x :: L := by simp
    rw [e]
    exact ih (some x :: L)

theorem g_walk_left {q : T.State} (h : ∀ x, T.tr q (some x) = (⟨some x, some .left⟩, some q))
    (X : List Bool) (y : Bool) (L C : List (Option Bool)) :
    Relation.ReflTransGen T.TransitionRelation
      (⟨some q, tq (sm X ++ none :: L) (some y :: C)⟩ : T.Cfg)
      (⟨some q, tq L (none :: sm (X.reverse ++ [y]) ++ C)⟩ : T.Cfg) := by
  induction X generalizing y C with
  | nil => exact .single (g_left (x := some y) (q' := some q) (h y))
  | cons x X ih =>
    refine .head (g_left (x := some y) (q' := some q) (h y)) ?_
    have e : none :: sm ((x :: X).reverse ++ [y]) ++ C =
        none :: sm (X.reverse ++ [x]) ++ some y :: C := by simp
    rw [e]
    exact ih x (some y :: C)

end steps

/-! ### The cleanup stage -/

/-- Erase stray cells on the left, find the data, erase stray cells on the right, and return to the
first cell. -/
def cleanTr : CS → Option Bool → Cslib.Turing.SingleTapeTM.Stmt Bool × Option CS
  | .s0, h => (⟨h, some .left⟩, some .lft)
  | .lft, some _ => (⟨none, some .left⟩, some .lft)
  | .lft, none => (⟨none, some .right⟩, some .toD)
  | .toD, none => (⟨none, some .right⟩, some .toD)
  | .toD, some x => (⟨some x, none⟩, some .toR)
  | .toR, some x => (⟨some x, some .right⟩, some .toR)
  | .toR, none => (⟨none, some .left⟩, some .trim)
  | .trim, some false => (⟨none, some .left⟩, some .trim)
  | .trim, some true => (⟨some true, none⟩, some .home)
  | .trim, none => (⟨none, none⟩, none)
  | .home, some x => (⟨some x, some .left⟩, some .home)
  | .home, none => (⟨none, some .right⟩, none)

section clean

open Cslib.Turing

variable {Λ : Type} [Inhabited Λ] {M : TM0.Machine Bool Λ} {S : Finset Λ}
  {hS : TM0.Supports M (S : Set Λ)} {enter : Λ → CS}

/-- The machine with this cleanup stage. -/
abbrev WC (M : TM0.Machine Bool Λ) (S : Finset Λ) (hS : TM0.Supports M (S : Set Λ))
    (enter : Λ → CS) : SingleTapeTM Bool := wrapG M S hS enter cleanTr

/-- A configuration in the cleanup stage. -/
abbrev cg (M : TM0.Machine Bool Λ) (S : Finset Λ) (hS : TM0.Supports M (S : Set Λ))
    (enter : Λ → CS) (s : CS) (L C : List (Option Bool)) : (WC M S hS enter).Cfg :=
  (⟨some (.inr s), tq L C⟩ : (WC M S hS enter).Cfg)

/-- Reachability in the machine. -/
abbrev RC (M : TM0.Machine Bool Λ) (S : Finset Λ) (hS : TM0.Supports M (S : Set Λ))
    (enter : Λ → CS) (x y : (WC M S hS enter).Cfg) : Prop :=
  Relation.ReflTransGen (WC M S hS enter).TransitionRelation x y

theorem lft_run (u : ℕ) (Z : List (Option Bool)) :
    RC M S hS enter
      (cg M S hS enter .lft (sm (List.replicate u false)).tail
        ((sm (List.replicate u false)).headD none :: Z))
      (cg M S hS enter .lft [] (none :: List.replicate u none ++ Z)) := by
  induction u generalizing Z with
  | zero => exact .refl
  | succ u ih =>
    have e : sm (List.replicate (u + 1) false) = some false :: sm (List.replicate u false) := by
      simp [List.replicate_succ]
    rw [e]
    refine .head (g_left (T := WC M S hS enter) (x := none) (q' := some (.inr .lft)) rfl) ?_
    have e₂ : none :: List.replicate (u + 1) none ++ Z =
        none :: List.replicate u none ++ none :: Z := by
      simp [List.replicate_succ']
    rw [e₂]
    exact ih (none :: Z)

theorem toD_run (u : ℕ) (L Y : List (Option Bool)) :
    RC M S hS enter (cg M S hS enter .toD L (List.replicate u none ++ Y))
      (cg M S hS enter .toD (List.replicate u none ++ L) Y) := by
  induction u generalizing L with
  | zero => exact .refl
  | succ u ih =>
    refine .head (g_right (T := WC M S hS enter) (x := none) (q' := some (.inr .toD)) rfl) ?_
    have e : List.replicate (u + 1) none ++ L = List.replicate u none ++ none :: L := by
      simp [List.replicate_succ']
    rw [e]
    exact ih (none :: L)

theorem trim_run (j : ℕ) (A Y : List (Option Bool)) :
    RC M S hS enter
      (cg M S hS enter .trim (sm (List.replicate j false) ++ some true :: A).tail
        ((sm (List.replicate j false) ++ some true :: A).headD none :: Y))
      (cg M S hS enter .trim A (some true :: List.replicate j none ++ Y)) := by
  induction j generalizing Y with
  | zero => exact .refl
  | succ j ih =>
    have e : sm (List.replicate (j + 1) false) ++ some true :: A =
        some false :: (sm (List.replicate j false) ++ some true :: A) := by
      simp [List.replicate_succ]
    rw [e]
    refine .head (g_left (T := WC M S hS enter) (x := none) (q' := some (.inr .trim)) rfl) ?_
    have e₂ : some true :: List.replicate (j + 1) none ++ Y =
        some true :: List.replicate j none ++ none :: Y := by
      simp [List.replicate_succ']
    rw [e₂]
    exact ih (none :: Y)

theorem stk_append_nones (X : List (Option Bool)) {Y : List (Option Bool)}
    (hY : ∀ y ∈ Y, y = none) : stk (X ++ Y) = stk X := by
  induction X with
  | nil => exact stk_nones hY
  | cons x X ih => simp only [List.cons_append, stk_cons, ih]

theorem tq_final' {L Y : List (Option Bool)} (hL : ∀ x ∈ L, x = none) (hY : ∀ y ∈ Y, y = none)
    (d : Bool) (D : List Bool) : tq L (sm (d :: D) ++ Y) = BiTape.mk₁ (d :: D) := by
  simp only [tq, stk_nones hL, List.map_cons, List.cons_append, List.headD_cons, List.tail_cons,
    stk_append_nones _ hY, stk_map_some]
  rfl

/-- **The cleanup stage.** Stray `false` cells on both sides are removed. -/
theorem clean_run (u j : ℕ) (d : Bool) (D X₀ : List Bool) (hX : (d :: D).reverse = true :: X₀) :
    RC M S hS enter
      (cg M S hS enter .s0 (sm (List.replicate u false)) (sm ((d :: D) ++ List.replicate j false)))
      ((WC M S hS enter).haltCfg (d :: D)) := by
  have e₀ : sm ((d :: D) ++ List.replicate j false) =
      some d :: sm (D ++ List.replicate j false) := by simp
  rw [e₀]
  set Zr := sm (D ++ List.replicate j false) with hZr
  refine .head (g_left (T := WC M S hS enter) (x := some d) (q' := some (.inr .lft)) rfl) ?_
  refine (lft_run u (some d :: Zr)).trans ?_
  refine .head (g_right (T := WC M S hS enter) (x := none) (q' := some (.inr .toD)) rfl) ?_
  refine (toD_run u [none] (some d :: Zr)).trans ?_
  refine .head (g_stay (T := WC M S hS enter) (x := some d) (q' := some (.inr .toR)) rfl) ?_
  have hL₁ : List.replicate u none ++ [none] = none :: List.replicate u (none : Option Bool) := by
    rw [← List.replicate_succ', List.replicate_succ]
  rw [hL₁]
  have hC : some d :: Zr = sm ((d :: D) ++ List.replicate j false) ++ [] := by
    rw [List.append_nil, e₀]
  have hw := g_walk_right (T := WC M S hS enter) (q := .inr .toR) (fun x => rfl)
    ((d :: D) ++ List.replicate j false) (none :: List.replicate u none) []
  have hC₂ : (some d :: Zr).tail = Zr := rfl
  simp only [List.tail_cons]
  rw [hC]
  refine hw.trans ?_
  refine .head (g_left (T := WC M S hS enter) (x := none) (q' := some (.inr .trim)) rfl) ?_
  have hrev : sm ((d :: D) ++ List.replicate j false).reverse ++ none :: List.replicate u none =
      sm (List.replicate j false) ++ some true :: (sm X₀ ++ none :: List.replicate u none) := by
    rw [List.reverse_append, hX, List.reverse_replicate]
    simp
  rw [hrev]
  refine (trim_run j (sm X₀ ++ none :: List.replicate u none) [none]).trans ?_
  refine .head (g_stay (T := WC M S hS enter) (x := some true) (q' := some (.inr .home)) rfl) ?_
  have hwl := g_walk_left (T := WC M S hS enter) (q := .inr .home) (fun x => rfl) X₀ true
    (List.replicate u none) (List.replicate j none ++ [none])
  refine hwl.trans ?_
  have hdata : X₀.reverse ++ [true] = d :: D := by
    have := congrArg List.reverse hX
    simpa using this.symm
  rw [hdata]
  refine .single ?_
  have hstep := g_right (T := WC M S hS enter) (q := .inr .home) (q' := none)
    (L := List.replicate u none)
    (C := none :: sm (d :: D) ++ (List.replicate j none ++ [none])) (x := none) rfl
  have hfinal : tq (none :: List.replicate u none) (sm (d :: D) ++ (List.replicate j none ++ [none]))
      = BiTape.mk₁ (d :: D) := by
    refine tq_final' ?_ ?_ d D
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · exact List.eq_of_mem_replicate hx
    · intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact List.eq_of_mem_replicate hy
      · simpa using hy
  have : (⟨none, tq (none :: List.replicate u none)
      (none :: sm (d :: D) ++ (List.replicate j none ++ [none])).tail⟩ : (WC M S hS enter).Cfg) =
      (WC M S hS enter).haltCfg (d :: D) := by
    show (⟨none, tq (none :: List.replicate u none)
      (sm (d :: D) ++ (List.replicate j none ++ [none]))⟩ : (WC M S hS enter).Cfg) = _
    rw [hfinal]
    rfl
  rwa [this] at hstep

end clean

/-! ### Tapes up to blanks -/

theorem mk_eq_of_last {X Y : List Bool} {Y₀ : List Bool} (h : Y.reverse = true :: Y₀)
    (he : (ListBlank.mk X : ListBlank Bool) = ListBlank.mk Y) :
    ∃ j, X = Y ++ List.replicate j false := by
  rcases Quotient.exact he with ⟨n, hn⟩ | ⟨n, hn⟩
  · have hn' : Y = X ++ List.replicate n false := hn
    rcases n with _ | n
    · exact ⟨0, by simpa using hn'.symm⟩
    · exfalso
      rw [hn', List.reverse_append, List.reverse_replicate, List.replicate_succ] at h
      simp at h
  · exact ⟨n, hn⟩

theorem mk_nil_eq {L : List Bool} (he : (ListBlank.mk L : ListBlank Bool) = ListBlank.mk []) :
    ∃ u, L = List.replicate u false := by
  rcases Quotient.exact he with ⟨n, hn⟩ | ⟨n, hn⟩
  · have hn' : ([] : List Bool) = L ++ List.replicate n false := hn
    exact ⟨0, by simpa using (List.append_eq_nil_iff.1 hn'.symm).1⟩
  · exact ⟨n, hn⟩

theorem tape_shape {data D₀ : List Bool} (hd : data.reverse = true :: D₀) {h : Option Bool}
    {L R : List Bool} (he : (Tape.mk₁ data : Tape Bool) = ab h L R) :
    ∃ u j, L = List.replicate u false ∧ h.getD false :: R = data ++ List.replicate j false := by
  have hL : (ListBlank.mk [] : ListBlank Bool) = ListBlank.mk L := congrArg Tape.left he
  have hR := congrArg Tape.right₀ he
  rw [Tape.mk₁, Tape.mk₂, Tape.mk'_right₀] at hR
  have hR' : (ListBlank.mk data : ListBlank Bool) = ListBlank.mk (h.getD false :: R) := by
    rw [hR]
    simp [Tape.right₀, ab, ListBlank.cons_mk]
  obtain ⟨u, hu⟩ := mk_nil_eq hL.symm
  obtain ⟨j, hj⟩ := mk_eq_of_last hd hR'.symm
  exact ⟨u, j, hu, hj⟩

/-! ### Blocks ending in `true` -/

theorem cell_ne_default (a : Γ') : cell false a ≠ (default : Γ2) := fun h => by
  have := congrFun (congrArg Prod.snd h) K'.main
  simp [cell] at this

theorem cell_true_ne_default (a : Γ') : cell true a ≠ (default : Γ2) := fun h => by
  have := congrArg Prod.fst h
  simp [cell] at this

/-- A block encoding of `Γ2`: the blank block is all `false`, every other block ends in `true`, and
the first bit of a digit block is the digit. -/
theorem exists_blockEnc :
    ∃ (k : ℕ) (enc : Γ2 → List.Vector Bool (k + 2)) (dec : List.Vector Bool (k + 2) → Γ2),
      enc default = List.Vector.replicate (k + 2) false ∧ (∀ a, dec (enc a) = a) ∧
      (∀ a, a ≠ default → ∃ X, (enc a).toList.reverse = true :: X) ∧
      (∃ r, (enc (cell false .bit0)).toList = false :: r) ∧
      (∃ r, (enc (cell false .bit1)).toList = true :: r) := by
  classical
  obtain ⟨k, e, d, -, ed⟩ := TM1to1.exists_enc_dec (Γ := Γ2)
  have hbits : cell false Γ'.bit0 ≠ cell false Γ'.bit1 := fun h => by
    have := congrFun (congrArg Prod.snd h) K'.main
    simp [cell] at this
  let mid : Γ2 → List Bool := fun a => decide (a = cell false .bit1) :: ((e a).toList ++ [true])
  have hmid : ∀ a, (mid a).length = k + 2 := fun a => by simp [mid]
  let enc : Γ2 → List.Vector Bool (k + 2) := fun a =>
    if a = default then List.Vector.replicate (k + 2) false else ⟨mid a, hmid a⟩
  let dec : List.Vector Bool (k + 2) → Γ2 := fun v =>
    if h : v.toList.getLast? = some true then
      d ⟨v.toList.tail.dropLast, by simp [List.Vector.toList_length]⟩
    else default
  refine ⟨k, enc, dec, by simp [enc], fun a => ?_, fun a ha => ?_,
    ⟨(e (cell false .bit0)).toList ++ [true], ?_⟩, ⟨(e (cell false .bit1)).toList ++ [true], ?_⟩⟩
  · by_cases ha : a = default
    · subst ha
      have : ¬ (List.Vector.replicate (k + 2) false).toList.getLast? = some true := by
        simp [List.Vector.toList, List.Vector.replicate, List.getLast?_replicate]
      show dec (enc default) = default
      rw [show enc default = List.Vector.replicate (k + 2) false from if_pos rfl]
      exact dif_neg this
    · have h₁ : (enc a).toList = mid a := by simp [enc, ha, List.Vector.toList]
      have h₂ : (enc a).toList.getLast? = some true := by
        rw [h₁, List.getLast?_eq_some_iff]
        exact ⟨decide (a = cell false .bit1) :: (e a).toList, rfl⟩
      have h₃ : (enc a).toList.tail.dropLast = (e a).toList := by rw [h₁]; simp [mid]
      simp only [dec, h₂, dite_true]
      have : (⟨(enc a).toList.tail.dropLast, by simp [List.Vector.toList_length]⟩ :
          List.Vector Bool k) = e a := Subtype.ext h₃
      rw [this, ed]
  · refine ⟨((e a).toList.reverse ++ [decide (a = cell false .bit1)]), ?_⟩
    have : (enc a).toList = mid a := by simp [enc, ha, List.Vector.toList]
    rw [this]
    simp [mid]
  · have : (enc (cell false .bit0)).toList = mid (cell false .bit0) := by
      simp [enc, cell_ne_default, List.Vector.toList]
    rw [this]
    simp [mid, hbits]
  · have : (enc (cell false .bit1)).toList = mid (cell false .bit1) := by
      simp [enc, cell_ne_default, List.Vector.toList]
    rw [this]
    simp [mid]

/-- The Bool tape of a list of nonblank cells ends in `true`. -/
theorem flat_last {k : ℕ} {enc : Γ2 → List.Vector Bool k}
    (he : ∀ a, a ≠ default → ∃ X, (enc a).toList.reverse = true :: X) (c : Γ2) (cs : List Γ2)
    (hc : ∀ x ∈ c :: cs, x ≠ default) :
    ∃ X, ((c :: cs).flatMap fun x => (enc x).toList).reverse = true :: X := by
  induction cs generalizing c with
  | nil =>
    obtain ⟨X, hX⟩ := he c (hc c List.mem_cons_self)
    exact ⟨X, by simpa using hX⟩
  | cons x cs ih =>
    obtain ⟨X, hX⟩ := ih x fun y hy => hc y (List.mem_cons_of_mem _ hy)
    refine ⟨X ++ (enc c).toList.reverse, ?_⟩
    rw [List.flatMap_cons, List.reverse_append, hX]
    rfl

/-- A partial recursive function, as a machine with a full output. -/
theorem exists_compiled (g : ℕ →. ℕ) (hg : Partrec g) :
    ∃ (W : Cslib.Turing.SingleTapeTM Bool) (k : ℕ) (e₀ : List Bool) (e : Γ' → List Bool)
      (r0 r1 : List Bool),
      e₀.length = k + 2 ∧ e .bit0 = false :: r0 ∧ r0.length = k + 1 ∧
      e .bit1 = true :: r1 ∧ r1.length = k + 1 ∧
      ∀ n m, m ∈ g n → W.Outputs (e₀ ++ (trNat n).reverse.flatMap e)
        (e₀ ++ (trNat m).reverse.flatMap e) := by
  classical
  obtain ⟨uc, huc⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.2 hg)
  obtain ⟨k, enc, dec, enc0, encdec, hlast, ⟨r0, hr0⟩, ⟨r1, hr1⟩⟩ := exists_blockEnc
  let M2 := tr2 uc
  let M1 := TM2to1.tr M2
  let Mb := TM1to1.tr enc dec M1
  let M0 := TM1to0.tr Mb
  have s1 := TM2to1.tr_supports M2 (supports2 uc)
  have sb := TM1to1.tr_supports (enc := enc) (dec := dec) M1 s1
  have s0 := TM1to0.tr_supports Mb sb
  have hlen : ∀ a, (enc a).toList.length = k + 2 := fun a => List.Vector.toList_length _
  refine ⟨wrapG M0 _ s0 (fun _ => CS.s0) cleanTr, k, (enc (cell true Γ'.cons)).toList,
    fun a => (enc (cell false a)).toList, r0, r1, hlen _, hr0, ?_, hr1, ?_, fun n m hm => ?_⟩
  · have := hlen (cell false .bit0)
    rw [hr0] at this
    simpa using this
  · have := hlen (cell false .bit1)
    rw [hr1] at this
    simpa using this
  have hv : [m] ∈ uc.eval [n] := by
    have h := huc ⟨[n], rfl⟩
    have h' : uc.eval [n] = pure <$> g n := h
    rw [h']
    exact (Part.mem_map_iff _).2 ⟨m, hm, rfl⟩
  have h2 := tr2_eval uc hv
  obtain ⟨b₁, hb₁, hb₁e⟩ := StateTransition.tr_eval (TM2to1.tr_respects M2)
    (TM2to1.trCfg_init K'.main (trList [n])) h2
  obtain ⟨b₂, hb₂, hb₂e⟩ := StateTransition.tr_eval (TM1to1.tr_respects dec M1 encdec (enc0 := enc0))
    (a₂ := (TM1.init ((TM2to1.trInit K'.main (trList [n])).flatMap fun x => (enc x).toList) :
      TM1.Cfg Bool (TM1to1.Λ' Γ2 _ _) _))
    (by simp only [TM1to1.trCfg, TM1.init, trTape_mk₁]; rfl) hb₁e
  obtain ⟨b₃, hb₃, hb₃e⟩ := StateTransition.tr_eval (TM1to0.tr_respects Mb)
    (a₂ := (TM0.init ((TM2to1.trInit K'.main (trList [n])).flatMap fun x => (enc x).toList) :
      TM0.Cfg Bool (TM1to0.Λ' Mb))) rfl hb₂e
  -- the final tape is the initial tape of `m`
  have hfin : b₁.Tape = Tape.mk₁ (TM2to1.trInit K'.main (trList [m])) := by
    have hi := TM2to1.trCfg_init (K := K') (Γ := fun _ => Γ') (Λ := L2 uc) (σ := Option Γ')
      K'.main (trList [m])
    generalize hinit : (TM1.init (TM2to1.trInit K'.main (trList [m])) :
      TM1.Cfg Γ2 (TM2to1.Λ' K' (fun _ => Γ') (L2 uc) (Option Γ')) (Option Γ')) = c₀ at hi
    have hc₀ : c₀.Tape = Tape.mk₁ (TM2to1.trInit K'.main (trList [m])) := by
      rw [← hinit]
      rfl
    rw [← hc₀]
    cases hb₁ with
    | mk L hL =>
      generalize hx : (TM2.init K'.main (trList [m]) : Cf2 (L2 uc)) = x at hi
      cases hi with
      | mk L' hL' =>
        have hstk : ∀ k, (K'.elim (trList [m]) [] [] []) k =
            (update (fun _ => ([] : List Γ')) K'.main (trList [m])) k := by
          intro k
          cases k <;> rfl
        have hxs := fun k => (congrFun (congrArg TM2.Cfg.stk hx) k).symm
        have hLL : L = L' := by
          refine ListBlank.ext fun i => funext fun k => ?_
          rw [TM2to1.stk_nth_val i (hL k), TM2to1.stk_nth_val i (hL' k)]
          have h₁ := hstk k
          have h₂ := hxs k
          exact congrArg (fun z => z.reverse[i]?) (h₁.trans h₂.symm)
        subst hLL
        rfl
  have hb₃T : b₃.Tape = Tape.mk₁ ((TM2to1.trInit K'.main (trList [m])).flatMap
      fun x => (enc x).toList) := by
    subst hb₂
    subst hb₃
    show TM1to1.trTape enc0 b₁.Tape = _
    rw [hfin, trTape_mk₁]
  obtain ⟨h, L, R, hr, hT⟩ := wrapG_reach M0 _ s0 (fun _ => CS.s0) cleanTr hb₃e
  have hflat : ∀ t, (TM2to1.trInit K'.main (trList [t])).flatMap (fun x => (enc x).toList) =
      (enc (cell true Γ'.cons)).toList ++ (trNat t).reverse.flatMap
        fun a => (enc (cell false a)).toList := by
    intro t
    rw [trInit_eq, List.flatMap_cons, List.flatMap_map]
  obtain ⟨X, hX⟩ : ∃ X, ((TM2to1.trInit K'.main (trList [m])).flatMap
      fun x => (enc x).toList).reverse = true :: X := by
    rw [trInit_eq]
    refine flat_last hlast _ _ fun x hx => ?_
    rcases List.mem_cons.1 hx with rfl | hx
    · exact cell_true_ne_default _
    · obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx
      exact cell_ne_default a
  rw [hb₃T] at hT
  obtain ⟨u, j, rfl, hj⟩ := tape_shape hX hT
  rw [hflat m] at hX hj
  rw [hflat n] at hr
  generalize (enc (cell true Γ'.cons)).toList ++ (trNat m).reverse.flatMap
    (fun a => (enc (cell false a)).toList) = data at hX hj ⊢
  cases data with
  | nil => simp at hX
  | cons d D =>
    have htp : tp (some (h.getD false)) (List.replicate u false) R =
        tq (sm (List.replicate u false)) (sm ((d :: D) ++ List.replicate j false)) := by
      rw [← hj]
      simp only [tp, tq, List.map_cons, List.headD_cons, List.tail_cons, stk_map_some]
    rw [htp] at hr
    exact hr.trans (clean_run (M := M0) (hS := s0) (enter := fun _ => CS.s0) u j d D X hX)

end DiagonaLean.Foundations.Computability
