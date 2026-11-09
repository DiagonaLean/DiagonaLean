/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

@[expose] public section

/-! # List-level configurations of Cslib machines

Cell lists may carry trailing blanks, and decode to Cslib's canonical `StackTape`s through `stk`.
So every step of a machine is a local rewrite next to the head, including at the tape ends.

## Main statements

* `Data`, `dstep`: the list-level configuration and step.
* `step_cfgOf`: `dstep` implements `SingleTapeTM.step` on running configurations.
* `exists_iterate_of_reflTransGen`: every Cslib run is a `dstep` iteration.
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing

variable {Sym : Type} [Inhabited Sym] [Fintype Sym] (M : SingleTapeTM Sym)

/-- A list-level configuration: state (`none` = halted), left cells (nearest first), head
symbol, right cells (nearest first). -/
structure Data where
  state : Option M.State
  l : List (Option Sym)
  h : Option Sym
  r : List (Option Sym)

variable {M}

/-- `d` is not halted. -/
def Data.Running (d : Data M) : Prop := d.state.isSome

instance : DecidablePred (Data.Running (M := M)) :=
  fun d => inferInstanceAs (Decidable (d.state.isSome = true))

variable (M) in
/-- The list-level step. -/
def dstep : Data M → Data M
  | ⟨none, l, h, r⟩ => ⟨none, l, h, r⟩
  | ⟨some q, l, h, r⟩ =>
    match M.tr q h with
    | (⟨wr, none⟩, q') => ⟨q', l, wr, r⟩
    | (⟨wr, some .right⟩, q') =>
      match r with
      | [] => ⟨q', wr :: l, none, []⟩
      | r₁ :: r' => ⟨q', wr :: l, r₁, r'⟩
    | (⟨wr, some .left⟩, q') =>
      match l with
      | [] => ⟨q', [], none, wr :: r⟩
      | l₁ :: l' => ⟨q', l', l₁, wr :: r⟩

/-! ### Decoding to Cslib configurations -/

/-- Decode a cell list to a canonical `StackTape`. -/
def stk (a : List (Option Sym)) : StackTape Sym := a.foldr StackTape.cons StackTape.nil

omit [Inhabited Sym] [Fintype Sym] in
@[simp] theorem stk_nil : stk ([] : List (Option Sym)) = StackTape.nil := rfl
omit [Inhabited Sym] [Fintype Sym] in
@[simp] theorem stk_cons (o : Option Sym) (a : List (Option Sym)) :
    stk (o :: a) = StackTape.cons o (stk a) := rfl

/-- The Cslib configuration of `d`. -/
def cfgOf (d : Data M) : M.Cfg := ⟨d.state, ⟨d.h, stk d.l, stk d.r⟩⟩

omit [Inhabited Sym] [Fintype Sym] in
theorem nil_head : (StackTape.nil : StackTape Sym).head = none := rfl
omit [Inhabited Sym] [Fintype Sym] in
theorem nil_tail : (StackTape.nil : StackTape Sym).tail = StackTape.nil := rfl

/-- **Simulation.** `dstep` implements `SingleTapeTM.step`. -/
theorem step_cfgOf (d : Data M) (hd : d.Running) : M.step (cfgOf d) = some (cfgOf (dstep M d)) := by
  obtain ⟨_ | q, l, h, r⟩ := d
  · exact absurd hd (by simp [Data.Running])
  · simp only [cfgOf, SingleTapeTM.step, dstep]
    rcases htr : M.tr q h with ⟨⟨wr, _ | _ | _⟩, q'⟩
    · simp [htr, BiTape.optionMove, BiTape.write]
    · cases l <;>
        simp [htr, BiTape.optionMove, BiTape.write, BiTape.move, BiTape.moveLeft, nil_head, nil_tail]
    · cases r <;>
        simp [htr, BiTape.optionMove, BiTape.write, BiTape.move, BiTape.moveRight, nil_head,
          nil_tail]

theorem step_cfgOf_halted (d : Data M) (hd : ¬ d.Running) : M.step (cfgOf d) = none := by
  obtain ⟨_ | q, l, h, r⟩ := d
  · rfl
  · exact absurd rfl hd

theorem dstep_halted (d : Data M) (hd : ¬ d.Running) : dstep M d = d := by
  obtain ⟨_ | q, l, h, r⟩ := d
  · rfl
  · exact absurd rfl hd

theorem iterate_halted (d : Data M) (hd : ¬ d.Running) (n : ℕ) : (dstep M)^[n] d = d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, dstep_halted d hd, ih]

/-- **Runs are iterations.** A Cslib run from `cfgOf d` passes only through `dstep`-iterates. -/
theorem exists_iterate_of_reflTransGen (d : Data M) {c : M.Cfg}
    (h : Relation.ReflTransGen M.TransitionRelation (cfgOf d) c) :
    ∃ n, cfgOf ((dstep M)^[n] d) = c := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    have hbc' : M.step _ = some _ := hbc
    have hrun : ((dstep M)^[n] d).Running := by
      by_contra hr
      have := step_cfgOf_halted _ hr
      rw [hn, hbc'] at this
      cases this
    have := step_cfgOf _ hrun
    rw [hn, hbc'] at this
    rw [Function.iterate_succ_apply']
    exact (Option.some.inj this).symm

/-- The list-level initial configuration on `input`. -/
def initData (input : List Sym) : Data M :=
  match input with
  | [] => ⟨some M.q₀, [], none, []⟩
  | a :: t => ⟨some M.q₀, [], some a, t.map some⟩

omit [Inhabited Sym] [Fintype Sym] in
theorem stk_map_some (t : List Sym) : stk (t.map some) = StackTape.mapSome t := by
  induction t with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, stk_cons, ih]; rfl

theorem cfgOf_initData (input : List Sym) : cfgOf (initData input : Data M) = M.initCfg input := by
  cases input with
  | nil => rfl
  | cons a t =>
    simp only [cfgOf, initData, SingleTapeTM.initCfg, BiTape.mk₁, stk_map_some]
    rfl

end DiagonaLean.Foundations.Computability
