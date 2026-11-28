/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Mathlib.Data.Fintype.Basic
import DiagonaLean.Halt.Basic
import DiagonaLean.Foundations.Computability.Normalize.Conditions

@[expose] public section

/-! # List machines

A list machine has a finite set of states `Q`, tape symbols `Γ` with a blank, and a transition
function `δ : Q → Γ → Act Q Γ`. A configuration is a state, the cells left of the head (nearest
first), the head cell, and the cells right of the head (nearest first) (`Cfg`, `next`, `Halts`).

A single-tape machine that never writes a blank (`NoBlankWrites`) is a list machine: its cells left
and right of the head are the lists of its two stacks (`cfgOf`, `next_cfgOf`). When it also never
moves left at the left end of its tape (`NoLeftBoundary`), it halts on `w` iff its list machine
halts from the initial configuration (`halts_iff`). `enumAll` lists the elements of a finite type
with an encoding, computably.

Renaming the states of a list machine keeps halting (`halts_mapCfg_iff`), and two machines that
agree on a set of states closed under steps halt together from it (`halts_congr`).
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing SingleTapeTM Relation DiagonaLean.Foundations.Computability.Normalize

/-! ### Stacks -/

section Stacks

variable {Symbol : Type}

/-- In the non-degenerate case, `StackTape.cons` does not strip blanks. -/
theorem cons_toList_of_nondeg (w : Option Symbol) (xs : StackTape Symbol)
    (h : w ≠ none ∨ xs.toList ≠ []) :
    (StackTape.cons w xs).toList = w :: xs.toList := by
  obtain ⟨tl, hLast⟩ := xs
  cases tl with
  | nil => cases w with
    | none => rcases h with h | h <;> exact absurd rfl h
    | some s => rfl
  | cons hd tl' => cases w with | none => rfl | some _ => rfl

/-- For a non-empty `StackTape`, `head :: tail.toList = toList`. -/
theorem head_cons_tail_toList (xs : StackTape Symbol) (h : xs.toList ≠ []) :
    xs.head :: xs.tail.toList = xs.toList := by
  obtain ⟨tl, hLast⟩ := xs
  cases tl with | nil => exact absurd rfl h | cons a rest => rfl

/-- The head of a stack is the first cell of its list, or the blank. -/
theorem stack_head_eq (xs : StackTape Symbol) : xs.head = xs.toList.headD none := by
  obtain ⟨l, h⟩ := xs
  cases l <;> rfl

/-- The tail of a stack is the tail of its list. -/
theorem stack_tail_toList (xs : StackTape Symbol) : xs.tail.toList = xs.toList.tail := by
  obtain ⟨l, h⟩ := xs
  cases l <;> rfl

end Stacks

namespace ListMachine

/-- The elements of a finite type with an encoding, listed by decoding every number up to the
largest code. -/
def enumAll (α : Type) [Fintype α] [Encodable α] : List α :=
  (List.range (Finset.univ.sup (Encodable.encode : α → ℕ) + 1)).filterMap Encodable.decode

/-- `enumAll α` lists every element of `α`. -/
theorem mem_enumAll {α : Type} [Fintype α] [Encodable α] (a : α) : a ∈ enumAll α := by
  simp only [enumAll, List.mem_filterMap, List.mem_range]
  exact ⟨Encodable.encode a,
    Nat.lt_succ_of_le (Finset.le_sup (f := (Encodable.encode : α → ℕ)) (Finset.mem_univ a)),
    Encodable.encodek a⟩

variable {Q Γ : Type}

/-- The outcome of a transition of a list machine: halt, or write a symbol, enter a state and stay,
move right or move left. -/
inductive Act (Q Γ : Type) where
  /-- The machine halts. -/
  | halt
  /-- Write `b`, enter `q`, and stay. -/
  | stay (q : Q) (b : Γ)
  /-- Write `b`, enter `q`, and move right. -/
  | right (q : Q) (b : Γ)
  /-- Write `b`, enter `q`, and move left. -/
  | left (q : Q) (b : Γ)

/-- A configuration of a list machine: the state, the cells left of the head (nearest first), the
head cell, and the cells right of the head (nearest first). -/
structure Cfg (Q Γ : Type) where
  /-- The state. -/
  q : Q
  /-- The cells left of the head, nearest first. -/
  l : List Γ
  /-- The head cell. -/
  c : Γ
  /-- The cells right of the head, nearest first. -/
  r : List Γ

/-- The next configuration, or `none` when the machine halts or moves left at the left end. -/
def next (δ : Q → Γ → Act Q Γ) (bl : Γ) (k : Cfg Q Γ) : Option (Cfg Q Γ) :=
  match δ k.q k.c with
  | .halt => none
  | .stay q b => some ⟨q, k.l, b, k.r⟩
  | .right q b => some ⟨q, b :: k.l, k.r.headD bl, k.r.tail⟩
  | .left q b =>
    match k.l with
    | [] => none
    | d :: l => some ⟨q, l, d, b :: k.r⟩

/-- The machine halts from `k`: it reaches a configuration whose transition is `halt`. -/
def Halts (δ : Q → Γ → Act Q Γ) (bl : Γ) (k : Cfg Q Γ) : Prop :=
  ∃ k', Relation.ReflTransGen (fun a b => next δ bl a = some b) k k' ∧ δ k'.q k'.c = .halt

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- The transition of `tm` in state `q` on the symbol `c`, as a list machine transition. -/
def tmAct (tm : SingleTapeTM Symbol) (q : tm.State) (c : Option Symbol) :
    Act tm.State (Option Symbol) :=
  match (tm.tr q c).2, (tm.tr q c).1.movement with
  | none, _ => .halt
  | some q', none => .stay q' (tm.tr q c).1.symbol
  | some q', some .right => .right q' (tm.tr q c).1.symbol
  | some q', some .left => .left q' (tm.tr q c).1.symbol

/-- The list configuration of a running configuration. -/
def cfgOf (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    Cfg tm.State (Option Symbol) :=
  ⟨q, t.left.toList, t.head, t.right.toList⟩

/-- **A step of a machine that never writes a blank is a step of its list machine**, when it does
not move left at the left end. -/
theorem next_cfgOf {tm : SingleTapeTM Symbol} (h_nbw : NoBlankWrites tm) {q q' : tm.State}
    {t : BiTape Symbol} (hq : (tm.tr q t.head).2 = some q')
    (hl : t.left.toList = [] → (tm.tr q t.head).1.movement ≠ some Turing.Dir.left) :
    next (tmAct tm) none (cfgOf tm q t) =
      some (cfgOf tm q' ((t.write (tm.tr q t.head).1.symbol).optionMove
        (tm.tr q t.head).1.movement)) := by
  have hw : (tm.tr q t.head).1.symbol ≠ none := h_nbw q t.head
  simp only [next, cfgOf, tmAct, hq]
  rcases hm : (tm.tr q t.head).1.movement with _ | _ | _
  · simp [BiTape.optionMove, BiTape.write]
  · simp only [hm] at hl
    cases hlt : t.left.toList with
    | nil => exact absurd rfl (hl hlt)
    | cons d l =>
      simp [BiTape.optionMove, BiTape.move, BiTape.moveLeft, BiTape.write, stack_head_eq,
        stack_tail_toList, hlt, cons_toList_of_nondeg _ _ (Or.inl hw)]
  · simp [BiTape.optionMove, BiTape.move, BiTape.moveRight, BiTape.write, stack_head_eq,
      stack_tail_toList, cons_toList_of_nondeg _ _ (Or.inl hw)]

/-- A halting step of the machine is a halting transition of its list machine. -/
theorem tmAct_eq_halt {tm : SingleTapeTM Symbol} {q : tm.State} {c : Option Symbol} :
    tmAct tm q c = .halt ↔ (tm.tr q c).2 = none := by
  simp only [tmAct]
  rcases h2 : (tm.tr q c).2 with _ | q'
  · simp
  · rcases (tm.tr q c).1.movement with _ | _ | _ <;> simp

/-- A run of the machine from a reachable configuration to a halted one gives a run of the list
machine to a halting transition. -/
theorem halts_of_run {tm : SingleTapeTM Symbol} (h_nbw : NoBlankWrites tm) {w : List Symbol}
    (h_nlb : NoLeftBoundary tm w) {c c' : tm.Cfg} (hrun : ReflTransGen tm.TransitionRelation c c')
    (hc' : c'.state = none) :
    ∀ q t, c = ⟨some q, t⟩ → ReflTransGen tm.TransitionRelation (initCfg tm w) c →
      Halts (tmAct tm) none (cfgOf tm q t) := by
  induction hrun using ReflTransGen.head_induction_on with
  | refl =>
    rintro q t rfl -
    simp at hc'
  | head hstep hrest ih =>
    rename_i c c₁
    rintro q t rfl hreach
    simp only [TransitionRelation, step] at hstep
    rcases hq : (tm.tr q t.head).2 with _ | q'
    · exact ⟨cfgOf tm q t, .refl, tmAct_eq_halt.2 hq⟩
    · rw [hq] at hstep
      cases hstep
      have hl : t.left.toList = [] → (tm.tr q t.head).1.movement ≠ some Turing.Dir.left :=
        h_nlb _ hreach q t rfl
      obtain ⟨k', hk', hhalt⟩ := ih q' _ rfl (hreach.tail (by simp [TransitionRelation, hq]))
      exact ⟨k', .head (next_cfgOf h_nbw hq hl) hk', hhalt⟩

/-- A run of the list machine to a halting transition, from the list configuration of a reachable
configuration, gives a run of the machine to a halted configuration. -/
theorem run_of_halts {tm : SingleTapeTM Symbol} (h_nbw : NoBlankWrites tm) {w : List Symbol}
    (h_nlb : NoLeftBoundary tm w) {k k' : Cfg tm.State (Option Symbol)}
    (hrun : ReflTransGen (fun a b => next (tmAct tm) none a = some b) k k')
    (hk' : tmAct tm k'.q k'.c = .halt) :
    ∀ q t, k = cfgOf tm q t → ReflTransGen tm.TransitionRelation (initCfg tm w) ⟨some q, t⟩ →
      ∃ tape, ReflTransGen tm.TransitionRelation (initCfg tm w) ⟨none, tape⟩ := by
  induction hrun using ReflTransGen.head_induction_on with
  | refl =>
    rintro q t rfl hreach
    have hq : (tm.tr q t.head).2 = none := tmAct_eq_halt.1 hk'
    exact ⟨(t.write (tm.tr q t.head).1.symbol).optionMove (tm.tr q t.head).1.movement,
      hreach.tail (by simp [TransitionRelation, hq])⟩
  | head hstep hrest ih =>
    rename_i k k₁
    rintro q t rfl hreach
    rcases hq : (tm.tr q t.head).2 with _ | q'
    · simp [next, cfgOf, tmAct_eq_halt.2 hq] at hstep
    · have hl : t.left.toList = [] → (tm.tr q t.head).1.movement ≠ some Turing.Dir.left :=
        h_nlb _ hreach q t rfl
      rw [next_cfgOf h_nbw hq hl] at hstep
      cases hstep
      exact ih q' _ rfl (hreach.tail (by simp [TransitionRelation, hq]))

/-- **A machine that never writes a blank and never moves left at the left end halts iff its list
machine halts.** -/
theorem halts_iff {tm : SingleTapeTM Symbol} (h_nbw : NoBlankWrites tm) {w : List Symbol}
    (h_nlb : NoLeftBoundary tm w) :
    DiagonaLean.Halt.Halts tm w ↔
      Halts (tmAct tm) none (cfgOf tm tm.q₀ (BiTape.mk₁ w)) := by
  constructor
  · rintro ⟨tape, hrun⟩
    exact halts_of_run h_nbw h_nlb hrun rfl _ _ rfl .refl
  · rintro ⟨k', hrun, hk'⟩
    exact run_of_halts h_nbw h_nlb hrun hk' _ _ rfl .refl

/-! ### Renaming states -/

section Rename

variable {Q Q' Γ : Type}

/-- `mapAct f a` is the transition `a` with its state renamed by `f`. -/
def mapAct (f : Q → Q') : Act Q Γ → Act Q' Γ
  | .halt => .halt
  | .stay q b => .stay (f q) b
  | .right q b => .right (f q) b
  | .left q b => .left (f q) b

/-- `mapCfg f k` is the configuration `k` with its state renamed by `f`. -/
def mapCfg (f : Q → Q') (k : Cfg Q Γ) : Cfg Q' Γ := ⟨f k.q, k.l, k.c, k.r⟩

variable {f : Q → Q'} {δ : Q → Γ → Act Q Γ} {δ' : Q' → Γ → Act Q' Γ} {bl : Γ}

/-- A renamed transition halts iff the transition does. -/
theorem mapAct_eq_halt {a : Act Q Γ} : mapAct f a = .halt ↔ a = .halt := by
  cases a <;> simp [mapAct]

/-- If `δ'` on renamed states is `δ` renamed, then a step of `δ'` from a renamed configuration is
the renamed step of `δ`. -/
theorem next_mapCfg (h : ∀ q c, δ' (f q) c = mapAct f (δ q c)) (k : Cfg Q Γ) :
    next δ' bl (mapCfg f k) = (next δ bl k).map (mapCfg f) := by
  obtain ⟨q, l, c, r⟩ := k
  simp only [next, mapCfg, h]
  cases δ q c with
  | halt => rfl
  | stay q' b => rfl
  | right q' b => rfl
  | left q' b => cases l <;> rfl

/-- **Renaming states keeps halting.** -/
theorem halts_mapCfg_iff (h : ∀ q c, δ' (f q) c = mapAct f (δ q c)) (k : Cfg Q Γ) :
    Halts δ' bl (mapCfg f k) ↔ Halts δ bl k := by
  constructor
  · rintro ⟨k₁, hreach, hh⟩
    generalize hk : mapCfg f k = a at hreach
    induction hreach using Relation.ReflTransGen.head_induction_on generalizing k with
    | refl =>
      subst hk
      refine ⟨k, Relation.ReflTransGen.refl, ?_⟩
      have := h k.q k.c
      simp only [mapCfg] at hh
      rw [hh] at this
      exact mapAct_eq_halt.mp this.symm
    | head hstep _ ih =>
      subst hk
      rw [next_mapCfg h] at hstep
      obtain ⟨k₂, hk₂, rfl⟩ := Option.map_eq_some_iff.mp hstep
      obtain ⟨k₃, hreach, hh⟩ := ih k₂ rfl
      exact ⟨k₃, Relation.ReflTransGen.head hk₂ hreach, hh⟩
  · rintro ⟨k₁, hreach, hh⟩
    have hlift : Relation.ReflTransGen (fun a b => next δ' bl a = some b) (mapCfg f k)
        (mapCfg f k₁) := by
      clear hh
      induction hreach with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hab ih => exact ih.tail (by rw [next_mapCfg h, hab]; rfl)
    exact ⟨mapCfg f k₁, hlift, by simp only [mapCfg, h, hh, mapAct]⟩

end Rename

/-! ### Machines that agree on a closed set of states -/

section Congr

variable {Q Γ : Type} {δ δ' : Q → Γ → Act Q Γ} {bl : Γ}

/-- Two machines with the same transition at `k` have the same step from `k`. -/
theorem next_congr {k : Cfg Q Γ} (h : δ' k.q k.c = δ k.q k.c) : next δ' bl k = next δ bl k := by
  simp only [next, h]

/-- If `δ'` agrees with `δ` on the states of `S`, and a step of `δ` from a state of `S` leads to a
state of `S`, then a halting run of `δ'` from a state of `S` is a halting run of `δ`. -/
theorem halts_of_agree (S : Q → Prop) (hagree : ∀ q, S q → ∀ c, δ' q c = δ q c)
    (hclosed : ∀ k k' : Cfg Q Γ, S k.q → next δ bl k = some k' → S k'.q) (k : Cfg Q Γ)
    (hk : S k.q) (h : Halts δ' bl k) : Halts δ bl k := by
  obtain ⟨k₁, hreach, hh⟩ := h
  revert hk
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hk
    exact ⟨_, Relation.ReflTransGen.refl, (hagree _ hk _).symm.trans hh⟩
  | head hstep _ ih =>
    intro hk
    rw [next_congr (hagree _ hk _)] at hstep
    obtain ⟨k₃, hr, h3⟩ := ih (hclosed _ _ hk hstep)
    exact ⟨k₃, Relation.ReflTransGen.head hstep hr, h3⟩

/-- **Machines that agree on a closed set of states halt together**: if `δ'` agrees with `δ` on
the states of `S`, and a step of `δ` from a state of `S` leads to a state of `S`, then from a
state of `S` the machine `δ'` halts iff `δ` does. -/
theorem halts_congr (S : Q → Prop) (hagree : ∀ q, S q → ∀ c, δ' q c = δ q c)
    (hclosed : ∀ k k' : Cfg Q Γ, S k.q → next δ bl k = some k' → S k'.q) (k : Cfg Q Γ)
    (hk : S k.q) : Halts δ' bl k ↔ Halts δ bl k :=
  ⟨halts_of_agree S hagree hclosed k hk,
    halts_of_agree S (fun q hq c => (hagree q hq c).symm)
      (fun a b ha hab => hclosed a b ha (by rwa [← next_congr (hagree _ ha _)])) k hk⟩

end Congr

end ListMachine

end DiagonaLean.Foundations.Computability
