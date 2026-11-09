/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.Foundations.Computability.RunAfterWrite
import DiagonaLean.Foundations.Computability.ListConfig
import DiagonaLean.Synthetic.Undecidability

@[expose] public section

/-! # Simulating a machine by a primitive recursive step

`rowsE M` tabulates the transitions of `M` as numbers, and `sstep` runs one step on a numeric
configuration, mirroring `dstep`. So "`M` halts on `w` within `k` steps" is a primitive
recursive test of the numeric data of `(M, w)`.

## Main statements

* `halt_iff_test`: `HaltProblem (M, w)` iff the test succeeds for some `k`.
* `test_prim`: the test is primitive recursive.
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Notation

/-- A numeric configuration: state code, left cells, head symbol, right cells. -/
abbrev SC := ℕ × List ℕ × ℕ × List ℕ

/-- The value of the first entry with the given key. -/
def lookup (rows : List (ℕ × ℕ)) (key : ℕ) : ℕ :=
  rows.foldr (fun r acc => if r.1 = key then r.2 else acc) 0

/-- One numeric step. -/
def sstep (rows : List (ℕ × ℕ)) (c : SC) : SC :=
  if c.1 = 0 then c
  else if rowM (lookup rows (Nat.pair (c.1 - 1) c.2.2.1)) = 0 then
    (rowX (lookup rows (Nat.pair (c.1 - 1) c.2.2.1)), c.2.1,
      rowA (lookup rows (Nat.pair (c.1 - 1) c.2.2.1)), c.2.2.2)
  else if rowM (lookup rows (Nat.pair (c.1 - 1) c.2.2.1)) = 1 then
    (rowX (lookup rows (Nat.pair (c.1 - 1) c.2.2.1)), c.2.1.tail, c.2.1.headI,
      rowA (lookup rows (Nat.pair (c.1 - 1) c.2.2.1)) :: c.2.2.2)
  else
    (rowX (lookup rows (Nat.pair (c.1 - 1) c.2.2.1)),
      rowA (lookup rows (Nat.pair (c.1 - 1) c.2.2.1)) :: c.2.1, c.2.2.2.headI, c.2.2.2.tail)

/-- The machine has halted within `k` steps. -/
def Test (d : List (ℕ × ℕ) × SC) (k : ℕ) : Prop := ((sstep d.1)^[k] d.2).1 = 0

section

variable (M : EncodableTM Bool)

attribute [local instance] EncodableTM.stateEncodable

/-- The row of a transition. -/
def rowT (x : SingleTapeTM.Stmt Bool × Option M.State) : ℕ :=
  mkRow (hc x.1.symbol) (mvc x.1.movement) (qc x.2)

/-- The transition table of `M`, as numbers. -/
def rowsE : List (ℕ × ℕ) :=
  (SingleTapeTM.statesList M).flatMap fun q =>
    syms.map fun o => (Nat.pair (Encodable.encode q) (hc o), rowT M (M.tr q o))

variable {M}

/-- The numeric configuration of `d`. -/
def absD (d : Data M.toSingleTapeTM) : SC := (qc d.state, d.l.map hc, hc d.h, d.r.map hc)

theorem mem_statesList (q : M.State) : q ∈ SingleTapeTM.statesList M := by
  let := M.stateFintype
  simp only [SingleTapeTM.statesList, List.mem_filterMap, List.mem_range]
  exact ⟨Encodable.encode q, Nat.lt_succ_of_le (Finset.le_sup (f := (Encodable.encode : M.State → ℕ))
    (Finset.mem_univ q)), Encodable.encodek q⟩

theorem lookup_eq {rows : List (ℕ × ℕ)} {key val : ℕ} (hm : (key, val) ∈ rows)
    (hu : ∀ kv ∈ rows, kv.1 = key → kv.2 = val) : lookup rows key = val := by
  induction rows with
  | nil => simp at hm
  | cons r rows ih =>
    unfold lookup
    simp only [List.foldr_cons]
    split
    · exact hu r List.mem_cons_self (by assumption)
    · rcases List.mem_cons.1 hm with rfl | hm
      · rename_i h
        exact absurd rfl h
      · exact ih hm fun kv hkv => hu kv (List.mem_cons_of_mem _ hkv)

theorem lookup_rowsE (q : M.State) (h : Option Bool) :
    lookup (rowsE M) (Nat.pair (Encodable.encode q) (hc h)) = rowT M (M.tr q h) := by
  refine lookup_eq ?_ ?_
  · exact List.mem_flatMap.2 ⟨q, mem_statesList q,
      List.mem_map.2 ⟨h, mem_syms h, rfl⟩⟩
  · intro kv hkv hk
    obtain ⟨q', _, hkv⟩ := List.mem_flatMap.1 hkv
    obtain ⟨o, _, rfl⟩ := List.mem_map.1 hkv
    obtain ⟨h₁, h₂⟩ := Nat.pair_eq_pair.1 hk
    obtain rfl := Encodable.encode_injective h₁
    obtain rfl := hc_injective h₂
    rfl

theorem sstep_absD (d : Data M.toSingleTapeTM) :
    sstep (rowsE M) (absD d) = absD (dstep M.toSingleTapeTM d) := by
  obtain ⟨_ | q, l, h, r⟩ := d
  · rfl
  · have hl : lookup (rowsE M) (Nat.pair (Encodable.encode q + 1 - 1) (hc h)) =
        rowT M (M.tr q h) := by
      simpa using lookup_rowsE q h
    have hne : Encodable.encode q + 1 ≠ 0 := Nat.succ_ne_zero _
    simp only [absD, sstep, qc, hne, ite_false, hl]
    rcases htr : M.tr q h with ⟨⟨wr, _ | _ | _⟩, q'⟩
    · simp [rowT, mvc, dstep, htr, absD]
      cases q' <;> rfl
    · cases l <;> simp [rowT, mvc, dstep, htr, absD, hc] <;> cases q' <;> rfl
    · cases r <;> simp [rowT, mvc, dstep, htr, absD, hc] <;> cases q' <;> rfl

theorem iterate_absD (d : Data M.toSingleTapeTM) (k : ℕ) :
    (sstep (rowsE M))^[k] (absD d) = absD ((dstep M.toSingleTapeTM)^[k] d) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, sstep_absD]

theorem reaches_iterate (d : Data M.toSingleTapeTM) (k : ℕ) :
    Relation.ReflTransGen M.toSingleTapeTM.TransitionRelation (cfgOf d)
      (cfgOf ((dstep M.toSingleTapeTM)^[k] d)) := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    by_cases hr : ((dstep M.toSingleTapeTM)^[k] d).Running
    · exact ih.tail (step_cfgOf _ hr)
    · rwa [dstep_halted _ hr]

/-- The data of a `HaltProblem` instance. -/
def dataOf (p : EncodableTM Bool × List Bool) : List (ℕ × ℕ) × SC :=
  (rowsE p.1, absD (initData p.2 : Data p.1.toSingleTapeTM))

/-- **`HaltProblem` is a search.** -/
theorem halt_iff_test (p : EncodableTM Bool × List Bool) :
    HaltProblem p ↔ ∃ k, Test (dataOf p) k := by
  obtain ⟨M, w⟩ := p
  constructor
  · rintro ⟨t, ht⟩
    rw [← cfgOf_initData] at ht
    obtain ⟨k, hk⟩ := exists_iterate_of_reflTransGen _ ht
    refine ⟨k, ?_⟩
    show ((sstep (rowsE M))^[k] (absD (initData w))).1 = 0
    rw [iterate_absD]
    have : ((dstep M.toSingleTapeTM)^[k] (initData w : Data M.toSingleTapeTM)).state = none :=
      congrArg SingleTapeTM.Cfg.state hk
    simp [absD, this, qc]
  · rintro ⟨k, hk⟩
    have hk' : ((sstep (rowsE M))^[k] (absD (initData w))).1 = 0 := hk
    rw [iterate_absD] at hk'
    have hs : ((dstep M.toSingleTapeTM)^[k] (initData w : Data M.toSingleTapeTM)).state = none := by
      rcases hx : ((dstep M.toSingleTapeTM)^[k] (initData w : Data M.toSingleTapeTM)).state with _ | q
      · rfl
      · simp [absD, hx, qc] at hk'
    have hr := reaches_iterate (initData w : Data M.toSingleTapeTM) k
    rw [cfgOf_initData] at hr
    have he : cfgOf ((dstep M.toSingleTapeTM)^[k] (initData w : Data M.toSingleTapeTM)) =
        ⟨none, (cfgOf ((dstep M.toSingleTapeTM)^[k] (initData w : Data M.toSingleTapeTM))).BiTape⟩ := by
      simp only [cfgOf, hs]
    rw [he] at hr
    exact ⟨_, hr⟩

end

/-! ### Primitive recursiveness -/

section Prim

variable {α : Type*} [Primcodable α]

theorem lookup_prim : Primrec fun y : List (ℕ × ℕ) × ℕ => lookup y.1 y.2 := by
  unfold lookup
  have h : Primrec₂ fun (x : List (ℕ × ℕ) × ℕ) (y : (ℕ × ℕ) × ℕ) =>
      if y.1.1 = x.2 then y.1.2 else y.2 := by
    apply Primrec₂.mk
    prim
  exact Primrec.list_foldr Primrec.fst (Primrec.const 0) h

theorem prim_lookup {f : α → List (ℕ × ℕ)} {g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => lookup (f x) (g x) := lookup_prim.comp (hf.pair hg)

end Prim

macro_rules
  | `(tactic| prim_step) => `(tactic| with_reducible apply prim_lookup)

theorem sstep_prim : Primrec fun y : List (ℕ × ℕ) × SC => sstep y.1 y.2 := by
  unfold sstep
  prim

/-- **The halting test is primitive recursive.** -/
theorem test_prim : PrimrecPred fun x : (List (ℕ × ℕ) × SC) × ℕ => Test x.1 x.2 := by
  unfold Test
  have h : Primrec fun x : (List (ℕ × ℕ) × SC) × ℕ => (sstep x.1.1)^[x.2] x.1.2 :=
    Primrec.nat_iterate Primrec.snd (prim_snd Primrec.fst)
      (Primrec₂.mk (sstep_prim.comp (prim_pair (prim_fst (prim_fst Primrec.fst)) Primrec.snd)))
  exact pred_eq (prim_fst h) (Primrec.const 0)

end DiagonaLean.Foundations.Computability
