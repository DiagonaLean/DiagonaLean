/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.Foundations.Computability.HaltSearch

@[expose] public section

/-! # Simulating a machine from its code

`encodeBoolTM` does not record what a machine writes on its halting step, but it does determine
whether the machine halts: a missing row means "halt". So `dataC` reads the numeric data of the
simulator directly off the code, and `selfHalt_iff_test` shows that the search over `Test` still
decides halting.

The bits of the code are split at each `true` into a list of numbers (`tokens`), so each field of
each transition sits at a fixed offset, and no recursion on the code is needed.

## Main statements

* `dataC`: the simulator's data, from a code. Primitive recursive (`dataC_prim`).
* `selfHalt_iff_test`: `M` halts on its own code iff the search over `dataC` of that code succeeds.
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing DiagonaLean.Halt DiagonaLean.Halt.Encoding

/-! ### Tokens -/

/-- The lengths of the runs of `false`, split at each `true`. -/
def tokens (w : List Bool) : List ℕ :=
  w.foldr (fun b acc => if b then 0 :: acc else (acc.headI + 1) :: acc.tail) [0]

theorem tokens_true (r : List Bool) : tokens (true :: r) = 0 :: tokens r := rfl

theorem tokens_false (r : List Bool) :
    tokens (false :: r) = ((tokens r).headI + 1) :: (tokens r).tail := rfl

theorem tokens_nat_true (a : ℕ) (r : List Bool) :
    tokens (encodeNat a ++ true :: r) = a :: tokens r := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [encodeNat_succ, List.cons_append]
    rw [tokens_false, ih]
    rfl

theorem tokens_nat (a : ℕ) : tokens (encodeNat a) = [a] := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [encodeNat_succ]
    rw [tokens_false, ih]
    rfl

/-- The five fields of a transition, as tokens. -/
def five (t : TransitionTuple) : List ℕ := [t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2]

theorem tokens_flatten (t : TransitionTuple) : tokens (flattenTransition t) = five t := by
  obtain ⟨i, j, k, l, m⟩ := t
  simp only [flattenTransition, List.append_assoc, List.cons_append, List.nil_append,
    tokens_nat_true, tokens_nat, five]

theorem tokens_flatten_tt (t : TransitionTuple) (r : List Bool) :
    tokens (flattenTransition t ++ [true, true] ++ r) = five t ++ 0 :: tokens r := by
  obtain ⟨i, j, k, l, m⟩ := t
  simp only [flattenTransition, List.append_assoc, List.cons_append, List.nil_append,
    tokens_nat_true, tokens_true, five]

/-- The tuple of a transition record. -/
def tupleOf (M : EncodableTM Bool) (t : BoolTransData M) : TransitionTuple :=
  encodeBoolTransition' M t.1 t.2.1 ⟨t.2.2.2.1, t.2.2.2.2⟩ t.2.2.1

theorem tokens_tr (M : EncodableTM Bool) (ts : List (BoolTransData M)) (i c : ℕ)
    (hi : i < ts.length) (hc : c < 5) :
    (tokens (encodeBoolTr M ts)).getD (6 * i + c) 0 = (five (tupleOf M ts[i])).getD c 0 := by
  induction ts generalizing i with
  | nil => simp at hi
  | cons t ts ih =>
    cases ts with
    | nil =>
      obtain rfl : i = 0 := by simpa using hi
      have : encodeBoolTr M [t] = flattenTransition (tupleOf M t) := rfl
      rw [this, tokens_flatten]
      simp
    | cons t' ts =>
      have : encodeBoolTr M (t :: t' :: ts) =
          flattenTransition (tupleOf M t) ++ [true, true] ++ encodeBoolTr M (t' :: ts) := rfl
      rw [this, tokens_flatten_tt]
      rcases i with _ | i
      · have hc' : 6 * 0 + c < (five (tupleOf M t)).length := by simp [five]; omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hc']
        simp
      · have e : 6 * (i + 1) + c = (five (tupleOf M t) ++ [0]).length + (6 * i + c) := by
          simp [five]; omega
        have hs : five (tupleOf M t) ++ 0 :: tokens (encodeBoolTr M (t' :: ts)) =
            (five (tupleOf M t) ++ [0]) ++ tokens (encodeBoolTr M (t' :: ts)) := by simp
        rw [hs, e, List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        exact ih i (by simpa using hi)

theorem tokens_code (M : EncodableTM Bool) :
    tokens (encodeBoolTM M) =
      boolStateIdx M M.q₀ :: 0 :: 0 :: (SingleTapeTM.toBoolMachineData M).2.length :: 0 :: 0 :: 0 ::
        tokens (encodeBoolTr M (SingleTapeTM.toBoolMachineData M).2) := by
  simp only [encodeBoolTM, encodeBoolTMData, List.append_assoc, List.cons_append, List.nil_append,
    tokens_nat_true, tokens_true]
  rfl

/-! ### The data -/

/-- The entry of the transition table at position `i` of the tokens. -/
def rowTok (t : List ℕ) (i : ℕ) : ℕ × ℕ :=
  (Nat.pair (t.getD (7 + (6 * i + 0)) 0 - 1) (t.getD (7 + (6 * i + 1)) 0 % 3),
    mkRow (t.getD (7 + (6 * i + 3)) 0 % 3) (t.getD (7 + (6 * i + 4)) 0 % 3)
      (t.getD (7 + (6 * i + 2)) 0))

/-- The transition table, from a code. -/
def rowsC (w : List Bool) : List (ℕ × ℕ) :=
  (List.range ((tokens w).getD 3 0)).map (rowTok (tokens w))

/-- The simulator's data, from a code, on input `w` itself. -/
def dataC (w : List Bool) : List (ℕ × ℕ) × SC :=
  (rowsC w, ((tokens w).headI, [], (if w.length = 0 then 0 else bitCode w.headI),
    w.tail.map bitCode))

theorem hc_of_idx (o : Option Bool) : boolSymbolIdx o % 3 = hc o := by
  rcases o with _ | _ | _ <;> rfl

theorem mvc_of_idx (o : Option Turing.Dir) : dirIdx o % 3 = mvc o := by
  rcases o with _ | _ | _ <;> rfl

section

variable (M : EncodableTM Bool)

attribute [local instance] EncodableTM.stateEncodable

/-- The row of a recorded transition. -/
def rowRec (t : BoolTransData M) : ℕ × ℕ :=
  (Nat.pair (Encodable.encode t.1) (hc t.2.1),
    mkRow (hc t.2.2.2.1) (mvc t.2.2.2.2) (Encodable.encode t.2.2.1 + 1))

theorem getD_seven (x₁ x₂ x₃ x₄ x₅ x₆ x₇ : ℕ) (T : List ℕ) (y : ℕ) :
    (x₁ :: x₂ :: x₃ :: x₄ :: x₅ :: x₆ :: x₇ :: T).getD (7 + y) 0 = T.getD y 0 := by
  rw [Nat.add_comm]
  rfl

theorem rowTok_code (i : ℕ) (hi : i < (SingleTapeTM.toBoolMachineData M).2.length) :
    rowTok (tokens (encodeBoolTM M)) i = rowRec M (SingleTapeTM.toBoolMachineData M).2[i] := by
  set ts := (SingleTapeTM.toBoolMachineData M).2 with hts
  have hget : ∀ c, c < 5 → (tokens (encodeBoolTM M)).getD (7 + (6 * i + c)) 0 =
      (five (tupleOf M ts[i])).getD c 0 := fun c hc => by
    rw [tokens_code, getD_seven]
    exact tokens_tr M ts i c hi hc
  simp only [rowTok, hget 0 (by omega), hget 1 (by omega), hget 2 (by omega), hget 3 (by omega),
    hget 4 (by omega)]
  simp only [five, tupleOf, encodeBoolTransition', List.getD_cons_zero, List.getD_cons_succ,
    rowRec, hc_of_idx, mvc_of_idx, boolStateIdx, Nat.add_sub_cancel]
  rfl

theorem rowsC_code :
    rowsC (encodeBoolTM M) = (SingleTapeTM.toBoolMachineData M).2.map (rowRec M) := by
  have hn : (tokens (encodeBoolTM M)).getD 3 0 = (SingleTapeTM.toBoolMachineData M).2.length := by
    rw [tokens_code]
    rfl
  unfold rowsC
  rw [hn]
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range]
  exact rowTok_code M i (by simpa using h₁)

theorem mem_ts {q : M.State} {h : Option Bool} {stmt : SingleTapeTM.Stmt Bool} {q' : M.State}
    (htr : M.tr q h = (stmt, some q')) :
    (q, h, q', stmt.symbol, stmt.movement) ∈ (SingleTapeTM.toBoolMachineData M).2 := by
  refine List.mem_filterMap.2 ⟨(q, h), ?_, ?_⟩
  · refine List.mem_product.2 ⟨mem_statesList q, ?_⟩
    rcases h with _ | _ | _ <;> simp
  · simp [htr]

theorem of_mem_ts {t : BoolTransData M} (ht : t ∈ (SingleTapeTM.toBoolMachineData M).2) :
    M.tr t.1 t.2.1 = (⟨t.2.2.2.1, t.2.2.2.2⟩, some t.2.2.1) := by
  obtain ⟨⟨q, x⟩, _, hx⟩ := List.mem_filterMap.1 ht
  rcases htr : M.tr q x with ⟨⟨sym, dir⟩, _ | q'⟩
  · simp [htr] at hx
  · simp only [htr, Option.some.injEq] at hx
    subst hx
    exact htr

variable {M}

theorem lookup_some {q : M.State} {h : Option Bool} {q' : M.State}
    (hq : (M.tr q h).2 = some q') :
    lookup (rowsC (encodeBoolTM M)) (Nat.pair (Encodable.encode q) (hc h)) = rowT M (M.tr q h) := by
  rw [rowsC_code]
  rcases htr : M.tr q h with ⟨stmt, n⟩
  rw [htr] at hq
  obtain rfl : n = some q' := hq
  refine lookup_eq (List.mem_map.2 ⟨_, mem_ts M htr, rfl⟩) ?_
  intro kv hkv hk
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hkv
  obtain ⟨h₁, h₂⟩ := Nat.pair_eq_pair.1 hk
  have e₁ : t.1 = q := Encodable.encode_injective h₁
  have e₂ : t.2.1 = h := hc_injective h₂
  have ht' := of_mem_ts M ht
  rw [e₁, e₂, htr] at ht'
  obtain ⟨hs, hn⟩ := Prod.mk.inj ht'
  have hn' : t.2.2.1 = q' := (Option.some.inj hn).symm
  show mkRow (hc t.2.2.2.1) (mvc t.2.2.2.2) (Encodable.encode t.2.2.1 + 1) = _
  rw [hn', show t.2.2.2.1 = stmt.symbol by rw [hs], show t.2.2.2.2 = stmt.movement by rw [hs]]
  rfl

theorem lookup_absent {rows : List (ℕ × ℕ)} {key : ℕ} (h : ∀ kv ∈ rows, kv.1 ≠ key) :
    lookup rows key = 0 := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    unfold lookup
    simp only [List.foldr_cons]
    rw [if_neg (h r List.mem_cons_self)]
    exact ih fun kv hkv => h kv (List.mem_cons_of_mem _ hkv)

theorem lookup_none {q : M.State} {h : Option Bool} (hq : (M.tr q h).2 = none) :
    lookup (rowsC (encodeBoolTM M)) (Nat.pair (Encodable.encode q) (hc h)) = 0 := by
  rw [rowsC_code]
  refine lookup_absent fun kv hkv hk => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hkv
  obtain ⟨h₁, h₂⟩ := Nat.pair_eq_pair.1 hk
  have e₁ : t.1 = q := Encodable.encode_injective h₁
  have e₂ : t.2.1 = h := hc_injective h₂
  have ht' := of_mem_ts M ht
  rw [e₁, e₂] at ht'
  rw [ht'] at hq
  cases hq

/-! ### The search -/

theorem sstep_of_some (q : M.State) (l : List (Option Bool)) (h : Option Bool)
    (r : List (Option Bool)) {q' : M.State} (hq : (M.tr q h).2 = some q') :
    sstep (rowsC (encodeBoolTM M)) (absD ⟨some q, l, h, r⟩) =
      absD (dstep M.toSingleTapeTM ⟨some q, l, h, r⟩) := by
  have hl : lookup (rowsC (encodeBoolTM M)) (Nat.pair (Encodable.encode q + 1 - 1) (hc h)) =
      rowT M (M.tr q h) := by
    simpa using lookup_some hq
  have hne : Encodable.encode q + 1 ≠ 0 := Nat.succ_ne_zero _
  simp only [absD, sstep, qc, hne, ite_false, hl]
  rcases htr : M.tr q h with ⟨⟨wr, _ | _ | _⟩, q''⟩
  · simp [rowT, mvc, dstep, htr, absD]
    cases q'' <;> rfl
  · cases l <;> simp [rowT, mvc, dstep, htr, absD, hc] <;> cases q'' <;> rfl
  · cases r <;> simp [rowT, mvc, dstep, htr, absD, hc] <;> cases q'' <;> rfl

theorem sstep_of_none (q : M.State) (l : List (Option Bool)) (h : Option Bool)
    (r : List (Option Bool)) (hq : (M.tr q h).2 = none) :
    (sstep (rowsC (encodeBoolTM M)) (absD ⟨some q, l, h, r⟩)).1 = 0 := by
  have hl := lookup_none hq
  have hne : Encodable.encode q + 1 ≠ 0 := Nat.succ_ne_zero _
  simp [absD, sstep, qc, hne, hl, rowM, rowX]

theorem dstep_state_none (q : M.State) (l : List (Option Bool)) (h : Option Bool)
    (r : List (Option Bool)) (hq : (M.tr q h).2 = none) :
    (dstep M.toSingleTapeTM ⟨some q, l, h, r⟩).state = none := by
  simp only [dstep]
  rcases htr : M.tr q h with ⟨⟨wr, _ | _ | _⟩, q''⟩
  all_goals rw [htr] at hq; obtain rfl : q'' = none := hq
  · simp [htr]
  · cases l <;> simp [htr]
  · cases r <;> simp [htr]

theorem state_absD {d : Data M.toSingleTapeTM} : (absD d).1 = 0 ↔ d.state = none := by
  rcases hd : d.state with _ | q
  · simp [absD, hd, qc]
  · simp [absD, hd, qc]

theorem sstep_zero (rows : List (ℕ × ℕ)) {c : SC} (hc : c.1 = 0) (k : ℕ) :
    ((sstep rows)^[k] c).1 = 0 := by
  have hf : sstep rows c = c := by simp [sstep, hc]
  rw [Function.iterate_fixed hf]
  exact hc

/-- The search on the table from the code sees exactly when `dstep` halts. -/
theorem search_iff (d : Data M.toSingleTapeTM) :
    (∃ k, ((sstep (rowsC (encodeBoolTM M)))^[k] (absD d)).1 = 0) ↔
      ∃ k, ((dstep M.toSingleTapeTM)^[k] d).state = none := by
  constructor
  · rintro ⟨k, hk⟩
    induction k generalizing d with
    | zero => exact ⟨0, state_absD.1 hk⟩
    | succ k ih =>
      obtain ⟨_ | q, l, h, r⟩ := d
      · exact ⟨0, rfl⟩
      · rcases hq : (M.tr q h).2 with _ | q'
        · refine ⟨1, ?_⟩
          rw [Function.iterate_one]
          exact dstep_state_none q l h r hq
        · rw [Function.iterate_succ_apply, sstep_of_some q l h r hq] at hk
          obtain ⟨k', hk'⟩ := ih _ hk
          exact ⟨k' + 1, by rwa [Function.iterate_succ_apply]⟩
  · rintro ⟨k, hk⟩
    induction k generalizing d with
    | zero => exact ⟨0, state_absD.2 hk⟩
    | succ k ih =>
      obtain ⟨_ | q, l, h, r⟩ := d
      · exact ⟨0, rfl⟩
      · rcases hq : (M.tr q h).2 with _ | q'
        · refine ⟨1, ?_⟩
          rw [Function.iterate_one]
          exact sstep_of_none q l h r hq
        · rw [Function.iterate_succ_apply] at hk
          obtain ⟨k', hk'⟩ := ih _ hk
          refine ⟨k' + 1, ?_⟩
          rw [Function.iterate_succ_apply, sstep_of_some q l h r hq]
          exact hk'

theorem halts_iff_dstep (w : List Bool) :
    Halts M.toSingleTapeTM w ↔
      ∃ k, ((dstep M.toSingleTapeTM)^[k] (initData w : Data M.toSingleTapeTM)).state = none := by
  constructor
  · rintro ⟨t, ht⟩
    rw [← cfgOf_initData] at ht
    obtain ⟨k, hk⟩ := exists_iterate_of_reflTransGen _ ht
    exact ⟨k, congrArg SingleTapeTM.Cfg.state hk⟩
  · rintro ⟨k, hs⟩
    have hr := reaches_iterate (initData w : Data M.toSingleTapeTM) k
    rw [cfgOf_initData] at hr
    have he : cfgOf ((dstep M.toSingleTapeTM)^[k] (initData w : Data M.toSingleTapeTM)) =
        ⟨none, (cfgOf ((dstep M.toSingleTapeTM)^[k] (initData w : Data M.toSingleTapeTM))).BiTape⟩ := by
      simp only [cfgOf, hs]
    rw [he] at hr
    exact ⟨_, hr⟩

theorem dataC_code :
    dataC (encodeBoolTM M) = (rowsC (encodeBoolTM M),
      absD (initData (encodeBoolTM M) : Data M.toSingleTapeTM)) := by
  have hhead : (tokens (encodeBoolTM M)).headI = qc (some M.q₀) := by
    rw [tokens_code]
    rfl
  have hne : encodeBoolTM M ≠ [] := by
    simp only [encodeBoolTM, encodeBoolTMData, List.append_assoc, List.cons_append, ne_eq,
      List.append_eq_nil_iff, reduceCtorEq, and_false, not_false_eq_true]
  obtain ⟨a, t, hw⟩ := List.exists_cons_of_ne_nil hne
  have hbit : ∀ b : Bool, bitCode b = hc (some b) := fun b => by cases b <;> rfl
  rw [dataC, hhead, hw]
  simp only [initData, absD, List.length_cons, List.headI_cons, List.tail_cons, List.map_nil, List.map_map]
  simp [hbit, Function.comp_def]

/-- **The search on the code decides self-halting.** -/
theorem selfHalt_iff_test :
    Halts M.toSingleTapeTM (encodeBoolTM M) ↔ ∃ k, Test (dataC (encodeBoolTM M)) k := by
  rw [halts_iff_dstep, dataC_code]
  exact (search_iff _).symm

end

/-! ### Primitive recursiveness -/

section Prim

variable {α : Type*} [Primcodable α]

theorem tokens_prim : Primrec tokens := by
  unfold tokens
  have h : Primrec₂ fun (_ : List Bool) (y : Bool × List ℕ) =>
      if y.1 = true then 0 :: y.2 else (y.2.headI + 1) :: y.2.tail := by
    apply Primrec₂.mk
    prim
  exact (Primrec.list_foldr (h := fun _ y => if y.1 = true then 0 :: y.2 else
    (y.2.headI + 1) :: y.2.tail) Primrec.id (Primrec.const [0]) h).of_eq fun w => by
      congr 1

theorem prim_tokens {f : α → List Bool} (hf : Primrec f) : Primrec fun x => tokens (f x) :=
  tokens_prim.comp hf

end Prim

macro_rules
  | `(tactic| prim_step) => `(tactic| with_reducible apply prim_tokens)

theorem dataC_prim : Primrec dataC := by
  unfold dataC rowsC rowTok
  prim

end DiagonaLean.Foundations.Computability
