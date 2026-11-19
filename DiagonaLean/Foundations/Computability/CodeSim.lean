/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.HaltSearch

@[expose] public section

/-! # Simulating a machine from its code

`encodeBoolTM` records every transition of a machine, with successor index `0` for a halting one,
which is the simulator's own code for "halt" (`qc`). So the table read off the code is the
machine's full table (`rowsC_eq_rowsE`), `dataC` reads the numeric data of the simulator directly
off the code, and `selfHalt_iff_test` shows that the search over `Test` decides halting. Since the
simulator follows the machine step by step, the code determines what the machine does.

The bits of the code are split at each `true` into a list of numbers (`tokens`), so each field of
each transition sits at a fixed offset, and no recursion on the code is needed.

## Main statements

* `dataC`: the simulator's data, from a code. Primitive recursive (`dataC_prim`).
* `selfHalt_iff_test`: `M` halts on its own code iff the search over `dataC` of that code succeeds.
* `halts_iff_of_code_eq`, `outputs_iff_of_code_eq`: machines with the same code halt on the same
  inputs and produce the same outputs.
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing DiagonaLean.Halt DiagonaLean.Halt.Encoding

/-! ### Tokens -/

/-- The lengths of the runs of `false`, split at each `true`. -/
def tokens (w : List Bool) : List ℕ :=
  w.foldr (fun b acc => if b then 0 :: acc else (acc.headI + 1) :: acc.tail) [0]

/-- A leading `true` starts a new token `0`. -/
theorem tokens_true (r : List Bool) : tokens (true :: r) = 0 :: tokens r := rfl

/-- A leading `false` adds one to the first token. -/
theorem tokens_false (r : List Bool) :
    tokens (false :: r) = ((tokens r).headI + 1) :: (tokens r).tail := rfl

/-- The encoding of `a` followed by `true` contributes the token `a`. -/
theorem tokens_nat_true (a : ℕ) (r : List Bool) :
    tokens (encodeNat a ++ true :: r) = a :: tokens r := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [encodeNat_succ, List.cons_append]
    rw [tokens_false, ih]
    rfl

/-- The tokens of the encoding of `a` are `[a]`. -/
theorem tokens_nat (a : ℕ) : tokens (encodeNat a) = [a] := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [encodeNat_succ]
    rw [tokens_false, ih]
    rfl

/-- The five fields of a transition, as tokens. -/
def five (t : TransitionTuple) : List ℕ := [t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2]

/-- The tokens of a flattened transition are its five fields. -/
theorem tokens_flatten (t : TransitionTuple) : tokens (flattenTransition t) = five t := by
  obtain ⟨i, j, k, l, m⟩ := t
  simp only [flattenTransition, List.append_assoc, List.cons_append, List.nil_append,
    tokens_nat_true, tokens_nat, five]

/-- The tokens of a flattened transition followed by `[true, true]` are its five fields, a `0`,
and the tokens of the rest. -/
theorem tokens_flatten_tt (t : TransitionTuple) (r : List Bool) :
    tokens (flattenTransition t ++ [true, true] ++ r) = five t ++ 0 :: tokens r := by
  obtain ⟨i, j, k, l, m⟩ := t
  simp only [flattenTransition, List.append_assoc, List.cons_append, List.nil_append,
    tokens_nat_true, tokens_true, five]

/-- The tuple of a transition record. -/
def tupleOf (M : EncodableTM Bool) (t : BoolTransData M) : TransitionTuple :=
  encodeBoolTransition' M t.1 t.2.1 ⟨t.2.2.2.1, t.2.2.2.2⟩ t.2.2.1

/-- Token `6 * i + c` of the encoded transitions is field `c` of the `i`-th transition, for
`c < 5`. -/
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

/-- The tokens of a machine's code are seven header tokens followed by the tokens of its
transitions. -/
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

/-- `boolSymbolIdx o % 3` is the simulator's symbol code `hc o`. -/
theorem hc_of_idx (o : Option Bool) : boolSymbolIdx o % 3 = hc o := by
  rcases o with _ | _ | _ <;> rfl

/-- `dirIdx o % 3` is the simulator's move code `mvc o`. -/
theorem mvc_of_idx (o : Option Turing.Dir) : dirIdx o % 3 = mvc o := by
  rcases o with _ | _ | _ <;> rfl

section

variable (M : EncodableTM Bool)

attribute [local instance] EncodableTM.stateEncodable

/-- The row of a recorded transition. -/
def rowRec (t : BoolTransData M) : ℕ × ℕ :=
  (Nat.pair (Encodable.encode t.1) (hc t.2.1),
    mkRow (hc t.2.2.2.1) (mvc t.2.2.2.2) (qc t.2.2.1))

/-- `optStateIdx M q` is the simulator's state code `qc q`. -/
theorem optStateIdx_eq_qc (q : Option M.State) : optStateIdx M q = qc q := by
  rcases q with _ | q <;> rfl

/-- Index `7 + y` of a list with seven leading entries is index `y` of the rest. -/
theorem getD_seven (x₁ x₂ x₃ x₄ x₅ x₆ x₇ : ℕ) (T : List ℕ) (y : ℕ) :
    (x₁ :: x₂ :: x₃ :: x₄ :: x₅ :: x₆ :: x₇ :: T).getD (7 + y) 0 = T.getD y 0 := by
  rw [Nat.add_comm]
  rfl

/-- The row read at position `i` of the tokens of the code is the row of the `i`-th recorded
transition. -/
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
    rowRec, hc_of_idx, mvc_of_idx, optStateIdx_eq_qc, boolStateIdx, Nat.add_sub_cancel]
  rfl

/-- The table read off the code is the list of rows of the recorded transitions. -/
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

/-- **The table read off the code is the machine's full table.** Every transition is recorded,
halting ones included, in the order `rowsE` lists them. -/
theorem rowsC_eq_rowsE : rowsC (encodeBoolTM M) = rowsE M := by
  rw [rowsC_code]
  simp only [SingleTapeTM.toBoolMachineData, rowsE, SProd.sprod, List.product, List.map_flatMap,
    List.map_map, syms]
  rfl

/-! ### The search -/

variable {M}

/-- The state component of `absD d` is `0` iff `d` has halted. -/
theorem state_absD {d : Data M.toSingleTapeTM} : (absD d).1 = 0 ↔ d.state = none := by
  rcases hd : d.state with _ | q
  · simp [absD, hd, qc]
  · simp [absD, hd, qc]

/-- The search on the table from the code sees exactly when `dstep` halts. -/
theorem search_iff (d : Data M.toSingleTapeTM) :
    (∃ k, ((sstep (rowsC (encodeBoolTM M)))^[k] (absD d)).1 = 0) ↔
      ∃ k, ((dstep M.toSingleTapeTM)^[k] d).state = none := by
  simp only [rowsC_eq_rowsE, iterate_absD, state_absD]

/-- `M` halts on `w` iff some iterate of `dstep` from the initial data reaches the halting state. -/
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
        ⟨none,
          (cfgOf ((dstep M.toSingleTapeTM)^[k] (initData w : Data M.toSingleTapeTM))).BiTape⟩ := by
      simp only [cfgOf, hs]
    rw [he] at hr
    exact ⟨_, hr⟩

/-- The simulator's data read off the code is the table from the code paired with the numeric
form of the initial data on the code. -/
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
  simp only [initData, absD, List.length_cons, List.headI_cons, List.tail_cons, List.map_nil,
    List.map_map]
  simp [hbit, Function.comp_def]

/-- **The search on the code decides self-halting.** -/
theorem selfHalt_iff_test :
    Halts M.toSingleTapeTM (encodeBoolTM M) ↔ ∃ k, Test (dataC (encodeBoolTM M)) k := by
  rw [halts_iff_dstep, dataC_code]
  exact (search_iff _).symm

/-- `M` outputs `v` on `w` iff some iterate of `dstep` from the initial data is the halting
configuration with tape `v`. -/
theorem outputs_iff_dstep (w v : List Bool) :
    M.toSingleTapeTM.Outputs w v ↔
      ∃ k, cfgOf ((dstep M.toSingleTapeTM)^[k] (initData w : Data M.toSingleTapeTM)) =
        M.toSingleTapeTM.haltCfg v := by
  constructor
  · intro ho
    rw [SingleTapeTM.Outputs, ← cfgOf_initData] at ho
    exact exists_iterate_of_reflTransGen _ ho
  · rintro ⟨k, hk⟩
    have hr := reaches_iterate (initData w : Data M.toSingleTapeTM) k
    rwa [cfgOf_initData, hk] at hr

end

/-! ### The code determines the machine's behaviour -/

section Faithful

variable {M N : EncodableTM Bool}

attribute [local instance] EncodableTM.stateEncodable

/-- The first token of a machine's code is the code of its start state. -/
theorem headI_tokens_code (M : EncodableTM Bool) :
    (tokens (encodeBoolTM M)).headI = qc (some M.q₀) := by
  rw [tokens_code]
  rfl

/-- Machines with the same code run in lockstep: after every number of steps, their
configurations have the same numeric form. -/
theorem absD_iterate_of_code_eq (h : encodeBoolTM M = encodeBoolTM N) (w : List Bool) (k : ℕ) :
    absD ((dstep M.toSingleTapeTM)^[k] (initData w : Data M.toSingleTapeTM)) =
      absD ((dstep N.toSingleTapeTM)^[k] (initData w : Data N.toSingleTapeTM)) := by
  have hq : qc (some M.q₀) = qc (some N.q₀) := by
    rw [← headI_tokens_code, h, headI_tokens_code]
  have h0 : absD (initData w : Data M.toSingleTapeTM) =
      absD (initData w : Data N.toSingleTapeTM) := by
    cases w <;> simp only [initData, absD, hq]
  rw [← iterate_absD, ← iterate_absD, ← rowsC_eq_rowsE, ← rowsC_eq_rowsE, h, h0]

/-- `cfgOf d` is the halting configuration with tape `v` iff the state code of `d` is `0` and its
tape is `BiTape.mk₁ v`. -/
theorem cfgOf_eq_haltCfg_iff (d : Data M.toSingleTapeTM) (v : List Bool) :
    cfgOf d = M.toSingleTapeTM.haltCfg v ↔
      (absD d).1 = 0 ∧ (⟨d.h, stk d.l, stk d.r⟩ : BiTape Bool) = BiTape.mk₁ v := by
  rw [state_absD]
  simp only [cfgOf, SingleTapeTM.haltCfg, SingleTapeTM.Cfg.mk.injEq]

/-- Data with the same numeric form have the same tape. -/
theorem tape_eq_of_absD_eq {d : Data M.toSingleTapeTM} {e : Data N.toSingleTapeTM}
    (h : absD d = absD e) : d.l = e.l ∧ d.h = e.h ∧ d.r = e.r := by
  simp only [absD, Prod.mk.injEq] at h
  exact ⟨List.map_injective_iff.2 hc_injective h.2.1, hc_injective h.2.2.1,
    List.map_injective_iff.2 hc_injective h.2.2.2⟩

/-- **The code determines halting.** Machines with the same code halt on the same inputs. -/
theorem halts_iff_of_code_eq (h : encodeBoolTM M = encodeBoolTM N) (w : List Bool) :
    Halts M.toSingleTapeTM w ↔ Halts N.toSingleTapeTM w := by
  simp only [halts_iff_dstep, ← state_absD, absD_iterate_of_code_eq h]

/-- **The code determines the output.** Machines with the same code produce the same outputs,
including what they write on their halting step. -/
theorem outputs_iff_of_code_eq (h : encodeBoolTM M = encodeBoolTM N) (w v : List Bool) :
    M.toSingleTapeTM.Outputs w v ↔ N.toSingleTapeTM.Outputs w v := by
  simp only [outputs_iff_dstep, cfgOf_eq_haltCfg_iff]
  refine exists_congr fun k => ?_
  have hk := absD_iterate_of_code_eq h w k
  obtain ⟨hl, hh, hr⟩ := tape_eq_of_absD_eq hk
  rw [hk, hl, hh, hr]

end Faithful

/-! ### Primitive recursiveness -/

section Prim

variable {α : Type*} [Primcodable α]

/-- `tokens` is primitive recursive. -/
theorem tokens_prim : Primrec tokens := by
  unfold tokens
  have h : Primrec₂ fun (_ : List Bool) (y : Bool × List ℕ) =>
      if y.1 = true then 0 :: y.2 else (y.2.headI + 1) :: y.2.tail := by
    apply Primrec₂.mk
    prim
  exact (Primrec.list_foldr (h := fun _ y => if y.1 = true then 0 :: y.2 else
    (y.2.headI + 1) :: y.2.tail) Primrec.id (Primrec.const [0]) h).of_eq fun w => by
      congr 1

/-- `tokens` of a primitive recursive function is primitive recursive. -/
theorem prim_tokens {f : α → List Bool} (hf : Primrec f) : Primrec fun x => tokens (f x) :=
  tokens_prim.comp hf

end Prim

macro_rules
  | `(tactic| prim_step) => `(tactic| with_reducible apply prim_tokens)

/-- `dataC` is primitive recursive. -/
theorem dataC_prim : Primrec dataC := by
  unfold dataC rowsC rowTok
  prim

end DiagonaLean.Foundations.Computability
