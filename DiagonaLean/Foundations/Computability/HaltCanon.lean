/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.CodeSim
import DiagonaLean.Foundations.Computability.ComputableReduction
import DiagonaLean.Synthetic.HaltReduction

@[expose] public section

/-! # The halting problem on canonical machines

`HaltProblem` is a predicate on `EncodableTM Bool × List Bool`. A machine bundles its type of
states, so these instances cannot be numbered computably, and `Computable` has no meaning on them.
A *canonical machine* (`CanonTM`) is a machine as data: its states are `0, …, n-1`, and its
transition table is a list of row codes in the format of the simulator (`HaltSearch.lean`). The type
is `Primcodable`, and every value is a real machine (`CanonTM.toTM`), so the halting problem on it
(`HaltCanon`) is an ordinary computable-theoretic problem, with no invalid instances.

* **Halting is the same.** Machines whose tables give the same lookup and that start in the same
  state halt on the same inputs (`halts_iff_of_lookup`): the simulator only reads a table through
  `lookup`. The table of `c.toTM` looks up like `c`'s rows (`lookup_rowsE_toTM`).
* **From codes.** `parse` reads a canonical machine off any bit string, primitive recursively. On
  the code of a machine `M` it gives a canonical machine that halts exactly where `M` does
  (`halts_parse_code`), keeping `M`'s state numbers; missing states get the row `0`, which halts, as
  the simulator's lookup does on a missing key.
* **Undecidable.** Self-halting reduces to `HaltCanon` through `parse`
  (`not_computablePred_haltCanon`).
* **The bridge.** `synthHaltToCanon : HaltProblem ⪯_s HaltCanon` is the synthetic reduction that
  connects the two layers.

`HaltReduction P` is a reduction from `HaltCanon` proved computable, and `HaltHard P` says one
exists: Mathlib's many-one hardness for the halting problem (`haltHard_iff`).
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions

/-! ### Canonical machines -/

/-- The raw data of a canonical machine: the number of states `n`, the start state, and the row
codes, one for each state `q` and head symbol code `s` at index `3 * q + s`. -/
abbrev CanonRaw := ℕ × ℕ × List ℕ

/-- A row code is valid for `n` states: its symbol and move codes are below `3`, and its next
state code (`0` for halt, `q + 1` for state `q`) is at most `n`. -/
def rowValid (n r : ℕ) : Bool :=
  decide (rowA r < 3) && decide (rowM r < 3) && decide (rowX r ≤ n)

/-- Raw data is valid: the start state is a state, there is one row for each state and symbol,
and every row is valid. -/
def canonValid (x : CanonRaw) : Bool :=
  decide (x.2.1 < x.1) && (x.2.2.length == 3 * x.1) && x.2.2.all (rowValid x.1)

section Prim

variable {α : Type*} [Primcodable α]

@[fun_prop] theorem prim_rowValid {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => rowValid (f x) (g x) := by
  unfold rowValid; fun_prop

theorem canonValid_prim : Primrec canonValid := by
  unfold canonValid; fun_prop

end Prim

/-- **A canonical machine**: valid raw data. -/
abbrev CanonTM := {x : CanonRaw // canonValid x = true}

theorem canonValid_primrecPred : PrimrecPred fun x : CanonRaw => canonValid x = true :=
  PrimrecPred.of_eq (Primrec.eq.comp canonValid_prim (Primrec.const true)) fun _ => Iff.rfl

instance : Primcodable CanonTM := Primcodable.subtype canonValid_primrecPred

namespace CanonTM

variable (c : CanonTM)

/-- The number of states. -/
def n : ℕ := c.1.1
/-- The start state. -/
def start : ℕ := c.1.2.1
/-- The row codes. -/
def rows : List ℕ := c.1.2.2

theorem start_lt : c.start < c.n := by
  have h := c.2
  simp only [canonValid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem rowValid_of_mem {r : ℕ} (hr : r ∈ c.rows) : rowValid c.n r = true := by
  have h := c.2
  simp only [canonValid, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 r hr

theorem rows_length : c.rows.length = 3 * c.n := by
  have h := c.2
  simp only [canonValid, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

/-- The row of state `q` on head symbol `o`. -/
def rowAt (q : ℕ) (o : Option Bool) : ℕ := c.rows.getD (3 * q + hc o) 0

theorem rowValid_rowAt (q : ℕ) (o : Option Bool) : rowValid c.n (c.rowAt q o) = true := by
  unfold rowAt
  rcases lt_or_ge (3 * q + hc o) c.rows.length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact c.rowValid_of_mem (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]
    rfl

/-- The next state of a row: `0` halts, `x + 1` goes to state `x`. -/
def nextOf (x : ℕ) : Option (Fin c.n) :=
  if h : 0 < x ∧ x - 1 < c.n then some ⟨x - 1, h.2⟩ else none

/-- States `Fin n`, numbered by their values. -/
@[reducible] def finEnc (n : ℕ) : Encodable (Fin n) where
  encode i := i.val
  decode k := if h : k < n then some ⟨k, h⟩ else none
  encodek i := by simp [i.isLt]

/-- **The machine of a canonical machine**: states `Fin n`, numbered by their values. -/
def toTM : EncodableTM Bool where
  State := Fin c.n
  stateFintype := inferInstance
  q₀ := ⟨c.start, c.start_lt⟩
  tr q o := (⟨optOf (rowA (c.rowAt q o)), mvOf (rowM (c.rowAt q o))⟩, c.nextOf (rowX (c.rowAt q o)))
  stateEncodable := finEnc c.n

/-- The lookup of a canonical machine's table: the row of a key `⟨q, s⟩` with `q` a state and `s` a
symbol code, and `0` otherwise. -/
def lookupC (k : ℕ) : ℕ :=
  if k.unpair.1 < c.n ∧ k.unpair.2 < 3 then c.rows.getD (3 * k.unpair.1 + k.unpair.2) 0 else 0

end CanonTM

/-! ### Halting through the table -/

attribute [local instance] EncodableTM.stateEncodable

/-- A key with no entry looks up as `0`. -/
theorem lookup_eq_zero {rows : List (ℕ × ℕ)} {k : ℕ} (h : ∀ kv ∈ rows, kv.1 ≠ k) :
    lookup rows k = 0 := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    unfold lookup at ih ⊢
    simp only [List.foldr_cons]
    simp only [h r List.mem_cons_self, ite_false]
    exact ih fun kv hkv => h kv (List.mem_cons_of_mem _ hkv)

/-- Every key of `rowsE M` is a state code paired with a symbol code. -/
theorem key_of_mem_rowsE {M : EncodableTM Bool} {kv : ℕ × ℕ} (h : kv ∈ rowsE M) :
    ∃ q : M.State, ∃ o : Option Bool, kv.1 = Nat.pair (Encodable.encode q) (hc o) := by
  obtain ⟨q, _, hkv⟩ := List.mem_flatMap.1 h
  obtain ⟨o, _, rfl⟩ := List.mem_map.1 hkv
  exact ⟨q, o, rfl⟩

theorem hc_optOf_of_lt {a : ℕ} (h : a < 3) : hc (optOf a) = a := by
  rcases a with _ | _ | _ | a <;> first | rfl | omega

theorem mvc_mvOf_of_lt {m : ℕ} (h : m < 3) : mvc (mvOf m) = m := by
  rcases m with _ | _ | _ | m <;> first | rfl | omega

theorem mkRow_rows (r : ℕ) : mkRow (rowA r) (rowM r) (rowX r) = r := by
  simp [mkRow, rowA, rowM, rowX]

namespace CanonTM

variable (c : CanonTM)

/-- The row recorded for a transition of `c.toTM` is the row it was read from. -/
theorem rowT_toTM (q : c.toTM.State) (o : Option Bool) :
    rowT c.toTM (c.toTM.tr q o) = c.rowAt q.val o := by
  have hv := c.rowValid_rowAt q.val o
  simp only [rowValid, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨ha, hm⟩, hx⟩ := hv
  have hq : @qc _ (finEnc c.n) (c.nextOf (rowX (c.rowAt q.val o))) = rowX (c.rowAt q.val o) := by
    unfold nextOf
    split
    · rename_i h; show _ + 1 = _; show rowX (c.rowAt q.val o) - 1 + 1 = _; omega
    · rename_i h
      show 0 = _
      omega
  show mkRow (hc (optOf (rowA (c.rowAt q.val o)))) (mvc (mvOf (rowM (c.rowAt q.val o))))
    (@qc _ (finEnc c.n) (c.nextOf (rowX (c.rowAt q.val o)))) = _
  rw [hc_optOf_of_lt ha, mvc_mvOf_of_lt hm, hq, mkRow_rows]

/-- **The table of `c.toTM` looks up like `c`'s rows.** -/
theorem lookup_rowsE_toTM (k : ℕ) : lookup (rowsE c.toTM) k = c.lookupC k := by
  unfold lookupC
  split
  · rename_i hk
    let q : c.toTM.State := ⟨k.unpair.1, hk.1⟩
    have hkey : k = Nat.pair (Encodable.encode q) (hc (optOf k.unpair.2)) := by
      show k = Nat.pair k.unpair.1 (hc (optOf k.unpair.2))
      rw [hc_optOf_of_lt hk.2, Nat.pair_unpair]
    rw [hkey, lookup_rowsE, rowT_toTM]
    show c.rows.getD (3 * k.unpair.1 + hc (optOf k.unpair.2)) 0 = _
    simp only [Nat.unpair_pair, hc_optOf_of_lt hk.2]
    rfl
  · rename_i hk
    refine lookup_eq_zero fun kv hkv heq => hk ?_
    obtain ⟨q, o, hq⟩ := key_of_mem_rowsE hkv
    rw [← heq, hq, Nat.unpair_pair]
    exact ⟨q.isLt, hc_lt o⟩

end CanonTM

/-- **Machines with the same lookup and the same start state halt on the same inputs.** The
simulator reads a table only through `lookup`. -/
theorem halts_iff_of_lookup {M N : EncodableTM Bool}
    (hq : Encodable.encode M.q₀ = Encodable.encode N.q₀)
    (hl : ∀ k, lookup (rowsE M) k = lookup (rowsE N) k) (w : List Bool) :
    Halts M.toSingleTapeTM w ↔ Halts N.toSingleTapeTM w := by
  have hs : sstep (rowsE M) = sstep (rowsE N) := by
    funext s; simp only [sstep, hl]
  have h₁ := halt_iff_test (M, w)
  have h₂ := halt_iff_test (N, w)
  simp only [dataOf, Test, absD_initData, qc, hq, hs] at h₁ h₂
  exact h₁.trans h₂.symm

/-- `c.toTM` halts where a machine with the same lookup and start state does. -/
theorem CanonTM.halts_toTM_iff (c : CanonTM) {M : EncodableTM Bool}
    (hq : c.start = Encodable.encode M.q₀) (hl : ∀ k, c.lookupC k = lookup (rowsE M) k)
    (w : List Bool) : Halts c.toTM.toSingleTapeTM w ↔ Halts M.toSingleTapeTM w :=
  halts_iff_of_lookup hq (fun k => (c.lookup_rowsE_toTM k).trans (hl k)) w

/-! ### A simple table of a canonical machine -/

section TablePrim

variable {α : Type*} [Primcodable α]

@[fun_prop] theorem prim_canon_val {f : α → CanonTM} (hf : Primrec f) : Primrec fun x => (f x).1 :=
  (Primrec.subtype_val (hp := canonValid_primrecPred)).comp hf

@[fun_prop] theorem prim_canon_n {f : α → CanonTM} (hf : Primrec f) : Primrec fun x => (f x).n :=
  Primrec.fst.comp (prim_canon_val hf)

@[fun_prop] theorem prim_canon_start {f : α → CanonTM} (hf : Primrec f) :
    Primrec fun x => (f x).start :=
  Primrec.fst.comp (Primrec.snd.comp (prim_canon_val hf))

@[fun_prop] theorem prim_canon_rows {f : α → CanonTM} (hf : Primrec f) :
    Primrec fun x => (f x).rows :=
  Primrec.snd.comp (Primrec.snd.comp (prim_canon_val hf))

end TablePrim

namespace CanonTM

variable (c : CanonTM)

/-- The table of `c` in the simulator's format, one entry per state and symbol: the same lookup
as the table of `c.toTM` (`lookup_table`), but primitive recursive in `c` (`table_prim`). -/
def table : List (ℕ × ℕ) :=
  (List.range c.n).flatMap fun q => syms.map fun o => (Nat.pair q (hc o), c.rowAt q o)

theorem table_prim : Primrec table := by
  unfold table rowAt; fun_prop

end CanonTM

@[fun_prop] theorem prim_canon_table {α : Type*} [Primcodable α] {f : α → CanonTM}
    (hf : Primrec f) : Primrec fun x => (f x).table :=
  CanonTM.table_prim.comp hf

namespace CanonTM

variable (c : CanonTM)

/-- `c.table` looks up like `c`'s rows. -/
theorem lookup_table (k : ℕ) : lookup c.table k = c.lookupC k := by
  unfold lookupC
  split
  · rename_i hk
    have hkey : k = Nat.pair k.unpair.1 (hc (optOf k.unpair.2)) := by
      rw [hc_optOf_of_lt hk.2, Nat.pair_unpair]
    rw [hkey]
    refine (lookup_eq (List.mem_flatMap.2 ⟨k.unpair.1, List.mem_range.2 hk.1,
      List.mem_map.2 ⟨optOf k.unpair.2, mem_syms _, rfl⟩⟩) ?_).trans ?_
    · intro kv hkv heq
      obtain ⟨q, -, hkv⟩ := List.mem_flatMap.1 hkv
      obtain ⟨o, -, rfl⟩ := List.mem_map.1 hkv
      obtain ⟨h₁, h₂⟩ := Nat.pair_eq_pair.1 heq
      obtain rfl := h₁
      obtain rfl := hc_injective h₂
      rfl
    · simp only [rowAt, Nat.unpair_pair, hc_optOf_of_lt hk.2]
  · rename_i hk
    refine lookup_eq_zero fun kv hkv heq => hk ?_
    obtain ⟨q, hq, hkv⟩ := List.mem_flatMap.1 hkv
    obtain ⟨o, -, rfl⟩ := List.mem_map.1 hkv
    rw [← heq, Nat.unpair_pair]
    exact ⟨List.mem_range.1 hq, hc_lt o⟩

/-- The state numbers of `c.table` are the states of `c`. -/
theorem mem_idx_table (i : ℕ) : i ∈ c.table.map (fun r => r.1.unpair.1) ↔ i < c.n := by
  simp only [table, List.map_flatMap, List.map_map, List.mem_flatMap, List.mem_map, List.mem_range,
    Function.comp_def, Nat.unpair_pair]
  constructor
  · rintro ⟨q, hq, -, -, rfl⟩
    exact hq
  · intro h
    exact ⟨i, h, none, mem_syms none, rfl⟩

end CanonTM

/-! ### Reading a canonical machine off a bit string -/

/-- A bound on the state codes in the table read off `w`, plus one. -/
def parseN (w : List Bool) : ℕ := ((rowsC w).map fun kv => kv.1.unpair.1).sum + 1

/-- The row at index `i` for `n` states: the row of the key `⟨i / 3, i % 3⟩` in the table read off
`w`, replaced by `0` if it is not valid. -/
def parseRow (w : List Bool) (n i : ℕ) : ℕ :=
  if rowValid n (lookup (rowsC w) (Nat.pair (i / 3) (i % 3))) then
    lookup (rowsC w) (Nat.pair (i / 3) (i % 3)) else 0

/-- The raw data read off `w`. -/
def parseRaw (w : List Bool) : CanonRaw :=
  (parseN w, if (tokens w).headI - 1 < parseN w then (tokens w).headI - 1 else 0,
    (List.range (3 * parseN w)).map (parseRow w (parseN w)))

theorem canonValid_parseRaw (w : List Bool) : canonValid (parseRaw w) = true := by
  simp only [canonValid, parseRaw, Bool.and_eq_true, beq_iff_eq,
    List.length_map, List.length_range, List.all_eq_true, List.mem_map, List.mem_range,
    forall_exists_index, and_imp]
  refine ⟨⟨by unfold parseN at *; split <;> simp_all, trivial⟩, ?_⟩
  rintro _ i - rfl
  unfold parseRow
  split
  · assumption
  · rfl

/-- **The canonical machine read off a bit string.** -/
def parse (w : List Bool) : CanonTM := ⟨parseRaw w, canonValid_parseRaw w⟩

theorem parseRaw_prim : Primrec parseRaw := by
  unfold parseRaw parseN parseRow; fun_prop

theorem parse_prim : Primrec parse :=
  Primrec.subtype_mk parseRaw_prim

section Code

variable (M : EncodableTM Bool)

/-- Every state code of `M` is below `parseN` of its code. -/
theorem encode_lt_parseN (q : M.State) : Encodable.encode q < parseN (encodeBoolTM M) := by
  unfold parseN
  rw [rowsC_eq_rowsE]
  have hmem : (Nat.pair (Encodable.encode q) (hc none), rowT M (M.tr q none)) ∈ rowsE M :=
    List.mem_flatMap.2 ⟨q, mem_statesList q, List.mem_map.2 ⟨none, mem_syms none, rfl⟩⟩
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun kv : ℕ × ℕ => kv.1.unpair.1) hmem)
  simp only [Nat.unpair_pair] at this
  omega

/-- Every row of `M`'s table is valid for `parseN` of its code. -/
theorem rowValid_lookup_rowsE (k : ℕ) :
    rowValid (parseN (encodeBoolTM M)) (lookup (rowsE M) k) = true := by
  by_cases hk : ∃ q : M.State, ∃ o : Option Bool, k = Nat.pair (Encodable.encode q) (hc o)
  · obtain ⟨q, o, rfl⟩ := hk
    rw [lookup_rowsE]
    simp only [rowValid, rowT, rowA, rowM, rowX, mkRow, Nat.unpair_pair, Bool.and_eq_true,
      decide_eq_true_eq]
    refine ⟨⟨hc_lt _, ?_⟩, ?_⟩
    · rcases (M.tr q o).1.movement with _ | _ | _ <;> decide
    · rcases (M.tr q o).2 with _ | q'
      · exact Nat.zero_le _
      · exact encode_lt_parseN M q'
  · rw [lookup_eq_zero fun kv hkv heq => hk ?_]
    · rfl
    · obtain ⟨q, o, h⟩ := key_of_mem_rowsE hkv
      exact ⟨q, o, heq ▸ h⟩

/-- The start state read off `M`'s code is `M`'s start state. -/
theorem parse_code_start : (parse (encodeBoolTM M)).start = Encodable.encode M.q₀ := by
  show (if (tokens (encodeBoolTM M)).headI - 1 < parseN (encodeBoolTM M) then _ else 0) = _
  rw [headI_tokens_code]
  simp only [qc, Nat.add_sub_cancel, encode_lt_parseN M M.q₀, ite_true]

/-- The canonical machine read off `M`'s code looks up like `M`'s table. -/
theorem parse_code_lookup (k : ℕ) :
    (parse (encodeBoolTM M)).lookupC k = lookup (rowsE M) k := by
  unfold CanonTM.lookupC
  split
  · rename_i hk
    have hi : 3 * k.unpair.1 + k.unpair.2 < 3 * parseN (encodeBoolTM M) := by
      have := hk.1; have := hk.2
      show _ < 3 * (parse (encodeBoolTM M)).n
      omega
    show ((List.range (3 * parseN (encodeBoolTM M))).map _).getD _ 0 = _
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
    have h3 : (3 * k.unpair.1 + k.unpair.2) / 3 = k.unpair.1 := by omega
    have h3' : (3 * k.unpair.1 + k.unpair.2) % 3 = k.unpair.2 := by omega
    simp only [parseRow, h3, h3', Nat.pair_unpair, rowsC_eq_rowsE, rowValid_lookup_rowsE, ite_true]
  · rename_i hk
    symm
    refine lookup_eq_zero fun kv hkv heq => hk ?_
    obtain ⟨q, o, hq⟩ := key_of_mem_rowsE hkv
    rw [← heq, hq, Nat.unpair_pair]
    exact ⟨encode_lt_parseN M q, hc_lt o⟩

/-- **The canonical machine read off a machine's code halts exactly where the machine does.** -/
theorem halts_parse_code (w : List Bool) :
    Halts (parse (encodeBoolTM M)).toTM.toSingleTapeTM w ↔ Halts M.toSingleTapeTM w :=
  (parse (encodeBoolTM M)).halts_toTM_iff (parse_code_start M) (parse_code_lookup M) w

end Code

/-! ### The halting problem on canonical machines -/

/-- **The halting problem on canonical machines.** -/
def HaltCanon (x : CanonTM × List Bool) : Prop := Halts x.1.toTM.toSingleTapeTM x.2

/-- **`HaltCanon` is undecidable**: self-halting reduces to it through `parse`. -/
theorem not_computablePred_haltCanon : ¬ ComputablePred HaltCanon :=
  not_computablePred_of_selfHalt (code := fun w => (parse w, w))
    (parse_prim.pair Primrec.id).to_comp fun M => (halts_parse_code M _).symm

/-- **The bridge between the layers**: the synthetic reduction from `HaltProblem` to `HaltCanon`,
reading the canonical machine off the machine's code. -/
def synthHaltToCanon : HaltProblem ⪯_s HaltCanon :=
  ⟨fun p => (parse (encodeBoolTM p.1), p.2), fun p => (halts_parse_code p.1 p.2).symm⟩

/-! ### Reductions from the halting problem, proved computable -/

variable {β : Type*} [Primcodable β]

/-- **A reduction from the halting problem, proved computable.** -/
abbrev HaltReduction (P : β → Prop) := HaltCanon ⪯ P

/-- **Halting-hardness**: a proved reduction from the halting problem exists. The proposition has
content because the computability of the reduction is proved. -/
abbrev HaltHard (P : β → Prop) : Prop := Nonempty (HaltReduction P)

/-- Halting-hardness is Mathlib's many-one reducibility from `HaltCanon`. -/
theorem haltHard_iff {P : β → Prop} : HaltHard P ↔ ManyOneReducible HaltCanon P :=
  ⟨fun ⟨r⟩ => r.manyOneReducible, fun ⟨f, hf, h⟩ => ⟨⟨f, hf, h⟩⟩⟩

/-- A halting reduction composes with a proved link. -/
def HaltReduction.trans {γ : Type*} [Primcodable γ] {p : β → Prop} {q : γ → Prop}
    (h : HaltReduction p) (r : p ⪯ q) : HaltReduction q :=
  ComputableReduction.trans h r

/-- A proved halting reduction gives a synthetic one, through the bridge. -/
def HaltReduction.toSynthHalt {P : β → Prop} (h : HaltReduction P) : SynthHaltReduction P :=
  synthHaltToCanon.trans h.toSynth

/-- **Halting-hard predicates are undecidable.** -/
theorem HaltHard.not_computablePred {P : β → Prop} (h : HaltHard P) : ¬ ComputablePred P :=
  let ⟨r⟩ := h
  r.not_computablePred not_computablePred_haltCanon

/-- **No machine decides a halting-hard predicate**, under any computable encoding. -/
theorem HaltHard.not_machineDecidable {P : β → Prop} (h : HaltHard P) {enc : β → List Bool}
    (henc : Computable enc) : ¬ MachineDecidable enc P :=
  not_machineDecidable_of_not_computablePred henc h.not_computablePred

end DiagonaLean.Foundations.Computability
