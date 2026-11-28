/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Foundations.Computability.ListMachine
import DiagonaLean.Foundations.Computability.Normalize.Table
import DiagonaLean.Foundations.Computability.DerivePrimcodable
import DiagonaLean.Foundations.Computability.DerivePrimrec
import DiagonaLean.Foundations.Computability.HaltResults

@[expose] public section

/-! # Halting of list machines given by a table

A program of a list machine on numeric states is a finite list of rules (`Program`): the rule
`((q, c), (m, q', b))` states that in state `q` on the symbol `c` the machine writes `b`, enters
`q'` and moves by `m`. A state and a symbol with no rule halt (`act`). The problem asks whether
the machine of a program halts from a start state on a tape, with the head on its first cell and
nothing left of it: `HaltsOn bl p q tape`, curried, and `DecisionProblem bl` on instances.

The problem is a source for reductions that simulate a machine. Its instances are data, so a
reduction from it is one function on tables, with one correctness proof and one computability
proof; it does not handle Turing machines, their normalisation or canonical machines.

Over the cells `Option Sym2` of normalised machines, with blank `none`, the problem is
halting-hard: `canonList` sends a canonical machine and an input to the table of its normalised
machine, on the state numbers `Nat.pair i c`, and the initial tape.

## Main definitions

* `Program`, `act`, `HaltsOn`, `DecisionProblem`: the problem.
* `states`: the states of a program and a start state, closed under steps (`states_closed`).

## Main statements

* `haltCanon_iff_listHalt`, `canonList_prim`: `canonList` reduces `HaltCanon` to the problem, and
  it is primitive recursive.
* `ListHalt.fromHalt`: the problem is halting-hard. By `halt_results`: `ListHalt.haltHard`,
  `ListHalt.not_computablePred`, `ListHalt.not_machineDecidable`.
* `ListHalt.synthFromHalt`: the synthetic reduction from the halting problem.
-/

namespace DiagonaLean.Foundations.Computability.ListHalt

/-- The movement of the head in a rule. -/
inductive Move where
  /-- The head stays. -/
  | stay
  /-- The head moves left. -/
  | left
  /-- The head moves right. -/
  | right
  deriving DecidableEq

end DiagonaLean.Foundations.Computability.ListHalt

derive_primcodable DiagonaLean.Foundations.Computability.ListHalt.Move

namespace DiagonaLean.Foundations.Computability.ListHalt

open Cslib.Turing DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Foundations.Computability.ListMachine
  DiagonaLean.Foundations.Computability.Normalize DiagonaLean.Synthetic.Definitions

/-! ### The problem -/

section Problem

variable {Γ : Type}

/-- A rule `((q, c), (m, q', b))`: in state `q` on the symbol `c`, write `b`, enter `q'` and move
by `m`. -/
abbrev Rule (Γ : Type) := (ℕ × Γ) × (Move × ℕ × Γ)

/-- A program of a list machine on numeric states is a list of rules. -/
abbrev Program (Γ : Type) := List (Rule Γ)

/-- `toAct r` is the transition of the right side `r` of a rule. -/
def toAct (r : Move × ℕ × Γ) : Act ℕ Γ :=
  if r.1 = .stay then .stay r.2.1 r.2.2
  else if r.1 = .right then .right r.2.1 r.2.2
  else .left r.2.1 r.2.2

variable [DecidableEq Γ]

/-- `rule? p q c` is the right side of the first rule of `p` for the state `q` and the symbol
`c`. -/
def rule? (p : Program Γ) (q : ℕ) (c : Γ) : Option (Move × ℕ × Γ) :=
  (p.find? fun r => decide (r.1 = (q, c))).map Prod.snd

/-- `act p` is the transition function of the program `p`: a state and a symbol with no rule
halt. -/
def act (p : Program Γ) (q : ℕ) (c : Γ) : Act ℕ Γ := ((rule? p q c).map toAct).getD .halt

/-- `start bl q tape` is the configuration in state `q` with the head on the first cell of `tape`
and nothing left of it. The head cell of the empty tape is the blank. -/
def start (bl : Γ) (q : ℕ) (tape : List Γ) : Cfg ℕ Γ := ⟨q, [], tape.headD bl, tape.tail⟩

/-- **Does the machine of the program `p` halt from the state `q` on `tape`?** -/
def HaltsOn (bl : Γ) (p : Program Γ) (q : ℕ) (tape : List Γ) : Prop :=
  Halts (act p) bl (start bl q tape)

/-- **Halting of list machines given by a table**, on an instance `(p, q, tape)`:
`HaltsOn bl p q tape`. -/
def DecisionProblem (bl : Γ) (x : Program Γ × ℕ × List Γ) : Prop := HaltsOn bl x.1 x.2.1 x.2.2

/-- The problem on an instance `(p, q, tape)` is the curried problem. -/
@[simp] theorem decisionProblem_mk (bl : Γ) (p : Program Γ) (q : ℕ) (tape : List Γ) :
    DecisionProblem bl (p, q, tape) ↔ HaltsOn bl p q tape := Iff.rfl

/-- `states p q` lists the start state `q` and the states the rules of `p` enter, without
repetition. -/
def states (p : Program Γ) (q : ℕ) : List ℕ := (q :: p.map fun r => r.2.2.1).dedup

omit [DecidableEq Γ] in
/-- The start state is a state of the program. -/
theorem mem_states_start (p : Program Γ) (q : ℕ) : q ∈ states p q :=
  List.mem_dedup.mpr List.mem_cons_self

/-- A step of the machine of `p` leads to a state of `states p q₀`. -/
theorem states_closed (bl : Γ) (p : Program Γ) (q₀ : ℕ) (k k' : Cfg ℕ Γ)
    (h : next (act p) bl k = some k') : k'.q ∈ states p q₀ := by
  obtain ⟨q, l, c, r⟩ := k
  simp only [next, act, rule?] at h
  cases hf : p.find? (fun r => decide (r.1 = (q, c))) with
  | none => simp [hf] at h
  | some e =>
    have he : e.2.2.1 ∈ states p q₀ :=
      List.mem_dedup.mpr (List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨e, List.mem_of_find?_eq_some hf, rfl⟩))
    simp only [hf, Option.map_some, Option.getD_some, toAct] at h
    split_ifs at h
    · simp only [Option.some.injEq] at h
      subst h
      exact he
    · simp only [Option.some.injEq] at h
      subst h
      exact he
    · cases l with
      | nil => simp at h
      | cons d l =>
        simp only [Option.some.injEq] at h
        subst h
        exact he

end Problem

derive_primrec rule? [Primcodable Γ]

derive_primrec states [Primcodable Γ]


/-! ### The table of a normalised machine -/

/-- `ruleR r` is the right side of the rule for a numeric transition `r` in the format of `simN`
(the symbol written, the movement code, and the next-state code), or `none` when it halts. -/
def ruleR (r : Option Sym2 × ℕ × ℕ) : Option (Move × ℕ × Option Sym2) :=
  if r.2.2 = 0 then none
  else some (if r.2.1 = 0 then .stay else if r.2.1 = 2 then .right else .left, r.2.2 - 1, r.1)

/-- `actN rows` is the list machine of the transition table `rows`: the normalised machine, on
the state numbers `Nat.pair i c`. -/
def actN (rows : List (ℕ × ℕ)) (s : ℕ) (a : Option Sym2) : Act ℕ (Option Sym2) :=
  ((ruleR (normTrN rows s.unpair.1 s.unpair.2 a)).map toAct).getD .halt

/-- `statesN rows` lists the state numbers of the normalised machine of the table `rows`,
without repetition. -/
def statesN (rows : List (ℕ × ℕ)) : List ℕ :=
  ((rows.map fun r => r.1.unpair.1).flatMap fun i => (List.range 8).map fun c => Nat.pair i c).dedup

/-- The cells of a normalised machine. -/
def cells : List (Option Sym2) := enumAll (Option Sym2)

/-- `tableN rows` is the program of the normalised machine of the transition table `rows`. -/
def tableN (rows : List (ℕ × ℕ)) : Program (Option Sym2) :=
  (statesN rows ×ˢ cells).filterMap fun p =>
    (ruleR (normTrN rows p.1.unpair.1 p.1.unpair.2 p.2)).map fun r => (p, r)

/-- `tapeN w` is the initial tape of a normalised machine on input `w`. -/
def tapeN (w : List Bool) : List (Option Sym2) :=
  some Mk :: w.flatMap fun b => [some (b, true), some Bl]

/-- **The instance of a canonical machine and an input**: the program of its normalised machine,
the start state number and the initial tape. -/
def canonList (x : CanonTM × List Bool) : Program (Option Sym2) × ℕ × List (Option Sym2) :=
  (tableN x.1.table, Nat.pair x.1.start 0, tapeN x.2)

derive_primrec ruleR

derive_primrec statesN

derive_primrec tableN

derive_primrec tapeN

derive_primrec canonList

/-- On a state number of the table, the program `tableN rows` acts as `actN rows`. -/
theorem act_tableN {rows : List (ℕ × ℕ)} {q : ℕ} (hq : q ∈ statesN rows) (a : Option Sym2) :
    act (tableN rows) q a = actN rows q a := by
  have hmem : (q, a) ∈ statesN rows ×ˢ cells := List.mem_product.mpr ⟨hq, mem_enumAll a⟩
  unfold act rule? actN
  cases hf : (tableN rows).find? (fun r => decide (r.1 = (q, a))) with
  | none =>
    cases hr : ruleR (normTrN rows q.unpair.1 q.unpair.2 a) with
    | none => rfl
    | some r =>
      have := List.find?_eq_none.mp hf ((q, a), r)
        (List.mem_filterMap.mpr ⟨(q, a), hmem, by simp [hr]⟩)
      simp at this
  | some e =>
    obtain ⟨p, -, hpe⟩ := List.mem_filterMap.mp (List.mem_of_find?_eq_some hf)
    have hkey := List.find?_some hf
    cases hr : ruleR (normTrN rows p.1.unpair.1 p.1.unpair.2 p.2) with
    | none => simp [hr] at hpe
    | some r =>
      simp only [hr, Option.map_some, Option.some.injEq] at hpe
      subst hpe
      simp only [decide_eq_true_eq] at hkey
      subst hkey
      simp [hr]

section

variable (c : CanonTM)

attribute [local instance] EncodableTM.stateEncodable

/-- The list machine of the table of `c` is the list machine of the normalised machine of
`c.toTM`, with states renamed by `stIdx`. -/
theorem actN_stIdx (s : c.toTM.State × Ctrl) (a : Option Sym2) :
    actN c.table (stIdx c.toTM s) a =
      mapAct (stIdx c.toTM) (tmAct (normTM c.toTM.toSingleTapeTM) s a) := by
  have hrows : normTrN c.table (Encodable.encode s.1) (Encodable.encode s.2) a =
      normTrN (rowsE c.toTM) (Encodable.encode s.1) (Encodable.encode s.2) a :=
    (normTrN_congr (CanonTM.sameTable c).1 _ _ a).symm
  unfold actN stIdx
  simp only [Nat.unpair_pair]
  rw [hrows, normTrN_eq]
  simp only [tmAct, codeOf, ruleR]
  obtain ⟨⟨wr, mv⟩, nx⟩ := normTr c.toTM.toSingleTapeTM s.1 s.2 a
  rcases nx with _ | s' <;> rcases mv with _ | _ | _ <;> simp [mvc, mapAct, stIdx, toAct]

/-- The state numbers of the table of `c` are the numbers of the states of the normalised
machine. -/
theorem mem_statesN (n : ℕ) :
    n ∈ statesN c.table ↔ ∃ s : c.toTM.State × Ctrl, stIdx c.toTM s = n := by
  rw [statesN, List.mem_dedup, List.mem_flatMap]
  constructor
  · rintro ⟨i, hi, hn⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hn
    rw [← (CanonTM.sameTable c).2, mem_idx] at hi
    obtain ⟨q, rfl⟩ := hi
    obtain ⟨kc, rfl⟩ := (mem_range_eight k).mp hk
    exact ⟨(q, kc), rfl⟩
  · rintro ⟨⟨q, kc⟩, rfl⟩
    exact ⟨Encodable.encode q,
      ((CanonTM.sameTable c).2 _).mp ((mem_idx _ _).mpr ⟨q, rfl⟩),
      List.mem_map.mpr ⟨Encodable.encode kc, (mem_range_eight _).mpr ⟨kc, rfl⟩, rfl⟩⟩

/-- **A canonical machine halts on an input iff the list machine of its table halts from the
initial configuration.** -/
theorem halts_iff_actN (w : List Bool) :
    Halts c.toTM.toSingleTapeTM w ↔
      ListMachine.Halts (actN c.table) none (start none (Nat.pair c.start 0) (tapeN w)) := by
  have hcfg : start none (Nat.pair c.start 0) (tapeN w) = mapCfg (stIdx c.toTM)
      (ListMachine.cfgOf (normTM c.toTM.toSingleTapeTM) (normTM c.toTM.toSingleTapeTM).q₀
        (BiTape.mk₁ (encInput w))) := by
    simp [start, tapeN, mapCfg, ListMachine.cfgOf, BiTape.mk₁, encInput, StackTape.mapSome,
      stIdx, List.map_flatMap]
    exact ⟨rfl, rfl⟩
  rw [halts_normTM_iff, halts_iff (normTM_noBlankWrites _) (normTM_noLeftBoundary _ _), hcfg,
    halts_mapCfg_iff (actN_stIdx c)]

/-- A step of the list machine of the table from a state number of the table leads to a state
number of the table. -/
theorem statesN_closed (k k' : Cfg ℕ (Option Sym2)) (hk : k.q ∈ statesN c.table)
    (h : next (actN c.table) none k = some k') : k'.q ∈ statesN c.table := by
  obtain ⟨s, hs⟩ := (mem_statesN c _).mp hk
  obtain ⟨q, l, a, r⟩ := k
  simp only at hs
  subst hs
  have hm := next_mapCfg (bl := (none : Option Sym2)) (actN_stIdx c) ⟨s, l, a, r⟩
  simp only [mapCfg] at hm
  rw [hm] at h
  obtain ⟨k₂, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (mem_statesN c _).mpr ⟨k₂.q, rfl⟩

end

/-- **A canonical machine halts on an input iff the list machine of its instance halts.** -/
theorem haltCanon_iff_listHalt (x : CanonTM × List Bool) :
    HaltCanon x ↔ DecisionProblem none (canonList x) := by
  obtain ⟨c, w⟩ := x
  have hstart : (start (none : Option Sym2) (Nat.pair c.start 0) (tapeN w)).q ∈ statesN c.table :=
    (mem_statesN c _).mpr ⟨(c.toTM.q₀, Ctrl.start), rfl⟩
  rw [HaltCanon, halts_iff_actN]
  exact (halts_congr (· ∈ statesN c.table) (fun q hq a => act_tableN hq a) (statesN_closed c) _
    hstart).symm

end DiagonaLean.Foundations.Computability.ListHalt

namespace DiagonaLean.Foundations.Computability.ListHalt

open DiagonaLean.Halt DiagonaLean.Foundations.Computability.Normalize
  DiagonaLean.Synthetic.Definitions

/-- **Halting of list machines given by a table is halting-hard**, over the cells `Option Sym2`
with blank `none`: `canonList` reduces the halting problem on canonical machines to it, and is
primitive recursive. -/
def fromHalt : HaltReduction (DecisionProblem (none : Option Sym2)) := by
  hard_reduce_from (ComputableReduction.refl HaltCanon) with canonList
    using haltCanon_iff_listHalt

halt_results (DecisionProblem (none : Option Sym2)) from fromHalt

/-- **Halting of list machines given by a table is synthetically halting-hard**: `fromHalt`, as a
synthetic reduction. -/
def synthFromHalt : SynthHaltReduction (DecisionProblem (none : Option Sym2)) :=
  fromHalt.toSynthHalt

end DiagonaLean.Foundations.Computability.ListHalt
