/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CM2.Assembler
import DiagonaLean.CM2.Reductions.Halt_to_CM2
import DiagonaLean.MPCP.Reductions.HaltCanon_to_MPCP
import DiagonaLean.Foundations.Computability.HaltCanon

@[expose] public section

/-! # From the halting problem on canonical machines to two-counter machines

`haltToCM2` (`Reductions/Halt_to_CM2.lean`) builds the program from a machine, whose type of states
is not `Primcodable`. Here the program is built from a transition table in the format of `rowsE`,
as `MPCP.Reduction.instOf` builds the MPCP instance: the states of the normalised machine are the
numbers `Nat.pair i c` (`stIdx`), its transitions are read off the table by `normTrN` (`actN`),
and the kinds and exits of the blocks are computed from them (`codesN`). The list machine of the
table is the list machine of the normalised machine with its states renamed (`actN_stIdx`), and
renaming states keeps halting (`halts_mapCfg_iff`).

On canonical machines the table is primitive recursive, and the assembler is primitive recursive
(`assemble_prim`), so `canonProgram` is primitive recursive.

## Main statements

* `halts_iff_cfgN`: a canonical machine halts on an input iff the list machine of its table halts
  from the initial configuration.
* `haltCanon_iff_cm2`, `canonProgram_prim`: `canonProgram` reduces `HaltCanon` to halting of
  two-counter machines from zero counters, and it is primitive recursive. The halting reduction
  built from them (`CM2.fromHalt`) is in `Undecidable.lean`.

## References

* [M. L. Minsky, *Computation: Finite and Infinite Machines*][Minsky1967], Section 14.1
-/

namespace DiagonaLean.CM2.Reduction

open Cslib.Turing DiagonaLean.Halt DiagonaLean.Halt.Encoding
  DiagonaLean.Foundations.Computability DiagonaLean.Foundations.Computability.ListMachine
  DiagonaLean.Foundations.Computability.Normalize DiagonaLean.MPCP.Reduction

/-! ### Renaming the states of a list machine -/

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

/-! ### The list machine of a transition table -/

/-- `actR r` is the transition of a list machine for a numeric transition `r` in the format of
`simN`: the symbol written, the movement code, and the next-state code. -/
def actR (r : Option Sym2 × ℕ × ℕ) : Act ℕ (Option Sym2) :=
  if r.2.2 = 0 then .halt
  else if r.2.1 = 0 then .stay (r.2.2 - 1) r.1
  else if r.2.1 = 2 then .right (r.2.2 - 1) r.1
  else .left (r.2.2 - 1) r.1

/-- `actN rows` is the list machine of the transition table `rows`: the normalised machine, on
the state numbers `Nat.pair i c`. -/
def actN (rows : List (ℕ × ℕ)) (s : ℕ) (a : Option Sym2) : Act ℕ (Option Sym2) :=
  actR (normTrN rows s.unpair.1 s.unpair.2 a)

/-- `statesN rows` lists the state numbers of the normalised machine of the table `rows`,
without repetition. -/
def statesN (rows : List (ℕ × ℕ)) : List ℕ :=
  ((rows.map fun r => r.1.unpair.1).flatMap fun i => (List.range 8).map fun c => Nat.pair i c).dedup

/-- `pairsN rows` lists the pairs of a state number of `rows` and a symbol. -/
def pairsN (rows : List (ℕ × ℕ)) : List (ℕ × Option Sym2) := statesN rows ×ˢ syms2

/-- `rightN w` lists the cells right of the head in the initial configuration on input `w`. -/
def rightN (w : List Bool) : List (Option Sym2) :=
  w.flatMap fun b => [some (b, true), some Bl]

/-- `cfgN q w` is the initial configuration of the list machine of a table with start state
number `q`, on input `w`. -/
def cfgN (q : ℕ) (w : List Bool) : Cfg ℕ (Option Sym2) := ⟨Nat.pair q 0, [], some Mk, rightN w⟩

/-- `stepCodeR r pairs n p` is the kind and exits of the block of the pair `p`, from its numeric
transition `r`, the list `pairs` of all pairs and the number `n` of load blocks. -/
def stepCodeR (r : Option Sym2 × ℕ × ℕ) (pairs : List (ℕ × Option Sym2)) (n : ℕ)
    (p : ℕ × Option Sym2) : Kind (Option Sym2) × List ℕ :=
  if r.2.2 = 0 then (.jump, [n + 2 + pairs.length])
  else if r.2.1 = 0 then (.jump, [n + 2 + pairIx pairs (r.2.2 - 1, r.1)])
  else if r.2.1 = 2 then
    (.right r.1, (n + 2 + pairIx pairs (r.2.2 - 1, none)) ::
      syms2.map fun c => n + 2 + pairIx pairs (r.2.2 - 1, c))
  else
    (.left r.1, (n + 2 + pairIx pairs p) :: syms2.map fun c => n + 2 + pairIx pairs (r.2.2 - 1, c))

/-- **The kinds and exits of the program of a transition table** `rows` with start state number
`q`, on input `w`. -/
def codesN (rows : List (ℕ × ℕ)) (q : ℕ) (w : List Bool) :
    List (Kind (Option Sym2) × List ℕ) :=
  (Kind.boot, [1]) ::
    ((List.range (rightN w).length).map fun i =>
      (Kind.load ((rightN w).reverse.getD i none), [i + 2])) ++
    (Kind.jump, [(rightN w).length + 2 + pairIx (pairsN rows) (Nat.pair q 0, some Mk)]) ::
    (pairsN rows).map fun p =>
      stepCodeR (normTrN rows p.1.unpair.1 p.1.unpair.2 p.2) (pairsN rows) (rightN w).length p

derive_primrec stepCodeR

derive_primrec statesN

derive_primrec pairsN

derive_primrec rightN

derive_primrec codesN

/-- `stepCodeR` on the transition of the table is `stepCode` of its list machine. -/
theorem stepCodeR_eq (rows : List (ℕ × ℕ)) (n : ℕ) (p : ℕ × Option Sym2) :
    stepCodeR (normTrN rows p.1.unpair.1 p.1.unpair.2 p.2) (pairsN rows) n p =
      stepCode (actN rows) none syms2 (stepIx (statesN rows) syms2 n)
        (n + 2 + (statesN rows ×ˢ syms2).length) p := by
  unfold stepCodeR stepCode actN actR
  split_ifs <;> rfl

/-- `codesN` is `codes` of the list machine of the table. -/
theorem codesN_eq (rows : List (ℕ × ℕ)) (q : ℕ) (w : List Bool) :
    codesN rows q w = codes (actN rows) none (statesN rows) syms2 (cfgN q w) := by
  simp only [codesN, codes, cfgN, stepCodeR_eq]
  rfl

/-! ### Correctness on canonical machines -/

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
  simp only [tmAct, codeOf, actR]
  obtain ⟨⟨wr, mv⟩, nx⟩ := normTr c.toTM.toSingleTapeTM s.1 s.2 a
  rcases nx with _ | s' <;> rcases mv with _ | _ | _ <;> simp [mvc, mapAct, stIdx]

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
theorem halts_iff_cfgN (w : List Bool) :
    Halts c.toTM.toSingleTapeTM w ↔ ListMachine.Halts (actN c.table) none (cfgN c.start w) := by
  have hcfg : cfgN c.start w = mapCfg (stIdx c.toTM)
      (ListMachine.cfgOf (normTM c.toTM.toSingleTapeTM) (normTM c.toTM.toSingleTapeTM).q₀
        (BiTape.mk₁ (encInput w))) := by
    simp [cfgN, mapCfg, ListMachine.cfgOf, BiTape.mk₁, encInput, StackTape.mapSome, rightN,
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

/-- `canonProgram (c, w)` is the two-counter program of the canonical machine `c` on the input
`w`. -/
def canonProgram (x : CanonTM × List Bool) : List Instr :=
  assemble syms2 (codesN x.1.table x.1.start x.2)

/-- `canonProgram` is primitive recursive. -/
@[fun_prop] theorem canonProgram_prim : Primrec canonProgram := by
  have h : Primrec fun x : CanonTM × List Bool => codesN x.1.table x.1.start x.2 := by fun_prop
  exact (assemble_prim syms2).comp h

/-- **A canonical machine halts on an input iff its two-counter program halts from zero
counters.** -/
theorem haltCanon_iff_cm2 (x : CanonTM × List Bool) :
    HaltCanon x ↔ DecisionProblem (canonProgram x) := by
  obtain ⟨c, w⟩ := x
  have hstart : (cfgN c.start w).q ∈ statesN c.table :=
    (mem_statesN c _).mpr ⟨(c.toTM.q₀, Ctrl.start), rfl⟩
  have h := haltsFrom_program_iff (δ := actN c.table) (bl := none) (cs := syms2)
    (qs := statesN c.table) (k₀ := cfgN c.start w) (fun a => MPCP.Reduction.mem_enumerate a)
    (statesN_closed c) hstart rfl
  rw [HaltCanon, halts_iff_cfgN, ← h, DecisionProblem, canonProgram, codesN_eq]
  rfl

end DiagonaLean.CM2.Reduction
