/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.MPCP.Undecidable
import DiagonaLean.PCP.Primrec
import DiagonaLean.Foundations.Computability.CodeSim
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # The MPCP instance of a transition table, numerically

`haltToMpcpNorm` builds the MPCP instance of a machine from the machine itself, so its input is not
`Primcodable` and it says nothing about machines. `instOf q rows w` builds the same instance from a
transition table `rows` in the format of `rowsE`, with start state number `q`, on input `w`: it
computes the transitions of the normalised machine `normTM` from the table (`normTrN`), and lists
the tiles of `haltTiles` with each state `(q, c)` renamed to the number
`Nat.pair (encode q) (encode c)` (`stIdx`). `instOf` is primitive recursive.

The tiles of `stackN (rowsE M)` are those of `haltTiles` for `normTM M`, renamed (`mem_stackN`), and
solvability depends only on the set of tiles (`mpcp_congr`). So `M` halts on `w` iff
`instOf (encode M.q₀) (rowsE M) w` is solvable (`halts_iff_mpcpN`). `canonInst` (`Hardness.lean`)
reads the table off a canonical machine, which gives the halting reduction `MPCP.fromHalt` and,
from it, the negative results.

## Main statements

* `halts_iff_mpcpN`: a machine halts on an input iff the instance of its table on it is solvable.
-/

derive_primcodable DiagonaLean.MPCP.Reduction.Alpha

namespace DiagonaLean.MPCP.MachineLevel

open Cslib.Turing SingleTapeTM DiagonaLean.PCP DiagonaLean.MPCP.Reduction
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Foundations.Computability
  DiagonaLean.Foundations.Computability.Normalize

/-- The transition of the normalised machine in a simulating control state (`simR` if `right`,
`simL` otherwise), from the transition table `rows` of the simulated machine, in state number `i` on
cell `a`. The result is the symbol written, the movement code `mvc` and the next-state code: `0`
halts, `Nat.pair j c + 1` is state number `j` with control state number `c`. -/
def simN (rows : List (ℕ × ℕ)) (i : ℕ) (right : Bool) (a : Option Normalize.Sym2) :
    Option Normalize.Sym2 × ℕ × ℕ :=
  if rowX (lookup rows (Nat.pair i (hc (decSym a)))) = 0 then
    (encSym (optOf (rowA (lookup rows (Nat.pair i (hc (decSym a)))))), 0, 0)
  else if rowM (lookup rows (Nat.pair i (hc (decSym a)))) = 0 then
    (encSym (optOf (rowA (lookup rows (Nat.pair i (hc (decSym a)))))), 0,
      Nat.pair (rowX (lookup rows (Nat.pair i (hc (decSym a)))) - 1) (if right then 1 else 2) + 1)
  else if rowM (lookup rows (Nat.pair i (hc (decSym a)))) = 2 then
    (encSym (optOf (rowA (lookup rows (Nat.pair i (hc (decSym a)))))), (if right then 2 else 1),
      Nat.pair (rowX (lookup rows (Nat.pair i (hc (decSym a)))) - 1) (if right then 3 else 6) + 1)
  else
    (encSym (optOf (rowA (lookup rows (Nat.pair i (hc (decSym a)))))), (if right then 1 else 2),
      Nat.pair (rowX (lookup rows (Nat.pair i (hc (decSym a)))) - 1) (if right then 5 else 4) + 1)

derive_primrec simN

/-- The transition `normTr` of the normalised machine, numerically, in state number `i` with control
state number `c` (the `Encodable` code of `Ctrl`), in the format of `simN`. -/
def normTrN (rows : List (ℕ × ℕ)) (i c : ℕ) (a : Option Normalize.Sym2) :
    Option Normalize.Sym2 × ℕ × ℕ :=
  if c = 0 then (some Mk, 2, Nat.pair i 1 + 1)
  else if c = 1 then simN rows i true a
  else if c = 2 then simN rows i false a
  else if c = 3 then (preserve a, 2, Nat.pair i 1 + 1)
  else if c = 4 then (preserve a, 2, Nat.pair i 2 + 1)
  else if c = 5 then
    (if a = some Mk then (some Mk, 2, Nat.pair i 4 + 1) else (preserve a, 1, Nat.pair i 1 + 1))
  else if c = 6 then (preserve a, 1, Nat.pair i 7 + 1)
  else (if a = some Mk then (some Mk, 2, Nat.pair i 1 + 1) else (preserve a, 0, Nat.pair i 2 + 1))

/-- The cell symbols of the normalised machine. -/
def syms2 : List (Option Normalize.Sym2) :=
  enumerate (Option Normalize.Sym2)

/-- The state marker of a next-state code. -/
def markerN (n : ℕ) : Alpha ℕ Normalize.Sym2 := if n = 0 then h⊥ else ↟ₛ(n - 1)

/-- The transition tiles of state number `s` on cell `a`, from its numeric transition `r`: the
numeric form of `transitionTilesFor`. -/
def trTilesN (s : ℕ) (a : Option Normalize.Sym2)
    (r : Option Normalize.Sym2 × ℕ × ℕ) :
    List (Tile (Alpha ℕ Normalize.Sym2)) :=
  if r.2.1 = 0 then [⟨[↟ₛs, ↟ₜa], [markerN r.2.2, ↟ₜr.1]⟩]
  else if r.2.1 = 2 then
    [⟨[↟ₛs, ↟ₜa], [↟ₜr.1, markerN r.2.2]⟩,
      ⟨[↟ₛs, ↟ₜa, #], [↟ₜr.1, markerN r.2.2, ↟ₜ(none : Option Normalize.Sym2), #]⟩]
  else syms2.map fun b => ⟨[↟ₜb, ↟ₛs, ↟ₜa], [markerN r.2.2, ↟ₜb, ↟ₜr.1]⟩

/-- All transition tiles of the normalised machine, from the transition table `rows` of the
simulated machine. The state numbers are the first components of the keys of `rows`. -/
def transN (rows : List (ℕ × ℕ)) : List (Tile (Alpha ℕ Normalize.Sym2)) :=
  (rows.map fun r => r.1.unpair.1).flatMap fun i => (List.range 8).flatMap fun c =>
    syms2.flatMap fun a => trTilesN (Nat.pair i c) a (normTrN rows i c a)

/-- The tiles of the instance, from the transition table `rows`: the numeric form of `haltTiles`. -/
def stackN (rows : List (ℕ × ℕ)) : Stack (Alpha ℕ Normalize.Sym2) :=
  syms2.map (fun a => ⟨[↟ₜa], [↟ₜa]⟩) ++ [⟨[#], [#]⟩] ++ transN rows ++
    syms2.flatMap (fun a => [⟨[↟ₜa, h⊥], [h⊥]⟩, ⟨[h⊥, ↟ₜa], [h⊥]⟩]) ++ [⟨[h⊥, #, #], [#]⟩]

/-- The start tile, for start state number `q` and input `w`: the numeric form of `startTile` for
the normalised machine on `encInput w`. -/
def startN (q : ℕ) (w : List Bool) : Tile (Alpha ℕ Normalize.Sym2) :=
  ⟨[#], # :: ↟ₛ(Nat.pair q 0) :: (encInput w).map (fun s => ↟ₜ(some s)) ++ [#]⟩

/-- **The MPCP instance of a transition table** `rows` with start state number `q`, on input `w`.
-/
def instOf (q : ℕ) (rows : List (ℕ × ℕ)) (w : List Bool) :
    Tile (Alpha ℕ Normalize.Sym2) × Stack (Alpha ℕ Normalize.Sym2) :=
  (startN q w, stackN rows)

derive_primrec markerN

derive_primrec normTrN

derive_primrec trTilesN

derive_primrec transN

derive_primrec stackN

derive_primrec encInput

derive_primrec startN

derive_primrec instOf

/-! ### Correctness -/

section

variable (M : EncodableTM Bool)

attribute [local instance] EncodableTM.stateEncodable

/-- The number of a state of the normalised machine: the pair of the codes of its components. -/
def stIdx (s : M.State × Ctrl) : ℕ := Nat.pair (Encodable.encode s.1) (Encodable.encode s.2)

/-- `stIdx` is injective. -/
theorem stIdx_injective : Function.Injective (stIdx M) := fun s t h => by
  obtain ⟨h₁, h₂⟩ := Nat.pair_eq_pair.1 h
  exact Prod.ext (Encodable.encode_injective h₁) (Encodable.encode_injective h₂)

/-- The numeric form of a transition of the normalised machine, in the format of `simN`. -/
def codeOf (r : Stmt Normalize.Sym2 × Option (M.State × Ctrl)) :
    Option Normalize.Sym2 × ℕ × ℕ :=
  (r.1.symbol, mvc r.1.movement, match r.2 with | none => 0 | some s => stIdx M s + 1)

/-- `simN` computes `simStep` from the transition table `rowsE M`. -/
theorem simN_eq (q : M.State) (right : Bool) (a : Option Normalize.Sym2) :
    simN (rowsE M) (Encodable.encode q) right a =
      codeOf M (simStep M.toSingleTapeTM q right a) := by
  unfold simN simStep
  rw [lookup_rowsE]
  obtain ⟨⟨wr, mv⟩, nx⟩ := M.tr q (decSym a)
  rcases nx with _ | q₂
  · simp [rowT, codeOf, qc, mvc, optOf_hc]
  · rcases mv with _ | _ | _ <;> cases right <;>
      simp [rowT, codeOf, qc, mvc, optOf_hc, stIdx, Ctrl.sim, Encodable.encode]

/-- `normTrN` computes `normTr` from the transition table `rowsE M`. -/
theorem normTrN_eq (q : M.State) (c : Ctrl) (a : Option Normalize.Sym2) :
    normTrN (rowsE M) (Encodable.encode q) (Encodable.encode c) a =
      codeOf M (normTr M.toSingleTapeTM q c a) := by
  cases c <;> simp [normTrN, normTr, simN_eq, codeOf, stIdx, mvc, Encodable.encode] <;>
    split_ifs <;> simp

/-- The renaming of states by `stIdx`, on tiles. -/
abbrev ren :
    Tile (Alpha (M.State × Ctrl) Normalize.Sym2) →
      Tile (Alpha ℕ Normalize.Sym2) :=
  Tile.map (Alpha.map (stIdx M))

/-- The renamed transition tiles of a state are `trTilesN` of its number and numeric transition. -/
theorem transitionTilesFor_ren (s : M.State × Ctrl) (a : Option Normalize.Sym2) :
    (transitionTilesFor (normTM M.toSingleTapeTM) s a).map (ren M) =
      trTilesN (stIdx M s) a (codeOf M ((normTM M.toSingleTapeTM).tr s a)) := by
  unfold transitionTilesFor trTilesN codeOf
  obtain ⟨⟨wr, mv⟩, nx⟩ := (normTM M.toSingleTapeTM).tr s a
  rcases mv with _ | _ | _ <;> rcases nx with _ | s' <;>
    simp [ren, mvc, Tile.map, Alpha.map, noMoveTile, rightMoveTile, rightMoveBoundaryTile,
      leftMoveTile, markerN, stateMarker, syms2]

/-- The state numbers read off `rowsE M` are the codes of the states of `M`. -/
theorem mem_idx (i : ℕ) :
    i ∈ (rowsE M).map (fun r => r.1.unpair.1) ↔ ∃ q : M.State, Encodable.encode q = i := by
  simp only [rowsE, List.map_flatMap, List.map_map, List.mem_flatMap, List.mem_map,
    Function.comp_def, Nat.unpair_pair]
  constructor
  · rintro ⟨q, -, -, -, rfl⟩
    exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, mem_statesList q, none, mem_syms none, rfl⟩

/-- The numbers below `8` are the codes of the control states. -/
theorem mem_range_eight (c : ℕ) : c ∈ List.range 8 ↔ ∃ k : Ctrl, Encodable.encode k = c := by
  rw [List.mem_range]
  constructor
  · intro h
    have : ∀ c : Fin 8, ∃ k : Ctrl, Encodable.encode k = c.val := by decide
    exact this ⟨c, h⟩
  · rintro ⟨k, rfl⟩
    cases k <;> decide

/-- The renamed transition tiles of the normalised machine are the tiles of `transN`. -/
theorem mem_transN (t : Tile (Alpha ℕ Normalize.Sym2)) :
    t ∈ (transitionTiles (normEnc M)).map (ren M) ↔ t ∈ transN (rowsE M) := by
  simp only [transN, List.mem_flatMap, mem_idx, mem_range_eight]
  constructor
  · intro ht
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ht
    obtain ⟨⟨q, k⟩, a, hx⟩ := (mem_transitionTiles _ _).1 hx
    refine ⟨_, ⟨q, rfl⟩, _, ⟨k, rfl⟩, a, mem_enumerate a, ?_⟩
    rw [normTrN_eq]
    exact transitionTilesFor_ren M (q, k) a ▸ List.mem_map_of_mem hx
  · rintro ⟨_, ⟨q, rfl⟩, _, ⟨k, rfl⟩, a, -, ht⟩
    rw [normTrN_eq] at ht
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (transitionTilesFor_ren M (q, k) a ▸ ht)
    exact List.mem_map_of_mem ((mem_transitionTiles _ _).2 ⟨(q, k), a, hx⟩)

/-- The renamed tiles of the normalised machine are the tiles of `stackN`. -/
theorem mem_stackN (t : Tile (Alpha ℕ Normalize.Sym2)) :
    t ∈ (haltTiles (normEnc M)).map (ren M) ↔ t ∈ stackN (rowsE M) := by
  have h₁ : (copyTiles (normTM M.toSingleTapeTM)).map (ren M) =
      syms2.map (fun a => ⟨[↟ₜa], [↟ₜa]⟩) := by
    rw [copyTiles, List.map_map]; rfl
  have h₂ : (absorbTiles (normTM M.toSingleTapeTM)).map (ren M) =
      syms2.flatMap (fun a => [⟨[↟ₜa, h⊥], [h⊥]⟩, ⟨[h⊥, ↟ₜa], [h⊥]⟩]) := by
    rw [absorbTiles, List.map_flatMap]; rfl
  unfold haltTiles stackN
  simp only [List.map_append, List.mem_append, h₁, h₂, mem_transN]
  rfl

/-- The renamed start tile of the normalised machine is `startN`. -/
theorem startTile_ren (w : List Bool) :
    ren M (startTile (normTM M.toSingleTapeTM) (encInput w)) =
      startN (Encodable.encode M.q₀) w := by
  simp [ren, startTile, startN, encodeCfg, initCfg, encInput, BiTape.mk₁, encodeRunningCfg,
    liftTape, StackTape.mapSome, Tile.map, Alpha.map, stIdx, Function.comp_def]
  rfl

/-- **A machine halts on an input iff the MPCP instance of its table on that input is solvable.**
The construction does not use that the input is the machine's own code. -/
theorem halts_iff_mpcpN (w : List Bool) :
    Halts M.toSingleTapeTM w ↔
      MPCP.DecisionProblem (instOf (Encodable.encode M.q₀) (rowsE M) w) := by
  show _ ↔ MPCP.Solvable (startN _ w) (stackN (rowsE M))
  rw [halts_normTM_iff,
    halt_iff_mpcp (normEnc M) (normTM_noBlankWrites _) _ (normTM_noLeftBoundary _ _),
    mpcp_map_iff _ (Alpha.map_injective (stIdx_injective M)), ← startTile_ren]
  exact mpcp_congr _ (mem_stackN M)

end

end DiagonaLean.MPCP.MachineLevel
