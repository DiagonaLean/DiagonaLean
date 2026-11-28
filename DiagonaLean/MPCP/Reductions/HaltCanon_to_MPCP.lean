/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.MPCP.Reductions.Halt_to_MPCP
import DiagonaLean.PCP.Primrec
import DiagonaLean.Foundations.Computability.CodeSim
import DiagonaLean.Foundations.Computability.MachineBridge
import DiagonaLean.Foundations.Computability.HaltCanon
import DiagonaLean.Foundations.Computability.Normalize.Table

@[expose] public section

/-! # From the halting problem on canonical machines to MPCP

`haltToMpcpNorm` builds the MPCP instance of a machine from the machine itself, so its input is not
`Primcodable` and it says nothing about machines. `instOf q rows w` builds the same instance from a
transition table `rows` in the format of `rowsE`, with start state number `q`, on input `w`: it
computes the transitions of the normalised machine `normTM` from the table (`normTrN`, in
`Foundations/Computability/Normalize/Table.lean`), and lists
the tiles of `haltTiles` with each state `(q, c)` renamed to the number
`Nat.pair (encode q) (encode c)` (`stIdx`). `instOf` is primitive recursive.

The tiles of `stackN (rowsE M)` are those of `haltTiles` for `normTM M`, renamed (`mem_stackN`), and
solvability depends only on the set of tiles (`mpcp_congr`). So `M` halts on `w` iff
`instOf (encode M.q₀) (rowsE M) w` is solvable (`halts_iff_mpcpN`).

On canonical machines the table is primitive recursive (`CanonTM.table`), and `stackN` depends on a
table only through its lookup and its set of state numbers (`mem_stackN_congr`), which `c.table`
shares with the table of `c.toTM`. So `canonInst (c, w) = instOf c.start c.table w` reduces
`HaltCanon` to MPCP (`haltCanon_iff_mpcp`), primitive recursively (`canonInst_prim`); the halting
reduction `MPCP.fromHalt` is in `Undecidable.lean`.

## Main statements

* `halts_iff_mpcpN`: a machine halts on an input iff the instance of its table on it is solvable.
* `haltCanon_iff_mpcp`, `canonInst_prim`: the reduction from `HaltCanon`, and its computability.
-/

derive_primcodable DiagonaLean.MPCP.Reduction.Alpha

namespace DiagonaLean.MPCP.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.PCP DiagonaLean.MPCP.Reduction
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Foundations.Computability
  DiagonaLean.Foundations.Computability.Normalize

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

end DiagonaLean.MPCP.Reduction

namespace DiagonaLean.MPCP.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.PCP DiagonaLean.PCP.Reduction DiagonaLean.MPCP.Reduction
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Foundations.Computability
  DiagonaLean.Foundations.Computability.Normalize

/-- `transN` depends on a table only through its lookup and its set of state numbers. -/
theorem mem_transN_congr {r₁ r₂ : List (ℕ × ℕ)} (h : SameTable r₁ r₂)
    (t : Tile (Alpha ℕ Normalize.Sym2)) : t ∈ transN r₁ ↔ t ∈ transN r₂ := by
  simp only [transN, List.mem_flatMap, normTrN_congr h.1, h.2]

/-- `stackN` depends on a table only through its lookup and its set of state numbers. -/
theorem mem_stackN_congr {r₁ r₂ : List (ℕ × ℕ)} (h : SameTable r₁ r₂)
    (t : Tile (Alpha ℕ Normalize.Sym2)) : t ∈ stackN r₁ ↔ t ∈ stackN r₂ := by
  simp only [stackN, List.mem_append, mem_transN_congr h]

/-- The MPCP instance of a canonical machine on an input. -/
def canonInst (x : CanonTM × List Bool) :
    Tile (Alpha ℕ Normalize.Sym2) × Stack (Alpha ℕ Normalize.Sym2) :=
  instOf x.1.start x.1.table x.2

theorem canonInst_prim : Primrec canonInst := by
  unfold canonInst
  fun_prop

/-- **A canonical machine halts on an input iff its MPCP instance is solvable.** -/
theorem haltCanon_iff_mpcp (x : CanonTM × List Bool) :
    HaltCanon x ↔ MPCP.DecisionProblem (canonInst x) := by
  obtain ⟨c, w⟩ := x
  exact (halts_iff_mpcpN c.toTM w).trans (mpcp_congr _ (mem_stackN_congr (CanonTM.sameTable c)))

end DiagonaLean.MPCP.Reduction
