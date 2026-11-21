/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.MPCP.Undecidable
import DiagonaLean.PCP.Primrec
import DiagonaLean.Foundations.Computability.CodeSim
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # MPCP is not a computable predicate

`haltToMpcpNorm` builds the MPCP instance of a machine from the machine itself, so its input is
not `Primcodable` and it says nothing about machines. `instC` builds the same instance from the
machine's *code* `encodeBoolTM M`, on input the code itself: it reads the transition table off the
code (`rowsC`, as `dataC` does), computes the transitions of the normalised machine `normTM` from
the table (`normTrN`), and lists the tiles of `haltTiles` with each state `(q, c)` renamed to the
number `Nat.pair (encode q) (encode c)` (`stIdx`). `instC` is primitive recursive (`instC_prim`).

The tiles of `instC (encodeBoolTM M)` are those of `haltTiles` for `normTM M`, renamed
(`mem_stackN`), and solvability depends only on the set of tiles (`mpcp_congr`). So `M` halts on its
own code iff `instC (encodeBoolTM M)` is solvable (`selfHalt_iff_instC`), and a computable decision
procedure for MPCP would decide self-halting, contradicting `self_halt_undecidable`.

## Main statements

* `instC_prim`: the instance of a code is primitive recursive in the code.
* `selfHalt_iff_instC`: `M` halts on its own code iff the instance of its code is solvable.
* `not_computablePred_mpcp`: MPCP over `Alpha ℕ Sym2` is not a computable predicate.
* `not_machineDecidable_mpcp`: no Turing machine decides it under any computable encoding.
-/

derive_primcodable DiagonaLean.MPCP.Reduction.Alpha

namespace DiagonaLean.MPCP.MachineLevel

open Cslib.Turing SingleTapeTM DiagonaLean.PCP DiagonaLean.PCP.Reduction DiagonaLean.MPCP.Reduction
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Foundations.Computability
  DiagonaLean.MPCP.Normalize

/-- The symbol written, as an `Option Bool`, from its code `hc`. -/
def hcInv (n : ℕ) : Option Bool := if n = 0 then none else if n = 1 then some false else some true

/-- The transition of the normalised machine in a simulating control state (`simR` if `right`,
`simL` otherwise), from the transition table `rows` of the simulated machine, in state number `i` on
cell `a`. The result is the symbol written, the movement code `mvc` and the next-state code: `0`
halts, `Nat.pair j c + 1` is state number `j` with control state number `c`. -/
def simN (rows : List (ℕ × ℕ)) (i : ℕ) (right : Bool) (a : Option Normalize.Sym2) :
    Option Normalize.Sym2 × ℕ × ℕ :=
  if rowX (lookup rows (Nat.pair i (hc (decSym a)))) = 0 then
    (encSym (hcInv (rowA (lookup rows (Nat.pair i (hc (decSym a)))))), 0, 0)
  else if rowM (lookup rows (Nat.pair i (hc (decSym a)))) = 0 then
    (encSym (hcInv (rowA (lookup rows (Nat.pair i (hc (decSym a)))))), 0,
      Nat.pair (rowX (lookup rows (Nat.pair i (hc (decSym a)))) - 1) (if right then 1 else 2) + 1)
  else if rowM (lookup rows (Nat.pair i (hc (decSym a)))) = 2 then
    (encSym (hcInv (rowA (lookup rows (Nat.pair i (hc (decSym a)))))), (if right then 2 else 1),
      Nat.pair (rowX (lookup rows (Nat.pair i (hc (decSym a)))) - 1) (if right then 3 else 6) + 1)
  else
    (encSym (hcInv (rowA (lookup rows (Nat.pair i (hc (decSym a)))))), (if right then 1 else 2),
      Nat.pair (rowX (lookup rows (Nat.pair i (hc (decSym a)))) - 1) (if right then 5 else 4) + 1)

section Prim

variable {α : Type*} [Primcodable α]

/-- `hc` of a primitive recursive function is primitive recursive. -/
@[fun_prop] theorem prim_hc {f : α → Option Bool} (hf : Primrec f) : Primrec fun x => hc (f x) :=
  (Primrec.dom_finite hc).comp hf

/-- `decSym` of a primitive recursive function is primitive recursive. -/
@[fun_prop] theorem prim_decSym {f : α → Option Normalize.Sym2} (hf : Primrec f) :
    Primrec fun x => decSym (f x) := (Primrec.dom_finite decSym).comp hf

/-- `encSym` of a primitive recursive function is primitive recursive. -/
@[fun_prop] theorem prim_encSym {f : α → Option Bool} (hf : Primrec f) :
    Primrec fun x => encSym (f x) := (Primrec.dom_finite encSym).comp hf

/-- `preserve` of a primitive recursive function is primitive recursive. -/
@[fun_prop] theorem prim_preserve {f : α → Option Normalize.Sym2} (hf : Primrec f) :
    Primrec fun x => preserve (f x) := (Primrec.dom_finite preserve).comp hf

/-- `hcInv` of a primitive recursive function is primitive recursive. -/
@[fun_prop] theorem prim_hcInv {f : α → ℕ} (hf : Primrec f) : Primrec fun x => hcInv (f x) := by
  unfold hcInv; fun_prop

end Prim

/-- `simN` is primitive recursive. -/
theorem simN_prim : Primrec fun x : (List (ℕ × ℕ) × ℕ) × Bool × Option Normalize.Sym2 =>
    simN x.1.1 x.1.2 x.2.1 x.2.2 := by
  unfold simN
  fun_prop

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
def syms2 : List (Option Normalize.Sym2) := enumerate (Option Normalize.Sym2)

/-- The state marker of a next-state code. -/
def markerN (n : ℕ) : Alpha ℕ Normalize.Sym2 := if n = 0 then h⊥ else ↟ₛ(n - 1)

/-- The transition tiles of state number `s` on cell `a`, from its numeric transition `r`: the
numeric form of `transitionTilesFor`. -/
def trTilesN (s : ℕ) (a : Option Normalize.Sym2) (r : Option Normalize.Sym2 × ℕ × ℕ) :
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

/-- **The MPCP instance of a machine code `w`**, on input `w` itself. The first token of a code is
the start state's code plus one (`headI_tokens_code`). -/
def instC (w : List Bool) : Tile (Alpha ℕ Normalize.Sym2) × Stack (Alpha ℕ Normalize.Sym2) :=
  (startN ((tokens w).headI - 1) w, stackN (rowsC w))

section Prim

variable {α : Type*} [Primcodable α]

/-- `rowsC` of a primitive recursive function is primitive recursive. -/
@[fun_prop] theorem prim_rowsC {f : α → List Bool} (hf : Primrec f) :
    Primrec fun x => rowsC (f x) := by
  unfold rowsC rowTok; fun_prop

/-- `markerN` of a primitive recursive function is primitive recursive. -/
@[fun_prop] theorem prim_markerN {f : α → ℕ} (hf : Primrec f) :
    Primrec fun x => markerN (f x) := by
  unfold markerN; fun_prop

end Prim

/-- `simN` of primitive recursive functions is primitive recursive. -/
@[fun_prop] theorem prim_simN {α : Type*} [Primcodable α] {f : α → List (ℕ × ℕ)} {g : α → ℕ}
    {h : α → Bool} {k : α → Option Normalize.Sym2} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec h) (hk : Primrec k) : Primrec fun x => simN (f x) (g x) (h x) (k x) :=
  (simN_prim.comp ((hf.pair hg).pair (hh.pair hk)) :)

/-- `normTrN` is primitive recursive. -/
theorem normTrN_prim : Primrec fun x : (List (ℕ × ℕ) × ℕ × ℕ) × Option Normalize.Sym2 =>
    normTrN x.1.1 x.1.2.1 x.1.2.2 x.2 := by
  unfold normTrN
  fun_prop

/-- `normTrN` of primitive recursive functions is primitive recursive. -/
@[fun_prop] theorem prim_normTrN {α : Type*} [Primcodable α] {f : α → List (ℕ × ℕ)} {g h : α → ℕ}
    {k : α → Option Normalize.Sym2} (hf : Primrec f) (hg : Primrec g) (hh : Primrec h)
    (hk : Primrec k) : Primrec fun x => normTrN (f x) (g x) (h x) (k x) :=
  normTrN_prim.comp ((hf.pair (hg.pair hh)).pair hk)

/-- **The instance of a code is primitive recursive in the code.** -/
theorem instC_prim : Primrec instC := by
  unfold instC startN stackN transN trTilesN encInput
  fun_prop

/-! ### Correctness -/

/-- `hcInv` inverts `hc`. -/
theorem hcInv_hc (o : Option Bool) : hcInv (hc o) = o := by
  rcases o with _ | _ | _ <;> rfl

section

variable (M : EncodableTM Bool)

attribute [local instance] EncodableTM.stateEncodable

/-- The number of a state of the normalised machine: the pair of the codes of its components. -/
def stIdx (s : (normTM M.toSingleTapeTM).State) : ℕ :=
  Nat.pair (Encodable.encode (s.1 : M.State)) (Encodable.encode (s.2 : Ctrl))

/-- `stIdx` is injective. -/
theorem stIdx_injective : Function.Injective (stIdx M) := fun s t h => by
  obtain ⟨h₁, h₂⟩ := Nat.pair_eq_pair.1 h
  exact Prod.ext (Encodable.encode_injective h₁) (Encodable.encode_injective h₂)

/-- The numeric form of a transition of the normalised machine, in the format of `simN`. -/
def codeOf (r : Stmt Normalize.Sym2 × Option (normTM M.toSingleTapeTM).State) :
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
  · simp [rowT, codeOf, qc, mvc, hcInv_hc]
  · rcases mv with _ | _ | _ <;> cases right <;>
      simp [rowT, codeOf, qc, mvc, hcInv_hc, stIdx, Ctrl.sim, Encodable.encode]

/-- `normTrN` computes `normTr` from the transition table `rowsE M`. -/
theorem normTrN_eq (q : M.State) (c : Ctrl) (a : Option Normalize.Sym2) :
    normTrN (rowsE M) (Encodable.encode q) (Encodable.encode c) a =
      codeOf M (normTr M.toSingleTapeTM q c a) := by
  cases c <;> simp [normTrN, normTr, simN_eq, codeOf, stIdx, mvc, Encodable.encode] <;>
    split_ifs <;> simp

/-- The renaming of states by `stIdx`, on tiles. -/
abbrev ren : Tile (Alpha (normTM M.toSingleTapeTM).State Normalize.Sym2) →
    Tile (Alpha ℕ Normalize.Sym2) :=
  Tile.map (Alpha.map (stIdx M))

/-- The renamed transition tiles of a state are `trTilesN` of its number and numeric transition. -/
theorem transitionTilesFor_ren (s : (normTM M.toSingleTapeTM).State)
    (a : Option Normalize.Sym2) :
    (transitionTilesFor (normTM M.toSingleTapeTM) s a).map (ren M) =
      trTilesN (stIdx M s) a (codeOf M ((normTM M.toSingleTapeTM).tr s a)) := by
  unfold transitionTilesFor trTilesN codeOf
  obtain ⟨⟨wr, mv⟩, nx⟩ := (normTM M.toSingleTapeTM).tr s a
  rcases mv with _ | _ | _ <;> rcases nx with _ | s' <;>
    simp [ren, mvc, Tile.map, Alpha.map, noMoveTile, rightMoveTile, rightMoveBoundaryTile,
      leftMoveTile, markerN, stateMarker, syms2]

/-- The normalised machine, with its states encoded as pairs. -/
abbrev normEnc : EncodableTM Normalize.Sym2 :=
  ⟨normTM M.toSingleTapeTM, (inferInstance : Encodable (M.State × Ctrl))⟩

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

/-- The transition tiles are those of the pairs of a state and a cell. -/
theorem mem_transitionTiles {S : Type} [Inhabited S] [Fintype S] [Encodable S]
    (tm : EncodableTM S) (x : Tile (Alpha tm.State S)) :
    x ∈ transitionTiles tm ↔ ∃ q a, x ∈ transitionTilesFor tm.toSingleTapeTM q a := by
  let := tm.stateEncodable
  simp only [transitionTiles, List.mem_flatMap]
  exact ⟨fun ⟨qa, _, h⟩ => ⟨qa.1, qa.2, h⟩, fun ⟨q, a, h⟩ => ⟨(q, a), mem_enumerate _, h⟩⟩

/-- The renamed transition tiles of the normalised machine are the tiles of `transN`. -/
theorem mem_transN (t : Tile (Alpha ℕ Normalize.Sym2)) :
    t ∈ (transitionTiles (normEnc M)).map (ren M) ↔ t ∈ transN (rowsE M) := by
  simp only [transN, List.mem_flatMap, mem_idx, mem_range_eight]
  constructor
  · intro ht
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ht
    obtain ⟨⟨q, k⟩, a, hx⟩ := (mem_transitionTiles _ _).1 hx
    refine ⟨_, ⟨q, rfl⟩, _, ⟨k, rfl⟩, a, mem_enumerate a, ?_⟩
    have h : ren M x ∈ (transitionTilesFor (normTM M.toSingleTapeTM)
        (show (normTM M.toSingleTapeTM).State from (q, k)) a).map (ren M) :=
      List.mem_map_of_mem hx
    rw [transitionTilesFor_ren] at h
    rw [normTrN_eq]
    exact h
  · rintro ⟨_, ⟨q, rfl⟩, _, ⟨k, rfl⟩, a, -, ht⟩
    rw [normTrN_eq] at ht
    have h := transitionTilesFor_ren M (show (normTM M.toSingleTapeTM).State from (q, k)) a
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (h ▸ ht)
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

/-- The renamed encoding of a start configuration. -/
theorem start_aux {Q : Type} (g : Q → ℕ) (q : Q) (L : List Normalize.Sym2) :
    List.map (Alpha.map g)
      (# :: (List.map Alpha.tape ([] : List (Option Normalize.Sym2)).reverse ++
        ↟ₛq :: List.map Alpha.tape (some Mk :: List.map some L)) ++ [#]) =
      # :: ↟ₛ(g q) :: List.map (fun s => ↟ₜ(some s)) (Mk :: L) ++ [#] := by
  simp [Alpha.map, Function.comp_def]

/-- The renamed start tile of the normalised machine is `startN`. -/
theorem startTile_ren (w : List Bool) :
    ren M (startTile (normTM M.toSingleTapeTM) (encInput w)) =
      startN (Encodable.encode M.q₀) w := by
  simp only [ren, startTile, startN, encodeCfg, initCfg, encInput, BiTape.mk₁,
    encodeRunningCfg, liftTape, StackTape.mapSome, Tile.map, normTM]
  congr 1
  exact start_aux (stIdx M) _ _

end

/-- Solvability of MPCP depends only on the set of tiles. -/
theorem mpcp_congr {α : Type} (c : Tile α) {P P' : Stack α} (h : ∀ t, t ∈ P ↔ t ∈ P') :
    MPCP.DecisionProblem c P ↔ MPCP.DecisionProblem c P' := by
  unfold MPCP.DecisionProblem
  simp only [List.mem_cons, h]

/-- **A machine halts on its own code iff the MPCP instance of its code is solvable.** -/
theorem selfHalt_iff_instC (M : EncodableTM Bool) :
    Halts M.toSingleTapeTM (encodeBoolTM M) ↔
      MPCP.DecisionProblem (instC (encodeBoolTM M)).1 (instC (encodeBoolTM M)).2 := by
  let := M.stateEncodable
  have hq : (tokens (encodeBoolTM M)).headI - 1 = Encodable.encode M.q₀ := by
    rw [headI_tokens_code]; rfl
  rw [instC, hq, rowsC_eq_rowsE, halts_normTM_iff,
    halt_iff_mpcp (normEnc M) (normTM_noBlankWrites _) _ (normTM_noLeftBoundary _ _),
    mpcp_map_iff _ (Alpha.map_injective (stIdx_injective M)), ← startTile_ren]
  exact mpcp_congr _ (mem_stackN M)

open DiagonaLean.Synthetic.Definitions DiagonaLean.Halt.Undecidable in
/-- **MPCP is not a computable predicate**, over the alphabet `Alpha ℕ Sym2`. A computable decision
procedure, composed with the primitive recursive `instC`, would give a machine that decides whether
a machine halts on its own code. -/
theorem not_computablePred_mpcp :
    ¬ ComputablePred fun x : Tile (Alpha ℕ Normalize.Sym2) × Stack (Alpha ℕ Normalize.Sym2) =>
      MPCP.DecisionProblem x.1 x.2 := by
  intro h
  have h' : ComputablePred fun w : List Bool => MPCP.DecisionProblem (instC w).1 (instC w).2 :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun x => MPCP.DecisionProblem x.1 x.2) instC_prim.to_comp) h
  obtain ⟨D, hD⟩ := machineDecidable_of_computablePred (enc := id) (dec := some)
    Computable.option_some (fun _ => rfl) h'
  refine self_halt_undecidable ⟨D, fun M => ?_⟩
  simpa only [id, ← selfHalt_iff_instC] using hD (encodeBoolTM M)

open DiagonaLean.Synthetic.Definitions in
/-- **No Turing machine decides MPCP**, over the alphabet `Alpha ℕ Sym2`, under any computable
encoding of instances as bit strings. -/
theorem not_machineDecidable_mpcp
    {enc : Tile (Alpha ℕ Normalize.Sym2) × Stack (Alpha ℕ Normalize.Sym2) → List Bool}
    (henc : Computable enc) : ¬ MachineDecidable enc fun x => MPCP.DecisionProblem x.1 x.2 :=
  not_machineDecidable_of_not_computablePred henc not_computablePred_mpcp

end DiagonaLean.MPCP.MachineLevel
