/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.MPCP.Reductions.HaltCanon_to_MPCP
import DiagonaLean.SemiThue.Basic
import DiagonaLean.SemiThue.Reductions.Halt_to_SemiThue
import DiagonaLean.Foundations.Codes.Rewriting
import DiagonaLean.Foundations.Computability.HaltCanon

@[expose] public section

/-! # From the halting problem on canonical machines to string rewriting

`Reductions/Halt_to_SemiThue.lean` shows that a machine halts iff its configuration string rewrites
to the empty string under `tmRules`. Here the system is read off a transition table, as
`MPCP.Reduction.instOf` reads the MPCP tiles: the transition tiles `transN`, the absorb rules and
the final rule, over the alphabet `Alpha ℕ Sym2` (`codeRules`, `toEmptyOf`). The rules of the table
of a machine are the rules of the normalised machine with its states renamed to numbers
(`mem_codeRules`), and renaming letters injectively keeps derivability
(`Codes.derives_mapRules_iff`), so a machine halts on an input iff the start string of its table
rewrites to the empty string (`halts_iff_toEmptyN`).

## Main statements

* `halts_iff_toEmptyN`, `codeRules_lhs_ne`: a machine halts iff the start string of its table
  rewrites to the empty string, and the rules have non-empty left sides.
* `haltCanon_iff_toEmpty`, `canonToEmpty_prim`, `canonWord_prim`: the reductions from `HaltCanon`.
  Their rules depend on the table only through its lookup and its state numbers
  (`mem_codeRules_congr`), which `c.table` shares with the table of `c.toTM`
  (`CanonTM.sameTable`), as for MPCP. The halting reductions built from them
  (`SemiThue.toEmptyFromHalt`, `SemiThue.posFromHalt`, …) are in `Undecidable.lean`.
-/

namespace DiagonaLean.SemiThue.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.PCP DiagonaLean.PCP.Reduction DiagonaLean.MPCP.Reduction
  DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Foundations.Computability
  DiagonaLean.Foundations.Computability.Normalize DiagonaLean.SemiThue.Reduction
  DiagonaLean.Foundations.Grammar DiagonaLean.Foundations.Rewriting
  DiagonaLean.Synthetic.Definitions

/-- The absorb rules and the final rule, over `Alpha ℕ Sym2`. -/
def haltRules : SRS (Alpha ℕ Normalize.Sym2) :=
  syms2.flatMap (fun a => [⟨[↟ₜa, h⊥], [h⊥]⟩, ⟨[h⊥, ↟ₜa], [h⊥]⟩]) ++ [⟨[#, h⊥, #], []⟩]

/-- The rewriting system of a machine code: the transition tiles of `transN` as rules, the absorb
rules and the final rule. -/
def codeRules (rows : List (ℕ × ℕ)) : SRS (Alpha ℕ Normalize.Sym2) :=
  (transN rows).map tileRule ++ haltRules

/-- **The instance of a transition table** `rows` with start state number `q`, on input `w`: its
rewriting system, and the start string of the normalised machine. -/
def toEmptyOf (q : ℕ) (rows : List (ℕ × ℕ)) (w : List Bool) :
    SRS (Alpha ℕ Normalize.Sym2) × List (Alpha ℕ Normalize.Sym2) :=
  (codeRules rows, (startN q w).bot)

derive_primrec tileRule [Primcodable α]

derive_primrec codeRules

derive_primrec toEmptyOf

/-- Every rule of `codeRules` has a non-empty left side. -/
theorem codeRules_lhs_ne (rows : List (ℕ × ℕ)) : ∀ lr ∈ codeRules rows, lr.lhs ≠ [] := by
  intro lr hlr
  simp only [codeRules, haltRules, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false] at hlr
  rcases hlr with ⟨T, hT, rfl⟩ | ⟨a, -, rfl | rfl⟩ | rfl
  · simp only [transN, List.mem_flatMap] at hT
    obtain ⟨_, -, _, -, _, -, hT⟩ := hT
    unfold trTilesN at hT
    split_ifs at hT
    · obtain rfl := List.mem_singleton.1 hT; simp [tileRule]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl <;> simp [tileRule]
    · obtain ⟨_, -, rfl⟩ := List.mem_map.1 hT; simp [tileRule]
  all_goals simp

section

variable (M : EncodableTM Bool)

attribute [local instance] EncodableTM.stateEncodable

/-- **The rules of the code are the renamed rules of the normalised machine.** -/
theorem mem_codeRules
    (lr : Rule (Alpha ℕ Normalize.Sym2)) :
    lr ∈ (tmRules (normEnc M)).mapRules (Alpha.map (stIdx M)) ↔ lr ∈ codeRules (rowsE M) := by
  have hlist : (tmRules (normEnc M)).mapRules (Alpha.map (stIdx M)) =
      ((transitionTiles (normEnc M)).map (ren M)).map tileRule ++ haltRules := by
    simp only [SRS.mapRules, tmRules, List.map_append, List.map_map, haltRules, List.append_assoc]
    congr 1
    congr 1
    rw [absorbTiles, List.map_flatMap]; rfl
  rw [hlist, codeRules, List.mem_append, List.mem_append]
  refine or_congr ⟨fun h => ?_, fun h => ?_⟩ Iff.rfl
  · obtain ⟨T, hT, rfl⟩ := List.mem_map.1 h
    exact List.mem_map_of_mem ((mem_transN M T).1 hT)
  · obtain ⟨T, hT, rfl⟩ := List.mem_map.1 h
    exact List.mem_map_of_mem ((mem_transN M T).2 hT)

/-- **A machine halts on an input iff the start string of its table on that input rewrites to the
empty string.** The construction does not use that the input is the machine's own code. -/
theorem halts_iff_toEmptyN (w : List Bool) :
    Halts M.toSingleTapeTM w ↔ ToEmptyProblem (toEmptyOf (Encodable.encode M.q₀) (rowsE M) w) := by
  have hstart : (startN (Encodable.encode M.q₀) w).bot =
      (block (normTM M.toSingleTapeTM)
        (initCfg (normTM M.toSingleTapeTM) (encInput w))).map (Alpha.map (stIdx M)) := by
    rw [← startTile_ren]; rfl
  rw [ToEmptyProblem, toEmptyOf, halts_normTM_iff,
    halt_iff_derives (tm := normEnc M) (normTM_noBlankWrites _) _ (normTM_noLeftBoundary _ _),
    ← Foundations.Codes.derives_mapRules_iff (Alpha.map_injective (stIdx_injective M))
      fun lr h => tmRules_lhs_ne (tm := normEnc M) lr h,
    SRS.derives_congr (mem_codeRules M), hstart]
  rfl

end

end DiagonaLean.SemiThue.Reduction

namespace DiagonaLean.SemiThue.Reduction

open DiagonaLean.PCP DiagonaLean.MPCP.Reduction DiagonaLean.Foundations.Computability
  DiagonaLean.Foundations.Computability.Normalize DiagonaLean.Foundations.Grammar
  DiagonaLean.Foundations.Rewriting

/-- `codeRules` depends on a table only through its lookup and its set of state numbers. -/
theorem mem_codeRules_congr {r₁ r₂ : List (ℕ × ℕ)} (h : SameTable r₁ r₂)
    (lr : Rule (Alpha ℕ Normalize.Sym2)) :
    lr ∈ codeRules r₁ ↔ lr ∈ codeRules r₂ := by
  simp only [codeRules, List.mem_append, List.mem_map, mem_transN_congr h]

/-- The rewriting instance of a canonical machine on an input. -/
def canonToEmpty (x : CanonTM × List Bool) :
    SRS (Alpha ℕ Normalize.Sym2) × List (Alpha ℕ Normalize.Sym2) :=
  toEmptyOf x.1.start x.1.table x.2

theorem canonToEmpty_prim : Primrec canonToEmpty := by
  unfold canonToEmpty
  fun_prop

/-- **A canonical machine halts on an input iff the start string of its instance rewrites to the
empty string.** -/
theorem haltCanon_iff_toEmpty (x : CanonTM × List Bool) :
    HaltCanon x ↔ ToEmptyProblem (canonToEmpty x) := by
  obtain ⟨c, w⟩ := x
  exact (halts_iff_toEmptyN c.toTM w).trans
    (SRS.derives_congr (mem_codeRules_congr (CanonTM.sameTable c)) _ _)

/-- The word problem of the instance with target `[]`. -/
def canonWord (x : CanonTM × List Bool) :
    SRS (Alpha ℕ Normalize.Sym2) × List (Alpha ℕ Normalize.Sym2) × List (Alpha ℕ Normalize.Sym2) :=
  ((canonToEmpty x).1, (canonToEmpty x).2, [])

theorem canonWord_prim : Primrec canonWord := by
  have := canonToEmpty_prim
  unfold canonWord
  fun_prop

end DiagonaLean.SemiThue.Reduction
