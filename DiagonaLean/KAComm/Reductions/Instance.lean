/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.RunAfterWrite
import DiagonaLean.KAComm.Reductions.ExprCode

@[expose] public section

/-! # The instance of `NM K l`

`rInst K l` is the equality instance of Theorem 18 for the machine `NM K l` on the empty input.
It differs from `eqRed` in three ways: the input is `[]` (the machine ignores its code), letters are
renamed by the explicit `letC`, and the sums over all letters follow the explicit order `letters`.
These sums are provably equal to those of `rhsS`, so the separation facts carry over. If `NM K l`
outputs `[true]` the two sides are equal in `T Σ̈`, and if it outputs `[false]` they are equal
neither in `K Σ̈` nor in `T Σ̈`.
-/

open scoped Computability

namespace DiagonaLean.KAComm.Reduction

open DiagonaLean.Foundations.KleeneAlgebra

open Cslib.Turing Enc RExp FreePreKA TD Undec DiagonaLean.Foundations.Computability

section letC

variable {St : Type} [Encodable St]

/-- The code of a letter. -/
def letC : Letter Bool St → ℕ
  | .lend => Nat.pair 0 0
  | .rend => Nat.pair 1 0
  | .cell o => Nat.pair 2 (hc o)
  | .head q o => Nat.pair 3 (Nat.pair (qc q) (hc o))

/-- `letC` is injective. -/
theorem letC_injective : Function.Injective (letC : Letter Bool St → ℕ) := by
  rintro (_ | _ | a | ⟨q, a⟩) (_ | _ | b | ⟨r, b⟩) h <;>
    simp [letC, Nat.pair_eq_pair] at h ⊢
  · exact hc_injective h
  · exact ⟨qc_injective h.1, hc_injective h.2⟩

end letC

variable (K : UConst) (l : List Bool)

/-- The optional states of `NM K l`. -/
def optStates : List (Option (NM K l).State) :=
  none :: (List.finRange (NN K l + 1)).map some

/-- All letters, in an explicit order. -/
def letters : List (Letter Bool (NM K l).State) :=
  [.lend, .rend] ++ syms.map .cell ++
    (optStates K l).flatMap fun q => syms.map (.head q)

/-- Every optional state of `NM K l` is in `optStates K l`. -/
theorem mem_optStates (q : Option (NM K l).State) : q ∈ optStates K l := by
  rcases q with _ | q
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_finRange q))

/-- Every letter is in `letters K l`. -/
theorem mem_letters (a : Letter Bool (NM K l).State) : a ∈ letters K l := by
  rcases a with _ | _ | o | ⟨q, o⟩
  · simp [letters]
  · simp [letters]
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (mem_syms o)))
  · exact List.mem_append_right _ (List.mem_flatMap.2 ⟨q, mem_optStates K l q,
      List.mem_map_of_mem (mem_syms o)⟩)

/-- `syms` has no duplicates. -/
theorem nodup_syms : syms.Nodup := by decide

/-- `optStates K l` has no duplicates. -/
theorem nodup_optStates : (optStates K l).Nodup :=
  List.nodup_cons.2 ⟨(fun h => by obtain ⟨_, _, h'⟩ := List.mem_map.1 h; cases h'),
    (List.nodup_finRange _).map (Option.some_injective _)⟩

/-- `letters K l` has no duplicates. -/
theorem nodup_letters : (letters K l).Nodup := by
  unfold letters
  refine List.Nodup.append (List.Nodup.append (by simp) ?_ ?_) ?_ ?_
  · exact nodup_syms.map fun a b h => by simpa using h
  · intro a ha hb
    simp only [List.mem_map] at hb
    obtain ⟨_, _, rfl⟩ := hb
    simp at ha
  · refine List.nodup_flatMap.2 ⟨fun q _ => nodup_syms.map fun a b h => by simpa using h, ?_⟩
    refine (nodup_optStates K l).imp fun {q r} hne x hx hy => ?_
    obtain ⟨o, _, rfl⟩ := List.mem_map.1 hx
    obtain ⟨o', _, ho⟩ := List.mem_map.1 hy
    exact hne (Letter.head.inj ho).1.symm
  · intro a ha hb
    obtain ⟨q, _, hb⟩ := List.mem_flatMap.1 hb
    obtain ⟨o, _, rfl⟩ := List.mem_map.1 hb
    simp [syms] at ha

/-- `letters K l` is a permutation of `enumL`. -/
theorem letters_perm : (letters K l).Perm (enumL (Letter Bool (NM K l).State)) :=
  (List.perm_ext_iff_of_nodup (nodup_letters K l) nodup_enumL).2 fun a =>
    ⟨fun _ => mem_enumL a, fun _ => mem_letters K l a⟩

/-- The letters of the doubled alphabet. -/
def lettersD : List (Letter Bool (NM K l).State ⊕ Letter Bool (NM K l).State) :=
  (letters K l).map .inl ++ (letters K l).map .inr

/-- `lettersD K l` is a permutation of `enumL` on the doubled alphabet. -/
theorem lettersD_perm :
    (lettersD K l).Perm (enumL (Letter Bool (NM K l).State ⊕ Letter Bool (NM K l).State)) := by
  refine (List.perm_ext_iff_of_nodup ?_ nodup_enumL).2 fun a =>
    ⟨fun _ => mem_enumL a, fun _ => ?_⟩
  · refine List.Nodup.append ((nodup_letters K l).map Sum.inl_injective)
      ((nodup_letters K l).map Sum.inr_injective) ?_
    intro a ha hb
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha
    obtain ⟨_, _, h⟩ := List.mem_map.1 hb
    cases h
  · rcases a with a | a
    · exact List.mem_append_left _ (List.mem_map_of_mem (mem_letters K l a))
    · exact List.mem_append_right _ (List.mem_map_of_mem (mem_letters K l a))

/-- `Σ`, in the order of `letters`. -/
def sigN : Ex (NM K l) := sumL ((letters K l).map fun a => pairS [a] [a])

/-- `Σ̈`, in the order of `lettersD`. -/
def sigAllN : Ex (NM K l) := sumL ((lettersD K l).map sym)

/-- `Σ^≠`, in the order of `letters`. -/
def sigNeN : Ex (NM K l) :=
  sumL ((letters K l).map fun a =>
    sumL (((letters K l).filter (· ≠ a)).map fun b => mul (sym (.inl a)) (sym (.inr b))))

/-- The residue, with explicit sums. -/
def rhoN : Ex (NM K l) :=
  mul (mul (RExp.star (sigAllN K l)) (bnd (rmS (NM K l)))) (RExp.star (rmS (NM K l)))

/-- The right-hand side, with explicit sums. -/
def rhsN : Ex (NM K l) :=
  plus (mul (RExp.star (sigN K l)) (plus (crunS (NM K l)) (haltS (NM K l) true)))
    (mul (RExp.star (sigN K l)) (mul (sigNeN K l) (rhoN K l)))

/-- Sums over permuted lists are equal in `TD`. -/
theorem mk_sumL_perm {β : Type} {L L' : List β} (h : L.Perm L')
    (f : β → Ex (NM K l)) :
    (mk (sumL (L.map f)) : TD _) = mk (sumL (L'.map f)) := by
  rw [mk_sumL, mk_sumL]
  exact ((h.map f).map mk).sum_eq

/-- `sigN K l` equals `sigS` in `TD`. -/
theorem mk_sigN : (mk (sigN K l) : TD _) = mk (sigS (NM K l)) :=
  mk_sumL_perm K l (letters_perm K l) _

/-- `sigAllN K l` equals `sigAllS` in `TD`. -/
theorem mk_sigAllN : (mk (sigAllN K l) : TD _) = mk (sigAllS (NM K l)) :=
  mk_sumL_perm K l (lettersD_perm K l) _

/-- `sigNeN K l` equals `sigNeS` in `TD`. -/
theorem mk_sigNeN : (mk (sigNeN K l) : TD _) = mk (sigNeS (NM K l)) := by
  unfold sigNeN sigNeS
  rw [mk_sumL_perm K l (letters_perm K l), mk_sumL, mk_sumL, List.map_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
  exact mk_sumL_perm K l ((letters_perm K l).filter _) _

/-- `rhsN K l` equals `rhsS` with output `true` in `TD`. -/
theorem mk_rhsN : (mk (rhsN K l) : TD _) = mk (rhsS (NM K l) true) := by
  simp only [rhsN, rhsS, rhoN, rhoS, mk_plus, mk_mul, mk_star, mk_sigN, mk_sigAllN, mk_sigNeN]

/-- The left-hand side, renamed. -/
def redA : RExp (ℕ ⊕ ℕ) := (lhsS (NM K l) []).map (dmap letC)

/-- The right-hand side, renamed. -/
def redB : RExp (ℕ ⊕ ℕ) := (rhsN K l).map (dmap letC)

/-- The instance `(e + f, f)`, where `e ≤ f` is the inequality of `NM K l` on empty input. -/
def rInst : Inst := (plus (redA K l) (redB K l), redB K l)

variable {K l}

/-- A machine with output `1` makes the two sides equal in `T Σ̈`. -/
theorem rInst_pos (h : (NM K l).Outputs [] [true]) :
    Equiv DComm (rInst K l).1 (rInst K l).2 := by
  have hle : (mk (lhsS (NM K l) []) : TD _) ≤ mk (rhsN K l) := by
    rw [mk_rhsN]
    exact le_of_outputs h
  have : Provable (redA K l, redB K l) := le_map letC hle
  exact (provable_iff_equiv _).1 this

/-- A machine with output `0` makes `redA K l ≤ redB K l` false in the model. -/
theorem not_modelLe (h : (NM K l).Outputs [] [false]) : ¬ ModelLe (redA K l, redB K l) := fun hle => by
  have h₁ := pl_le_of_map letC_injective hle
  rw [mk_rhsN] at h₁
  exact not_pl_le_of_outputs h (by decide) h₁

/-- A machine with output `0` keeps the two sides apart in `T Σ̈`. -/
theorem rInst_neg (h : (NM K l).Outputs [] [false]) :
    ¬ Equiv DComm (rInst K l).1 (rInst K l).2 := fun hE =>
  not_modelLe h ((provable_iff_equiv (redA K l, redB K l)).2 hE).modelLe

/-- A machine with output `1` makes the two sides equal in `K Σ̈`. -/
theorem rInst_pos_ka (h : (NM K l).Outputs [] [true]) :
    KAEquiv DComm (rInst K l).1 (rInst K l).2 :=
  .ofEquiv (rInst_pos h)

/-- A machine with output `0` keeps the two sides apart in `K Σ̈`. -/
theorem rInst_neg_ka (h : (NM K l).Outputs [] [false]) :
    ¬ KAEquiv DComm (rInst K l).1 (rInst K l).2 := fun hE =>
  not_modelLe h (KAProvable.modelLe (i := (redA K l, redB K l)) hE)

end DiagonaLean.KAComm.Reduction
