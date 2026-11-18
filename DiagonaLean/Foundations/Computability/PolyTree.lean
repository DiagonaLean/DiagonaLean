/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.PrimrecRec

@[expose] public section

/-! # Finitely branching trees are `Primcodable`

`PTree α ar` is the type of trees whose nodes carry a shape `a : α` and exactly `ar a` children:
the W-type of the polynomial with shapes `α` and arities `ar`. Almost every inductive type is of
this form. When `α` is `Primcodable` and `ar` is primitive recursive, `PTree α ar` is `Primcodable`
(Theorem A of `AUTOMATION.md`).

The encoding sends `node a cs` to `Nat.pair (encode a) (encode [encode (cs 0), …])`. A child's code
is smaller than its parent's (`encode_child_lt`), so decoding is a recursion on the code. Because
the encoding is canonical, `encode (decode n)` is `n + 1` when `n` is the code of a tree and `0`
otherwise, so the decoder is primitive recursive as soon as the set of codes is
(`valid_primrec`), which is a course-of-values recursion.

`PTree` is its own inductive type rather than Mathlib's `WType`, which already has a different
`Encodable` instance.
-/

namespace DiagonaLean.Foundations.Computability

open Encodable

/-- Trees whose nodes carry a shape `a : α` and `ar a` children. -/
inductive PTree (α : Type) (ar : α → ℕ) : Type where
  /-- A node with shape `a` and children `cs`. -/
  | node (a : α) (cs : Fin (ar a) → PTree α ar)

namespace PTree

variable {α : Type} {ar : α → ℕ}

section Encode

variable [Encodable α]

/-- The code of a tree. -/
def code : PTree α ar → ℕ
  | node a cs => Nat.pair (encode a) (encode (List.ofFn fun i => code (cs i)))

/-- An element of a list of numbers is smaller than the list's code. -/
theorem lt_encode_of_mem {c : ℕ} : ∀ {l : List ℕ}, c ∈ l → c < encode l
  | x :: l, h => by
    rw [encode_list_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.lt_succ_of_le (Nat.left_le_pair _ _)
    · exact Nat.lt_succ_of_le ((lt_encode_of_mem h).le.trans (Nat.right_le_pair _ _))

/-- A child's code is smaller than its parent's. -/
theorem code_child_lt (a : α) (cs : Fin (ar a) → PTree α ar) (i : Fin (ar a)) :
    code (cs i) < code (node a cs) := by
  rw [code]
  have h : code (cs i) ∈ List.ofFn fun j => code (cs j) := List.mem_ofFn.2 ⟨i, rfl⟩
  exact (lt_encode_of_mem h).trans_le (Nat.right_le_pair _ _)

/-- Decoding: a node is decoded when its shape decodes (with `decode₂`, so that decoding is
canonical), its list of child codes has length
`ar a` and only smaller entries, and every child decodes. -/
def decodeT (n : ℕ) : Option (PTree α ar) :=
  match decode₂ α n.unpair.1, decode₂ (List ℕ) n.unpair.2 with
  | some a, some l =>
    if hl : l.length = ar a ∧ ∀ c ∈ l, c < n then
      let cs : Fin (ar a) → Option (PTree α ar) := fun i =>
        have : l[i.val] < n := hl.2 _ (List.getElem_mem _)
        decodeT l[i.val]
      if hall : ∀ i, (cs i).isSome then some (node a fun i => (cs i).get (hall i)) else none
    else none
  | _, _ => none
termination_by n

/-- Decoding inverts the code. -/
theorem decodeT_code (t : PTree α ar) : decodeT (code t) = some t := by
  induction t with
  | node a cs ih =>
    rw [decodeT, code, Nat.unpair_pair, encodek₂, encodek₂]
    simp only
    have hl : (List.ofFn fun i => code (cs i)).length = ar a ∧
        ∀ c ∈ List.ofFn (fun i => code (cs i)), c < Nat.pair (encode a)
          (encode (List.ofFn fun i => code (cs i))) := by
      refine ⟨List.length_ofFn, fun c hc => ?_⟩
      exact (lt_encode_of_mem hc).trans_le (Nat.right_le_pair _ _)
    rw [dite_eq_left_of_eq_true (eq_true hl)]
    have hc : ∀ i : Fin (ar a), decodeT (α := α) (ar := ar)
        (List.ofFn fun j => code (cs j))[i.val] = some (cs i) := fun i => by
      simp only [List.getElem_ofFn]
      exact ih i
    have hall : ∀ i : Fin (ar a), (decodeT (α := α) (ar := ar)
        (List.ofFn fun j => code (cs j))[i.val]).isSome := fun i => by rw [hc i]; rfl
    rw [dite_eq_left_of_eq_true (eq_true hall)]
    congr 2
    funext i
    simp only [hc i, Option.get_some]

/-- Decoding is canonical: a decoded tree has the code it was decoded from. -/
theorem code_of_decodeT : ∀ (n : ℕ) {t : PTree α ar}, decodeT n = some t → code t = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t ht
    rw [decodeT] at ht
    split at ht
    · rename_i a l ha hl'
      split at ht
      · rename_i hl
        dsimp only at ht
        split at ht
        · cases ht
          rw [code, (decode₂_eq_some.1 ha)]
          conv_rhs => rw [← Nat.pair_unpair n]
          congr 1
          conv_rhs => rw [← decode₂_eq_some.1 hl']
          congr 1
          apply List.ext_getElem (by simp [hl.1])
          intro j hj₁ hj₂
          simp only [List.getElem_ofFn]
          exact ih _ (hl.2 _ (List.getElem_mem _)) (Option.get_mem _)
        · cases ht
      · cases ht
    · cases ht

/-- One step of the test for codes: `n` is a code, given the table `T` of answers below `n`. -/
def validStep (n : ℕ) (T : List Bool) : Bool :=
  (decode₂ α n.unpair.1).elim false fun a =>
    (decode₂ (List ℕ) n.unpair.2).elim false fun l =>
      decide (l.length = ar a) && l.all fun c => decide (c < n) && T.getD c false

/-- Whether `n` is a code satisfies the course-of-values equation of `validStep`. -/
theorem isSome_decodeT (n : ℕ) : (decodeT (α := α) (ar := ar) n).isSome =
    validStep (α := α) (ar := ar) n ((List.range n).map fun m => (decodeT (α := α) (ar := ar) m).isSome) := by
  rw [decodeT, validStep]
  split
  · rename_i a l ha hl'
    rw [ha, hl']
    simp only [Option.elim]
    by_cases hl : l.length = ar a ∧ ∀ c ∈ l, c < n
    · rw [dite_eq_left_of_eq_true (eq_true hl)]
      have hlook : ∀ c ∈ l, (decide (c < n) && ((List.range n).map fun m =>
          (decodeT (α := α) (ar := ar) m).isSome).getD c false) =
          (decodeT (α := α) (ar := ar) c).isSome := fun c hc => by
        rw [getD_map_range_of_lt _ (hl.2 c hc)]
        simp [hl.2 c hc]
      have hall' : (l.all fun c => decide (c < n) && ((List.range n).map fun m =>
          (decodeT (α := α) (ar := ar) m).isSome).getD c false) =
          l.all fun c => (decodeT (α := α) (ar := ar) c).isSome := by
        rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
        exact ⟨fun h c hc => hlook c hc ▸ h c hc, fun h c hc => (hlook c hc).symm ▸ h c hc⟩
      rw [hall']
      by_cases hall : ∀ i : Fin (ar a), (decodeT (α := α) (ar := ar) l[i.val]).isSome
      · rw [dite_eq_left_of_eq_true (eq_true hall)]
        simp only [Option.isSome_some, hl.1, decide_true, Bool.true_and]
        symm
        rw [List.all_eq_true]
        intro c hc
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
        exact hall ⟨j, hl.1 ▸ hj⟩
      · rw [dite_eq_right_of_eq_false (eq_false hall)]
        simp only [Option.isSome_none, hl.1, decide_true, Bool.true_and]
        symm
        rw [Bool.eq_false_iff, ne_eq, List.all_eq_true]
        intro h
        exact hall fun i => h _ (List.getElem_mem _)
    · rw [dite_eq_right_of_eq_false (eq_false hl)]
      simp only [Option.isSome_none]
      symm
      rw [Bool.eq_false_iff, ne_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      rintro ⟨hlen, h⟩
      refine hl ⟨hlen, fun c hc => ?_⟩
      have := h c hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
  · rename_i x y hxy
    simp only [Option.isSome_none]
    cases ha : decode₂ α n.unpair.1 <;> cases hl' : decode₂ (List ℕ) n.unpair.2 <;>
      simp_all [Option.elim]

/-- Trees are `Encodable`, through `code` and `decodeT`. -/
instance : Encodable (PTree α ar) where
  encode := code
  decode := decodeT
  encodek := decodeT_code

/-- The code of a decoded number: `n + 1` for a code, `0` otherwise. -/
theorem encode_decodeT (n : ℕ) :
    encode (decodeT (α := α) (ar := ar) n) = if (decodeT (α := α) (ar := ar) n).isSome then n + 1
      else 0 := by
  cases h : decodeT (α := α) (ar := ar) n with
  | none => rfl
  | some t =>
    show code t + 1 = _
    rw [code_of_decodeT n h]
    rfl

end Encode

section Prim

variable [Primcodable α]

/-- The test step is primitive recursive. -/
theorem validStep_primrec (hAr : Primrec ar) :
    Primrec fun q : ℕ × List Bool => validStep (α := α) (ar := ar) q.1 q.2 := by
  unfold validStep
  fun_prop

/-- **The codes of trees form a primitive recursive set.** -/
theorem valid_primrec (hAr : Primrec ar) :
    Primrec fun n => (decodeT (α := α) (ar := ar) n).isSome := by
  have h := Primrec.nat_strong_rec (fun (_ : Unit) n => (decodeT (α := α) (ar := ar) n).isSome)
    (g := fun _ T => some (validStep (α := α) (ar := ar) T.length T))
    (Primrec.option_some.comp ((validStep_primrec hAr).comp
      ((prim_length Primrec.snd).pair Primrec.snd)))
    (fun _ n => by rw [List.length_map, List.length_range, isSome_decodeT n])
  exact h.comp (Primrec.const ()) Primrec.id

/-- **Theorem A.** Finitely branching trees with `Primcodable` shapes and primitive recursive
arities are `Primcodable`. -/
instance primcodable [Fact (Primrec ar)] : Primcodable (PTree α ar) where
  prim := by
    have hv := valid_primrec (α := α) (Fact.out : Primrec ar)
    have h : Primrec fun n => if (decodeT (α := α) (ar := ar) n).isSome then n + 1 else 0 := by
      fun_prop
    exact (Primrec.nat_iff.1 h).of_eq fun n => (encode_decodeT n).symm

end Prim

end PTree

end DiagonaLean.Foundations.Computability
