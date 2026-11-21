/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.Prim
import Mathlib.Logic.Equiv.Finset
import Mathlib.Data.List.Sort

@[expose] public section

/-! # Finite sets are `Primcodable`

Mathlib encodes a finite set as the code of the list of its elements, sorted by their codes
(`Finset.encodable`). That encoding has a primitive recursive decoder, so `Finset β` is
`Primcodable` on top of it (`Finset.primcodable`), with no second encoding.

The sorted list is the insertion sort by code (`encode_finset_mk`), since sorted permutations
under an antisymmetric order are equal; insertion sort is primitive recursive (`prim_insertionSort`),
and so is `encode (decode n)` (`encode_decode_finset`). `List.toFinset` is primitive recursive
(`prim_toFinset`).
-/

namespace DiagonaLean.Foundations.Computability

open Encodable

section Enc

variable {β : Type} [Encodable β]

/-- Comparison by code. -/
def encLE (a b : β) : Prop := encode a ≤ encode b

instance : DecidableRel (encLE (β := β)) := fun _ _ => inferInstanceAs (Decidable (_ ≤ _))
instance : IsTrans β encLE := ⟨fun _ _ _ h₁ h₂ => Nat.le_trans h₁ h₂⟩
instance : Std.Total (encLE (β := β)) := ⟨fun a b => Nat.le_total (encode a) (encode b)⟩
instance : Std.Antisymm (encLE (β := β)) :=
  ⟨fun _ _ h₁ h₂ => encode_injective (Nat.le_antisymm h₁ h₂)⟩

/-- **Mathlib's code of a finite set** is the code of its elements, sorted by their codes. -/
theorem encode_finset_mk (l : List β) (h : l.Nodup) :
    encode (⟨↑l, h⟩ : Finset β) = encode (l.insertionSort encLE) := by
  show encodeMultiset (↑l : Multiset β) = _
  unfold encodeMultiset
  congr 1
  apply List.Perm.eq_of_pairwise' (r := encLE)
  · exact Multiset.pairwise_sort _ _
  · exact List.pairwise_insertionSort _ _
  · exact (List.mergeSort_perm l _).trans (List.perm_insertionSort _ _).symm

/-- `encode (decode n)` for finite sets: the decoded list, if it has no duplicates, sorted. -/
theorem encode_decode_finset [DecidableEq β] (n : ℕ) : encode (decode (α := Finset β) n) =
    (decode (α := List β) n).elim 0 fun l =>
      if l.Nodup then encode (l.insertionSort encLE) + 1 else 0 := by
  simp only [decode, decodeSubtype]
  show encode (((decodeMultiset n).bind _).bind _) = _
  unfold decodeMultiset
  cases h : decode (α := List β) n with
  | none =>
    have h' : decodeList n = none := h
    simp [h']
  | some l =>
    have h' : decodeList n = some l := h
    by_cases hn : l.Nodup
    · simp only [h', Option.elim, hn, ite_true]
      simp only [Option.map_eq_map, Option.map_some, Option.bind_some, Multiset.coe_nodup, hn,
          ↓reduceDIte, Equiv.symm_mk, Equiv.coe_fn_mk, Function.comp_apply, encode_some,
          Nat.succ_eq_add_one, Nat.add_right_cancel_iff]
      exact encode_finset_mk l hn
    · simp [h', hn]
end Enc

section Prim

variable {α β : Type} [Primcodable α] [Primcodable β]

/-- `orderedInsert` by code, as a list recursion that also uses the tail. -/
theorem orderedInsert_eq (a : β) (l : List β) : l.orderedInsert encLE a =
    List.recOn l [a] fun b l ih => if encode a ≤ encode b then a :: b :: l else b :: ih := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.orderedInsert, ← ih]; rfl

@[fun_prop] theorem prim_orderedInsert {f : α → β} {g : α → List β} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => (g x).orderedInsert encLE (f x) := by
  have h : Primrec fun q : β × List β => List.recOn (motive := fun _ => List β) q.2 [q.1]
      fun b l ih => if encode q.1 ≤ encode b then q.1 :: b :: l else b :: ih := by
    refine Primrec.list_rec (g := fun q : β × List β => [q.1])
      (h := fun q y => if encode q.1 ≤ encode y.1 then q.1 :: y.1 :: y.2.1 else y.1 :: y.2.2)
      Primrec.snd (by fun_prop) ?_
    apply Primrec₂.mk
    fun_prop
  exact (h.of_eq fun q => (orderedInsert_eq q.1 q.2).symm).comp (hf.pair hg)

@[fun_prop] theorem prim_insertionSort {f : α → List β} (hf : Primrec f) :
    Primrec fun x => (f x).insertionSort encLE := by
  have h : Primrec fun l : List β => l.foldr (fun b acc => acc.orderedInsert encLE b) [] := by
    fun_prop
  exact (h.of_eq fun l => by induction l <;> simp_all [List.insertionSort]).comp hf

theorem pred_nodup [DecidableEq β] {f : α → List β} (hf : Primrec f) :
    PrimrecPred fun x => (f x).Nodup :=
  (pred_eq (prim_dedup hf) hf).of_eq fun _ => List.dedup_eq_self

/-- **Finite sets are `Primcodable`**, with Mathlib's encoding. -/
instance Finset.primcodable : Primcodable (Finset β) :=
  { (inferInstance : Encodable (Finset β)) with
    prim := by
      have := decidableEqOfEncodable β
      have hn := pred_nodup (f := fun l : List β => l) Primrec.id
      have h : Primrec fun n : ℕ => (decode (α := List β) n).elim 0 fun l =>
          if l.Nodup then encode (l.insertionSort encLE) + 1 else 0 := by fun_prop
      exact (Primrec.nat_iff.1 h).of_eq fun n => (encode_decode_finset n).symm }

/-- **`List.toFinset` is primitive recursive.** -/
@[fun_prop] theorem prim_toFinset [DecidableEq β] {f : α → List β} (hf : Primrec f) :
    Primrec fun x => (f x).toFinset := by
  have h : Primrec fun l : List β => encode (l.dedup.insertionSort encLE) := by fun_prop
  refine (Primrec.encode_iff.1 (h.of_eq fun l => ?_)).comp hf
  show _ = encode (⟨↑l.dedup, List.nodup_dedup l⟩ : Finset β)
  rw [encode_finset_mk]

end Prim

end DiagonaLean.Foundations.Computability
