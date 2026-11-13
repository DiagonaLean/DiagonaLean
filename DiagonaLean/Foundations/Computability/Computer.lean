/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.Compiler
import DiagonaLean.Foundations.Computability.Interpreter
import DiagonaLean.Halt.Undecidable

@[expose] public section

/-! # A computable function on bit strings, as a Cslib machine

`exists_computer`: every `Computable f : List Bool → List Bool` is computed by a `SingleTapeTM Bool`
on raw bits, with exactly `f l` on the tape at the end.

The machine is a composition of three. A queue machine expands the raw bits into blocks, the
compiled machine of `exists_compiled` runs, and another queue machine contracts the blocks back to
raw bits. A string `l` is carried as the number whose binary digits, most significant first, are `1`
followed by `l` (`numOf`).

## Main statements

* `exists_computer`: the machine.
* `exists_computes`: the form used for reductions, `ComputesReduction R enc₁ enc₂ f`.
-/

namespace DiagonaLean.Foundations.Computability

open Turing PartrecToTM2 Cslib.Turing SingleTapeTM DiagonaLean.Halt.Undecidable
  DiagonaLean.Halt.Compositions

/-! ### Strings as numbers -/

/-- The number whose binary digits are `1` followed by `l`. -/
def numOf (l : List Bool) : ℕ := l.foldl (fun acc b => 2 * acc + b.toNat) 1

/-- The inverse of `numOf`. -/
def listOf (n : ℕ) : List Bool := (bitsOf n).reverse.tail

theorem numOf_snoc (l : List Bool) (b : Bool) : numOf (l ++ [b]) = 2 * numOf l + b.toNat := by
  simp [numOf, List.foldl_append]

theorem numOf_pos (l : List Bool) : 0 < numOf l := by
  induction l using List.reverseRecOn with
  | nil => decide
  | append_singleton l b ih =>
    rw [numOf_snoc]
    omega

theorem trNat_numOf (l : List Bool) : trNat (numOf l) = l.reverse.map bitG ++ [.bit1] := by
  induction l using List.reverseRecOn with
  | nil =>
    have h := trNat_step (n := 1) (by omega)
    simpa [numOf, bitG, PartrecToTM2.trNat_zero] using h
  | append_singleton l b ih =>
    have hne : numOf (l ++ [b]) ≠ 0 := (numOf_pos _).ne'
    rw [trNat_step hne, numOf_snoc]
    have h1 : (2 * numOf l + b.toNat) % 2 = b.toNat := by cases b <;> simp
    have h2 : (2 * numOf l + b.toNat) / 2 = numOf l := by cases b <;> simp; omega
    rw [h1, h2, ih]
    cases b <;> simp

theorem bitG_injective : Function.Injective bitG := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitG]

theorem bitsOf_numOf (l : List Bool) : bitsOf (numOf l) = l.reverse ++ [true] := by
  apply List.map_injective_iff.2 bitG_injective
  rw [bitsOf_map, trNat_numOf]
  simp [bitG]

theorem listOf_numOf (l : List Bool) : listOf (numOf l) = l := by
  simp [listOf, bitsOf_numOf]

theorem numOf_prim : Primrec numOf := by
  unfold numOf
  have h : Primrec₂ fun (_ : List Bool) (y : ℕ × Bool) => 2 * y.1 + y.2.toNat := by
    apply Primrec₂.mk
    have hb : Primrec fun z : List Bool × (ℕ × Bool) => z.2.2.toNat :=
      (Primrec.dom_finite Bool.toNat).comp (prim_snd Primrec.snd)
    exact prim_add (prim_mul (Primrec.const 2) (prim_fst Primrec.snd)) hb
  exact Primrec.list_foldl Primrec.id (Primrec.const 1) h

theorem listOf_prim : Primrec listOf :=
  prim_tail (prim_reverse bitsOf_prim)

/-! ### The machine -/

theorem flat_singletons (l : List Bool) : flat (l.map fun b => (b, ([] : List Bool))) = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa [flat] using ih

theorem flatMap_fst {β : Type} (g : Bool → β) (l : List Bool) :
    (l.map fun b => (b, g b)).flatMap (fun x => [x.1]) = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa using ih

/-- **Every computable function on bit strings is computed by a Cslib machine.** -/
theorem exists_computer (f : List Bool → List Bool) (hf : Computable f) :
    ∃ R : SingleTapeTM Bool, ∀ l, R.Outputs l (f l) := by
  let g : ℕ → ℕ := fun n => numOf (f (listOf n))
  have hg : Computable g := numOf_prim.to_comp.comp (hf.comp listOf_prim.to_comp)
  obtain ⟨W, k, e₀, e, r0, r1, he₀, h0, hr0, h1, hr1, hW⟩ := exists_compiled (g : ℕ →. ℕ) hg.partrec
  -- the tape of a string
  have htape : ∀ l, e₀ ++ (trNat (numOf l)).reverse.flatMap e =
      e₀ ++ (e .bit1 ++ l.flatMap fun b => e (bitG b)) := by
    intro l
    rw [trNat_numOf]
    simp [List.flatMap_map]
  -- expansion
  let wE : Bool → List Bool := fun b => e (bitG b)
  let PE : List Bool := e₀ ++ e .bit1
  have hwE : ∀ b, (wE b).length = k + 2 := by
    intro b
    cases b
    · simp [wE, bitG, h0, hr0]
    · simp [wE, bitG, h1, hr1]
  let E := queueTM 0 1 (PE.length + (k + 2)) wE PE
  have hE : ∀ l, E.Outputs l (e₀ ++ (trNat (numOf l)).reverse.flatMap e) := by
    intro l
    have := queue_outputs (s := 0) (a := 1) (M := PE.length + (k + 2)) (w := wE) (P := PE)
      (by
        rintro (_ | _ | b)
        · simp [srcW]
        · simp [srcW]
        · simp only [srcW, hwE]
          omega)
      (l.map fun b => (b, [])) (by simp)
    rw [flat_singletons] at this
    rw [htape]
    have hout : PE ++ (List.drop 0 (l.map fun b => (b, ([] : List Bool)))).flatMap
        (fun x => wE x.1) = e₀ ++ (e .bit1 ++ l.flatMap fun b => e (bitG b)) := by
      simp [PE, wE, List.flatMap_map, List.append_assoc]
    rw [hout] at this
    exact this
  -- contraction
  obtain ⟨h₀, t₀, rfl⟩ : ∃ h₀ t₀, e₀ = h₀ :: t₀ := by
    cases e₀ with
    | nil => simp at he₀
    | cons a t => exact ⟨a, t, rfl⟩
  let C := queueTM 2 (k + 2) 1 (fun b => [b]) []
  have hC : ∀ l, C.Outputs (h₀ :: t₀ ++ (trNat (numOf l)).reverse.flatMap e) l := by
    intro l
    have := queue_outputs (s := 2) (a := k + 2) (M := 1) (w := fun b => [b]) (P := [])
      (by rintro (_ | _ | b) <;> simp [srcW])
      ((h₀, t₀) :: (true, r1) :: l.map fun b => (b, if b then r1 else r0))
      (by
        intro x hx
        simp only [List.mem_cons, List.mem_map] at hx
        rcases hx with rfl | rfl | ⟨b, _, rfl⟩
        · simpa using he₀
        · simp [hr1]
        · cases b <;> simp [hr0, hr1])
    have hflat : flat ((h₀, t₀) :: (true, r1) :: l.map fun b => (b, if b then r1 else r0)) =
        h₀ :: t₀ ++ (trNat (numOf l)).reverse.flatMap e := by
      rw [htape, h1]
      have hb : ∀ b : Bool, e (bitG b) = b :: (if b then r1 else r0) := by
        intro b
        cases b
        · simpa [bitG] using h0
        · simpa [bitG] using h1
      simp only [flat, List.flatMap_cons, List.flatMap_map, hb]
    rw [hflat] at this
    have hout : [] ++ (List.drop 2 ((h₀, t₀) :: (true, r1) ::
        l.map fun b => (b, if b then r1 else r0))).flatMap (fun x => [x.1]) = l := by
      simpa using flatMap_fst (fun b => if b then r1 else r0) l
    rw [hout] at this
    exact this
  refine ⟨compComputer E (compComputer W C), fun l => ?_⟩
  have hgl : g (numOf l) = numOf (f l) := by simp [g, listOf_numOf]
  refine compComputer_seq_outputs (hE l)
    (compComputer_seq_outputs (hW (numOf l) (numOf (f l)) ?_) (hC (f l)))
  show numOf (f l) ∈ Part.some (g (numOf l))
  rw [hgl]
  exact Part.mem_some _

/-- A reduction computed through a computable function on codes. -/
theorem exists_computes {X Y : Type*} {enc₁ : X → List Bool} {enc₂ : Y → List Bool} {f : X → Y}
    (F : List Bool → List Bool) (hF : Computable F) (h : ∀ x, F (enc₁ x) = enc₂ (f x)) :
    ∃ R : SingleTapeTM Bool, ComputesReduction R enc₁ enc₂ f := by
  obtain ⟨R, hR⟩ := exists_computer F hF
  exact ⟨R, fun x => h x ▸ hR (enc₁ x)⟩

end DiagonaLean.Foundations.Computability
