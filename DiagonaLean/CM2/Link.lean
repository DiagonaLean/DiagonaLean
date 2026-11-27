/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CM2.Assembly

@[expose] public section

/-! # Linking blocks into a program

A list of blocks whose exits are labelled by natural numbers is linked into one program
(`link`): the blocks are laid out in order, and exit `i` is the address of block `i` (`addr`).
An exit beyond the last block is the length of the program, where the machine halts
(`length_link`). Each block is loaded at its address (`loaded_link`).

A halting computation is analysed by induction on the configurations it passes through
(`halting_induction`).
-/

namespace DiagonaLean.CM2

open Block StateTransition

/-- The address of block `i`: the total size of the blocks before it. -/
def addr (bs : List (Block ℕ)) (i : ℕ) : ℕ := ((bs.take i).map Block.size).sum

/-- The code of the blocks `bs` laid out from the address `base`, with exits resolved by `dst`. -/
def emitAll (dst : ℕ → ℕ) : List (Block ℕ) → ℕ → List Instr
  | [], _ => []
  | b :: bs, base => b.emit base dst ++ emitAll dst bs (base + b.size)

/-- The program of the blocks `bs`: exit `i` of every block is the address of block `i`. -/
def link (bs : List (Block ℕ)) : List Instr := emitAll (addr bs) bs 0

/-- The code of a list of blocks has the total size of the blocks. -/
theorem length_emitAll (dst : ℕ → ℕ) (bs : List (Block ℕ)) (base : ℕ) :
    (emitAll dst bs base).length = (bs.map Block.size).sum := by
  induction bs generalizing base with
  | nil => rfl
  | cons b bs ih => simp [emitAll, b.length_emit, ih]

/-- The exit beyond the last block is the length of the program. -/
theorem length_link (bs : List (Block ℕ)) : (link bs).length = addr bs bs.length := by
  simp [link, addr, length_emitAll]

/-- The code of a list of blocks is the code of each block at its address. -/
theorem emitAll_eq_flatMap (dst : ℕ → ℕ) (bs : List (Block ℕ)) (base : ℕ) :
    emitAll dst bs base = bs.zipIdx.flatMap fun p => p.1.emit (base + addr bs p.2) dst := by
  induction bs generalizing base with
  | nil => rfl
  | cons b bs ih =>
    rw [emitAll, ih, List.zipIdx_cons', List.flatMap_cons, List.flatMap_map]
    simp [addr, Nat.add_assoc]

/-- In the code of `pre ++ b :: post` placed after `base` instructions, the block `b` is loaded
at its address. -/
theorem loaded_emitAll (dst : ℕ → ℕ) (pre : List (Block ℕ)) (b : Block ℕ)
    (post : List (Block ℕ)) (base : ℕ) (xs : List Instr) (hx : xs.length = base) :
    Loaded (xs ++ emitAll dst (pre ++ b :: post) base) (base + (pre.map Block.size).sum)
      (b.emit (base + (pre.map Block.size).sum) dst) := by
  induction pre generalizing base xs with
  | nil =>
    intro i j hj
    subst hx
    simp only [List.map_nil, List.sum_nil, Nat.add_zero, List.nil_append, emitAll] at hj ⊢
    have hi := (List.getElem?_eq_some_iff.mp hj).choose
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hi, hj]
  | cons a pre ih =>
    have h := ih (base + a.size) (xs ++ a.emit base dst) (by simp [hx, a.length_emit])
    simpa [emitAll, Nat.add_assoc] using h

/-- Block `j` of a linked program is loaded at `addr bs j`, with exits resolved by `addr bs`. -/
theorem loaded_link (bs : List (Block ℕ)) (j : ℕ) (hj : j < bs.length) :
    Loaded (link bs) (addr bs j) (bs[j].emit (addr bs j) (addr bs)) := by
  have h := loaded_emitAll (addr bs) (bs.take j) bs[j] (bs.drop (j + 1)) 0 [] rfl
  rw [← List.drop_eq_getElem_cons hj, List.take_append_drop] at h
  simpa [link, addr] using h

/-- A block of a linked program that runs to exit `i` takes the program from the block's address
to the address of block `i`. -/
theorem reaches_link {bs : List (Block ℕ)} {j : ℕ} (hj : j < bs.length) {a b i a' b' : ℕ}
    (h : bs[j].Runs a b i a' b') :
    Reaches₁ (step (link bs)) (addr bs j, a, b) (addr bs i, a', b') :=
  h _ _ _ (loaded_link bs j hj)

/-- **Induction along a halting computation.** A property holds at a configuration from which the
machine halts if it holds at every such configuration whose later configurations have it. -/
theorem halting_induction {p : List Instr} {C : Config → Prop} {s : Config}
    (hs : Halting (p, s))
    (H : ∀ s, Halting (p, s) → (∀ s', Reaches₁ (step p) s s' → C s') → C s) : C s := by
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp hs
  have key : ∀ s', Reaches (step p) s s' → C s' := by
    refine evalInduction (C := fun a => ∀ s', Reaches (step p) a s' → C s') hb ?_
    intro a _ ih s' hreach
    refine H s' ?_ ?_
    · change (eval (step p) s').Dom
      rw [← reaches_eval hreach]
      exact Part.dom_iff_mem.mpr ⟨b, ‹_›⟩
    · intro s'' h₁
      obtain ⟨a₁, ha₁, hrest⟩ := Relation.TransGen.head'_iff.mp
        (Relation.TransGen.trans_right hreach h₁)
      exact ih a₁ ha₁ s'' hrest
  exact key s Relation.ReflTransGen.refl

/-- Halting is invariant along a computation. -/
theorem halting_of_reaches₁ {p : List Instr} {s s' : Config} (h : Reaches₁ (step p) s s') :
    Halting (p, s) ↔ Halting (p, s') := by
  change (eval (step p) s).Dom ↔ (eval (step p) s').Dom
  rw [reaches_eval h.to_reflTransGen]

/-- The machine halts at a configuration outside its program. -/
theorem halting_of_length_le {p : List Instr} {s : Config} (h : p.length ≤ s.1) :
    Halting (p, s) := by
  change (eval (step p) s).Dom
  have hmem : s ∈ eval (step p) s :=
    mem_eval.mpr ⟨Relation.ReflTransGen.refl, (step_eq_none_iff p s).mpr h⟩
  exact Part.dom_iff_mem.mpr ⟨s, hmem⟩

end DiagonaLean.CM2
