/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CM2.Simulation
import DiagonaLean.Foundations.Computability.Prim

@[expose] public section

/-! # The assembler is primitive recursive

A program of the simulation is given by a list of pairs of a kind of block and a list of exits
(`Simulation.lean`). `assemble cs` turns such a list into the list of instructions, and it is
primitive recursive when the symbols are finite (`assemble_prim`): there are finitely many
kinds, and the instructions of each kind are primitive recursive in the address and the exit
addresses (`Block.prim_emit`).
-/

derive_primcodable DiagonaLean.CM2.Kind

namespace DiagonaLean.CM2

open DiagonaLean.Foundations.Computability

/-- **A definition by finitely many cases is primitive recursive.** If `all` lists every element
of `S` and each `g a` is primitive recursive, then so is `fun x => g (s x) x` for a primitive
recursive `s`. -/
theorem prim_cases {S X Y : Type} [Primcodable S] [Primcodable X] [Primcodable Y]
    [DecidableEq S] [Inhabited Y] (all : List S) (hall : ∀ a, a ∈ all) {s : X → S}
    (hs : Primrec s) {g : S → X → Y} (hg : ∀ a, Primrec (g a)) :
    Primrec fun x => g (s x) x := by
  have key : ∀ l : List S, Primrec fun x =>
      l.foldr (fun a acc => if s x = a then g a x else acc) default := by
    intro l
    induction l with
    | nil => exact Primrec.const _
    | cons a l ih =>
      exact Primrec.ite (Primrec.eq.comp hs (Primrec.const a)) (hg a) ih
  refine (key all).of_eq fun x => ?_
  have h : ∀ l : List S, s x ∈ l →
      l.foldr (fun a acc => if s x = a then g a x else acc) default = g (s x) x := by
    intro l
    induction l with
    | nil => intro h; cases h
    | cons a l ih =>
      intro hm
      by_cases e : s x = a
      · simp [e]
      · simp only [List.foldr_cons, e, ite_false]
        exact ih ((List.mem_cons.mp hm).resolve_left e)
  exact h all (hall _)

/-- Some list contains every kind, when the symbols are finite. -/
theorem exists_all_kinds {Γ : Type} [Finite Γ] : ∃ all : List (Kind Γ), ∀ a, a ∈ all := by
  obtain ⟨l, -, hl⟩ := Finite.exists_univ_list Γ
  refine ⟨.jump :: .boot :: l.flatMap (fun b => [.right b, .left b, .load b]), fun a => ?_⟩
  cases a <;> simp [hl]

variable {Γ : Type} [DecidableEq Γ]

/-- The instructions of the program given by a list of kinds and exits. -/
def assemble (cs : List Γ) (c : List (Kind Γ × List ℕ)) : List Instr :=
  link (c.map (codeBlock cs))

variable [Primcodable Γ] [Finite Γ]

/-- The size of the block of a kind is primitive recursive in the kind. -/
theorem size_kindBlock_prim (cs : List Γ) :
    Primrec fun k : Kind Γ => (kindBlock cs k).size := by
  obtain ⟨all, hall⟩ := exists_all_kinds (Γ := Γ)
  exact prim_cases all hall Primrec.id (g := fun a _ => (kindBlock cs a).size)
    fun _ => Primrec.const _

/-- **The assembler is primitive recursive.** -/
theorem assemble_prim (cs : List Γ) : Primrec (assemble cs) := by
  obtain ⟨all, hall⟩ := exists_all_kinds (Γ := Γ)
  have hsize := size_kindBlock_prim cs
  -- the address of block `i`
  let A : List (Kind Γ × List ℕ) → ℕ → ℕ := fun c i =>
    ((c.map fun p => (kindBlock cs p.1).size).take i).sum
  have hA : Primrec₂ A :=
    prim_sum (prim_take Primrec.snd
      (Primrec.list_map Primrec.fst ((hsize.comp (Primrec.fst.comp Primrec.snd)).to₂)))
  -- the code of one block, from the whole list, the block and its index
  have hE : Primrec fun y : List (Kind Γ × List ℕ) × (Kind Γ × List ℕ) × ℕ =>
      (kindBlock cs y.2.1.1).emit (A y.1 y.2.2) fun e => A y.1 (y.2.1.2.getD e 0) :=
    prim_cases all hall
      (s := fun y : List (Kind Γ × List ℕ) × (Kind Γ × List ℕ) × ℕ => y.2.1.1) (by fun_prop)
      (g := fun a y => (kindBlock cs a).emit (A y.1 y.2.2) fun e => A y.1 (y.2.1.2.getD e 0))
      fun a => (kindBlock cs a).prim_emit (hA.comp Primrec.fst (by fun_prop))
        fun e => hA.comp Primrec.fst (by fun_prop)
  refine (prim_flatMap (g := fun c (p : (Kind Γ × List ℕ) × ℕ) =>
      (kindBlock cs p.1.1).emit (A c p.2) fun e => A c (p.1.2.getD e 0))
    (prim_zipIdx Primrec.id (Primrec.const 0)) hE).of_eq fun c => ?_
  simp [A, assemble, link, emitAll_eq_flatMap, List.zipIdx_map, List.flatMap_map, addr, codeBlock,
    Block.rename, List.map_map, Function.comp_def]

end DiagonaLean.CM2
