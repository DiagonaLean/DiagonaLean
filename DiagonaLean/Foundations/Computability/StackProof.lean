/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.Prim

@[expose] public section

/-! # Proof systems checked by a stack machine

Derivability in a grammar, convertibility of SKI or λ-terms, and provability in an equational
theory are recursively enumerable for the same reason: a proof is a program for a stack machine
whose entries are judgements, and running the program is primitive recursive. This file does that
once, for any instance type `X` and judgement type `J`.

A `System X J` is a primitive recursive step `step x s n`: the stack after instruction `n` on the
stack `s`, for the instance `x`. `run` runs a program, `Checks x k j` says that the program with
code `k` ends with `j` on top, and `checks_prim` says that this is a primitive recursive predicate.
Given a predicate `Good x` of judgements, every instruction of which keeps a good stack good
(soundness), and a program pushing every good judgement (completeness), `good_iff_checks` gives
`Good x j ↔ ∃ k, Checks x k j`. The halves are `good_of_checks` and `checks_of_pushes`, for a system
whose completeness covers only some of its judgements.

Completeness proofs build programs with `Pushes`: `pushes_append` and `pushes_append₂` combine the
programs for the premises of a rule with the instruction of the rule.
-/

namespace DiagonaLean.Foundations.Computability.StackProof

/-- A proof system checked by a stack machine: `step x s n` is the stack after instruction `n` on
the stack `s`, for the instance `x`. -/
structure System (X J : Type) [Primcodable X] [Primcodable J] where
  /-- One instruction. -/
  step : X → List J → ℕ → List J
  /-- The step is primitive recursive. -/
  step_prim : Primrec fun y : X × List J × ℕ => step y.1 y.2.1 y.2.2

variable {X J : Type} [Primcodable X] [Primcodable J] (S : System X J) (x : X)

/-- Run a program from a stack. -/
def run (p : List ℕ) (s : List J) : List J := p.foldl (S.step x) s

@[simp] theorem run_nil (s : List J) : run S x [] s = s := rfl

theorem run_append (p q : List ℕ) (s : List J) : run S x (p ++ q) s = run S x q (run S x p s) := by
  simp [run, List.foldl_append]

theorem run_one (n : ℕ) (s : List J) : run S x [n] s = S.step x s n := rfl

/-! ### Soundness -/

section Sound

variable {S x} (Good : J → Prop)

/-- Every entry of the stack is good. -/
def Inv (s : List J) : Prop := ∀ j ∈ s, Good j

variable {Good}

omit [Primcodable J] in
theorem Inv.nil : Inv Good ([] : List J) := fun _ h => absurd h List.not_mem_nil

omit [Primcodable J] in
theorem Inv.cons {j : J} {s : List J} (hj : Good j) (hs : Inv Good s) : Inv Good (j :: s) :=
  fun y hy => (List.mem_cons.1 hy).elim (· ▸ hj) (hs y)

omit [Primcodable J] in
theorem Inv.tail {s : List J} (hs : Inv Good s) : Inv Good s.tail := by
  cases s with
  | nil => exact hs
  | cons j s => exact fun y hy => hs y (List.mem_cons_of_mem _ hy)

omit [Primcodable J] in
/-- The head of a good stack is good, if the default judgement is. -/
theorem Inv.headI [Inhabited J] (hd : Good default) {s : List J} (hs : Inv Good s) :
    Good s.headI := by
  cases s with
  | nil => exact hd
  | cons j s => exact hs j List.mem_cons_self

/-- Running a program keeps a good stack good, if every instruction does. -/
theorem run_inv (hstep : ∀ s, Inv Good s → ∀ n, Inv Good (S.step x s n)) (p : List ℕ)
    {s : List J} (hs : Inv Good s) : Inv Good (run S x p s) := by
  induction p generalizing s with
  | nil => exact hs
  | cons n p ih => exact ih (hstep s hs n)

end Sound

/-! ### Completeness -/

/-- `p` pushes `j` onto any stack. -/
def Pushes (p : List ℕ) (j : J) : Prop := ∀ s, run S x p s = j :: s

variable {S x}

/-- An instruction `n` that replaces `a` on top by `c` turns a program pushing `a` into one
pushing `c`. -/
theorem pushes_append {p : List ℕ} {a c : J} (n : ℕ) (hp : Pushes S x p a)
    (hn : ∀ s, S.step x (a :: s) n = c :: s) : Pushes S x (p ++ [n]) c := fun s => by
  rw [run_append, hp, run_one, hn]

/-- An instruction `n` that replaces `b` on top of `a` by `c` turns programs pushing `a` and `b`
into one pushing `c`. -/
theorem pushes_append₂ {p q : List ℕ} {a b c : J} (n : ℕ) (hp : Pushes S x p a)
    (hq : Pushes S x q b) (hn : ∀ s, S.step x (b :: a :: s) n = c :: s) :
    Pushes S x (p ++ q ++ [n]) c := fun s => by
  rw [run_append, run_append, hp, hq, run_one, hn]

/-- An instruction `n` that pushes `c` on any stack is a program pushing `c`. -/
theorem pushes_one {c : J} (n : ℕ) (hn : ∀ s, S.step x s n = c :: s) : Pushes S x [n] c :=
  fun s => by rw [run_one, hn]

/-- `step` applied to primitive recursive functions is primitive recursive. -/
theorem prim_step {α : Type*} [Primcodable α] {f : α → X} {g : α → List J} {h : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec fun a => S.step (f a) (g a) (h a) :=
  S.step_prim.comp (hf.pair (hg.pair hh))

/-! ### Checking -/

variable (S x) [Inhabited J]

/-- The program with code `k` ends with `j` on top. -/
def Checks (k : ℕ) (j : J) : Prop := (run S x (Denumerable.ofNat (List ℕ) k) []).headI = j

instance [DecidableEq J] (k : ℕ) (j : J) : Decidable (Checks S x k j) :=
  inferInstanceAs (Decidable (_ = _))

/-- **Soundness of checking.** If every instruction keeps good stacks good, a checked judgement is
good. -/
theorem good_of_checks {Good : J → Prop} (hd : Good default)
    (hstep : ∀ s, Inv Good s → ∀ n, Inv Good (S.step x s n)) {k : ℕ} {j : J}
    (h : Checks S x k j) : Good j :=
  h ▸ (run_inv hstep _ Inv.nil).headI hd

variable {S x} in
/-- **Completeness of checking.** A judgement that some program pushes is checked. -/
theorem checks_of_pushes {p : List ℕ} {j : J} (h : Pushes S x p j) : ∃ k, Checks S x k j :=
  ⟨Encodable.encode p, by simp [Checks, Denumerable.ofNat_encode, h []]⟩

/-- **Derivability is checking.** If every instruction keeps good stacks good and every good
judgement is pushed by some program, then `j` is good iff some program checks it. -/
theorem good_iff_checks {Good : J → Prop} (hd : Good default)
    (hstep : ∀ s, Inv Good s → ∀ n, Inv Good (S.step x s n))
    (hcomp : ∀ j, Good j → ∃ p, Pushes S x p j) (j : J) :
    Good j ↔ ∃ k, Checks S x k j :=
  ⟨fun h => (hcomp j h).elim fun _ hp => checks_of_pushes hp,
    fun ⟨_, hk⟩ => good_of_checks S x hd hstep hk⟩

/-! ### Primitive recursion -/

omit [Inhabited J] in
/-- Running the program with code `k` from the empty stack is primitive recursive in `x` and
`k`. -/
theorem run_prim : Primrec fun y : X × ℕ => run S y.1 (Denumerable.ofNat (List ℕ) y.2) [] := by
  unfold run
  exact prim_foldl (Primrec.ofNat (List ℕ) |>.comp Primrec.snd) (Primrec.const [])
    (prim_step (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))

/-- **`Checks` is a primitive recursive predicate.** -/
theorem checks_prim : PrimrecPred fun y : X × ℕ × J => Checks S y.1 y.2.1 y.2.2 := by
  classical
  unfold Checks
  exact pred_eq (prim_headI ((run_prim S).comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))))
    (Primrec.snd.comp Primrec.snd)

end DiagonaLean.Foundations.Computability.StackProof
