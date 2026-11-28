/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CM2.Basic

@[expose] public section

/-! # Blocks of two-counter code

A block is a piece of code of a fixed size with exits labelled by a type `α` (`Block`). Its
instructions are produced from the address where it is placed and the addresses of its exits:
every instruction names its successors, which are addresses inside the block or exits.
`c.Runs a b i a' b'` states that, wherever `c` is loaded, the machine goes from the first
instruction of `c` with counters `a`, `b` to exit `i` with counters `a'`, `b'`, in at least one
step. The blocks are built from a jump (`goto`), an increment and a decrement followed by blocks
(`inc`, `dec`), a relabelling of exits (`rename`) and a loop (`loop`), each with its `Runs`
theorems. The field `prim_emit` is used in `Assembler.lean`, for the proof that the reduction
from the halting problem is computable.
-/

namespace DiagonaLean.CM2

open DiagonaLean.Foundations.Computability StateTransition

/-- A block is a piece of two-counter code with exits labelled by `α`. -/
structure Block (α : Type) where
  /-- The number of instructions, the same at every address. -/
  size : ℕ
  /-- The instructions, from the address of the first one and the addresses of the exits. -/
  emit : ℕ → (α → ℕ) → List Instr
  /-- The code has `size` instructions. -/
  length_emit : ∀ pc dst, (emit pc dst).length = size
  /-- The instructions are primitive recursive in the address and the exit addresses. -/
  prim_emit {X : Type} [Primcodable X] {pc : X → ℕ} {dst : X → α → ℕ} :
    Primrec pc → (∀ i, Primrec fun x => dst x i) → Primrec fun x => emit (pc x) (dst x)

namespace Block

variable {α β : Type}

/-- The instructions `code` are in the program `p` from the address `base` on. -/
def Loaded (p : List Instr) (base : ℕ) (code : List Instr) : Prop :=
  ∀ i j, code[i]? = some j → p[base + i]? = some j

/-- The first instruction of loaded code is at its address. -/
private theorem Loaded.first {p pc i ts} (h : Loaded p pc (i :: ts)) : p[pc]? = some i := by
  simpa using h 0 i rfl

/-- The rest of loaded code is loaded at the next address. -/
private theorem Loaded.rest {p pc i ts} (h : Loaded p pc (i :: ts)) :
    Loaded p (pc + 1) ts := by
  intro n j hj
  simpa [Nat.add_assoc, Nat.add_comm 1 n] using h (n + 1) j hj

/-- A prefix of loaded code is loaded at the same address. -/
private theorem Loaded.left {p pc xs ys} (h : Loaded p pc (xs ++ ys)) : Loaded p pc xs := by
  intro i j hj
  have hi := (List.getElem?_eq_some_iff.mp hj).choose
  exact h i j (by rwa [List.getElem?_append_left hi])

/-- A suffix of loaded code is loaded after the prefix. -/
private theorem Loaded.right {p pc xs ys} (h : Loaded p pc (xs ++ ys)) :
    Loaded p (pc + xs.length) ys := by
  intro i j hj
  rw [Nat.add_assoc]
  apply h
  simp [List.getElem?_append_right, hj]

/-- Wherever the block is loaded, the machine goes from its first instruction with counters `a`,
`b` to exit `i` with counters `a'`, `b'`, in at least one step. -/
def Runs (c : Block α) (a b : ℕ) (i : α) (a' b' : ℕ) : Prop :=
  ∀ p pc dst, Loaded p pc (c.emit pc dst) →
    Reaches₁ (step p) ⟨pc, a, b⟩ ⟨dst i, a', b'⟩

/-- `goto i` jumps to exit `i`: an increment of the first counter, then a decrement of it with
exit `i` as both successors. -/
def goto (i : α) : Block α where
  size := 2
  emit pc dst := [.inc .fst (pc + 1), .dec .fst (dst i) (dst i)]
  length_emit _ _ := rfl
  prim_emit hb hd := by have := hd i; fun_prop

/-- `goto i` runs to exit `i` and keeps the counters. -/
theorem runs_goto (i : α) (a b : ℕ) : (goto i).Runs a b i a b := by
  intro p pc dst h
  have first := h.first
  have second := h.rest.first
  apply Relation.TransGen.tail (b := ⟨pc + 1, a + 1, b⟩) (Relation.TransGen.single ?_)
  · simp [Option.mem_def, step, second, execute]
  · simp [Option.mem_def, step, first, execute]

/-- `inc r k` increments counter `r`, then continues with the block `k`. -/
def inc (r : Counter) (k : Block α) : Block α where
  size := k.size + 1
  emit pc dst := .inc r (pc + 1) :: k.emit (pc + 1) dst
  length_emit pc dst := by simp [k.length_emit]
  prim_emit hb hd := prim_cons (by fun_prop) (k.prim_emit (by fun_prop) hd)

/-- `dec r z s` continues with the block `z` when counter `r` is zero, and otherwise decrements
it and continues with the block `s`. -/
def dec (r : Counter) (z s : Block α) : Block α where
  size := z.size + s.size + 1
  emit pc dst :=
    .dec r (pc + 1 + z.size) (pc + 1) :: z.emit (pc + 1) dst ++ s.emit (pc + 1 + z.size) dst
  length_emit pc dst := by simp [z.length_emit, s.length_emit]
  prim_emit hb hd := by
    exact prim_cons (by fun_prop) (prim_append (z.prim_emit (by fun_prop) hd)
      (s.prim_emit (by fun_prop) hd))

/-- If `k` runs from the incremented counters, then `inc r k` runs from the counters. -/
theorem runs_inc {r a b i a' b'} {k : Block α}
    (h : k.Runs (if r = .snd then a else a + 1) (if r = .snd then b + 1 else b) i a' b') :
    (inc r k).Runs a b i a' b' := by
  intro p pc dst loaded
  apply (h p (pc + 1) dst loaded.rest).head
  cases r <;> simp [Option.mem_def, step, loaded.first, execute]

/-- If counter `r` is zero and `z` runs, then `dec r z s` runs. -/
theorem runs_dec_zero {r a b i a' b'} {z s : Block α} (hz : (if r = .snd then b else a) = 0)
    (h : z.Runs a b i a' b') : (dec r z s).Runs a b i a' b' := by
  intro p pc dst loaded
  apply (h p (pc + 1) dst loaded.rest.left).head
  cases r <;> simp_all [Option.mem_def, step, loaded.first, execute]

/-- If `s` runs from the decremented counters, then `dec r z s` runs from the counters. -/
theorem runs_dec_succ {r a b i a' b'} {z s : Block α} (h : s.Runs a b i a' b') :
    (dec r z s).Runs (if r = .snd then a else a + 1) (if r = .snd then b + 1 else b) i a' b' := by
  intro p pc dst loaded
  have hs := loaded.rest.right
  rw [z.length_emit] at hs
  apply (h p (pc + 1 + z.size) dst hs).head
  cases r <;> simp [Option.mem_def, step, loaded.first, execute]

/-- `k.rename f` is the block `k` with exit `i` relabelled `f i`. -/
def rename (f : α → β) (k : Block α) : Block β where
  size := k.size
  emit pc dst := k.emit pc (dst ∘ f)
  length_emit _ _ := k.length_emit _ _
  prim_emit hb hd := k.prim_emit hb (fun i => hd (f i))

/-- `body.loop` repeats `body`: exit `none` of the body returns to its first instruction. -/
def loop (body : Block (Option α)) : Block α where
  size := body.size
  emit pc dst := body.emit pc (fun i => i.elim pc dst)
  length_emit _ _ := body.length_emit _ _
  prim_emit hb hd := body.prim_emit hb (fun | none => hb | some i => hd i)

/-- A run of `c` to exit `i` is a run of `c.rename f` to exit `f i`. -/
theorem Runs.rename {c : Block α} {a b i a' b'} (h : c.Runs a b i a' b') (f : α → β) :
    (c.rename f).Runs a b (f i) a' b' :=
  fun p pc dst => h p pc (dst ∘ f)

/-- A run of the body to exit `some i` is a run of the loop to exit `i`. -/
theorem Runs.loop_exit {c : Block (Option α)} {a b i a' b'} (h : c.Runs a b (some i) a' b') :
    c.loop.Runs a b i a' b' :=
  fun p pc dst => h p pc (fun j => j.elim pc dst)

/-- A run of the body to exit `none`, followed by a run of the loop, is a run of the loop. -/
theorem Runs.loop_again {c : Block (Option α)} {a b a₁ b₁ i a' b'}
    (h : c.Runs a b none a₁ b₁) (next : c.loop.Runs a₁ b₁ i a' b') :
    c.loop.Runs a b i a' b' :=
  fun p pc dst loaded => (h p pc (fun j => j.elim pc dst) loaded).trans (next p pc dst loaded)

end Block

end DiagonaLean.CM2
