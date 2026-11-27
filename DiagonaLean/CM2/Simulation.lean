/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CM2.Link
import DiagonaLean.CM2.Registers
import DiagonaLean.Foundations.Computability.ListMachine

@[expose] public section

/-! # A two-counter machine that simulates a list machine

The cells left and right of the head of a list machine are two stacks. A stack is the number
whose digits, in base `cs.length + 1`, are the positions of its symbols in the list `cs` of all
symbols, each plus one (`val`). The two numbers are the exponents of 2 and 3 in the first counter
(`Register.encode`); the exponent of 5 is scratch space. The state and the head cell are the
address of a block of the program.

A block pushes on a stack by a multiplication and pops by a division with remainder
(`push`, `pop`). Every block of the program is one of finitely many blocks (`Kind`,
`kindBlock`) with its exits relabelled by a list of block indices, so a program is given by a
list of pairs of a kind and a list of indices (`codes`, `program`). The block of a state and a
head cell performs their transition (`stepCode`): a halting transition leaves the program, and a
left move with nothing left of the head, where the list machine has no next configuration and
does not halt, returns to its own block with the same counters.

The program starts from zero counters: block 0 sets the first counter to 1, one block for each
cell right of the head of the initial configuration `k₀` pushes it on the right stack, and a jump
enters the block of the state and head cell of `k₀`. The two-counter machine halts from zero
counters iff the list machine halts from `k₀` (`halting_program_iff`).

## References

* [M. L. Minsky, *Computation: Finite and Infinite Machines*][Minsky1967], Section 14.1
-/

namespace DiagonaLean.CM2

open Block Register StateTransition DiagonaLean.Foundations.Computability.ListMachine

variable {Q Γ : Type} [DecidableEq Γ] {α : Type}

/-! ### Stacks as numbers -/

/-- The digit of a symbol: its position in `cs`, plus one. -/
def digit (cs : List Γ) (c : Γ) : ℕ := cs.idxOf c + 1

/-- The number of a stack, in base `cs.length + 1`, top symbol in the lowest digit. -/
def val (cs : List Γ) : List Γ → ℕ
  | [] => 0
  | c :: l => digit cs c + val cs l * (cs.length + 1)

/-- The digit of a symbol of `cs` is below the base. -/
theorem digit_lt {cs : List Γ} {c : Γ} (hc : c ∈ cs) : digit cs c < cs.length + 1 :=
  Nat.succ_lt_succ (List.idxOf_lt_length_of_mem hc)

/-- In a list of exits, one for the digit 0 and one for each symbol of `cs`, the exit of the digit
of a symbol `c` of `cs` is the exit for `c`. -/
theorem getD_digit {cs : List Γ} (f : Γ → ℕ) (z : ℕ) {c : Γ} (hc : c ∈ cs) :
    (z :: cs.map f).getD (digit cs c) 0 = f c := by
  simp [digit, List.getD, List.getElem?_idxOf hc]

/-- The number of a stack splits into a digit for its top cell and the number of the rest. In a
list of exits, one for the blank and one for each symbol of `cs`, the exit of that digit is the
exit for the top cell, the blank on the empty stack. -/
theorem val_split {cs : List Γ} (hcs : ∀ c, c ∈ cs) (bl : Γ) (f : Γ → ℕ) (l : List Γ) :
    ∃ d, d < cs.length + 1 ∧ val cs l = d + val cs l.tail * (cs.length + 1) ∧
      (f bl :: cs.map f).getD d 0 = f (l.headD bl) := by
  cases l with
  | nil => exact ⟨0, Nat.succ_pos _, by simp [val], rfl⟩
  | cons c l => exact ⟨digit cs c, digit_lt (hcs c), rfl, getD_digit f _ (hcs c)⟩

/-! ### Push and pop -/

/-- Push the digit `d` in base `B`: multiply the register by `B` and add `d`. -/
def push (s : Register) (B d : ℕ) (k : Block α) : Block α :=
  s.multiply (factor 5) B (s.add d k)

/-- Pop a digit in base `B`: divide the register by `B` and continue with `k` of the
remainder. -/
def pop (s : Register) (B : ℕ) (k : ℕ → Block α) : Block α :=
  s.divide (factor 5) B k

/-- The exponents of 2 and 5 are two registers. -/
theorem pairModels_two (r : ℕ) :
    PairModels (factor 2) (factor 5) (fun l t => encode l r t) :=
  ⟨fun t => models_two r t, fun l => models_five l r⟩

/-- The exponents of 3 and 5 are two registers. -/
theorem pairModels_three (l : ℕ) :
    PairModels (factor 3) (factor 5) (fun r t => encode l r t) :=
  ⟨fun t => models_three l t, fun r => models_five l r⟩

/-- If `k` runs from the left stack `d + l * B`, then the push of `d` runs from the left stack
`l`. -/
theorem runs_push_left {B d l r : ℕ} {k : Block α} {i : α} {w : ℕ × ℕ}
    (h : RunsAt k (encode (d + l * B) r 0) i w) :
    RunsAt (push (factor 2) B d k) (encode l r 0) i w := by
  apply (pairModels_two r).multiply
  apply (models_two r 0).add
  rwa [Nat.add_comm]

/-- If `k` runs from the right stack `d + r * B`, then the push of `d` runs from the right stack
`r`. -/
theorem runs_push_right {B d l r : ℕ} {k : Block α} {i : α} {w : ℕ × ℕ}
    (h : RunsAt k (encode l (d + r * B) 0) i w) :
    RunsAt (push (factor 3) B d k) (encode l r 0) i w := by
  apply (pairModels_three l).multiply
  apply (models_three l 0).add
  rwa [Nat.add_comm]

/-- If `d < B` and `k d` runs from the left stack `l`, then the pop runs from the left stack
`d + l * B`. -/
theorem runs_pop_left {B d l r : ℕ} (hd : d < B) {k : ℕ → Block α} {i : α} {w : ℕ × ℕ}
    (h : RunsAt (k d) (encode l r 0) i w) :
    RunsAt (pop (factor 2) B k) (encode (d + l * B) r 0) i w :=
  (pairModels_two r).divide hd l 0 (by simpa using h)

/-- If `d < B` and `k d` runs from the right stack `r`, then the pop runs from the right stack
`d + r * B`. -/
theorem runs_pop_right {B d l r : ℕ} (hd : d < B) {k : ℕ → Block α} {i : α} {w : ℕ × ℕ}
    (h : RunsAt (k d) (encode l r 0) i w) :
    RunsAt (pop (factor 3) B k) (encode l (d + r * B) 0) i w :=
  (pairModels_three l).divide hd r 0 (by simpa using h)

/-! ### Kinds of blocks -/

/-- The kinds of the blocks of a program. -/
inductive Kind (Γ : Type) where
  /-- A jump to exit 0. -/
  | jump
  /-- A right move that writes `b`: push `b` on the left stack and pop the right stack. The exit
  is the popped digit. -/
  | right (b : Γ)
  /-- A left move that writes `b`: pop the left stack; on digit 0 take exit 0, otherwise push `b`
  on the right stack and take the exit of the popped digit. -/
  | left (b : Γ)
  /-- Push `b` on the right stack and take exit 0. -/
  | load (b : Γ)
  /-- Increment the first counter and take exit 0. -/
  | boot
  deriving DecidableEq

/-- The block of a kind, with exits labelled by natural numbers. -/
def kindBlock (cs : List Γ) : Kind Γ → Block ℕ
  | .jump => goto 0
  | .right b =>
    push (factor 2) (cs.length + 1) (digit cs b) (pop (factor 3) (cs.length + 1) fun d => goto d)
  | .left b =>
    pop (factor 2) (cs.length + 1) fun d =>
      if d = 0 then goto 0 else push (factor 3) (cs.length + 1) (digit cs b) (goto d)
  | .load b => push (factor 3) (cs.length + 1) (digit cs b) (goto 0)
  | .boot => Block.inc false (goto 0)

/-- The block of a kind and a list of block indices: exit `e` of the kind is relabelled by
entry `e` of the list. -/
def codeBlock (cs : List Γ) (c : Kind Γ × List ℕ) : Block ℕ :=
  (kindBlock cs c.1).rename fun e => c.2.getD e 0

/-- A run of the block of a kind to exit `e` is a run of the relabelled block to entry `e` of
the list. -/
theorem runs_codeBlock {cs : List Γ} {s : Kind Γ} {v w : ℕ × ℕ} {e : ℕ}
    (h : RunsAt (kindBlock cs s) v e w) (ls : List ℕ) :
    RunsAt (codeBlock cs (s, ls)) v (ls.getD e 0) w :=
  Runs.rename h _

/-- The jump takes exit 0 and keeps the counters. -/
theorem runs_jump (cs : List Γ) (v : ℕ × ℕ) : RunsAt (kindBlock cs .jump) v 0 v :=
  runs_goto _ _ _

/-- A right move pushes on the left stack, pops the digit `d` from the right stack, and takes
exit `d`. -/
theorem runs_right (cs : List Γ) (b : Γ) {d : ℕ} (hd : d < cs.length + 1) (l r : ℕ) :
    RunsAt (kindBlock cs (.right b)) (encode l (d + r * (cs.length + 1)) 0) d
      (encode (digit cs b + l * (cs.length + 1)) r 0) :=
  runs_push_left (runs_pop_right hd (runs_goto _ _ _))

/-- A left move on the empty left stack takes exit 0 and keeps the counters. -/
theorem runs_left_zero (cs : List Γ) (b : Γ) (r : ℕ) :
    RunsAt (kindBlock cs (.left b)) (encode 0 r 0) 0 (encode 0 r 0) := by
  have h : RunsAt (kindBlock cs (.left b)) (encode (0 + 0 * (cs.length + 1)) r 0) 0
      (encode 0 r 0) :=
    runs_pop_left (Nat.succ_pos _) (by simpa using runs_goto _ _ _)
  simpa using h

/-- A left move pops the digit `d ≠ 0` from the left stack, pushes on the right stack, and takes
exit `d`. -/
theorem runs_left (cs : List Γ) (b : Γ) {d : ℕ} (hd : d < cs.length + 1) (h0 : d ≠ 0)
    (l r : ℕ) :
    RunsAt (kindBlock cs (.left b)) (encode (d + l * (cs.length + 1)) r 0) d
      (encode l (digit cs b + r * (cs.length + 1)) 0) := by
  apply runs_pop_left hd
  simp only [h0, ite_false]
  exact runs_push_right (runs_goto _ _ _)

/-- A load pushes on the right stack and takes exit 0. -/
theorem runs_load (cs : List Γ) (b : Γ) (l r : ℕ) :
    RunsAt (kindBlock cs (.load b)) (encode l r 0) 0
      (encode l (digit cs b + r * (cs.length + 1)) 0) :=
  runs_push_right (runs_goto _ _ _)

/-- From zero counters, the boot block takes exit 0 with the counters of two empty stacks. -/
theorem runs_boot (cs : List Γ) : RunsAt (kindBlock cs .boot) (0, 0) 0 (encode 0 0 0) := by
  have h : (Block.inc false (goto (0 : ℕ))).Runs 0 0 0 1 0 :=
    runs_inc (r := false) (runs_goto _ _ _)
  simpa [RunsAt, kindBlock, encode] using h

/-! ### The block of a state and a head cell -/

/-- The kind and exits of the block for the state and head cell `p`: the transition
`δ p.1 p.2` on the two stacks. The block of `p'` has index `ix p'`; the index `haltIx` is beyond
the program. -/
def stepCode (δ : Q → Γ → Act Q Γ) (bl : Γ) (cs : List Γ) (ix : Q × Γ → ℕ) (haltIx : ℕ)
    (p : Q × Γ) : Kind Γ × List ℕ :=
  match δ p.1 p.2 with
  | .halt => (.jump, [haltIx])
  | .stay q b => (.jump, [ix (q, b)])
  | .right q b => (.right b, ix (q, bl) :: cs.map fun c => ix (q, c))
  | .left q b => (.left b, ix p :: cs.map fun c => ix (q, c))

/-- The counters of a configuration: the numbers of its two stacks. -/
def counters (cs : List Γ) (k : Cfg Q Γ) : ℕ × ℕ := encode (val cs k.l) (val cs k.r) 0

variable {δ : Q → Γ → Act Q Γ} {bl : Γ} {cs : List Γ} {ix : Q × Γ → ℕ} {haltIx : ℕ}

/-- On a halting transition the block takes the halting exit. -/
theorem runs_stepCode_halt {k : Cfg Q Γ} (h : δ k.q k.c = .halt) :
    RunsAt (codeBlock cs (stepCode δ bl cs ix haltIx (k.q, k.c))) (counters cs k) haltIx
      (counters cs k) := by
  simp only [stepCode, h]
  exact runs_codeBlock (runs_jump cs _) [haltIx]

/-- **A step of the list machine is a run of its block.** -/
theorem runs_stepCode_next (hcs : ∀ c, c ∈ cs) {k k' : Cfg Q Γ} (h : next δ bl k = some k') :
    RunsAt (codeBlock cs (stepCode δ bl cs ix haltIx (k.q, k.c))) (counters cs k)
      (ix (k'.q, k'.c)) (counters cs k') := by
  obtain ⟨q, l, c, r⟩ := k
  simp only [next] at h
  simp only [stepCode, counters]
  cases hδ : δ q c with
  | halt => simp [hδ] at h
  | stay q' b =>
    simp only [hδ, Option.some.injEq] at h
    subst h
    exact runs_codeBlock (runs_jump cs _) [ix (q', b)]
  | right q' b =>
    simp only [hδ, Option.some.injEq] at h
    subst h
    obtain ⟨d, hd, hv, hs⟩ := val_split hcs bl (fun c => ix (q', c)) r
    have hrun := runs_codeBlock (runs_right cs b hd (val cs l) (val cs r.tail))
      (ix (q', bl) :: cs.map fun c => ix (q', c))
    rw [hs, ← hv] at hrun
    exact hrun
  | left q' b =>
    simp only [hδ] at h
    cases l with
    | nil => simp at h
    | cons e l =>
      simp only [Option.some.injEq] at h
      subst h
      have hrun := runs_codeBlock
        (runs_left cs b (digit_lt (hcs e)) (Nat.succ_ne_zero _) (val cs l) (val cs r))
        (ix (q, c) :: cs.map fun c => ix (q', c))
      rw [getD_digit _ _ (hcs e)] at hrun
      exact hrun

/-- When the list machine has no next configuration and does not halt, the block returns to
itself with the same counters. -/
theorem runs_stepCode_stuck {k : Cfg Q Γ} (hh : δ k.q k.c ≠ .halt) (h : next δ bl k = none) :
    RunsAt (codeBlock cs (stepCode δ bl cs ix haltIx (k.q, k.c))) (counters cs k)
      (ix (k.q, k.c)) (counters cs k) := by
  obtain ⟨q, l, c, r⟩ := k
  simp only [next] at h
  simp only [stepCode, counters]
  cases hδ : δ q c with
  | halt => exact absurd hδ hh
  | stay q' b => simp [hδ] at h
  | right q' b => simp [hδ] at h
  | left q' b =>
    simp only [hδ] at h
    cases l with
    | cons e l => simp at h
    | nil =>
      exact runs_codeBlock (runs_left_zero cs b (val cs r))
        (ix (q, c) :: cs.map fun c => ix (q', c))

/-! ### The program -/

section Program

variable [DecidableEq Q]

/-- The position of a pair in a list of pairs, by decidable equality. -/
abbrev pairIx (pairs : List (Q × Γ)) (p : Q × Γ) : ℕ :=
  @List.idxOf (Q × Γ) instBEqOfDecidableEq p pairs

/-- The index of the block of a state and a head cell, in the program with `n` load blocks. -/
def stepIx (qs : List Q) (cs : List Γ) (n : ℕ) (p : Q × Γ) : ℕ := n + 2 + pairIx (qs ×ˢ cs) p

/-- The kinds and exits of the program of a list machine with states `qs` and symbols `cs`, for
the initial configuration `k₀`: the boot block, a load block for each cell right of the head,
farthest first, a jump to the block of `k₀`, and a block for each pair of a state and a
symbol. -/
def codes (δ : Q → Γ → Act Q Γ) (bl : Γ) (qs : List Q) (cs : List Γ) (k₀ : Cfg Q Γ) :
    List (Kind Γ × List ℕ) :=
  (.boot, [1]) ::
    ((List.range k₀.r.length).map fun i => (Kind.load (k₀.r.reverse.getD i bl), [i + 2])) ++
    (.jump, [stepIx qs cs k₀.r.length (k₀.q, k₀.c)]) ::
    (qs ×ˢ cs).map
      (stepCode δ bl cs (stepIx qs cs k₀.r.length) (k₀.r.length + 2 + (qs ×ˢ cs).length))

/-- The blocks of the program. -/
def program (δ : Q → Γ → Act Q Γ) (bl : Γ) (qs : List Q) (cs : List Γ) (k₀ : Cfg Q Γ) :
    List (Block ℕ) :=
  (codes δ bl qs cs k₀).map (codeBlock cs)

/-- The configuration of the two-counter machine for a configuration of the list machine. -/
def config (δ : Q → Γ → Act Q Γ) (bl : Γ) (qs : List Q) (cs : List Γ) (k₀ k : Cfg Q Γ) :
    Config :=
  (addr (program δ bl qs cs k₀) (stepIx qs cs k₀.r.length (k.q, k.c)), counters cs k)

variable {qs : List Q} {k₀ : Cfg Q Γ}

/-- A run of block `j` of the program to exit `i` takes the program from the address of block `j`
to the address of block `i`. -/
theorem reaches_code {j : ℕ} {c : Kind Γ × List ℕ} (hc : (codes δ bl qs cs k₀)[j]? = some c)
    {v w : ℕ × ℕ} {i : ℕ} (h : RunsAt (codeBlock cs c) v i w) :
    Reaches₁ (step (link (program δ bl qs cs k₀))) (addr (program δ bl qs cs k₀) j, v)
      (addr (program δ bl qs cs k₀) i, w) := by
  have hj : j < (program δ bl qs cs k₀).length := by
    simpa [program] using (List.getElem?_eq_some_iff.mp hc).choose
  have hget : (program δ bl qs cs k₀)[j] = codeBlock cs c := by
    simp [program, (List.getElem?_eq_some_iff.mp hc).choose_spec]
  rw [← hget] at h
  exact reaches_link hj h

/-- The program has `k₀.r.length + 2 + (qs ×ˢ cs).length` blocks. -/
theorem length_codes :
    (codes δ bl qs cs k₀).length = k₀.r.length + 2 + (qs ×ˢ cs).length := by
  simp [codes]; omega

/-- Block 0 is the boot block. -/
theorem codes_zero : (codes δ bl qs cs k₀)[0]? = some (.boot, [1]) := rfl

/-- Block `i + 1` loads cell `i` of the reversed right stack. -/
theorem codes_load {i : ℕ} (hi : i < k₀.r.length) :
    (codes δ bl qs cs k₀)[i + 1]? = some (.load (k₀.r.reverse.getD i bl), [i + 2]) := by
  simp [codes, List.getElem?_append_left, hi]

/-- The block after the load blocks jumps to the block of `k₀`. -/
theorem codes_jump :
    (codes δ bl qs cs k₀)[k₀.r.length + 1]? =
      some (.jump, [stepIx qs cs k₀.r.length (k₀.q, k₀.c)]) := by
  simp [codes]

/-- The block at the index of a pair `p` of a state of `qs` and a symbol of `cs` is the
`stepCode` of `p`. -/
theorem codes_step {p : Q × Γ} (hp : p ∈ qs ×ˢ cs) :
    (codes δ bl qs cs k₀)[stepIx qs cs k₀.r.length p]? =
      some (stepCode δ bl cs (stepIx qs cs k₀.r.length)
        (k₀.r.length + 2 + (qs ×ˢ cs).length) p) := by
  have hlt : pairIx (qs ×ˢ cs) p < (qs ×ˢ cs).length := List.idxOf_lt_length_of_mem hp
  have e : stepIx qs cs k₀.r.length p = (k₀.r.length + (pairIx (qs ×ˢ cs) p + 1)) + 1 := by
    simp only [stepIx]; omega
  rw [e, codes, List.cons_append, List.getElem?_cons_succ, List.getElem?_append_right (by simp)]
  simp [hlt, List.getElem_idxOf hlt]

/-- After the boot block and `i` load blocks, the right stack holds the `i` farthest cells. -/
theorem reaches_load (i : ℕ) (hi : i ≤ k₀.r.length) :
    Reaches₁ (step (link (program δ bl qs cs k₀))) (0, 0, 0)
      (addr (program δ bl qs cs k₀) (i + 1),
        encode 0 (val cs (k₀.r.reverse.take i).reverse) 0) := by
  induction i with
  | zero =>
    have h := reaches_code (codes_zero (δ := δ) (bl := bl) (qs := qs) (k₀ := k₀))
      (runs_codeBlock (runs_boot cs) [1])
    simpa [addr, val] using h
  | succ i ih =>
    have hi' : i < k₀.r.reverse.length := by simpa using hi
    have h := reaches_code (codes_load (δ := δ) (bl := bl) (qs := qs) (k₀ := k₀) hi)
      (runs_codeBlock (runs_load cs (k₀.r.reverse.getD i bl) 0
        (val cs (k₀.r.reverse.take i).reverse)) [i + 2])
    have hv : val cs (k₀.r.reverse.take (i + 1)).reverse =
        digit cs (k₀.r.reverse.getD i bl) +
          val cs (k₀.r.reverse.take i).reverse * (cs.length + 1) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi']
      simp [val, List.getD, List.getElem?_eq_getElem hi']
    rw [hv]
    exact (ih (Nat.le_of_succ_le hi)).trans h

/-- **From zero counters the program reaches the configuration of `k₀`**, when nothing is left of
the head of `k₀`. -/
theorem reaches_config (hl : k₀.l = []) :
    Reaches₁ (step (link (program δ bl qs cs k₀))) (0, 0, 0) (config δ bl qs cs k₀ k₀) := by
  have h := reaches_load (δ := δ) (bl := bl) (cs := cs) (qs := qs) (k₀ := k₀) k₀.r.length
    (Nat.le_refl _)
  rw [← List.length_reverse, List.take_length, List.reverse_reverse, List.length_reverse] at h
  have hj := reaches_code (codes_jump (δ := δ) (bl := bl) (qs := qs) (cs := cs) (k₀ := k₀))
    (runs_codeBlock (runs_jump cs (encode 0 (val cs k₀.r) 0))
      [stepIx qs cs k₀.r.length (k₀.q, k₀.c)])
  have hc : counters cs k₀ = encode 0 (val cs k₀.r) 0 := by simp [counters, hl, val]
  rw [config, hc]
  exact h.trans hj

/-- If the block of `k` runs from the counters of `k` to exit `i` with counters `w`, then the
program goes from the configuration of `k` to the address of block `i` with counters `w`. -/
theorem reaches_step (hcs : ∀ c, c ∈ cs) {k : Cfg Q Γ} (hk : k.q ∈ qs) {i : ℕ} {w : ℕ × ℕ}
    (h : RunsAt (codeBlock cs (stepCode δ bl cs (stepIx qs cs k₀.r.length)
      (k₀.r.length + 2 + (qs ×ˢ cs).length) (k.q, k.c))) (counters cs k) i w) :
    Reaches₁ (step (link (program δ bl qs cs k₀))) (config δ bl qs cs k₀ k)
      (addr (program δ bl qs cs k₀) i, w) :=
  reaches_code (codes_step (List.mem_product.mpr ⟨hk, hcs _⟩)) h

/-- The two-counter machine halts from the configuration of `k` iff the list machine halts from
`k`, when the state of `k` is in `qs` and a step from a state of `qs` leads to a state of
`qs`. -/
theorem halting_config_iff (hcs : ∀ c, c ∈ cs)
    (hqs : ∀ k k' : Cfg Q Γ, k.q ∈ qs → next δ bl k = some k' → k'.q ∈ qs) (k : Cfg Q Γ)
    (hk : k.q ∈ qs) :
    Halting (link (program δ bl qs cs k₀), config δ bl qs cs k₀ k) ↔ Halts δ bl k := by
  constructor
  · intro h
    refine halting_induction
      (C := fun s => ∀ k, k.q ∈ qs → config δ bl qs cs k₀ k = s → Halts δ bl k) h ?_ k hk rfl
    · rintro _ _ ih k hk rfl
      by_cases hh : δ k.q k.c = .halt
      · exact ⟨k, Relation.ReflTransGen.refl, hh⟩
      · cases hn : next δ bl k with
        | none => exact ih _ (reaches_step hcs hk (runs_stepCode_stuck hh hn)) k hk rfl
        | some k' =>
          obtain ⟨k'', hreach, hhalt⟩ :=
            ih _ (reaches_step hcs hk (runs_stepCode_next hcs hn)) k' (hqs k k' hk hn) rfl
          exact ⟨k'', Relation.ReflTransGen.head hn hreach, hhalt⟩
  · rintro ⟨k', hreach, hhalt⟩
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl =>
      refine (halting_of_reaches₁ (reaches_step hcs hk
        (runs_stepCode_halt hhalt))).mpr (halting_of_length_le ?_)
      simp [length_link, program, length_codes]
    | head hn _ ih =>
      rename_i a b _
      exact (halting_of_reaches₁ (reaches_step hcs hk
        (runs_stepCode_next hcs hn))).mpr (ih (hqs a b hk hn))

/-- **The two-counter machine halts from zero counters iff the list machine halts from `k₀`**,
when nothing is left of the head of `k₀`, its state is in `qs`, and a step from a state of `qs`
leads to a state of `qs`. -/
theorem halting_program_iff (hcs : ∀ c, c ∈ cs)
    (hqs : ∀ k k' : Cfg Q Γ, k.q ∈ qs → next δ bl k = some k' → k'.q ∈ qs)
    (hk : k₀.q ∈ qs) (hl : k₀.l = []) :
    Halting (link (program δ bl qs cs k₀), (0, 0, 0)) ↔ Halts δ bl k₀ :=
  (halting_of_reaches₁ (reaches_config hl)).trans (halting_config_iff hcs hqs k₀ hk)

end Program

end DiagonaLean.CM2
