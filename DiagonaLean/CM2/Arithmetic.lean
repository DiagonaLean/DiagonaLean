/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CM2.Assembly

@[expose] public section

/-! # Arithmetic on registers

A register is a pair of code templates, an increment and a decrement with a zero test
(`Register`). `r.Models repr` states that the templates act as increment and decrement on a value
`n` stored in the two counters as `repr n`. The counters themselves are registers (`physical`),
and so are the exponents of primes in a counter (`Registers.lean`). A constant is added to a
register by `add`. On two registers stored together (`PairModels`), `multiply` multiplies one by
a constant and `divide` divides it by a constant with remainder. Each has its run theorem.
-/

namespace DiagonaLean.CM2

open Block

/-- A register: code for an increment and for a decrement with a zero test. -/
structure Register where
  /-- Increment the register, then continue with the block. -/
  inc {α : Type} : Block α → Block α
  /-- On zero continue with the first block; otherwise decrement and continue with the second. -/
  dec {α : Type} : Block α → Block α → Block α

namespace Register

variable {α : Type}

/-- `k` runs from the counters `v` to exit `i` with counters `w`. -/
abbrev RunsAt (k : Block α) (v : ℕ × ℕ) (i : α) (w : ℕ × ℕ) := k.Runs v.1 v.2 i w.1 w.2

/-- The templates of `r` act as increment and decrement on the value `n` stored as `repr n`. -/
structure Models (r : Register) (repr : ℕ → ℕ × ℕ) : Prop where
  /-- If `k` runs from the value `n + 1`, then `r.inc k` runs from `n`. -/
  inc {α : Type} {k : Block α} {n i w} :
    RunsAt k (repr (n + 1)) i w → RunsAt (r.inc k) (repr n) i w
  /-- If `z` runs from the value 0, then `r.dec z s` runs from 0. -/
  zero {α : Type} {z s : Block α} {i w} :
    RunsAt z (repr 0) i w → RunsAt (r.dec z s) (repr 0) i w
  /-- If `s` runs from the value `n`, then `r.dec z s` runs from `n + 1`. -/
  succ {α : Type} {z s : Block α} {n i w} :
    RunsAt s (repr n) i w → RunsAt (r.dec z s) (repr (n + 1)) i w

/-- The register of counter `r`. -/
def physical (r : Counter) : Register := ⟨Block.inc r, Block.dec r⟩

/-- The first counter is a register, for every value of the second. -/
theorem models_left (b : ℕ) : (physical .fst).Models (fun a => (a, b)) :=
  ⟨fun h => runs_inc (r := .fst) h, fun h => runs_dec_zero (r := .fst) rfl h,
   fun h => runs_dec_succ (r := .fst) h⟩

/-- The second counter is a register, for every value of the first. -/
theorem models_right (a : ℕ) : (physical .snd).Models (fun b => (a, b)) :=
  ⟨fun h => runs_inc (r := .snd) h, fun h => runs_dec_zero (r := .snd) rfl h,
   fun h => runs_dec_succ (r := .snd) h⟩

/-- Add the constant `n` to the register: `n` increments. -/
def add (r : Register) (n : ℕ) (k : Block α) : Block α :=
  n.rec k (fun _ c => r.inc c)

/-- If `k` runs from the value `n + d`, then `r.add d k` runs from `n`. -/
theorem Models.add {r repr} (hr : Models r repr) (d : ℕ) {k : Block α} {n i w}
    (h : RunsAt k (repr (n + d)) i w) : RunsAt (r.add d k) (repr n) i w := by
  induction d generalizing n with
  | zero => exact h
  | succ d ih => exact hr.inc (ih (by simpa [Nat.add_right_comm, Nat.add_assoc] using h))

/-- Empty the register `src`, adding `m` times its value to the register `dst`. -/
def transfer (src dst : Register) (m : ℕ) (k : Block α) : Block α :=
  (src.dec (k.rename some) (dst.add m (goto none))).loop

/-- Two registers stored together: the values `a` and `b` are stored as `repr a b`. -/
structure PairModels (src dst : Register) (repr : ℕ → ℕ → ℕ × ℕ) : Prop where
  /-- `src` is a register for every value of `dst`. -/
  first (b : ℕ) : Models src (fun a => repr a b)
  /-- `dst` is a register for every value of `src`. -/
  second (a : ℕ) : Models dst (repr a)

/-- Two registers stored together can be taken in the other order. -/
theorem PairModels.swap {s t repr} (h : PairModels s t repr) :
    PairModels t s (fun b a => repr a b) := ⟨h.second, h.first⟩

/-- If `k` runs from the values `0` and `b + a * m`, then `s.transfer t m k` runs from `a` and
`b`. -/
theorem PairModels.transfer {s t repr} (hr : PairModels s t repr) (m : ℕ)
    {k : Block α} {a b i w} (h : RunsAt k (repr 0 (b + a * m)) i w) :
    RunsAt (s.transfer t m k) (repr a b) i w := by
  induction a generalizing b with
  | zero =>
    apply Runs.loop_exit
    apply (hr.first b).zero
    exact (by simpa using h : RunsAt k (repr 0 b) i w).rename some
  | succ a ih =>
    apply Runs.loop_again (a₁ := (repr a (b + m)).1) (b₁ := (repr a (b + m)).2)
    · apply (hr.first b).succ
      apply (hr.second a).add
      exact runs_goto _ _ _
    · exact ih (by simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h)

/-- Multiply the register `s` by the constant `m`, with the register `t`, zero at the start and
at the end, as scratch space. -/
def multiply (s t : Register) (m : ℕ) (k : Block α) : Block α :=
  s.transfer t m (t.transfer s 1 k)

/-- If `k` runs from the values `a * m` and `0`, then `s.multiply t m k` runs from `a` and `0`. -/
theorem PairModels.multiply {s t repr} (hr : PairModels s t repr) (m : ℕ)
    {k : Block α} {a i w} (h : RunsAt k (repr (a * m) 0) i w) :
    RunsAt (s.multiply t m k) (repr a 0) i w := by
  apply hr.transfer
  apply hr.swap.transfer
  simpa using h

/-- Decrement the register `n` times, then continue with `full`. If the register reaches zero
after `r < n` decrements, continue with `short r`. -/
def group (s : Register) : ℕ → (ℕ → Block α) → Block α → Block α
  | 0, _, full => full
  | n + 1, short, full => s.dec (short 0) (s.group n (fun r => short (r + 1)) full)

/-- If `full` runs from the value `a`, then `s.group n short full` runs from `a + n`. -/
theorem Models.group_full {s repr} (hr : Models s repr) (n : ℕ) (short : ℕ → Block α)
    {full : Block α} {a i w} (h : RunsAt full (repr a) i w) :
    RunsAt (s.group n short full) (repr (a + n)) i w := by
  induction n generalizing short with
  | zero => exact h
  | succ n ih => exact hr.succ (ih _)

/-- If `r < n` and `short r` runs from the value 0, then `s.group n short full` runs from `r`. -/
theorem Models.group_short {s repr} (hr : Models s repr) (n : ℕ) (short : ℕ → Block α)
    (full : Block α) {r i w} (hlt : r < n) (h : RunsAt (short r) (repr 0) i w) :
    RunsAt (s.group n short full) (repr r) i w := by
  induction n generalizing r short with
  | zero => omega
  | succ n ih =>
    cases r with
    | zero => exact hr.zero h
    | succ r => exact hr.succ (ih _ (by omega) h)

/-- Divide the register `s` by the constant `d`: the quotient is left in `s`, and the block
`k r` of the remainder `r` follows. The register `t` counts the quotient. -/
def divide (s t : Register) (d : ℕ) (k : ℕ → Block α) : Block α :=
  (s.group d (fun r => (t.transfer s 1 (k r)).rename some) (t.inc (goto none))).loop

/-- If `r < d` and `k r` runs from the values `b + q` and `0`, then `s.divide t d k` runs from
`r + q * d` and `b`. -/
theorem PairModels.divide {s t repr} (hr : PairModels s t repr) {d r : ℕ} (hlt : r < d)
    {k : ℕ → Block α} (q b : ℕ) {i w} (h : RunsAt (k r) (repr (b + q) 0) i w) :
    RunsAt (s.divide t d k) (repr (r + q * d) b) i w := by
  induction q generalizing b with
  | zero =>
    simp only [Nat.zero_mul, Nat.add_zero] at *
    apply Runs.loop_exit
    apply (hr.first b).group_short _ _ _ hlt
    apply Runs.rename (f := some)
    apply hr.swap.transfer
    simpa using h
  | succ q ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc]
    apply Runs.loop_again (a₁ := (repr (r + q * d) (b + 1)).1)
      (b₁ := (repr (r + q * d) (b + 1)).2)
    · apply (hr.first b).group_full
      apply (hr.second _).inc
      exact runs_goto _ _ _
    · exact ih (b + 1) (by simpa [Nat.succ_add, Nat.add_assoc] using h)

end Register

end DiagonaLean.CM2
