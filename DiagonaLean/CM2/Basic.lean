/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Mathlib.Computability.StateTransition
import DiagonaLean.Foundations.Computability.DerivePrimcodable

@[expose] public section

/-! # Halting of a two-counter machine

A two-counter machine is a list of instructions on two counters with values in `ℕ` (`Instr`): an
increment falls through, and a decrement falls through on zero and jumps on success. A
configuration is a program counter and the two counter values (`Config`, `step`). The machine
halts when the program counter leaves the program (`step_eq_none_iff`). The decision problem
(`DecisionProblem`) takes a program and asks whether it halts from address 0 with both counters
zero; `Halting` is halting from a given configuration.

The instruction set is that of the machines `CM2` in the Coq Library of Undecidability Proofs.

## References

* [M. L. Minsky, *Computation: Finite and Infinite Machines*][Minsky1967], Section 14.1
* [A. Dudenhefner, *Certified Decision Procedures for Two-Counter Machines*][Dudenhefner2022]
-/

namespace DiagonaLean.CM2

/-- An instruction of a two-counter machine. The counter is the first (`false`) or the second
(`true`). -/
inductive Instr where
  /-- Increment the selected counter and fall through. -/
  | inc (counter : Bool)
  /-- On zero fall through, otherwise decrement and jump to the given address. -/
  | dec (counter : Bool) (jump : ℕ)
  deriving DecidableEq

end DiagonaLean.CM2

derive_primcodable DiagonaLean.CM2.Instr

namespace DiagonaLean.CM2

/-- A configuration: the program counter and the values of the two counters. -/
abbrev Config := ℕ × ℕ × ℕ

/-- The configuration after the instruction at the program counter of `s`. -/
def execute (s : Config) : Instr → Config
  | .inc c => if c then (s.1 + 1, s.2.1, s.2.2 + 1) else (s.1 + 1, s.2.1 + 1, s.2.2)
  | .dec c j =>
    if c then
      if s.2.2 = 0 then (s.1 + 1, s.2.1, 0) else (j, s.2.1, s.2.2 - 1)
    else
      if s.2.1 = 0 then (s.1 + 1, 0, s.2.2) else (j, s.2.1 - 1, s.2.2)

/-- One step: the instruction at the program counter is executed. There is no step when the
program counter is outside the program. -/
def step (program : List Instr) (s : Config) : Option Config :=
  program[s.1]?.map (execute s)

/-- The machine `x.1` halts from the configuration `x.2`: it reaches a configuration with no
step, possibly `x.2` itself. -/
def Halting (x : List Instr × Config) : Prop := (StateTransition.eval (step x.1) x.2).Dom

/-- The decision problem: does the two-counter machine `p` halt from address 0 with both counters
zero? -/
def DecisionProblem (p : List Instr) : Prop := Halting (p, (0, 0, 0))

/-- There is no step from `s` iff its program counter is outside the program. -/
theorem step_eq_none_iff (p : List Instr) (s : Config) : step p s = none ↔ p.length ≤ s.1 := by
  rcases s with ⟨pc, a, b⟩
  by_cases h : pc < p.length
  · simp [step, List.getElem?_eq_getElem h, h.not_ge]
  · simp [step, Nat.le_of_not_gt h]

end DiagonaLean.CM2
