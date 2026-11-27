/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Mathlib.Computability.StateTransition
import DiagonaLean.Foundations.Computability.DerivePrimcodable

@[expose] public section

/-! # Halting of a two-counter machine

A two-counter machine is a list of instructions on two counters with values in `ℕ` (`Instr`).
The instruction at address `i` is the state `i` of the machine. `inc c n`
increments counter `c` and goes to `n`. `dec c n z` goes to `z` when counter `c` is zero, and
otherwise decrements it and goes to `n`. A configuration is an address and the two counter values
(`Config`, `step`). An address outside the program has no instruction, and the machine halts
there (`step_eq_none_iff`).

`HaltsFrom p s` states that the machine `p` reaches such an address from the configuration `s`.
The decision problem (`DecisionProblem`) takes a program and asks whether it halts from address 0
with both counters zero.

These are the deterministic two-counter Minsky machines of Niskanen, Potapov and Reichert, with
the addresses as states and address 0 as the initial state. Their machines have one sink state;
here every address outside the program is a sink.

## References

* [M. L. Minsky, *Computation: Finite and Infinite Machines*][Minsky1967], Section 14.1
* [R. Niskanen, I. Potapov, J. Reichert, *On decidability and complexity of low-dimensional
  robot games*][NiskanenPotapovReichert2020], Section 2
-/

namespace DiagonaLean.CM2

/-- The two counters of a machine. -/
inductive Counter where
  /-- The first counter. -/
  | fst
  /-- The second counter. -/
  | snd
  deriving DecidableEq

/-- An instruction of a two-counter machine. -/
inductive Instr where
  /-- Increment the counter and go to `next`. -/
  | inc (counter : Counter) (next : ℕ)
  /-- If the counter is zero go to `ifZero`; otherwise decrement it and go to `next`. -/
  | dec (counter : Counter) (next : ℕ) (ifZero : ℕ)
  deriving DecidableEq

/-- A configuration: the address of the current instruction and the values of the two
counters. -/
structure Config where
  /-- The address of the current instruction. -/
  pc : ℕ
  /-- The value of the first counter. -/
  a : ℕ
  /-- The value of the second counter. -/
  b : ℕ
  deriving DecidableEq, Inhabited

end DiagonaLean.CM2

derive_primcodable DiagonaLean.CM2.Counter

derive_primcodable DiagonaLean.CM2.Instr

derive_primcodable DiagonaLean.CM2.Config

namespace DiagonaLean.CM2

/-- The configuration after an instruction, from the counter values of `s`. -/
def execute (s : Config) : Instr → Config
  | .inc c n => if c = .fst then ⟨n, s.a + 1, s.b⟩ else ⟨n, s.a, s.b + 1⟩
  | .dec c n z =>
    if c = .fst then
      if s.a = 0 then ⟨z, s.a, s.b⟩ else ⟨n, s.a - 1, s.b⟩
    else
      if s.b = 0 then ⟨z, s.a, s.b⟩ else ⟨n, s.a, s.b - 1⟩

/-- One step: the instruction at the address of `s` is executed. There is no step when the
address is outside the program. -/
def step (p : List Instr) (s : Config) : Option Config :=
  p[s.pc]?.map (execute s)

/-- The machine `p` halts from the configuration `s`: it reaches, in zero or more steps, a
configuration whose address is outside the program. -/
def HaltsFrom (p : List Instr) (s : Config) : Prop :=
  ∃ t, Relation.ReflTransGen (fun x y => step p x = some y) s t ∧ p.length ≤ t.pc

/-- The decision problem: does the two-counter machine `p` halt from address 0 with both counters
zero? -/
def DecisionProblem (p : List Instr) : Prop := HaltsFrom p ⟨0, 0, 0⟩

/-- There is no step from `s` iff its address is outside the program. -/
theorem step_eq_none_iff (p : List Instr) (s : Config) : step p s = none ↔ p.length ≤ s.pc := by
  by_cases h : s.pc < p.length
  · simp [step, List.getElem?_eq_getElem h, h.not_ge]
  · simp [step, Nat.le_of_not_gt h]

/-- The machine halts from `s` iff the evaluation of `step p` from `s` is defined. -/
theorem haltsFrom_iff_dom (p : List Instr) (s : Config) :
    HaltsFrom p s ↔ (StateTransition.eval (step p) s).Dom := by
  rw [Part.dom_iff_mem]
  simp only [HaltsFrom, StateTransition.mem_eval, step_eq_none_iff]
  rfl

end DiagonaLean.CM2
