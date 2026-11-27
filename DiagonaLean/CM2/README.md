```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
```
# `CM2`: Halting of Two-Counter Machines
## Problem Statement
A two-counter machine is a list of instructions on two counters with values in `ℕ`. `inc c` increments counter `c` and falls through. `dec c j` falls through when counter `c` is zero, and otherwise decrements it and jumps to address `j`. A configuration is a program counter and the two counter values. The machine halts when the program counter leaves the program. Given a program, does the machine halt from address 0 with both counters zero? This is `DecisionProblem p` in `Basic.lean`. `Halting (p, s)` is halting from a configuration `s`.

## Layout
* `Basic.lean`: instructions, configurations, `step`, and the problem.
* `Execution.lean`: `run p s n` runs at most `n` steps; halting from a configuration is recursively enumerable (`rePred_halting`).
* `Assembly.lean`: blocks of code with labelled exits (`Block`), the statement that a block runs from given counters to an exit (`Block.Runs`), and the blocks `goto`, `inc`, `dec`, `rename`, `loop`.
* `Arithmetic.lean`: registers (`Register`, `Register.Models`), and addition, multiplication and division with remainder by a constant (`add`, `multiply`, `divide`).
* `Registers.lean`: the exponents of 2, 3 and 5 in the first counter are three registers (`Register.factor`, `Register.encode`).
* `Link.lean`: a list of blocks linked into one program (`link`, `loaded_link`), and induction along a halting computation (`halting_induction`).
* `Simulation.lean`: the kinds of blocks (`Kind`, `kindBlock`), the program of a list machine for an initial configuration (`codes`, `program`), and its correctness (`halting_program_iff`).
* `Reductions/Halt_to_CM2.lean`: the halting problem many-one reduces to two-counter halting (`CM2.synthFromHalt`). See `Reductions/README.md`.
* `Undecidable.lean`: points to `CM2.synthFromHalt`; two-counter halting is synthetically halting-hard.
* `Assembler.lean`: turning a list of kinds and exits into instructions is primitive recursive (`assemble_prim`).
* `MachineLevel.lean`: the program built from a transition table (`codesN`, `canonProgram`); two-counter halting is halting-hard by a reduction proved computable (`CM2.fromHalt`), it is not a computable predicate (`not_computablePred_cm2`), and no Turing machine decides it under any computable encoding (`not_machineDecidable_cm2`).

## Proof sketch
The tape of a Turing machine left and right of the head is two stacks. A stack is a number in base `B`, one more than the number of tape symbols, with the top symbol in the lowest digit and digits starting at 1, so the empty stack is 0. A push multiplies by `B` and adds a digit; a pop divides by `B` and branches on the remainder. Three registers hold the two stacks and scratch space. They are the exponents of 2, 3 and 5 in the first counter; the second counter is zero between operations. An increment of an exponent multiplies the first counter by the prime, and a decrement divides it by the prime, both by loops that move the value through the second counter. The state and the head symbol are the address of a block of the program, one block for each pair. The block performs the transition on the two stacks and jumps to the block of the next pair, or out of the program on a halting transition. The program starts from zero counters: its first blocks set the first counter to 1 and push the input on the right stack, cell by cell, before the jump to the block of the start state.

## References
* M. L. Minsky, *Computation: Finite and Infinite Machines* (1967), Section 14.1
* A. Dudenhefner, *Certified Decision Procedures for Two-Counter Machines* (2022)
