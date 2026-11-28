/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CM2.Assembler
import DiagonaLean.Foundations.Computability.ListHalt
import DiagonaLean.Synthetic.Tactics.ReductionPath

@[expose] public section

/-! # Halting of list machines reduces to halting of two-counter machines

An instance of `ListHalt` is a program `p` of a list machine on numeric states, a start state `q`
and a tape. The reduction `listToCM2` assembles the two-counter program of `Simulation.lean` for
the machine of `p`, with the states `ListHalt.states p q` and every symbol of the finite alphabet
`Γ`. The kinds and exits of its blocks are computed from the rules of `p` (`stepCodeT`, `codesT`),
and they are the ones of the simulation (`codesT_eq`). The program loads the tape itself, so it
starts from zero counters, and `haltsFrom_program_iff` makes `listToCM2` a reduction
(`listHalt_reducesto_cm2_spec`). It is primitive recursive (`listToCM2_prim`), because the
assembler is (`assemble_prim`).

## Main statements

* `listHalt_reducesto_cm2_spec`: the machine of an instance halts iff its two-counter program
  halts from zero counters.
* `listToCM2_prim`: `listToCM2` is primitive recursive.

## References

* [M. L. Minsky, *Computation: Finite and Infinite Machines*][Minsky1967], Section 14.1
-/

namespace DiagonaLean.CM2.Reduction

open DiagonaLean.Foundations.Computability DiagonaLean.Foundations.Computability.ListMachine
  DiagonaLean.Foundations.Computability.ListHalt DiagonaLean.Synthetic.Definitions

variable {Γ : Type} [DecidableEq Γ]

/-- `stepCodeT bl cs rule pairs n p` is the kind and exits of the block of the pair `p`, from its
rule, the list `pairs` of all pairs and the number `n` of load blocks. A pair with no rule jumps
out of the program. -/
def stepCodeT (bl : Γ) (cs : List Γ) (rule : Option (Move × ℕ × Γ)) (pairs : List (ℕ × Γ))
    (n : ℕ) (p : ℕ × Γ) : Kind Γ × List ℕ :=
  (rule.map fun r =>
    if r.1 = .stay then (Kind.jump, [n + 2 + pairIx pairs (r.2.1, r.2.2)])
    else if r.1 = .right then
      (Kind.right r.2.2, (n + 2 + pairIx pairs (r.2.1, bl)) ::
        cs.map fun c => n + 2 + pairIx pairs (r.2.1, c))
    else
      (Kind.left r.2.2, (n + 2 + pairIx pairs p) ::
        cs.map fun c => n + 2 + pairIx pairs (r.2.1, c))).getD
    (Kind.jump, [n + 2 + pairs.length])

/-- `stepCodeT` on the rule of a pair is `stepCode` of the machine of the program. -/
theorem stepCodeT_eq (bl : Γ) (cs : List Γ) (p : Program Γ) (qs : List ℕ) (n : ℕ)
    (x : ℕ × Γ) :
    stepCodeT bl cs (rule? p x.1 x.2) (qs ×ˢ cs) n x =
      stepCode (act p) bl cs (stepIx qs cs n) (n + 2 + (qs ×ˢ cs).length) x := by
  unfold stepCodeT stepCode act
  cases rule? p x.1 x.2 with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.getD_some, toAct]
    split_ifs <;> rfl

variable [Fintype Γ] [Primcodable Γ]

/-- **The kinds and exits of the program of an instance** `(p, q, tape)`: the boot block, a load
block for each cell right of the head, a jump to the block of the start state and the head cell,
and a block for each pair of a state of `ListHalt.states p q` and a symbol. -/
def codesT (bl : Γ) (x : Program Γ × ℕ × List Γ) : List (Kind Γ × List ℕ) :=
  (Kind.boot, [1]) ::
    ((List.range x.2.2.tail.length).map fun i =>
      (Kind.load (x.2.2.tail.reverse.getD i bl), [i + 2])) ++
    (Kind.jump, [x.2.2.tail.length + 2 +
      pairIx (states x.1 x.2.1 ×ˢ enumAll Γ) (x.2.1, x.2.2.headD bl)]) ::
    (states x.1 x.2.1 ×ˢ enumAll Γ).map fun p =>
      stepCodeT bl (enumAll Γ) (rule? x.1 p.1 p.2) (states x.1 x.2.1 ×ˢ enumAll Γ)
        x.2.2.tail.length p

/-- `codesT` is `codes` of the machine of the program, from its start configuration. -/
theorem codesT_eq (bl : Γ) (p : Program Γ) (q : ℕ) (tape : List Γ) :
    codesT bl (p, q, tape) =
      codes (act p) bl (states p q) (enumAll Γ) (start bl q tape) := by
  simp only [codesT, codes, start, stepCodeT_eq]
  rfl

/-- **The reduction.** `listToCM2 bl (p, q, tape)` is the two-counter program of the machine of
`p` from the state `q` on `tape`. -/
def listToCM2 (bl : Γ) (x : Program Γ × ℕ × List Γ) : List Instr :=
  assemble (enumAll Γ) (codesT bl x)

/-- `listToCM2 bl` witnesses the reduction from halting of list machines given by a table to
halting of two-counter machines. -/
theorem listHalt_reducesto_cm2_spec (bl : Γ) :
    ListHalt.DecisionProblem bl ⪯_s[listToCM2 bl] CM2.DecisionProblem := by
  rintro ⟨p, q, tape⟩
  rw [listToCM2, codesT_eq]
  exact (haltsFrom_program_iff mem_enumAll (fun k k' _ h => states_closed bl p q k k' h)
    (mem_states_start p q) rfl).symm

derive_primrec stepCodeT [Primcodable Γ]

derive_primrec codesT

/-- `listToCM2 bl` is primitive recursive. -/
@[fun_prop] theorem listToCM2_prim (bl : Γ) : Primrec (listToCM2 bl) := by
  have h : Primrec (codesT bl) := by fun_prop
  exact (assemble_prim (enumAll Γ)).comp h

/-- Halting of two-counter machines is displayed as "Two-counter machine halting". -/
instance : Synthetic.ReductionChain.ProblemName CM2.DecisionProblem :=
  ⟨"Two-counter machine halting"⟩

end DiagonaLean.CM2.Reduction
