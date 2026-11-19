# ⊢ DiagonaLean

A Lean 4 library of machine-checked undecidability results, built on [Mathlib](https://github.com/leanprover-community/mathlib4) and [Cslib](https://github.com/leanprover/cslib).

## About

Most undecidability proofs in textbooks and papers are a chain of reductions: halting reduces to problem A, A reduces to B, and so on. Each step is a construction that is easy to get slightly wrong and hard to check by eye. DiagonaLean formalises these chains in Lean 4. Each problem gets an exact definition, each reduction gets a correctness proof, and each undecidability result says exactly what it means.

The project has three goals:

* **A library of undecidable problems.** Each problem is stated once, and the reductions to it are proved correct. The classical problems from automata theory are covered, and so are results from current research, such as the undecidability of Kleene algebra with commutativity conditions (arXiv:2411.15979).
* **Honest statements.** Lean's logic is classical, so a naive statement of undecidability can be proved by a case split on whether a machine halts. The library rules this out in two ways, described in [Two notions of undecidability](#two-notions-of-undecidability).
* **Tactics for reductions.** Composing reductions and reusing the reduction graph should take one line. `reduceFromPCP` is the first such tactic.

DiagonaLean continues <https://github.com/aalok-thakkar/undecidability/>.

## Formalisations So Far

Every reduction starts from the halting problem for single-tape Turing machines over `{0, 1}`. Its undecidability is proved by diagonalisation, which gives the library its name.

```mermaid
graph LR
  HALT --> MPCP --> PCP
  PCP --> AmbigCFG
  PCP --> EmpCFG
  PCP --> MatMort
  HALT --> UTMHalt
  HALT --> SKIConv
  HALT --> BetaConv
  HALT --> KA["KAComm: KA with commutativity<br/>(8 problems: T, K, L equality and L inclusion,<br/>over ℕ and over {0, 1})"]
```

| Problem | Question | Folder | Proved |
|---|---|---|---|
| Halting | Does Turing machine $M$ halt on input $w$? | [`Halt/`](DiagonaLean/Halt/README.md) | `¬ MachineDecidable` (`halt_not_machinedecidable`); no machine decides it or self-halting (`halt_undecidable`, `self_halt_undecidable`) |
| Universal machine halting | For a fixed weakly universal machine $U$, does $U$ halt on $w$? | [`UTMHalt/`](DiagonaLean/UTMHalt/README.md) | No machine decides it (`not_exists_haltDeciderFor_of_isWeaklyUniversal`) |
| Modified PCP | Given tiles and a designated start tile, is there a match that begins with it? | [`MPCP/`](DiagonaLean/MPCP/README.md) | `Undecidable` |
| Post Correspondence Problem | Given tiles $(u_i, v_i)$, is there a nonempty sequence with $u_{i_1}\cdots u_{i_n} = v_{i_1}\cdots v_{i_n}$? | [`PCP/`](DiagonaLean/PCP/README.md) | `Undecidable`, over any alphabet with at least two letters |
| Ambiguity of CFGs | Does a context-free grammar have two parse trees for some word? | [`AmbigCFG/`](DiagonaLean/AmbigCFG/README.md) | `Undecidable` |
| Intersection of CFGs | Do the languages of two context-free grammars intersect? (Emptiness of the intersection is the complement.) | [`EmpCFG/`](DiagonaLean/EmpCFG/README.md) | `Undecidable` |
| Matrix mortality | Given a finite set of $3 \times 3$ integer matrices, does some product of them equal $0$? | [`MatMort/`](DiagonaLean/MatMort/README.md) | `Undecidable` |
| SKI convertibility | Do two SKI terms have a common reduct? | [`SKIConv/`](DiagonaLean/SKIConv/README.md) | `Undecidable`, `¬ MachineDecidable` |
| β-conversion | Are two λ-terms β-convertible? | [`BetaConv/`](DiagonaLean/BetaConv/README.md) | `Undecidable`, `¬ MachineDecidable` |
| Kleene algebra with commutativity | Is $e = f$ provable in Kleene algebra (`KATermEq`) or pre-Kleene algebra (`TermEq`) with commutativity conditions on letters? Is $\mathcal L(e) = \mathcal L(f)$ (`LangEq`), or $\mathcal L(e) \subseteq \mathcal L(f)$ (`ModelLe`), in the language model? Each over $\Sigma = \mathbb N$ and over $\Sigma = \{0, 1\}$ (`XBool`). | [`KAComm/`](DiagonaLean/KAComm/README.md) | `Undecidable` (for `LangEq`, `ModelLe`: of the complement), `¬ MachineDecidable`; also `¬ MachineDecidable` for every theory between pre-Kleene algebra and the language model (Theorem 18) |

The Kleene algebra folder formalises A. Azevedo de Amorim, C. Zhang and M. Gaboardi, *Kleene algebra with commutativity conditions is undecidable* (arXiv:2411.15979). Its main results hold with no hypotheses. It also finds and repairs an error in the paper's Theorem 6. Its [README](DiagonaLean/KAComm/README.md) states the results mathematically and explains how to audit them, and [STATUS.md](DiagonaLean/KAComm/STATUS.md) records what is open.

Shared machinery lives in `Foundations/`:

* the computability infrastructure (`Foundations/Computability/`): a Turing-machine interpreter for Mathlib's partial recursive codes, machines computing primitive recursive functions, and a race between a halting search and a proof search, following Smullyan;
* proof search for combinatory logic and the λ-calculus (`Foundations/CombinatoryLogic/`, `Foundations/LambdaCalculus/`).

`Synthetic/` holds the definitions of reductions and undecidability, and the reduction check.

## Two Notions of Undecidability

Lean is classical, so every proposition is "decidable" in the sense of `Classical.propDecidable`. Undecidability therefore has to be stated relative to some notion of computation. The library uses two: `Undecidable p` and `¬ MachineDecidable enc p`. In the table above, a problem lists each notion that is proved for it.

### 1. `Undecidable p`: a compiled many-one reduction from halting

```lean
-- simplified from Synthetic/Definitions.lean and Synthetic/Undecidability.lean
structure ManyOneReduces (p : X → Prop) (q : Y → Prop) where
  f  : X → Y
  hf : ∀ x, p x ↔ q (f x)          -- written p ⪯ₘ[f] q

abbrev Undecidable (p : X → Prop) : Type := HaltProblem ⪯ₘ p
```

`Undecidable p` is a **type**, not a proposition. An undecidability result is a **definition** whose value is the reduction, and composing results composes their functions (`undecidabilityFromReducibility`). The point is that **Lean must compile the reduction**. The cheating "reduction" `fun x => if HaltProblem x then a else b` is classical, and Lean refuses to compile it. So a result means something because it is a definition that Lean compiles. `#check_reductions` enforces this in CI over every declaration in the library. It checks that the reduction is a compiled definition, that nothing in its dependencies is `sorry`, an axiom or `native_decide`, that no reduction is wrapped in a way that hides it, and that no `Prop` statement concludes that a reduction exists. The conventions it relies on are listed in [CONTRIBUTING.md](CONTRIBUTING.md#reductions).

* *Strength:* reductions compose, and each one is visibly a program.
* *Limitation:* "Lean compiles it" is not the same as "a Turing machine computes it on encoded inputs". Also, constants that exist only classically, such as a universal program obtained from Mathlib's recursion theorem, cannot be computed inside a definition, so they become explicit arguments of the result (for example `undecidableSKIConv C hu hC`).

### 2. `¬ MachineDecidable enc P`: no Turing machine decides it

```lean
-- with TMDeciderFor unfolded
def MachineDecidable (enc : X → List Bool) (P : X → Prop) : Prop :=
  ∃ D : SingleTapeTM Bool, ∀ x,
    (P x → D.Outputs (enc x) [true]) ∧ (¬ P x → D.Outputs (enc x) [false])
```

This statement quantifies over actual Turing machines (Cslib's `SingleTapeTM`) running on an encoding `enc` of the instances as bit strings, so it cannot hold vacuously. It is a plain theorem with no parameters, so constants that exist only classically are no obstacle. There are three ways to prove it:

* from a reduction that a machine computes on encodings: `ComputesReduction R enc₁ enc₂ f` together with `not_machineDecidable_of_halt_reduces`;
* from a race between halting and a proof search (`Foundations/Computability/ProofRace.lean`);
* from the computably inseparable pair "outputs 1 on its own code" and "outputs 0 on its own code" (`Halt/Inseparable.lean`).

* *Strength:* this is the textbook statement, and it is unconditional.
* *Limitation:* it is relative to the encoding. An encoding that stores the answer in its first bit makes any predicate decidable. So the library's reference encodings are proved injective, and the Kleene algebra results come with `_of_conv` variants that hold for any encoding a machine computes from the reference one.

### Which to read
For trust, read the `¬ MachineDecidable` theorem and the definitions it uses (see the [audit guide](DiagonaLean/KAComm/README.md#auditing-the-definitions)). For composing results and building the reduction graph, use `Undecidable`.

## How to Use It

### Build
You need [elan](https://github.com/leanprover/elan). The toolchain is pinned in `lean-toolchain` (Lean `v4.35.0`).

```sh
git clone https://github.com/DiagonaLean/DiagonaLean
cd DiagonaLean
lake exe cache get   # download prebuilt Mathlib
lake build
```

### Depend on it
In your project's `lakefile.toml`:

```toml
[[require]]
name = "DiagonaLean"
git = "https://github.com/DiagonaLean/DiagonaLean"
rev = "main"
```

### Prove a new problem undecidable
Reduce from a problem that is already undecidable, and give the reduction as a named definition:

```lean
import DiagonaLean

open DiagonaLean.Synthetic.Definitions DiagonaLean.Synthetic.Notation DiagonaLean.PCP
  DiagonaLean.PCP.Reduction

/-- A toy problem: PCP with the two rows of every tile swapped. -/
def SwappedPCP (A : Stack Bool) : Prop := DecisionProblem (A.map fun t => ⟨t.bot, t.top⟩)

/-- The reduction function: swap the rows of every tile. -/
def swap (A : Stack Bool) : Stack Bool := A.map fun t => ⟨t.bot, t.top⟩

/-- Correctness of the reduction. -/
theorem swap_spec : (@DecisionProblem Bool) ⪯ₘ[swap] SwappedPCP := fun A => by
  simp [SwappedPCP, swap, List.map_map, Function.comp_def]

/-- The reduction, as data. -/
def pcpReducesSwapped : (@DecisionProblem Bool) ⪯ₘ SwappedPCP := ⟨swap, swap_spec⟩

/-- `SwappedPCP` is undecidable. -/
def swappedUndecidable : Undecidable SwappedPCP :=
  undecidabilityFromReducibility (undecidablePCP true false (by decide)) pcpReducesSwapped

#check_reductions local          -- checks the definitions in this file
#print axioms swappedUndecidable  -- propext, Classical.choice, Quot.sound
```

### Inspect a result
`#check @name` shows a statement with all its binders, and `#print axioms name` lists what it depends on. A sound result lists only `propext`, `Classical.choice` and `Quot.sound`. For example:

```lean
#check @DiagonaLean.KAComm.KATermEqBool.Reduction.not_machineDecidable_kaTermEqBool
-- ¬ MachineDecidable encBool KATermEqBoolProblem
```

### Contribute
Read [CONTRIBUTING.md](CONTRIBUTING.md) first. It covers:

* the commit conventions;
* the folder layout: each problem `X` has `Basic.lean` (the problem), `Reductions/Y_to_X.lean` (the reductions) and `Undecidable.lean` (the results); problems from one larger result are subfolders of a shared folder, as in `KAComm/`; and `Foundations/` may depend only on `Foundations`, `Synthetic` and `Halt`;
* the conventions for reductions that `#check_reductions` relies on.

CI runs `lake build`, `lake lint`, `#check_reductions`, `scripts/CheckMetaprograms.lean` (no metaprogram that edits the environment) and `scripts/CheckLayering.lean`.

## Roadmap

* **Core framework:** the problems above, `Undecidable` and `MachineDecidable`, the reduction check, and the `reduceFromPCP` tactic. String rewriting is still to come.
* **Base theorems:** the acceptance problem, Rice, Rice–Shapiro and Greibach. A reduction graph registered through attributes, and a tactic that searches it.
* **Standard reduction library:** more models of computation (RAM machines, register machines, μ-recursive functions) and their equivalence with Turing machines, where Cslib does not already have them.
