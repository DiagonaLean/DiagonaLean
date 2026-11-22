```
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
```
# `KAComm`: Kleene Algebra with Commutativity Conditions is Undecidable

A formalisation of

> Arthur Azevedo de Amorim, Cheng Zhang and Marco Gaboardi. *Kleene algebra with commutativity conditions is undecidable.* arXiv:2411.15979 [math.LO], 2024. <https://arxiv.org/abs/2411.15979>

```bibtex
@misc{AmorimZhangGaboardi2024,
  author        = {Azevedo de Amorim, Arthur and Zhang, Cheng and Gaboardi, Marco},
  title         = {Kleene algebra with commutativity conditions is undecidable},
  year          = {2024},
  eprint        = {2411.15979},
  archiveprefix = {arXiv},
  primaryclass  = {math.LO}
}
```

The entry is `AmorimZhangGaboardi2024` in the repository's `bibliography.bib`, and docstrings cite it by that key. Paper numbering below refers to arXiv version 1. How much of the paper is formalised, with the caveats and open work, is in [`STATUS.md`](STATUS.md).

## Problem Statement
An instance is a pair of expressions `e₁ e₂ : RExp (Σ ⊕ Σ)` over the doubled alphabet, in which every left letter `.inl a` commutes with every right letter `.inr b` (`DComm`). The paper asks four questions about such a pair, from the most syntactic to the most semantic. Each is a problem for `Σ = ℕ` (instances `Inst`) and for `Σ = {0, 1}` (instances `InstB`, the `Bool` problems), so `KAComm/` holds eight problems:

| Question | `Σ = ℕ` | `Σ = {0, 1}` |
|---|---|---|
| Equality on `T Σ̈`: is `e₁ = e₂` provable in pre-Kleene algebra with these commutations? | `TermEq` | `TermEqBool` |
| Equality on `K Σ̈`: is `e₁ = e₂` provable in Kleene algebra with these commutations? This is the theory of the title. | `KATermEq` | `KATermEqBool` |
| Equality on `L Σ̈`: do `e₁` and `e₂` have the same language in the model `TD.pl`? | `LangEq` | `LangEqBool` |
| Inclusion in `L Σ̈`: is the language of `e₁` contained in that of `e₂`? | `ModelLe` | `ModelLeBool` |

The problem `X` is `KAComm.X.DecisionProblem`, named `XProblem`, and its results are in the namespace `DiagonaLean.KAComm.X.Reduction`, for example `KAComm.TermEq.synthFromHalt`.

## Layout
* `X/`, for each of the eight problems: `Basic.lean` (the problem), `Reductions/Halt_to_X.lean` (a reduction from `HaltProblem`, to the complement for the four language-model problems) and `Undecidable.lean` (the results).
* `KleeneAlgebra/`: the algebra, the encoding of Turing machines as terms (`KleeneAlgebra/MachineEncoding/`), the race program and Theorem 18 for every theory in between (`KleeneAlgebra/Between.lean`).

The interpreter the race program relies on is in `Foundations/Computability/`.

## Main Results

### Context
A Kleene algebra is an idempotent semiring with a star operation $x^*$ satisfying Kozen's unfolding and induction axioms. The equational theory of Kleene algebra is decidable: by Kozen's completeness theorem, $\mathsf{KA} \vdash e = f$ holds exactly when $e$ and $f$ denote the same regular language. Verification applications often need extra hypotheses. The simplest are commutativity conditions $pq = qp$ between primitive letters, which model, for instance, independent program actions. Whether the equational theory stays decidable with such conditions was a long-standing open question, and the paper answers it negatively. The paper's proof works for a whole range of theories at once: it shows that every theory between a weak, induction-free fragment and the intended language model is undecidable.

### Setting
Let $\Sigma$ be an alphabet and $\ddot\Sigma = \{a_l, a_r : a \in \Sigma\}$ its *doubled* alphabet, which has a left and a right copy of each letter. The commutativity conditions are

$$H_\Sigma = \{\, a_l\, b_r = b_r\, a_l \;:\; a, b \in \Sigma \,\},$$

so every left letter commutes with every right letter. $\mathrm{Exp}(\ddot\Sigma)$ is the set of regular expressions over $\ddot\Sigma$, built from $0$, $1$, letters, $+$, $\cdot$ and ${}^*$.

* **Pre-Kleene algebra** $\mathsf{PKA}$ consists of the idempotent semiring axioms and left unfolding $x^* = 1 + x x^*$, with **no induction axioms**. Its free model with the conditions is $T\ddot\Sigma = \mathrm{Exp}(\ddot\Sigma)/(\mathsf{PKA} + H_\Sigma)$.
* **Kleene algebra** $\mathsf{KA}$ is $\mathsf{PKA}$ together with Kozen's induction axioms $xy \le y \Rightarrow x^* y \le y$ and $yx \le y \Rightarrow y x^* \le y$, where $x \le y$ means $x + y = y$. Its free model with the conditions is $K\ddot\Sigma$.
* **The language model.** $\mathcal{L} : \mathrm{Exp}(\ddot\Sigma) \to \mathcal{P}(\Sigma^* \times \Sigma^*)$ is the homomorphism with $\mathcal{L}(a_l) = \{(a, \varepsilon)\}$ and $\mathcal{L}(a_r) = \{(\varepsilon, a)\}$, where products are taken componentwise. The set $\mathcal{L}(e)$ is the relation that a two-tape automaton accepts, and $L\ddot\Sigma$ is its image. The conditions $H_\Sigma$ hold in it, so $\mathsf{PKA} + H_\Sigma \vdash e = f$ implies $\mathsf{KA} + H_\Sigma \vdash e = f$, which in turn implies $\mathcal L(e) = \mathcal L(f)$.

**Decidability** refers to Turing machines. A set $S \subseteq \mathrm{Exp}(\ddot\Sigma)^2$ is *decidable* if some Turing machine over $\{0, 1\}$, given the binary digits of the Gödel number $\ulcorner e, f \urcorner$, halts with output $1$ if $(e, f) \in S$ and $0$ otherwise. The encoding is injective. Every result below also holds for any encoding that a Turing machine computes from this one.

### Theorems

> **Theorem 1** (main theorem of the paper). For $\Sigma = \{0, 1\}$, the set
> $$\{\,(e, f) \;:\; \mathsf{KA} + H_\Sigma \vdash e = f\,\}$$
> is undecidable. The same holds for $\Sigma = \mathbb N$.

This is the claim of the paper's title: Kleene algebra with a fixed finite set of commutativity conditions on primitive letters has an undecidable equational theory.
*Lean:* `KATermEqBool.Reduction.not_machineDecidable_kaTermEqBool`, `KATermEq.Reduction.not_machineDecidable_kaTermEq`.

> **Theorem 2** (without induction). For $\Sigma = \{0, 1\}$ and for $\Sigma = \mathbb N$, the set
> $$\{\,(e, f) \;:\; \mathsf{PKA} + H_\Sigma \vdash e = f\,\}$$
> is undecidable.

So undecidability does not come from the induction axioms. The abstract states it as "our results hold even for weaker theories".
*Lean:* `TermEqBool.Reduction.not_machineDecidable_termEqBool`, `TermEq.Reduction.not_machineDecidable_termEq`.

> **Theorem 3** (paper's Theorem 18, for every theory in between). Let $\Sigma = \{0, 1\}$ or $\Sigma = \mathbb N$, and let $S \subseteq \mathrm{Exp}(\ddot\Sigma)^2$ satisfy
> $$\mathsf{PKA} + H_\Sigma \vdash e \le f \;\Longrightarrow\; (e, f) \in S \;\Longrightarrow\; \mathcal L(e) \subseteq \mathcal L(f).$$
> Then $S$ is undecidable. The same holds with equations in place of inequalities: if $\mathsf{PKA} + H_\Sigma \vdash e = f \Rightarrow (e, f) \in S \Rightarrow \mathcal L(e) = \mathcal L(f)$, then $S$ is undecidable.

Theorems 1 and 2 are instances of this. The proof reduces from the computably inseparable pair "machine $M$ outputs $1$ on its own code" and "machine $M$ outputs $0$ on its own code". The first is sent to inequalities provable in $\mathsf{PKA} + H_\Sigma$, and the second to inequalities false in $\mathcal L$. For $\Sigma = \{0, 1\}$, the instances are translated from $\mathbb N$ by writing the letter $n$ as the word $1^n0$. This substitution preserves provability and reflects language inclusion.
*Lean:* `not_machineDecidable_between`, `not_machineDecidable_eq_between` and their `_bool` versions.

> **Corollary 4.** For $\Sigma = \{0, 1\}$ and for $\Sigma = \mathbb N$:
> 1. equality $\mathcal L(e) = \mathcal L(f)$ and inclusion $\mathcal L(e) \subseteq \mathcal L(f)$ in the language model are undecidable;
> 2. for every theory $\mathsf T \supseteq \mathsf{PKA}$ for which $\mathcal L$ is sound under $H_\Sigma$, the set $\{(e, f) : \mathsf T + H_\Sigma \vdash e = f\}$ is undecidable.

*Lean:* `not_machineDecidable_langEqBool`, `not_machineDecidable_modelLeBool`, `not_machineDecidable_langEq`, `not_machineDecidable_modelLe`, each in its problem's `Reduction` namespace; part 2 is Theorem 3 with $S$ the theory.

> **Theorem 5** (Theorem 18 on a model). Let $\Sigma = \mathbb N$. Suppose the language map factors through a set $X$ as
> $$T\ddot\Sigma \xrightarrow{\ \varphi\ } X \xrightarrow{\ g\ } L\ddot\Sigma, \qquad g \circ \varphi = \mathcal L.$$
> Then $\{(e, f) : \varphi[e] = \varphi[f]\}$ is undecidable.

This is the paper's form of Theorem 18. Taking $X = T\ddot\Sigma$, $K\ddot\Sigma$ or $L\ddot\Sigma$ gives Theorems 2, 1 and Corollary 4 again. Equality on $X$ itself is undecidable if moreover a Turing machine computes $\varphi$ on the codes of expressions (`not_machineDecidable_eqOn`, in `Between.lean`), or if a Turing machine computes the paper's map $\eta$, which is the paper's hypothesis (`not_machineDecidable_eqOn_of_computes`, in `Separation.lean`).
*Lean:* `not_machineDecidable_eqVia`; `not_machineDecidable_eqOn` and `not_machineDecidable_eqOn_of_computes` for equality on $X$.

> **Theorem 6** (many-one reductions). Let $\mathrm{HALT}$ be the halting problem for Turing machines over $\{0, 1\}$. Then $\mathrm{HALT} \le_m$ each of
> $$\{(e, f) : \mathsf{KA} + H_\Sigma \vdash e = f\}, \qquad \{(e, f) : \mathsf{PKA} + H_\Sigma \vdash e = f\}, \qquad \{(e, f) : \mathcal L(e) \ne \mathcal L(f)\}$$
> and $\{(e, f) : \mathcal L(e) \not\subseteq \mathcal L(f)\}$, for $\Sigma = \{0, 1\}$ and for $\Sigma = \mathbb N$. Each reduction is given as an explicit program.

For the provability problems, the reduction depends on two finite constants that are known to exist only classically: a table for a fixed program interpreter and a "race" program, from the paper's Theorem 19. They are therefore parameters of the reduction. Theorems 1 and 2 do not need them.
*Lean:* `KAComm.KATermEq.synthFromHalt`, `KAComm.TermEq.synthFromHalt`, `KAComm.LangEq.synthComplFromHalt`, `KAComm.ModelLe.synthComplFromHalt` and their `Bool` versions.

> **Proposition 7** (the axioms are the paper's). Let $\mathsf{KA}'$ be Kleene algebra in Mathlib's formulation: $\mathsf{PKA}$ plus right unfolding $x^* x \le x^*$ and both induction axioms. Then for all $e, f$,
> $$\mathsf{KA}' + H_\Sigma \vdash e = f \iff \mathsf{KA} + H_\Sigma \vdash e = f.$$

This holds because right unfolding is derivable from left induction: $x^* x \le x^* x^* \le x^*$. So Theorem 1 is about the paper's theory exactly.
*Lean:* `kaEquiv_iff_paperKAEquiv`.

> **Proposition 8** (a correction). The paper's Theorem 6 says that every $e \in T X$ with finite language is the sum of the words in $\mathcal L(e)$. It is false: $\mathcal L(1^*) = \{\varepsilon\}$, but $1^* \ne 1$ in $T X$, for every alphabet $X$ and every set of commutativity conditions. The same term refutes Corollary 7 (injectivity of $\mathcal L$ on terms with finite language) and Theorem 9. All three hold for *guarded* terms, where no starred subterm accepts the empty word. The formalisation uses only these repaired forms.

*Lean:* `not_forall_finite_lang_eq_sum`, `not_lang_injective_on_finite`; repaired as `eq_sum_of_guarded_of_finite_lang`, `eq_of_guarded_of_lang_eq`.

Theorems 1–5 and Propositions 7–8 are proved exactly as stated, with no extra hypotheses. Theorem 6 takes the two constants described above as parameters. All proofs use only Lean's standard axioms.

## Where the paper's results are
Files under `KleeneAlgebra/` unless stated otherwise.

| Paper | File |
|---|---|
| Example 1 (a pre-Kleene algebra that is not a Kleene algebra) | `PreKleeneNotKleene.lean` |
| Theorem 5, the doubled alphabet and its language model | `Doubled.lean` |
| Theorem 6, Corollary 7: **false as stated** (counterexample at `e = 1∗`) | `FiniteLangCounterexample.lean` |
| Theorem 6, Corollaries 7 and 8, Theorem 9: repaired | `FiniteLangExpansion.lean`, `BoundedOutput.lean`, `Representable.lean` |
| Theorem 9, pre-Kleene algebras | `PreKleene.lean` |
| Definition 13, Lemma 14, Lemma 35: the transition term of a machine | `MachineEncoding/Transition.lean`, `MachineEncoding/MachineTerms.lean` |
| Theorem 15, soundness | `Soundness.lean`, `MachineEncoding/LanguageSoundness.lean`, `MachineEncoding/Halting.lean` |
| Theorem 16, completeness | `Completeness.lean`, `MachineEncoding/TraceCompleteness.lean` |
| Theorem 18, undecidability | `Between.lean`, `Separation.lean`, `Instance.lean`, `FreeKA.lean`; the problem folders `KAComm/X/` |
| Theorem 19, the race program | `Race.lean` |
| Definition 20, Lemma 21, Theorem 22, Lemma 34: representable relations | `Representable.lean` |
| Definitions 23 and 25, Lemmas 24 and 26: derivatives and finite-state terms | `Automata.lean`, `Syntax.lean` |
| Lemma 27, the expansion lemma | `Expansion.lean` |
| Definition 28, Lemmas 29–31: bounded-output terms | `BoundedOutput.lean` |
| Definition 32, Lemmas 33 and 34: single-step representability | `SingleStep.lean` |

## Auditing the Definitions
A machine-checked theorem means what its statement means, and the statement is only as good as the definitions it uses. To trust Theorem 1, you need to read the definitions below, not the proofs. Lean checks the proofs.

**1. Read the statement.** In a file that imports `DiagonaLean.KAComm.KATermEqBool.Undecidable`, run

```lean
open DiagonaLean
#check @KAComm.KATermEqBool.Reduction.not_machineDecidable_kaTermEqBool
-- ¬ MachineDecidable encBool KATermEqBoolProblem   (namespaces omitted)
```

`#check @…` shows every binder. The headline theorems have none, so they are unconditional. The project leaves `autoImplicit` on, so a misspelt name in a statement silently becomes a universally quantified variable. `#check @…` exposes such a variable.

**2. Read the definitions the statement uses.** Each is short. Check it against the paper or textbook notion.

| Definition | File | What to check |
|---|---|---|
| `RExp` | `KleeneAlgebra/Free.lean` | Six constructors: `0`, `1`, letters, `+`, `·`, `∗`. |
| `Equiv C` | `KleeneAlgebra/Free.lean` | Least congruence with the semiring laws, `x + x = x`, `x∗ = 1 + x x∗`, and `x y = y x` for `C x y`. No other axiom. This is the paper's pre-Kleene algebra (Section 2). |
| `KAEquiv C`, `PaperKAEquiv C` | `KleeneAlgebra/FreeKA.lean` | `Equiv C` plus Kozen's star axioms. `PaperKAEquiv` transcribes the paper's list, and Proposition 7 makes the two the same. |
| `DComm` | `KleeneAlgebra/Doubled.lean` | Holds exactly for `(a_l, b_r)` and `(b_r, a_l)`: the conditions `H`. |
| `TD`, `FreePreKA`, `mk` | `KleeneAlgebra/Doubled.lean`, `Free.lean` | `T Σ̈` as the quotient of `RExp` by `Equiv DComm`. |
| `pl`, `gen`, `lift` | `KleeneAlgebra/Doubled.lean`, `Free.lean` | The language model: `a_l ↦ {(a, ε)}`, `b_r ↦ {(ε, b)}`, extended as a homomorphism into Mathlib's `SetSemiring`. |
| `EqInstance`, `Inst`, `InstB` | `KleeneAlgebra/Inequality.lean` | An instance is a pair of expressions over `α ⊕ α`. |
| `encNat`, `encBool`, `rc`, `bitsPair`, `bitsOf`, `toNat` | `KleeneAlgebra/Race.lean`, `ExprCode.lean`, `BinarySubst.lean`, `Foundations/Computability/Interpreter.lean` | Input encodings. Their injectivity is proved, so only "is this a reasonable encoding" needs judging. |
| `MachineDecidable`, `TMDeciderFor` | `Synthetic/Definitions.lean` | Some `SingleTapeTM Bool` outputs `[true]` on every yes-instance and `[false]` on every no-instance. |
| `SingleTapeTM`, `SingleTapeTM.Outputs` | Cslib, `Cslib/Computability/Machines/Turing/SingleTape/Deterministic.lean` (revision pinned in `lake-manifest.json`) | A standard deterministic single-tape machine with finite state and alphabet. "Outputs" means it halts with exactly that list on the tape. |

For Theorems 3–6, also read `Provable`, `ModelLe` (`KleeneAlgebra/Inequality.lean`), `LangFactor`, `EqVia` (`KleeneAlgebra/Separation.lean`), the eight `DecisionProblem`s (`X/Basic.lean`), and `SynthHaltReduction`, `SynthReduction` and `HaltProblem` (`Synthetic/HaltReduction.lean`, `Synthetic/Definitions.lean`, `Halt/Basic.lean`). Use `#print X` to see a definition as Lean elaborated it.

**3. Check the axioms.**

```lean
#print axioms KAComm.KATermEqBool.Reduction.not_machineDecidable_kaTermEqBool
-- depends on axioms: [propext, Classical.choice, Quot.sound]
```

The result must list only these three, Lean's standard axioms. Any `sorryAx`, any `Lean.ofReduceBool` (from `native_decide`) or any user-declared axiom means the proof is incomplete or trusts the compiler. Do the same for each result you rely on.

**4. Check the reductions are programs.** Lean is classical, so a value of `SynthHaltReduction p` (`HaltProblem ⪯_s p`) means something only if its function is computable. Otherwise it could case on whether a machine halts. CI checks every reduction in the library with `#check_reductions` (`scripts/CheckReductions.lean`; rules in [`CONTRIBUTING.md`](../../CONTRIBUTING.md#reductions)). `scripts/CheckMetaprograms.lean` rejects metaprograms that could bypass that check. This only concerns Theorem 6. Theorems 1–5 quantify over Turing machines directly, so they need no such check.

**5. Build from a fresh checkout.** Run `lake exe cache get && lake build` and confirm there are no errors and no `sorry` warnings. The commands in steps 1 and 3 can be run with `lake env lean <file>.lean`.
