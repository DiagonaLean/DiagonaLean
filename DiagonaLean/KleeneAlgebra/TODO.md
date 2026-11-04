# KA with commutativity conditions: plan and next steps

Formalization of de Amorim, Zhang, Gaboardi, *Kleene algebra with commutativity conditions is
undecidable* (arXiv:2411.15979; PDF in `../Kleene Algebra/`). Last updated 2026-11-02 (after M7 and D3).

## Decisions needed

- [x] **D1. Undecidability notion.** The paper separates A = "halts with output 1" from
  B = "halts with output 0". It never gives `HALT ⪯ₘ`. Options:
  (a) Σ⁰₁-completeness (Thm 19) via Mathlib's `Nat.Partrec.Code.fixed_point`, which gives
  `Undecidable` as the framework defines it;
  (b) a new "computably inseparable ⇒ ¬ MachineDecidable" notion;
  (c) the algebraic core only (soundness + completeness). Recommended: (c) first, then (b).
  **(c) is done** (`TM/Theorem15.le_iff_halting`, `le_iff_outputs`).
  **Decided 2026-11-02: (b)**, done as M7.
- [x] **D2. Machine model: Cslib single-tape TMs, configurations as words** (decided 2026-11-02).
  Word `⊢ rev(l) [q,h] r ⊣`; cell lists may keep trailing blanks, decoded by
  `foldr StackTape.cons nil`, so every step is a local rewrite (`TM/Encoding.lean`).
- [x] **D3. Repair of Thm 6 / Cor 7.** Decided 2026-11-02: formalize the repair. Done in
  `Theorem6Repair`: for *guarded* terms (`RExp.guarded`: every starred subterm has `[e]₀ = 0`)
  over `T Σ̈`, `theorem6`, `corollary7`, `theorem9` hold. Finite sums of strings are guarded, so
  every use in the undecidability proof is covered; `1∗` is not guarded.

## Milestones

- [x] **M0. Pre-KA layer + Thm 6 check.** `PreKleene`, `Example1`, `Free`, `Theorem6Counterexample`.
- [x] **M1′. Language model for `T Σ̈`** (scoped down from M1; general trace monoids are not needed
  for completeness). `SetStar` (`P M` as a pre-KA), `Doubled` (strings = pairs, `pl`, Thm 5,
  Cor 8 reproved, `[−]₀`, sizes).
- [x] **M4. Representable relations.** `Representable`: Def 20, Lemma 21, Thm 22.
- [x] **M5. Derivatives and finite-state terms.** `Automata` (Def 23, Lemma 24, Def 25, Lemma 26),
  `Expansion` (Lemma 27).
- [x] **M6. Bounded output and Lemma 34.** `BoundedOutput` (Def 28, Lemmas 29–31), `SingleStep`
  (Lemmas 33, 34).
- [x] **M6′. Machine-independent completeness.** `Completeness`: `Rel.complete_of_trace`, the
  proof of Thm 16 for any representable term that is deterministic along a terminating trace.
- [x] **M2. Machine encoding.** `TM/Encoding` (words, `dstep`, simulation of Cslib `step`,
  prefix-freeness), `Copy` (copy terms), `TM/Transition` (Def 13 `RM`, Lemma 14 `mem_RM`).
- [x] **M6″. Lemma 35 + Theorem 16.** `TM/Transition.rel_RM`; `TM/Theorem16.theorem16` and
  `theorem16_outputs` (stated with Cslib's `SingleTapeTM.Outputs`). Bounded output comes from
  `|wd (dstep d)| ≤ |wd d| + 1` (fanout 1), not from the closure lemmas.
- [x] **M3. Soundness** (Thm 15). `Soundness.sound_of_trace` (machine-independent: the trace
  string `(s₀⋯sₙ₋₁, s₀⋯sₙ)` has its left part a prefix of its right part, so it avoids
  `Σ∗ Σ^≠ Σ̈∗`); `TM/Theorem15.theorem15`, `theorem15_outputs`. Uses `Σ̈∗ = sigAll∗`, which is
  the top of the language model (`mem_sigAll_kstar`) but not provably the top in `T Σ̈`.
- [x] **D1(c). Algebraic core.** `TM/Theorem15.le_iff_halting`: one `ρ` per machine such that,
  along a halting run, `(s₀)_r R_M∗ ≤ Σ∗ (C_M + t)_r + Σ∗ Σ^≠ ρ` holds iff `t` is the halting
  word, both in `T Σ̈` and in the language model. `le_iff_outputs` is the Cslib `Outputs` form.
  `Theorem16.exists_halting_trace` extracts the minimal halting trace from `Outputs`.
- [x] **M7. Undecidability** (D1(b)). `TM/Undecidable`:
  * `selfOut_inseparable`: "outputs `[true]` on own code" vs "outputs `[false]`" is not separated
    by any `MachineDecidable` set (diagonal via `compComputer D flipTM`).
  * `kaRed`: an executable Lean function `EncodableTM Bool → Inst` (pairs of `RExp (ℕ ⊕ ℕ)`).
  * `sepReduces_of_between`, `insepUndecidable_provable`, `insepUndecidable_modelLe`: every `S`
    with `Provable ⊆ S ⊆ ModelLe` is separation-reducible from the pair (covers KA too).
  * `not_machineDecidable_of_between`: no TM decides such `S`, assuming a TM computes `kaRed`
    (`ComputesReduction`); building that TM is the Church–Turing gap, not formalized.
  * Explicit residue: `FiniteStateLe` (Automata), `lemma34_le`, `Rel.ResidBy`,
    `complete_of_trace_le`, `theorem16_le`; `ρ_M = Σ̈∗ bnd(R_M) R_M∗` with the syntax-directed
    `RExp.bnd` (`Syntax.finiteStateLe_mk`). Syntax-level terms in `TM/Syntax`.
  * `TM/Halting` + `undecidable_not_modelLe`: `HALT ⪯ₘ Complement ModelLe` (library's
    `Undecidable`), using the new divergent-run lemma `pl_le_of_forall_running`.
  * The right side uses `T_a = ⊢ ␣∗ [halt, a] ␣∗ ⊣` instead of one halting word, because
    list-level configurations may keep blank cells.
- [ ] Optional: general commutable sets / trace monoids (old M1), uniqueness of `lift`.

## Paper issues found

- Thm 6, Cor 7, Thm 9 are false at `e = 1∗` (`Theorem6Counterexample.lean`). Every use in the
  completeness proof applies them to genuine finite sums of strings, where they hold.
- Cor 8 is true, but its proof goes through the false Cor 7. Reprove it directly: `l(e) = ∅ → e = 0`
  by induction on syntax.
- Def 20 needs the residue bound only for `Λ ⊆ L` (Lemma 34 can only prove it there, via
  prefix-freeness of `L`); the paper's Def 20 says "for every finite Λ".
- Lemma 34's proof simplifies: step (4) needs only `≤`, so no reindexing bijection; step (6) can
  apply Lemma 33 to `s` and `π_l s′` directly. Lemma 33 must keep its right context to the right
  of the remainder string, since pre-KA cannot absorb strings to the right of `Σ̈∗`.
- Typos: Thm 16 should read `s_r R∗_M` (as in Thm 15); Lemma 34 step (5) `s_l s′` should be `s_r s′`.

## Status

All milestones M0–M7 and decisions D1–D3 are done; ≈4.5k lines in `KleeneAlgebra/`, no sorries,
axioms `propext`, `Classical.choice`, `Quot.sound`. `kaRed` evaluates with `#eval` (the bit-flip
machine gives expressions of 258 and 1743 nodes). The TM layer takes
`[DecidableEq Sym] [DecidableEq M.State]`; `kaRed` gets them from the machine's `Encodable` state.

Gaps and possible extensions are in `GAPS.md`.

## Notes

- `FreePreKA X C` is syntax modulo the pre-KA axioms plus `x y = y x` for `C x y`. It is the
  paper's `T X` without the category theory. `lift` gives the universal property; uniqueness
  isn't proved yet.
- `lang` currently needs `C = Eq` (discrete), because Mathlib's `Language X` is over free words.
  The completeness development instead uses `TD.pl` on `T Σ̈`, which handles commutation.
- Namespace is `DiagonaLean.KAComm`, to avoid clashing with Mathlib's `KleeneAlgebra` class.
