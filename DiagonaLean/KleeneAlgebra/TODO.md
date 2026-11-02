# KA with commutativity conditions: plan and next steps

Formalization of de Amorim, Zhang, Gaboardi, *Kleene algebra with commutativity conditions is
undecidable* (arXiv:2411.15979; PDF in `../Kleene Algebra/`). Last updated 2026-11-02 (after M6′).

## Decisions needed

- [ ] **D1. Undecidability notion.** The paper separates A = "halts with output 1" from
  B = "halts with output 0". It never gives `HALT ⪯ₘ`. Options:
  (a) Σ⁰₁-completeness (Thm 19) via Mathlib's `Nat.Partrec.Code.fixed_point`, which gives
  `Undecidable` as the framework defines it;
  (b) a new "computably inseparable ⇒ ¬ MachineDecidable" notion;
  (c) the algebraic core only (soundness + completeness). Recommended: (c) first, then (b).
- [x] **D2. Machine model: Cslib single-tape TMs, configurations as words** (decided 2026-11-02).
  Word `⊢ rev(l) [q,h] r ⊣`; cell lists may keep trailing blanks, decoded by
  `foldr StackTape.cons nil`, so every step is a local rewrite (`TM/Encoding.lean`).
- [ ] **D3. Repair of Thm 6 / Cor 7.** Candidate: restrict to terms where star is only applied to
  `e` with `[e]₀ = 0`. Check every use of Thm 6 / Cor 7 in the paper against the restriction.

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
- [ ] **M3. Soundness** (Thm 15).
- [ ] **M7.** The undecidability statement chosen in D1.
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

## Completeness (Thm 16): done

≈2.9k lines total in `KleeneAlgebra/`, no sorries. Next: M3 (soundness), then D1 / M7.
The TM layer takes `[DecidableEq Sym] [DecidableEq M.State]` and uses the derived
`DecidableEq (Letter Sym M.State)`, with no classical instance (`Data.Running` has its own
`DecidablePred`). Terms like `RM` are still `noncomputable` defs (quotient type + `cpf`); D1(b)
would need a syntax-level (`RExp`) version of the reduction.

## Notes

- `FreePreKA X C` is syntax modulo the pre-KA axioms plus `x y = y x` for `C x y`. It is the
  paper's `T X` without the category theory. `lift` gives the universal property; uniqueness
  isn't proved yet.
- `lang` currently needs `C = Eq` (discrete), because Mathlib's `Language X` is over free words.
  The completeness development instead uses `TD.pl` on `T Σ̈`, which handles commutation.
- Namespace is `DiagonaLean.KAComm`, to avoid clashing with Mathlib's `KleeneAlgebra` class.
