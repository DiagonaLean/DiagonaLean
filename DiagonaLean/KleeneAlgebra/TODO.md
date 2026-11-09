# KA with commutativity conditions: plan and next steps

Formalization of de Amorim, Zhang, Gaboardi, *Kleene algebra with commutativity conditions is
undecidable* (arXiv:2411.15979; PDF in `../Kleene Algebra/`). Last updated 2026-11-09 (`Undecidable` for T and K proved).

## Decisions needed

- [x] **D1. Undecidability notion.** The paper separates A = "halts with output 1" from
  B = "halts with output 0". It never gives `HaltProblem ⪯ₘ`. Options:
  (a) Σ⁰₁-completeness (Thm 19) via Mathlib's `Nat.Partrec.Code.fixed_point`, which gives
  `Undecidable` as the framework defines it;
  (b) a new "computably inseparable ⇒ ¬ MachineDecidable" notion;
  (c) the algebraic core only (soundness + completeness). Recommended: (c) first, then (b).
  **(c) is done** (`MachineEncoding/LanguageSoundness.le_iff_halting`, `le_iff_outputs`).
  **Decided 2026-11-02: (b)**, done as M7.
- [x] **D2. Machine model: Cslib single-tape TMs, configurations as words** (decided 2026-11-02).
  Word `⊢ rev(l) [q,h] r ⊣`; cell lists may keep trailing blanks, decoded by
  `foldr StackTape.cons nil`, so every step is a local rewrite (`MachineEncoding/Configurations.lean`).
- [x] **D3. Repair of Thm 6 / Cor 7.** Decided 2026-11-02: formalize the repair. Done in
  `FiniteLangExpansion`: for *guarded* terms (`RExp.guarded`: every starred subterm has `[e]₀ = 0`)
  over `T Σ̈`, `eq_sum_of_guarded_of_finite_lang`, `eq_of_guarded_of_lang_eq`, `mul_sigAll_kstar_le_of_guarded` hold. Finite sums of strings are guarded, so
  every use in the undecidability proof is covered; `1∗` is not guarded.

- [x] **D4. Route for M8b–d: (b), the Mathlib bridge** (user's decision, 2026-11-09). Start with
  M8b, which gives Theorem 18 on encoded expressions through `not_machineDecidable_eqVia_of_computes`.
  Under the `ManyOneReduces` convention, a code from Mathlib's `∃` statements may only be a finite
  constant passed to an untagged `def`. Original notes: nothing in the repo yet gives a universal machine or a
  recursion theorem for Cslib machines (`Foundations/UniversalTuringMachine` only defines
  `IsUniversal`). Options:
  (a) native Cslib machines: build a universal machine, s-m-n and the recursion theorem, plus the
  machines of M8b, M8c, with trace proofs as in `Halt/Compositions.lean`;
  (b) a bridge to Mathlib: prove that Cslib machines and `Nat.Partrec.Code` simulate each other
  computably, then use `Nat.Partrec.Code.fixed_point` and show `eqRed` and proof enumeration are
  `Computable` with `Primrec` (as `LatticeUndecidability/Reduction.lean` does). The direction
  Partrec → Cslib can start from Mathlib's `PartrecToTM2`, `TM2to1`, `TM1to1`, `TM1to0`, but
  `Turing.PartrecToTM2.Λ'` is infinite, so only the finite support of each code can be compiled.

## Milestones

- [x] **M0. Pre-KA layer + Thm 6 check.** `PreKleene`, `PreKleeneNotKleene`, `Free`, `FiniteLangCounterexample`.
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
- [x] **M2. Machine encoding.** `MachineEncoding/Configurations` (words, `dstep`, simulation of Cslib `step`,
  prefix-freeness), `Copy` (copy terms), `MachineEncoding/Transition` (Def 13 `RM`, Lemma 14 `mem_RM`).
- [x] **M6″. Lemma 35 + Theorem 16.** `MachineEncoding/Transition.rel_RM`; `MachineEncoding/TraceCompleteness.exists_le_err_of_halting_run` and
  `exists_le_err_of_outputs` (stated with Cslib's `SingleTapeTM.Outputs`). Bounded output comes from
  `|wd (dstep d)| ≤ |wd d| + 1` (fanout 1), not from the closure lemmas.
- [x] **M3. Soundness** (Thm 15). `Soundness.sound_of_trace` (machine-independent: the trace
  string `(s₀⋯sₙ₋₁, s₀⋯sₙ)` has its left part a prefix of its right part, so it avoids
  `Σ∗ Σ^≠ Σ̈∗`); `MachineEncoding/LanguageSoundness.wdF_eq_of_pl_le`, `exists_wdF_of_outputs_of_pl_le`. Uses `Σ̈∗ = sigAll∗`, which is
  the top of the language model (`mem_sigAll_kstar`) but not provably the top in `T Σ̈`.
- [x] **D1(c). Algebraic core.** `MachineEncoding/LanguageSoundness.le_iff_halting`: one `ρ` per machine such that,
  along a halting run, `(s₀)_r R_M∗ ≤ Σ∗ (C_M + t)_r + Σ∗ Σ^≠ ρ` holds iff `t` is the halting
  word, both in `T Σ̈` and in the language model. `le_iff_outputs` is the Cslib `Outputs` form.
  `TraceCompleteness.exists_halting_trace` extracts the minimal halting trace from `Outputs`.
- [x] **M7. Undecidability** (D1(b)). `Reductions/SelfOut_to_ModelLe`:
  * `selfOut_inseparable`: "outputs `[true]` on own code" vs "outputs `[false]`" is not separated
    by any `MachineDecidable` set (diagonal via `compComputer D flipTM`).
  * `kaRed`: an executable Lean function `EncodableTM Bool → Inst` (pairs of `RExp (ℕ ⊕ ℕ)`).
  * `sepReduces_of_between`, `insepUndecidable_provable`, `insepUndecidable_modelLe`: every `S`
    with `Provable ⊆ S ⊆ ModelLe` is separation-reducible from the pair (covers KA too).
  * `not_machineDecidable_of_between`: no TM decides such `S`, assuming a TM computes `kaRed`
    (`ComputesReduction`); building that TM is the Church–Turing gap, not formalized.
  * Explicit residue: `FiniteStateLe` (Automata), `rel_resid_of_finiteStateLe`, `Rel.ResidBy`,
    `complete_of_trace_le`, `le_err_of_halting_run`; `ρ_M = Σ̈∗ bnd(R_M) R_M∗` with the syntax-directed
    `RExp.bnd` (`Syntax.finiteStateLe_mk`). Syntax-level terms in `MachineEncoding/MachineTerms`.
  * `MachineEncoding/Halting` + `undecidable_not_modelLe`: `HaltProblem ⪯ₘ Complement ModelLe` (library's
    `Undecidable`), using the new divergent-run lemma `pl_le_of_forall_running`.
  * The right side uses `T_a = ⊢ ␣∗ [halt, a] ␣∗ ⊣` instead of one halting word, because
    list-level configurations may keep blank cells.
- [x] **M7½. Theorem 18 as the paper states it** (2026-11-07). `FreeKA` (free KA `K X`, Mathlib
  `KleeneAlgebra` instance, `SetSemiring` is a KA, `plK_ofPre`); `Reductions/SelfOut_to_Eq` (`LangFactor`,
  `EqVia`, `eqRed`, `sepReduces_eqOn*`, `*_separated`, `≤`/`=` bridges, `insepUndecidable_kaProvable`,
  `undecidable_not_langEq`, `not_machineDecidable_selfEq`/`_termEq`/`_kaTermEq`).
- [ ] **M8. `Undecidable` for equality on `T Σ̈` and `K Σ̈`** (paper's Theorem 19, Smullyan).
  * [x] M8a. Logical core: `Reductions/Sigma1` (`SmullyanFamily`, `halt_iff_selfEq`,
    `undecidable_termEq_of_family`, `undecidable_kaTermEq_of_family`). Conditional on a family.
  * [x] **`Undecidable` for equality on `T Σ̈` and `K Σ̈` is proved** (2026-11-09):
    `Reductions/Halt_to_TermEq.lean`, `undecidable_termEq`, `undecidable_kaTermEq`. This goes through `Reductions/`
    and does not use `SmullyanFamily`, M8b or `encodeBoolTM`: the race machine runs on empty input.
    The results that aren't about Kleene algebra are in `Foundations/Computability/`, which imports
    nothing from `KleeneAlgebra/`: `exists_machine`, `wrap_outputs`, `exists_uconst`,
    `exists_base`, `halt_iff_test`, `test_prim` and the `prim` tactic. `Data`, `dstep`, `cfgOf` and `initData` moved
    there too, and `Enc` re-exports them.
  * [x] **The same over `{0, 1}`** (2026-11-09): `Reductions/Halt_to_TermEqBool.lean`, `undecidable_termEq_bool`,
    `undecidable_kaTermEq_bool`, `undecidable_not_langEq_bool`. `GAPS.md`, item 1a.
  * [x] **No machine decides equality on `T Σ̈` and `K Σ̈`** (2026-11-09):
    `Reductions/SelfHalt_to_TermEq.lean`. General tools in `Foundations/Computability/`: `exists_computer`,
    `exists_compiled`, `queue_outputs`, `selfHalt_iff_test`. `L Σ̈` is open at machine level.
  * [ ] M8b. A machine computing `eqRed` from `encodeBoolTM M` (also discharges `GAPS.md` item 1).
    No longer needed for `Undecidable`, only for machine-level statements.
    **Blocked as stated (2026-11-09):** `encodeBoolTM` drops halting transitions, so `eqRed` is not
    a function of the code and no such machine exists for an injective `enc`. See `GAPS.md`, item 0.
  * [ ] M8c. A machine enumerating proofs of `Equiv DComm` / `KAEquiv DComm`.
  * [ ] M8d. The recursion theorem for `SingleTapeTM Bool`, and the race machine `N p` built from
    it, giving a `SmullyanFamily` constructed from data. Route is decision D4.
- [ ] Optional: general commutable sets / trace monoids (old M1), uniqueness of `lift`.

## Paper issues found

- Thm 6, Cor 7, Thm 9 are false at `e = 1∗` (`FiniteLangCounterexample.lean`). Every use in the
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
