# KA with commutativity: where each result is proved

Formalization of de Amorim, Zhang, Gaboardi, *Kleene algebra with commutativity conditions is
undecidable* (arXiv:2411.15979). Paths are relative to `DiagonaLean/KleeneAlgebra/`, and line
numbers are as of 2026-11-02. Namespaces: `DiagonaLean.KAComm` (with `TD`, `FreePreKA`, `Enc`
inside it), and `DiagonaLean.KAComm.Undec` for the final results.

Status: every box is checked. There are no `sorry`s, and the axioms are `propext`,
`Classical.choice` and `Quot.sound`. Open gaps are in `GAPS.md`.

## Final results

- [x] **`HALT ⪯ₘ` form, the library's `Undecidable`.** `HALT` many-one reduces to the *failure*
  of language-model inclusion: `Undec.undecidable_not_modelLe : Undecidable (Complement ModelLe)`,
  `TM/Undecidable.lean:210`; reduction `haltReduces`, `:206`; `halt_iff_not_modelLe`, `:196`.
  Machine level: `Enc.halts_iff_not_pl_le`, `TM/Halting.lean:169`, with the divergent case
  `Enc.pl_le_of_forall_running`, `:144` (not in the paper).
- [x] **Main theorem.** Pre-KA with commutativity conditions is undecidable.
  `Undec.insepUndecidable_provable`, `TM/Undecidable.lean:161`
- [x] Every theory between pre-KA provability and the language model, KA included.
  `Undec.insepUndecidable_of_between`, `TM/Undecidable.lean:156`
- [x] No Turing machine decides such a theory, assuming a TM computes `kaRed`.
  `Undec.not_machineDecidable_of_between`, `TM/Undecidable.lean:170`
- [x] Inclusion in the language model is undecidable too.
  `Undec.insepUndecidable_modelLe`, `TM/Undecidable.lean:165`
- [x] The inseparable pair (outputs `[true]` vs `[false]` on own code).
  `Undec.selfOut_inseparable`, `TM/Undecidable.lean:97`
- [x] The reduction, an executable Lean function. `Undec.kaRed`, `TM/Undecidable.lean:133`
  - [x] Output 1 ⇒ provable: `kaRed_pos` (`:139`), from `Enc.le_of_outputs`
    (`TM/Syntax.lean:358`)
  - [x] Output 0 ⇒ fails in the model: `kaRed_neg` (`:144`), from
    `Enc.not_pl_le_of_outputs` (`TM/Syntax.lean:367`)

## Paper results, in order

### §2 Pre-Kleene algebra and free algebras

- [x] Pre-Kleene algebra (§2). `PreKleeneAlgebra`, `PreKleene.lean:35`
- [x] Example 1, a pre-KA that is not a KA. `Ex1`, `Example1.lean:35`
- [x] Free algebra `T X` with commutation. `FreePreKA`, `Free.lean:117`; `lift`, `Free.lean:194`
- [x] Theorem 5: `s ≤ e ↔ s ∈ l(e)`. `TD.ofPair_le_iff_mem`, `Doubled.lean:153`
- [x] Theorem 6 is **false** as stated. `FreePreKA.not_theorem6`, `Theorem6Counterexample.lean:72`
  - [x] Repaired for guarded terms. `TD.theorem6`, `Theorem6Repair.lean:80`
- [x] Corollary 7 is **false** as stated. `FreePreKA.not_corollary7`,
  `Theorem6Counterexample.lean:82`
  - [x] Repaired. `TD.corollary7`, `Theorem6Repair.lean:183`
- [x] Corollary 8: every nonzero term lies above a string. `TD.exists_ofPair_le`, `Doubled.lean:218`
  (reproved directly through `TD.eq_zero_of_pl_eq_zero`, `Doubled.lean:197`)
- [x] Theorem 9 is **false** as stated. `FreePreKA.not_theorem9`, `Theorem6Counterexample.lean:90`
  - [x] Repaired. `TD.theorem9`, `Theorem6Repair.lean:191`

### §3 Encoding Turing machines

- [x] Doubled alphabet `T Σ̈` (Def 12) and its language model. `TD`, `Doubled.lean`;
  `TD.pl`, `Doubled.lean:125`
- [x] Configurations as words, one-step simulation. `Enc.dstep`, `TM/Encoding.lean:81`;
  `Enc.step_cfgOf`, `TM/Encoding.lean:115`; prefix-freeness `Enc.prefixFree`, `TM/Encoding.lean:207`
- [x] Definition 13, the transition term `R_M`. `Enc.RM`, `TM/Transition.lean:78`
- [x] Lemma 14, the language of `R_M`. `Enc.mem_RM`, `TM/Transition.lean:158`
- [x] Theorem 15 (soundness). `Enc.theorem15`, `TM/Theorem15.lean:108`;
  `Enc.theorem15_outputs`, `:124`; machine-independent core `TD.sound_of_trace`,
  `Soundness.lean:116`
- [x] Theorem 16 (completeness). `Enc.theorem16`, `TM/Theorem16.lean:121`;
  explicit-residue form `Enc.theorem16_le`, `:84`; `Enc.theorem16_outputs`, `:174`
- [x] Soundness and completeness combined (the core of Theorem 18). `Enc.le_iff_halting`,
  `TM/Theorem15.lean:141`; `Enc.le_iff_outputs`, `:162`
- [x] Theorem 18 / undecidability. See "Final results" above.

### §4 Representable relations

- [x] Definition 20. `TD.Rel`, `Representable.lean:120` (residue bound only for `Λ ⊆ L`)
- [x] Lemma 21. `TD.Rel.lemma21`, `Representable.lean:154`
- [x] Theorem 22. `TD.Rel.theorem22`, `Representable.lean:203`
- [x] Completeness along a trace (used for Theorem 16). `TD.Rel.complete_of_trace_le`,
  `Completeness.lean:69`

### §5.1 Derivatives and automata

- [x] Definition 23, derivatives. `TD.HasDerivs`, `Automata.lean:76`
- [x] Lemma 24, derivative formulas. `HasDerivs.add/mul/kstar`, `Automata.lean:90–115`
- [x] Definition 25, automata and finite-state terms. `TD.IsAutomaton`, `Automata.lean:128`;
  `TD.FiniteState`, `:135`
- [x] Lemma 26, closure. `TD.FiniteState.*`, `Automata.lean:353–373`; with explicit bounds,
  `TD.FiniteStateLe.*`, `Automata.lean:248–335`
- [x] Lemma 27, expansion. `TD.IsAutomaton.expansion`, `Expansion.lean:84`

### §5.2 Bounded output and single steps

- [x] Definition 28. `TD.Fanout`, `TD.BoundedOutput`, `BoundedOutput.lean:44–48`
- [x] Lemma 29. `TD.Fanout.next_finite`, `BoundedOutput.lean:66`
- [x] Lemma 30. `TD.Fanout.zero/one/of/add/mul/kstar`, `BoundedOutput.lean:73–102`
- [x] Lemma 31. `TD.IsAutomaton.lemma31`, `BoundedOutput.lean:130`
- [x] Lemma 33. `TD.lemma33`, `SingleStep.lean:101` (paper form `lemma33'`, `:118`)
- [x] Lemma 34. `TD.lemma34`, `SingleStep.lean:221`; explicit residue `TD.lemma34_le`, `:130`
- [x] Lemma 35, `R_M` is representable. `Enc.rel_RM`, `TM/Transition.lean:216`;
  `Enc.rel_RM_le`, `:194`

## Extra infrastructure (not in the paper)

- [x] Syntax-directed residue bound. `TD.finiteStateLe_mk`, `Syntax.lean:215`
- [x] Renaming letters preserves provability (`TD.le_map`, `Syntax.lean:318`) and reflects
  model inclusion (`TD.pl_le_of_map`, `Syntax.lean:311`)
- [x] Expression-level `R_M`, `C_M`, `T_a`, `ρ_M`. `TM/Syntax.lean` (`rmS`, `crunS`, `haltS`,
  `rhoS`, `lhsS`, `rhsS`, each with an `mk_*` lemma)
