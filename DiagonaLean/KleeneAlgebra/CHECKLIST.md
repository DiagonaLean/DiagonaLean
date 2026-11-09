# KA with commutativity: where each result is proved

Formalization of de Amorim, Zhang, Gaboardi, *Kleene algebra with commutativity conditions is
undecidable* (arXiv:2411.15979). Paths are relative to `DiagonaLean/KleeneAlgebra/`, and line
numbers are as of 2026-11-02. Namespaces: `DiagonaLean.KAComm` (with `TD`, `FreePreKA`, `Enc`
inside it), and `DiagonaLean.KAComm.Undec` for the final results.

Status: every box is checked except the one open item under Theorem 18. There are no `sorry`s, and the axioms are `propext`,
`Classical.choice` and `Quot.sound`. Open gaps are in `GAPS.md`.

## Final results

- [x] **`HALT ⪯ₘ` form, the library's `Undecidable`.** `HALT` many-one reduces to the *failure*
  of language-model inclusion: `Undec.undecidable_not_modelLe : Undecidable (Complement ModelLe)`,
  `Reductions/SelfOut_to_ModelLe.lean:210`; reduction `haltReduces`, `:206`; `halt_iff_not_modelLe`, `:196`.
  Machine level: `Enc.halts_iff_not_pl_le`, `MachineEncoding/Halting.lean:169`, with the divergent case
  `Enc.pl_le_of_forall_running`, `:144` (not in the paper).
- [x] **Main theorem.** Pre-KA with commutativity conditions is undecidable.
  `Undec.insepUndecidable_provable`, `Reductions/SelfOut_to_ModelLe.lean:161`
- [x] Every theory between pre-KA provability and the language model, KA included.
  `Undec.insepUndecidable_of_between`, `Reductions/SelfOut_to_ModelLe.lean:156`
- [x] No Turing machine decides such a theory, assuming a TM computes `kaRed`.
  `Undec.not_machineDecidable_of_between`, `Reductions/SelfOut_to_ModelLe.lean:170`
- [x] Inclusion in the language model is undecidable too.
  `Undec.insepUndecidable_modelLe`, `Reductions/SelfOut_to_ModelLe.lean:165`
- [x] The inseparable pair (outputs `[true]` vs `[false]` on own code).
  `Undec.selfOut_inseparable`, `Reductions/SelfOut_to_ModelLe.lean:97`
- [x] The reduction, an executable Lean function. `Undec.kaRed`, `Reductions/SelfOut_to_ModelLe.lean:133`
  - [x] Output 1 ⇒ provable: `kaRed_pos` (`:139`), from `Enc.le_of_outputs`
    (`MachineEncoding/MachineTerms.lean:358`)
  - [x] Output 0 ⇒ fails in the model: `kaRed_neg` (`:144`), from
    `Enc.not_pl_le_of_outputs` (`MachineEncoding/MachineTerms.lean:367`)

## Paper results, in order

### §2 Pre-Kleene algebra and free algebras

- [x] Pre-Kleene algebra (§2). `PreKleeneAlgebra`, `PreKleene.lean:35`
- [x] Example 1, a pre-KA that is not a KA. `NatBotTop`, `PreKleeneNotKleene.lean:35`
- [x] Free algebra `T X` with commutation. `FreePreKA`, `Free.lean:117`; `lift`, `Free.lean:194`
- [x] Theorem 5: `s ≤ e ↔ s ∈ l(e)`. `TD.ofPair_le_iff_mem`, `Doubled.lean:153`
- [x] Theorem 6 is **false** as stated. `FreePreKA.not_forall_finite_lang_eq_sum`, `FiniteLangCounterexample.lean:72`
  - [x] Repaired for guarded terms. `TD.eq_sum_of_guarded_of_finite_lang`, `FiniteLangExpansion.lean:80`
- [x] Corollary 7 is **false** as stated. `FreePreKA.not_lang_injective_on_finite`,
  `FiniteLangCounterexample.lean:82`
  - [x] Repaired. `TD.eq_of_guarded_of_lang_eq`, `FiniteLangExpansion.lean:183`
- [x] Corollary 8: every nonzero term lies above a string. `TD.exists_ofPair_le`, `Doubled.lean:218`
  (reproved directly through `TD.eq_zero_of_pl_eq_zero`, `Doubled.lean:197`)
- [x] Theorem 9 is **false** as stated. `FreePreKA.not_forall_finite_lang_mul_kstar_le`, `FiniteLangCounterexample.lean:90`
  - [x] Repaired. `TD.mul_sigAll_kstar_le_of_guarded`, `FiniteLangExpansion.lean:191`

### §3 Encoding Turing machines

- [x] Doubled alphabet `T Σ̈` (Def 12) and its language model. `TD`, `Doubled.lean`;
  `TD.pl`, `Doubled.lean:125`
- [x] Configurations as words, one-step simulation. `Enc.dstep`, `MachineEncoding/Configurations.lean:81`;
  `Enc.step_cfgOf`, `MachineEncoding/Configurations.lean:115`; prefix-freeness `Enc.prefixFree`, `MachineEncoding/Configurations.lean:207`
- [x] Definition 13, the transition term `R_M`. `Enc.RM`, `MachineEncoding/Transition.lean:78`
- [x] Lemma 14, the language of `R_M`. `Enc.mem_RM`, `MachineEncoding/Transition.lean:158`
- [x] Theorem 15 (soundness). `Enc.wdF_eq_of_pl_le`, `MachineEncoding/LanguageSoundness.lean:108`;
  `Enc.exists_wdF_of_outputs_of_pl_le`, `:124`; machine-independent core `TD.sound_of_trace`,
  `Soundness.lean:116`
- [x] Theorem 16 (completeness). `Enc.exists_le_err_of_halting_run`, `MachineEncoding/TraceCompleteness.lean:121`;
  explicit-residue form `Enc.le_err_of_halting_run`, `:84`; `Enc.exists_le_err_of_outputs`, `:174`
- [x] Soundness and completeness combined (the core of Theorem 18). `Enc.le_iff_halting`,
  `MachineEncoding/LanguageSoundness.lean:141`; `Enc.le_iff_outputs`, `:162`
- [x] Theorem 18 / undecidability. See "Final results" above. For the paper's own form, equality
  on `X`, `T Σ̈`, `K Σ̈` and `L Σ̈`, see `Reductions/SelfOut_to_Eq.lean`:
  - [x] The diagram `T Σ̈ → X → L Σ̈`. `Undec.LangFactor`; `η` is `Undec.eta`, on syntax `Undec.eqRed`
  - [x] Equality on `X`. `Undec.sepReduces_eqOn`, `sepReduces_eqVia`, `not_machineDecidable_eqOn_of_computes`
  - [x] Equality on `T Σ̈`, `K Σ̈`, `L Σ̈`. `Undec.termEq_separated`, `kaTermEq_separated`,
    `langEq_separated`; free KA in `FreeKA.lean`
  - [x] `≤` versus `=`. `Undec.provable_iff_equiv`, `modelLe_iff_langEq`, `kaProvable_iff_le`
  - [x] `Undecidable` in the synthetic framework, for the failure of equality in the language
    model. `Undec.undecidable_not_langEq`, general form `undecidable_not_eqVia`
  - [x] No machine decides the problem on machine codes, with no hypothesis, for any `X`.
    `Undec.not_machineDecidable_selfEq`, `not_machineDecidable_termEq`,
    `not_machineDecidable_kaTermEq`; it reduces to equality by `selfEq_reduces`
  - [ ] `Undecidable` for equality on `T Σ̈` and `K Σ̈`, through `HALT ⪯ₘ`. See `GAPS.md`, item 2
    - [x] Logical core (Theorem 19, Smullyan), given a `SmullyanFamily`.
      `Undec.undecidable_termEq_of_family`, `undecidable_kaTermEq_of_family`, `Reductions/Sigma1.lean`

### §4 Representable relations

- [x] Definition 20. `TD.Rel`, `Representable.lean:120` (residue bound only for `Λ ⊆ L`)
- [x] Lemma 21. `TD.Rel.le_below_add_iter`, `Representable.lean:154`
- [x] Theorem 22. `TD.Rel.le_below_of_iter_eq_empty`, `Representable.lean:203`
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
- [x] Lemma 31. `TD.IsAutomaton.exists_fanout_expansion`, `BoundedOutput.lean:130`
- [x] Lemma 33. `TD.exists_le_sigNe_of_not_prefix`, `SingleStep.lean:101` (paper form `le_sigNe_kstar_of_not_prefix`, `:118`)
- [x] Lemma 34. `TD.rel_of_finiteState`, `SingleStep.lean:221`; explicit residue `TD.rel_resid_of_finiteStateLe`, `:130`
- [x] Lemma 35, `R_M` is representable. `Enc.rel_RM`, `MachineEncoding/Transition.lean:216`;
  `Enc.rel_RM_le`, `:194`

## Extra infrastructure (not in the paper)

- [x] Syntax-directed residue bound. `TD.finiteStateLe_mk`, `Syntax.lean:215`
- [x] Renaming letters preserves provability (`TD.le_map`, `Syntax.lean:318`) and reflects
  model inclusion (`TD.pl_le_of_map`, `Syntax.lean:311`)
- [x] Expression-level `R_M`, `C_M`, `T_a`, `ρ_M`. `MachineEncoding/MachineTerms.lean` (`rmS`, `crunS`, `haltS`,
  `rhoS`, `lhsS`, `rhsS`, each with an `mk_*` lemma)
