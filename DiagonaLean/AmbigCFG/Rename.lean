/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.AmbigCFG.Basic
import DiagonaLean.Foundations.Grammar.Code

@[expose] public section

/-! # Renaming symbols keeps ambiguity

Renaming the terminals and nonterminals of a presented grammar (`GrammarPres.map`) renames its parse
trees (`ParseTree.rename`), and their yields (`ParseTree.rename_yield`). When the renaming of rules
is injective on the rules of the grammar, distinct trees stay distinct (`ParseTree.rename_inj`), so
an ambiguous grammar stays ambiguous (`decisionProblem_map`). For injective renamings the converse
follows by renaming back with left inverses (`decisionProblem_map_iff`).

Distinct trees can sit at distinct nonterminals, so injectivity is stated for pairs of a nonterminal
and a tree (`Σ n, ParseTree G n`); this avoids heterogeneous equality of trees.
-/

namespace DiagonaLean.AmbigCFG

open DiagonaLean.Foundations.Grammar

variable {T T' N M : Type} [DecidableEq T] [DecidableEq T'] [DecidableEq N] [DecidableEq M]
  {f : T → T'} {e : N → M} {p : GrammarPres N T}

mutual
  /-- The renaming of a parse tree. -/
  def ParseTree.rename (f : T → T') (e : N → M) {n : N} :
      ParseTree p.toCFG n → ParseTree (p.map f e).toCFG (e n)
    | .node r hr cs =>
      .node (@ruleMap T T' N M f e r) ((mem_rules_map_toCFG f e p _).2 ⟨r, hr, rfl⟩)
        (Forest.rename f e cs)

  /-- The renaming of a forest. -/
  def Forest.rename (f : T → T') (e : N → M) {ss : List (Symbol T N)} :
      Forest p.toCFG ss → Forest (p.map f e).toCFG (ss.map (Symbol.mapBoth f e))
    | .nil => .nil
    | .consT t rest => .consT (f t) (Forest.rename f e rest)
    | .consN tr rest => .consN (ParseTree.rename f e tr) (Forest.rename f e rest)
end

mutual
  /-- Renaming a tree renames its yield. -/
  theorem ParseTree.rename_yield {n : N} :
      ∀ t : ParseTree p.toCFG n, (t.rename f e).yield = t.yield.map f
    | .node r hr cs => by
      simp only [ParseTree.rename, ParseTree.yield]
      exact Forest.rename_yield cs

  /-- Renaming a forest renames its yield. -/
  theorem Forest.rename_yield {ss : List (Symbol T N)} :
      ∀ fs : Forest p.toCFG ss, (fs.rename f e).yield = fs.yield.map f
    | .nil => rfl
    | .consT t rest => by
      simp only [Forest.rename, Forest.yield, List.map_cons]
      rw [Forest.rename_yield rest]
    | .consN tr rest => by
      simp only [Forest.rename, Forest.yield, List.map_append]
      rw [ParseTree.rename_yield tr, Forest.rename_yield rest]
end

/-- The rule at the root of a tree. -/
def ParseTree.rootRule {G : ContextFreeGrammar T} : (Σ n, ParseTree G n) → ContextFreeRule T G.NT
  | ⟨_, .node r _ _⟩ => r

section Inj

/-- The renaming of rules by `f` and `e` is injective on the rules of `p`. -/
abbrev RulesInj (f : T → T') (e : N → M) (p : GrammarPres N T) : Prop :=
  ∀ r₁ ∈ p.toCFG.rules, ∀ r₂ ∈ p.toCFG.rules, ruleMap f e r₁ = ruleMap f e r₂ → r₁ = r₂

mutual
  /-- Renaming is injective on trees, when it is injective on the rules of the grammar. -/
  theorem ParseTree.rename_inj
      (H : RulesInj f e p) :
      ∀ {n m : N} (t₁ : ParseTree p.toCFG n) (t₂ : ParseTree p.toCFG m),
      (⟨e n, t₁.rename f e⟩ : Σ k, ParseTree (p.map f e).toCFG k) = ⟨e m, t₂.rename f e⟩ →
        (⟨n, t₁⟩ : Σ k, ParseTree p.toCFG k) = ⟨m, t₂⟩
    | _, _, .node r₁ h₁ c₁, .node r₂ h₂ c₂, h => by
      have hr : ruleMap f e r₁ = ruleMap f e r₂ := by
        simpa [ParseTree.rename, ParseTree.rootRule] using congrArg ParseTree.rootRule h
      obtain rfl := H r₁ h₁ r₂ h₂ hr
      have hc : Forest.rename f e c₁ = Forest.rename f e c₂ := by
        have := eq_of_heq (Sigma.mk.inj h).2
        simp only [ParseTree.rename] at this
        injection this
      rw [Forest.rename_inj H c₁ c₂ hc]

  /-- Renaming is injective on forests, when it is injective on the rules of the grammar. -/
  theorem Forest.rename_inj
      (H : RulesInj f e p) : ∀ {ss : List (Symbol T N)} (f₁ f₂ : Forest p.toCFG ss),
      f₁.rename f e = f₂.rename f e → f₁ = f₂
    | _, .nil, .nil, _ => rfl
    | _, .consT t r₁, .consT _ r₂, h => by
      simp only [Forest.rename] at h
      injection h with _ _ h2
      rw [Forest.rename_inj H r₁ r₂ h2]
    | _, .consN t₁ r₁, .consN t₂ r₂, h => by
      simp only [Forest.rename] at h
      injection h with _ _ h1 h2
      have ht := ParseTree.rename_inj H t₁ t₂ (by rw [h1])
      rw [eq_of_heq (Sigma.mk.inj ht).2, Forest.rename_inj H r₁ r₂ h2]
end

/-- **Renaming keeps ambiguity**, when it is injective on the rules of the grammar. -/
theorem decisionProblem_map (H : RulesInj f e p)
    (h : DecisionProblem p.toCFG) : DecisionProblem (p.map f e).toCFG := by
  obtain ⟨t₁, t₂, hne, hy⟩ := h
  refine ⟨t₁.rename f e, t₂.rename f e, fun heq => hne ?_, ?_⟩
  · exact eq_of_heq (Sigma.mk.inj (ParseTree.rename_inj H t₁ t₂ (by rw [heq]))).2
  · exact (ParseTree.rename_yield t₁).trans
      ((congrArg (List.map f) hy).trans (ParseTree.rename_yield t₂).symm)

end Inj

omit [DecidableEq T] [DecidableEq T'] [DecidableEq N] [DecidableEq M] in
theorem map_map {T'' M' : Type} (f : T → T') (e : N → M) (f' : T' → T'') (e' : M → M')
    (p : GrammarPres N T) : (p.map f e).map f' e' = p.map (f' ∘ f) (e' ∘ e) := by
  simp [GrammarPres.map, List.map_map, Function.comp_def, Sum.map_map]

omit [DecidableEq T] [DecidableEq T'] [DecidableEq N] [DecidableEq M] in
theorem map_id (p : GrammarPres N T) : p.map id id = p := by
  simp [GrammarPres.map]

/-- **Injective renamings keep and reflect ambiguity.** -/
theorem decisionProblem_map_iff [Nonempty T] [Nonempty N] (hf : Function.Injective f)
    (he : Function.Injective e) : DecisionProblem (p.map f e).toCFG ↔ DecisionProblem p.toCFG := by
  have hrule : Function.Injective (ruleMap f e) := fun r₁ r₂ h => by
    simp only [ruleMap, ContextFreeRule.mk.injEq] at h
    exact ContextFreeRule.ext (he h.1)
      (List.map_injective_iff.2 (Symbol.mapBoth_injective hf he) h.2)
  constructor
  · intro h
    classical
    have hl : (p.map f e).map (Function.invFun f) (Function.invFun e) = p := by
      rw [map_map, Function.invFun_comp hf, Function.invFun_comp he, map_id]
    have := decisionProblem_map (f := Function.invFun f) (e := Function.invFun e) (p := p.map f e)
      (fun r₁ h₁ r₂ h₂ hr => by
        obtain ⟨s₁, -, rfl⟩ := (mem_rules_map_toCFG f e p r₁).1 h₁
        obtain ⟨s₂, -, rfl⟩ := (mem_rules_map_toCFG f e p r₂).1 h₂
        have k : ∀ s : ContextFreeRule T N,
            ruleMap (Function.invFun f) (Function.invFun e) (ruleMap f e s) = s := by
          rintro ⟨i, o⟩
          simp only [ruleMap, List.map_map, ContextFreeRule.mk.injEq]
          refine ⟨Function.leftInverse_invFun he i, ?_⟩
          conv_rhs => rw [← List.map_id o]
          refine List.map_congr_left fun x _ => ?_
          rcases x with x | x
          · simp [Symbol.mapBoth, Function.leftInverse_invFun hf x]
          · simp [Symbol.mapBoth, Function.leftInverse_invFun he x]
        rw [k, k] at hr
        rw [hr]) h
    rwa [hl] at this
  · exact decisionProblem_map (fun r₁ _ r₂ _ h => hrule h)

end DiagonaLean.AmbigCFG
