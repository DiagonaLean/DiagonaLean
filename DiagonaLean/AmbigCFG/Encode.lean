/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.AmbigCFG.Rename
import DiagonaLean.Foundations.Codes.Grammar

@[expose] public section

/-! # Encoding the terminals keeps and reflects ambiguity

Encoding every terminal of a grammar by a code (`Foundations.Codes.grammarEncode`) encodes its
parse trees (`ParseTree.enc`): a terminal leaf `t` becomes the leaves of the word `c t`
(`Forest.consTs`), and the yield is encoded (`ParseTree.enc_yield`).

* Distinct trees stay distinct (`ParseTree.enc_inj`), since encoding rules is injective for a
  code; so an ambiguous grammar stays ambiguous.
* Every tree of the encoded grammar is the encoding of a tree (`ParseTree.enc_surj`): its rules
  are encoded rules, and a forest over an encoded list of symbols is decoded symbol by symbol,
  the leaves of a code word together. Two distinct trees of the encoded grammar with the same
  yield come from two distinct trees whose yields have the same encoding, hence are equal, since
  `c` is a code. So ambiguity is reflected.

Together: `decisionProblem_grammarEncode_iff`.
-/

namespace DiagonaLean.AmbigCFG

open DiagonaLean.Foundations.Codes

variable {T β : Type}

/-- Prepending terminal leaves to a forest. -/
def Forest.consTs {H : ContextFreeGrammar β} :
    (w : List β) → {ss : List (Symbol β H.NT)} → Forest H ss →
      Forest H (w.map Symbol.terminal ++ ss)
  | [], _, f => f
  | b :: w, _, f => .consT b (Forest.consTs w f)

theorem Forest.consTs_yield {H : ContextFreeGrammar β} (w : List β) {ss : List (Symbol β H.NT)}
    (f : Forest H ss) : (Forest.consTs w f).yield = w ++ f.yield := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [Forest.consTs, Forest.yield, ih, List.cons_append]

theorem Forest.consTs_inj {H : ContextFreeGrammar β} (w : List β) {ss : List (Symbol β H.NT)}
    {f₁ f₂ : Forest H ss} (h : Forest.consTs w f₁ = Forest.consTs w f₂) : f₁ = f₂ := by
  induction w with
  | nil => exact h
  | cons b w ih =>
    simp only [Forest.consTs] at h
    exact ih (Forest.consT.inj h)

variable {c : T → List β} {G : ContextFreeGrammar T}

/-- The words of a code are not empty. -/
theorem IsCode.ne_nil (hc : IsCode c) (t : T) : c t ≠ [] := fun h =>
  List.cons_ne_nil t [] (hc (by simp [h] : encode c [t] = encode c []))

mutual
  /-- The encoding of a parse tree. -/
  def ParseTree.enc (hc : IsCode c) {n : G.NT} : ParseTree G n → ParseTree (grammarEncode c hc G) n
    | .node r hr cs =>
      (.node (ruleEncode c r) (Finset.mem_map_of_mem _ hr) (Forest.enc hc cs) :
        ParseTree (grammarEncode c hc G) (ruleEncode c r).input)

  /-- The encoding of a forest. -/
  def Forest.enc (hc : IsCode c) {ss : List (Symbol T G.NT)} :
      Forest G ss → Forest (grammarEncode c hc G) (Foundations.Codes.encode (symCode c) ss)
    | .nil => .nil
    | .consT t rest => Forest.consTs (c t) (Forest.enc hc rest)
    | .consN tr rest => .consN (ParseTree.enc hc tr) (Forest.enc hc rest)
end

variable (hc : IsCode c)

mutual
  /-- Encoding a tree encodes its yield. -/
  theorem ParseTree.enc_yield {n : G.NT} :
      ∀ t : ParseTree G n, (t.enc hc).yield = Foundations.Codes.encode c t.yield
    | .node r hr cs => by
      simp only [ParseTree.enc, ParseTree.yield]
      exact Forest.enc_yield cs

  /-- Encoding a forest encodes its yield. -/
  theorem Forest.enc_yield {ss : List (Symbol T G.NT)} :
      ∀ f : Forest G ss, (f.enc hc).yield = Foundations.Codes.encode c f.yield
    | .nil => rfl
    | .consT t rest => by
      show (Forest.consTs (c t) (Forest.enc hc rest)).yield =
        Foundations.Codes.encode c (t :: rest.yield)
      rw [Forest.consTs_yield, Forest.enc_yield rest, encode_cons]
    | .consN tr rest => by
      show (ParseTree.enc hc tr).yield ++ (Forest.enc hc rest).yield =
        Foundations.Codes.encode c (tr.yield ++ rest.yield)
      rw [ParseTree.enc_yield tr, Forest.enc_yield rest, encode_append]
end

mutual
  /-- **Every tree of the encoded grammar is the encoding of a tree.** -/
  theorem ParseTree.enc_surj :
      ∀ {n : G.NT} (t' : ParseTree (grammarEncode c hc G) n), ∃ t : ParseTree G n, t.enc hc = t'
    | _, .node r' hr' cs' => by
      have IH := Forest.enc_surj cs'
      obtain ⟨r, hr, rfl⟩ := Finset.mem_map.1 hr'
      obtain ⟨f, hf⟩ := IH [] r.output rfl
      have hf' : f.enc hc = cs' := eq_of_heq hf
      subst hf'
      exact ⟨.node r hr f, rfl⟩

  /-- **Every forest over an encoded list of symbols, after some terminal leaves, is the encoding
  of a forest after those leaves.** -/
  theorem Forest.enc_surj :
      ∀ {ss' : List (Symbol β G.NT)} (f' : Forest (grammarEncode c hc G) ss') (pre : List β)
        (ss : List (Symbol T G.NT)),
        ss' = pre.map Symbol.terminal ++ Foundations.Codes.encode (symCode c) ss →
        ∃ f : Forest G ss, HEq (Forest.consTs pre (f.enc hc)) f'
    | _, .nil, pre, ss, h => by
      obtain ⟨hpre, hss⟩ := List.append_eq_nil_iff.1 h.symm
      obtain rfl := List.map_eq_nil_iff.1 hpre
      rcases ss with _ | ⟨s, ss⟩
      · exact ⟨.nil, HEq.rfl⟩
      · rcases s with t | m
        · obtain ⟨b, w, hcw⟩ := List.exists_cons_of_ne_nil (IsCode.ne_nil hc t)
          simp [symCode, hcw] at hss
        · simp [symCode] at hss
    | _, .consT b rest', pre, ss, h => by
      have IH := Forest.enc_surj rest'
      rcases pre with _ | ⟨b', pre⟩
      · rcases ss with _ | ⟨s, ss⟩
        · simp at h
        · rcases s with t | m
          · obtain ⟨b'', w, hcw⟩ := List.exists_cons_of_ne_nil (IsCode.ne_nil hc t)
            have h' := h
            simp only [List.map_nil, List.nil_append, encode_cons, symCode, hcw, List.map_cons,
              List.cons_append, List.cons.injEq, Symbol.terminal.injEq] at h'
            obtain ⟨rfl, h₁⟩ := h'
            obtain ⟨f, hf⟩ := IH w ss h₁
            refine ⟨.consT t f, ?_⟩
            show HEq (Forest.consTs (c t) (f.enc hc)) (Forest.consT b rest')
            subst h₁
            have hf' : Forest.consTs w (f.enc hc) = rest' := eq_of_heq hf
            subst hf'
            generalize hct : c t = cw
            obtain rfl : cw = b :: w := hct.symm.trans hcw
            exact HEq.rfl
          · simp [symCode] at h
      · simp only [List.map_cons, List.cons_append, List.cons.injEq, Symbol.terminal.injEq] at h
        obtain ⟨rfl, h₁⟩ := h
        obtain ⟨f, hf⟩ := IH pre ss h₁
        subst h₁
        have hf' : Forest.consTs pre (f.enc hc) = rest' := eq_of_heq hf
        subst hf'
        exact ⟨f, HEq.rfl⟩
    | _, .consN tr rest', pre, ss, h => by
      have IHt := ParseTree.enc_surj tr
      have IHf := Forest.enc_surj rest'
      rcases pre with _ | ⟨b', pre⟩
      · rcases ss with _ | ⟨s, ss⟩
        · simp at h
        · rcases s with t | m
          · obtain ⟨b'', w, hcw⟩ := List.exists_cons_of_ne_nil (IsCode.ne_nil hc t)
            simp [symCode, hcw] at h
          · simp only [List.map_nil, List.nil_append, encode_cons, symCode, List.singleton_append,
              List.cons.injEq, Symbol.nonterminal.injEq] at h
            obtain ⟨rfl, h₁⟩ := h
            obtain ⟨t₀, ht₀⟩ := IHt
            obtain ⟨f, hf⟩ := IHf [] ss h₁
            subst h₁ ht₀
            have hf' : f.enc hc = rest' := eq_of_heq hf
            subst hf'
            exact ⟨.consN t₀ f, HEq.rfl⟩
      · simp at h
end

mutual
  /-- **Encoding is injective on trees**, since encoding rules is injective for a code. -/
  theorem ParseTree.enc_inj :
      ∀ {n m : G.NT} (t₁ : ParseTree G n) (t₂ : ParseTree G m),
      (⟨n, t₁.enc hc⟩ : Σ k, ParseTree (grammarEncode c hc G) k) = ⟨m, t₂.enc hc⟩ →
        (⟨n, t₁⟩ : Σ k, ParseTree G k) = ⟨m, t₂⟩
    | _, _, .node r₁ h₁ c₁, .node r₂ h₂ c₂, h => by
      have hr : ruleEncode c r₁ = ruleEncode c r₂ := by
        simpa [ParseTree.enc, ParseTree.rootRule] using congrArg ParseTree.rootRule h
      obtain rfl := ruleEncode_injective hc hr
      have hc' : Forest.enc hc c₁ = Forest.enc hc c₂ := by
        have := eq_of_heq (Sigma.mk.inj h).2
        simp only [ParseTree.enc] at this
        injection this
      rw [Forest.enc_inj c₁ c₂ hc']

  /-- **Encoding is injective on forests.** -/
  theorem Forest.enc_inj : ∀ {ss : List (Symbol T G.NT)} (f₁ f₂ : Forest G ss),
      f₁.enc hc = f₂.enc hc → f₁ = f₂
    | _, .nil, .nil, _ => rfl
    | _, .consT t r₁, .consT _ r₂, h => by
      simp only [Forest.enc] at h
      rw [Forest.enc_inj r₁ r₂ (Forest.consTs_inj (c t) h)]
    | _, .consN t₁ r₁, .consN t₂ r₂, h => by
      simp only [Forest.enc] at h
      injection h with _ _ h1 h2
      have ht := ParseTree.enc_inj t₁ t₂ (by rw [h1])
      rw [eq_of_heq (Sigma.mk.inj ht).2, Forest.enc_inj r₁ r₂ h2]
end

/-- **Encoding the terminals by a code keeps and reflects ambiguity.** -/
theorem decisionProblem_grammarEncode_iff :
    DecisionProblem (grammarEncode c hc G) ↔ DecisionProblem G := by
  constructor
  · rintro ⟨t₁', t₂', hne, hy⟩
    obtain ⟨t₁, rfl⟩ := ParseTree.enc_surj hc t₁'
    obtain ⟨t₂, rfl⟩ := ParseTree.enc_surj hc t₂'
    refine ⟨t₁, t₂, fun h => hne (by rw [h]), hc ?_⟩
    rw [← ParseTree.enc_yield hc, ← ParseTree.enc_yield hc, hy]
  · rintro ⟨t₁, t₂, hne, hy⟩
    refine ⟨t₁.enc hc, t₂.enc hc, fun h => hne ?_, ?_⟩
    · exact eq_of_heq (Sigma.mk.inj (ParseTree.enc_inj hc t₁ t₂ (by rw [h]))).2
    · exact (ParseTree.enc_yield hc t₁).trans
        ((congrArg _ hy).trans (ParseTree.enc_yield hc t₂).symm)

end DiagonaLean.AmbigCFG
