/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.TeamGame.Basic

@[expose] public section

/-! # Team games given by a successor function, as games over `ℕ`

A team game can be given by a start position, a successor function `succ` from a position and two
actions to a list of positions, and the observations `obs` of the two players, each a bit
(`IsSuccPlay`). When the positions reachable from the start lie in a finite list `allP`, the
actions in a finite list `allA`, and positions and actions have injective codes, `codeGame` lists
the coded edges as a `Game ℕ`. The team has strategies making every play visit `goal` iff it wins
the reachability problem of the coded game (`reachProblem_codeGame_iff`), and likewise for safety
(`safetyProblem_codeGame_iff`).
-/

namespace DiagonaLean.TeamGame

variable {P A : Type}

/-- `g` is a play from `start` along `succ` in which player 0 follows `σ₀` and player 1 follows
`σ₁`, each seeing its bit of `obs`. -/
def IsSuccPlay (start : P) (succ : P → A → A → List P) (obs : P → Bool × Bool)
    (σ₀ σ₁ : List Bool → A) (g : ℕ → P) : Prop :=
  g 0 = start ∧ ∀ k, g (k + 1) ∈
    succ (g k) (σ₀ (history (fun p => (obs p).1) g k)) (σ₁ (history (fun p => (obs p).2) g k))

/-- The game over `ℕ` of a successor function: positions in `allP` and actions in `allA`, coded by
`enc` and `encA`, observations coded as `0` and `1`. -/
def codeGame (enc : P → ℕ) (encA : A → ℕ) (start : P) (succ : P → A → A → List P)
    (obs : P → Bool × Bool) (allP : List P) (allA : List A) (goal : List P) : Game ℕ where
  init := enc start
  acts := allA.map encA
  edges := allP.flatMap fun p => allA.flatMap fun a₀ => allA.flatMap fun a₁ =>
    (succ p a₀ a₁).map fun p' => (enc p, encA a₀, encA a₁, enc p')
  obs := allP.map fun p => (enc p, (obs p).1.toNat, (obs p).2.toNat)
  goal := goal.map enc

section Coding

variable {enc : P → ℕ} {encA : A → ℕ} {start : P} {succ : P → A → A → List P}
  {obs : P → Bool × Bool} {allP : List P} {allA : List A} {goal : List P}

/-- The observation of player 0 of a coded position is its bit. -/
theorem obs₀_codeGame (henc : Function.Injective enc) {p : P} (hp : p ∈ allP) :
    (codeGame enc encA start succ obs allP allA goal).obs₀ 0 (enc p) = (obs p).1.toNat := by
  unfold Game.obs₀ codeGame
  cases h : (allP.map fun p => (enc p, (obs p).1.toNat, (obs p).2.toNat)).find?
      (fun o => o.1 = enc p) with
  | none =>
    exact absurd (List.find?_eq_none.1 h _ (List.mem_map_of_mem hp)) (by simp)
  | some o =>
    have h₁ := List.find?_some h
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some h)
    simp only [decide_eq_true_eq] at h₁
    rw [henc h₁]
    rfl

/-- The observation of player 1 of a coded position is its bit. -/
theorem obs₁_codeGame (henc : Function.Injective enc) {p : P} (hp : p ∈ allP) :
    (codeGame enc encA start succ obs allP allA goal).obs₁ 0 (enc p) = (obs p).2.toNat := by
  unfold Game.obs₁ codeGame
  cases h : (allP.map fun p => (enc p, (obs p).1.toNat, (obs p).2.toNat)).find?
      (fun o => o.1 = enc p) with
  | none =>
    exact absurd (List.find?_eq_none.1 h _ (List.mem_map_of_mem hp)) (by simp)
  | some o =>
    have h₁ := List.find?_some h
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some h)
    simp only [decide_eq_true_eq] at h₁
    rw [henc h₁]
    rfl

/-- The coded histories of a play inside `allP` are its histories, with bits coded. -/
theorem history_codeGame (henc : Function.Injective enc) {g : ℕ → P} (hg : ∀ k, g k ∈ allP)
    (k : ℕ) :
    history ((codeGame enc encA start succ obs allP allA goal).obs₀ 0) (enc ∘ g) k =
        (history (fun p => (obs p).1) g k).map Bool.toNat ∧
      history ((codeGame enc encA start succ obs allP allA goal).obs₁ 0) (enc ∘ g) k =
        (history (fun p => (obs p).2) g k).map Bool.toNat := by
  simp [history, Function.comp_def, obs₀_codeGame henc (hg _), obs₁_codeGame henc (hg _)]

/-- The coded edges are the codes of the edges of `succ` between listed positions for listed
actions. -/
theorem mem_edges_codeGame {x : ℕ × ℕ × ℕ × ℕ} :
    x ∈ (codeGame enc encA start succ obs allP allA goal).edges ↔ ∃ p ∈ allP, ∃ a₀ ∈ allA,
      ∃ a₁ ∈ allA, ∃ p' ∈ succ p a₀ a₁, x = (enc p, encA a₀, encA a₁, enc p') := by
  simp only [codeGame, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨p, hp, a₀, ha₀, a₁, ha₁, p', hp', rfl⟩
    exact ⟨p, hp, a₀, ha₀, a₁, ha₁, p', hp', rfl⟩
  · rintro ⟨p, hp, a₀, ha₀, a₁, ha₁, p', hp', rfl⟩
    exact ⟨p, hp, a₀, ha₀, a₁, ha₁, p', hp', rfl⟩

/-- A coded edge between coded positions for coded actions is an edge of `succ`. -/
theorem mem_edges_codeGame_enc (henc : Function.Injective enc) (hencA : Function.Injective encA)
    {p p' : P} {a₀ a₁ : A} :
    (enc p, encA a₀, encA a₁, enc p') ∈ (codeGame enc encA start succ obs allP allA goal).edges ↔
      p ∈ allP ∧ a₀ ∈ allA ∧ a₁ ∈ allA ∧ p' ∈ succ p a₀ a₁ := by
  rw [mem_edges_codeGame]
  constructor
  · rintro ⟨q, hq, b₀, hb₀, b₁, hb₁, q', hq', h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    rw [henc h₁, hencA h₂, hencA h₃, henc h₄]
    exact ⟨hq, hb₀, hb₁, hq'⟩
  · rintro ⟨hp, ha₀, ha₁, hp'⟩
    exact ⟨p, hp, a₀, ha₀, a₁, ha₁, p', hp', rfl⟩

/-- Reading back the bits of a coded history gives the history. -/
theorem map_toNat_beq (h : List Bool) : (h.map Bool.toNat).map (· == 1) = h := by
  induction h with
  | nil => rfl
  | cons b h ih => cases b <;> simp_all

/-- The coded strategy of a strategy: read the bits, code the action. -/
def encStrat (encA : A → ℕ) (σ : List Bool → A) (h : List ℕ) : ℕ := encA (σ (h.map (· == 1)))

/-- The strategy read from a coded strategy: code the bits, decode the action (`default` when it
is no listed action). -/
def decStrat [Inhabited A] (encA : A → ℕ) (allA : List A) (σ : List ℕ → ℕ) (h : List Bool) : A :=
  (allA.find? (encA · = σ (h.map Bool.toNat))).getD default

/-- A coded strategy choosing listed actions is the code of the strategy read from it. -/
theorem encA_decStrat [Inhabited A] {σ : List ℕ → ℕ} {h : List Bool}
    (hσ : σ (h.map Bool.toNat) ∈ allA.map encA) :
    encA (decStrat encA allA σ h) = σ (h.map Bool.toNat) := by
  unfold decStrat
  cases hf : allA.find? (encA · = σ (h.map Bool.toNat)) with
  | none =>
    obtain ⟨a, ha, he⟩ := List.mem_map.1 hσ
    exact absurd (List.find?_eq_none.1 hf a ha) (by simp [he])
  | some a => simpa using List.find?_some hf

/-- **Plays of the coded game are coded plays**: when the coded strategies are the codes of `σ₀`
and `σ₁`, every play of the coded game is the code of a play along `succ`. -/
theorem exists_succPlay (henc : Function.Injective enc)
    (hencA : Function.Injective encA) (hstart : start ∈ allP)
    (hclosed : ∀ p ∈ allP, ∀ a₀ a₁, ∀ p' ∈ succ p a₀ a₁, p' ∈ allP) {σ₀ σ₁ : List Bool → A}
    {f : ℕ → ℕ} (hf : IsPlay (codeGame enc encA start succ obs allP allA goal) 0
      (encStrat encA σ₀) (encStrat encA σ₁) f) :
    ∃ g, IsSuccPlay start succ obs σ₀ σ₁ g ∧ f = enc ∘ g := by
  have hmem : ∀ k, ∃ p ∈ allP, f k = enc p := by
    intro k
    induction k with
    | zero => exact ⟨start, hstart, hf.1⟩
    | succ k ih =>
      obtain ⟨q, hq, b₀, -, b₁, -, q', hq', h⟩ := mem_edges_codeGame.1 (hf.2 k)
      simp only [Prod.mk.injEq] at h
      exact ⟨q', hclosed q hq b₀ b₁ q' hq', h.2.2.2⟩
  choose g hg hfg using hmem
  have hfe : f = enc ∘ g := funext hfg
  refine ⟨g, ⟨henc (by rw [← hfg, hf.1]; rfl), fun k => ?_⟩, hfe⟩
  have h := hf.2 k
  obtain ⟨h₀, h₁⟩ := history_codeGame (encA := encA) (start := start) (succ := succ) (obs := obs)
    (goal := goal) henc hg k
  rw [hfe, h₀, h₁] at h
  simp only [Function.comp_apply, encStrat, map_toNat_beq] at h
  exact ((mem_edges_codeGame_enc henc hencA).1 h).2.2.2

/-- **Coded plays are plays of the coded game**: when the coded strategies `σ₀` and `σ₁` choose
listed actions, the code of every play along `succ` that follows the strategies read from them is
a play of the coded game. -/
theorem isPlay_enc [Inhabited A] (henc : Function.Injective enc)
    (hencA : Function.Injective encA) (hstart : start ∈ allP)
    (hclosed : ∀ p ∈ allP, ∀ a₀ a₁, ∀ p' ∈ succ p a₀ a₁, p' ∈ allP) (hallA : ∀ a, a ∈ allA)
    {σ₀ σ₁ : List ℕ → ℕ} (hl : Legal (codeGame enc encA start succ obs allP allA goal) σ₀ σ₁)
    {g : ℕ → P} (hg : IsSuccPlay start succ obs (decStrat encA allA σ₀) (decStrat encA allA σ₁) g) :
    IsPlay (codeGame enc encA start succ obs allP allA goal) 0 σ₀ σ₁ (enc ∘ g) := by
  have hin : ∀ k, g k ∈ allP := by
    intro k
    induction k with
    | zero => rw [hg.1]; exact hstart
    | succ k ih => exact hclosed _ ih _ _ _ (hg.2 k)
  refine ⟨by simp [hg.1]; rfl, fun k => ?_⟩
  obtain ⟨h₀, h₁⟩ := history_codeGame (encA := encA) (start := start) (succ := succ) (obs := obs)
    (goal := goal) henc hin k
  have e₀ := encA_decStrat (σ := σ₀) (h := history (fun p => (obs p).1) g k) (hl _).1
  have e₁ := encA_decStrat (σ := σ₁) (h := history (fun p => (obs p).2) g k) (hl _).2
  show (enc (g k), σ₀ _, σ₁ _, enc (g (k + 1))) ∈ _
  rw [h₀, h₁, ← e₀, ← e₁]
  exact (mem_edges_codeGame_enc henc hencA).2 ⟨hin k, hallA _, hallA _, hg.2 k⟩

/-- **The reachability problem of the coded game** is the reachability game along `succ`. -/
theorem reachProblem_codeGame_iff [Inhabited A] (henc : Function.Injective enc)
    (hencA : Function.Injective encA) (hstart : start ∈ allP)
    (hclosed : ∀ p ∈ allP, ∀ a₀ a₁, ∀ p' ∈ succ p a₀ a₁, p' ∈ allP) (hallA : ∀ a, a ∈ allA) :
    ReachProblem (codeGame enc encA start succ obs allP allA goal, 0) ↔
      ∃ σ₀ σ₁ : List Bool → A, ∀ g, IsSuccPlay start succ obs σ₀ σ₁ g → ∃ k, g k ∈ goal := by
  constructor
  · rintro ⟨σ₀, σ₁, hl, hw⟩
    refine ⟨decStrat encA allA σ₀, decStrat encA allA σ₁, fun g hg => ?_⟩
    obtain ⟨k, hk⟩ := hw _ (isPlay_enc henc hencA hstart hclosed hallA hl hg)
    obtain ⟨p, hp, hpk⟩ := List.mem_map.1 hk
    exact ⟨k, henc hpk ▸ hp⟩
  · rintro ⟨σ₀, σ₁, hw⟩
    refine ⟨encStrat encA σ₀, encStrat encA σ₁,
      fun _ => ⟨List.mem_map_of_mem (hallA _), List.mem_map_of_mem (hallA _)⟩, fun f hf => ?_⟩
    obtain ⟨g, hg, rfl⟩ := exists_succPlay henc hencA hstart hclosed hf
    obtain ⟨k, hk⟩ := hw g hg
    exact ⟨k, List.mem_map_of_mem hk⟩

/-- **The safety problem of the coded game** is the safety game along `succ`. -/
theorem safetyProblem_codeGame_iff [Inhabited A] (henc : Function.Injective enc)
    (hencA : Function.Injective encA) (hstart : start ∈ allP)
    (hclosed : ∀ p ∈ allP, ∀ a₀ a₁, ∀ p' ∈ succ p a₀ a₁, p' ∈ allP) (hallA : ∀ a, a ∈ allA) :
    SafetyProblem (codeGame enc encA start succ obs allP allA goal, 0) ↔
      ∃ σ₀ σ₁ : List Bool → A, ∀ g, IsSuccPlay start succ obs σ₀ σ₁ g → ∀ k, g k ∉ goal := by
  constructor
  · rintro ⟨σ₀, σ₁, hl, hw⟩
    exact ⟨decStrat encA allA σ₀, decStrat encA allA σ₁, fun g hg k hk =>
      hw _ (isPlay_enc henc hencA hstart hclosed hallA hl hg) k (List.mem_map_of_mem hk)⟩
  · rintro ⟨σ₀, σ₁, hw⟩
    refine ⟨encStrat encA σ₀, encStrat encA σ₁,
      fun _ => ⟨List.mem_map_of_mem (hallA _), List.mem_map_of_mem (hallA _)⟩, fun f hf k hk => ?_⟩
    obtain ⟨g, hg, rfl⟩ := exists_succPlay henc hencA hstart hclosed hf
    obtain ⟨p, hp, hpk⟩ := List.mem_map.1 hk
    exact hw g hg k (henc hpk ▸ hp)

end Coding

end DiagonaLean.TeamGame
