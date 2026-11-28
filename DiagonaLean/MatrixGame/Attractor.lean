/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.MatrixGame.Basic

@[expose] public section

/-! # Winning positions as an attractor

The problem is stated with strategies (`Basic.lean`). The proofs use an inductive form instead:
`ForceZero G p`, the least set of positions that contains zero and contains `p` as soon as Eve has
a move `a` such that every reply `b` of Adam leads into the set (`p * a * b`), the attractor of
zero. This file proves that the two agree.

* From an attractor position Eve has a winning strategy (`exists_strategy_of_forceZero`): by
  induction on `ForceZero`; after Adam's first reply `b` Eve follows a winning strategy from
  `p * a * b`, and the play continues as the shifted play (`play_succ_eq_cons`). A strategy needs a
  move even where the game is already won, so this direction assumes that Eve has one.
* From a position with a winning strategy, the position is in the attractor
  (`forceZero_of_exists_strategy`): from a position outside it Adam replies so that the product
  stays outside, and zero is inside.

So the problem is membership of the identity in the attractor (`decisionProblem_iff_forceZero`),
which holds also when Eve has no move: then neither holds.

## Main definitions

* `ForceZero G p`: the attractor of zero.

## Main statements

* `forceZero_iff_exists_strategy`: if Eve has a move, `ForceZero G p` holds iff Eve has a legal
  strategy that wins from `p`.
* `decisionProblem_iff_forceZero`: the problem is `ForceZero G 1`.

## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

namespace DiagonaLean.MatrixGame

/-- `ForceZero G p`: Eve can force zero from `p`, inductively. Either `p` is zero, or Eve has a move
`a` after which she can force zero from `p * a * b` for every reply `b` of Adam. -/
inductive ForceZero (G : Arena) : Position → Prop where
  | target : ForceZero G 0
  | move {p : Position} (a : Position) (ha : a ∈ G.1)
      (next : ∀ b ∈ G.2, ForceZero G (p * a * b)) : ForceZero G p

/-- A round played last multiplies the product on the right. -/
theorem histProd_append (h : History) (r : Position × Position) :
    histProd (h ++ [r]) = histProd h * r.1 * r.2 := by
  induction h with
  | nil => simp [histProd]
  | cons s h ih => simp only [List.cons_append, histProd, ih, mul_assoc]

/-- The play of `σ` against `τ` after the first round `(a, b)`: Eve's strategy restarted on the
rest of the history, against Adam's strategy shifted by that round. -/
theorem play_succ_eq_cons {σ σ' : EveStrategy} {τ : AdamStrategy} {a b : Position}
    (h0 : σ [] = a) (hb : τ [] a = b) (hσ : ∀ h, σ ((a, b) :: h) = σ' h) (t : ℕ) :
    play σ τ (t + 1) = (a, b) :: play σ' (fun h e => τ ((a, b) :: h) e) t := by
  induction t with
  | zero => simp [play, h0, hb]
  | succ t ih =>
    rw [play, ih, play, hσ]
    rfl

/-- **A winning position has a winning strategy**, given a move for Eve (a strategy needs one even
where the game is already won). -/
theorem exists_strategy_of_forceZero {G : Arena} (hE : G.1.Nonempty) {p : Position}
    (h : ForceZero G p) : ∃ σ, LegalEve G σ ∧ WinsFrom G σ p := by
  classical
  obtain ⟨e₀, he₀⟩ := hE
  induction h with
  | target => exact ⟨fun _ => e₀, fun _ => he₀, fun _ _ => ⟨0, by simp⟩⟩
  | @move p a ha _ ih =>
    -- after Adam's reply `b`, Eve follows a winning strategy from `p * a * b`
    let next (b : Position) : EveStrategy :=
      if hb : b ∈ G.2 then (ih b hb).choose else fun _ => e₀
    let σ : EveStrategy := fun
      | [] => a
      | (_, b) :: h => next b h
    have hnext : ∀ b, LegalEve G (next b) := fun b h => by
      by_cases hb : b ∈ G.2
      · simpa [next, hb] using (ih b hb).choose_spec.1 h
      · simpa [next, hb] using he₀
    refine ⟨σ, fun h => ?_, fun τ hτ => ?_⟩
    · match h with
      | [] => exact ha
      | (_, b) :: h => exact hnext b h
    · have hb := hτ [] a
      obtain ⟨t, ht⟩ := (by simpa [next, hb] using (ih _ hb).choose_spec.2 :
        WinsFrom G (next (τ [] a)) (p * a * τ [] a)) _ (fun h e => hτ _ e)
      refine ⟨t + 1, ?_⟩
      rw [play_succ_eq_cons (σ' := next (τ [] a)) rfl rfl (fun _ => rfl), histProd]
      simpa [mul_assoc] using ht

/-- **A position with a winning strategy is winning**: from a losing position Adam keeps the
product among losing positions, which are not zero. -/
theorem forceZero_of_exists_strategy {G : Arena} {p : Position}
    (h : ∃ σ, LegalEve G σ ∧ WinsFrom G σ p) : ForceZero G p := by
  classical
  obtain ⟨σ, hσ, hwin⟩ := h
  by_contra hp
  -- Adam has a move: with none, Eve's first move would win
  obtain ⟨b₀, hb₀⟩ : G.2.Nonempty := by
    by_contra hA
    rw [Finset.not_nonempty_iff_eq_empty] at hA
    exact hp (.move (σ []) (hσ []) (by simp [hA]))
  -- Adam replies to keep the product losing, when he can
  let τ : AdamStrategy := fun h e =>
    if hx : ∃ b ∈ G.2, ¬ ForceZero G (p * histProd h * e * b) then hx.choose else b₀
  have hτ : LegalAdam G τ := fun h e => by
    by_cases hx : ∃ b ∈ G.2, ¬ ForceZero G (p * histProd h * e * b)
    · simpa [τ, hx] using hx.choose_spec.1
    · simpa [τ, hx] using hb₀
  have hlose : ∀ t, ¬ ForceZero G (p * histProd (play σ τ t)) := by
    intro t
    induction t with
    | zero => simpa [play, histProd] using hp
    | succ t ih =>
      let q := p * histProd (play σ τ t)
      have hx : ∃ b ∈ G.2, ¬ ForceZero G (q * σ (play σ τ t) * b) := by
        by_contra hx
        push Not at hx
        exact ih (.move _ (hσ _) hx)
      have hτt : τ (play σ τ t) (σ (play σ τ t)) = hx.choose := dite_eq_left hx
      rw [play, histProd_append, hτt]
      have hc := hx.choose_spec.2
      simp only [q, mul_assoc] at hc ⊢
      exact hc
  obtain ⟨t, ht⟩ := hwin τ hτ
  exact hlose t (ht ▸ .target)

/-- **Eve can force zero from `p` iff she has a legal strategy that wins from `p`**, when she has a
move. -/
theorem forceZero_iff_exists_strategy {G : Arena} (hE : G.1.Nonempty) (p : Position) :
    ForceZero G p ↔ ∃ σ, LegalEve G σ ∧ WinsFrom G σ p :=
  ⟨exists_strategy_of_forceZero hE, forceZero_of_exists_strategy⟩

/-- **The matrix game is membership of the identity in the attractor of zero.** -/
theorem decisionProblem_iff_forceZero (G : Arena) : DecisionProblem G ↔ ForceZero G 1 := by
  by_cases hE : G.1.Nonempty
  · exact (forceZero_iff_exists_strategy hE 1).symm
  · rw [Finset.not_nonempty_iff_eq_empty] at hE
    -- with no move for Eve, she wins only where the product is already zero
    have hzero : ∀ {q}, ForceZero G q → q = 0 := fun h => by
      induction h with
      | target => rfl
      | move a ha _ _ => simp [hE] at ha
    constructor
    · rintro ⟨σ, hσ, -⟩
      simpa [hE] using hσ []
    · exact fun h => absurd (hzero h) one_ne_zero

end DiagonaLean.MatrixGame
