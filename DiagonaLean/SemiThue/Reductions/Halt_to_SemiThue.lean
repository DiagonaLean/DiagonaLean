/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.MPCP.Reductions.Halt_to_MPCP
import DiagonaLean.Foundations.Grammar.Rewriting
import DiagonaLean.Foundations.Codes.Rewriting
import DiagonaLean.SemiThue.Basic

@[expose] public section

/-! # A machine halts iff its configuration string rewrites to the empty string

The transition tiles of the MPCP reduction (`Halt_to_MPCP.lean`) pair a window of a configuration
with its successor, so read as rules `top → bot` they rewrite the configuration string
`# … q a … #` (`block`) one machine step at a time. With the absorb tiles, which let the halting
marker `h⊥` swallow the tape around it, and a final rule `# h⊥ # → []`, they form the string
rewriting system `tmRules tm`, and for a machine that never writes a blank and never moves left at
the left end, `tm` halts on `w` iff `block (initCfg w)` derives the empty string
(`halt_iff_derives`).

* **Forward** (`derives_of_halts`): each step of the run is one rewrite (`step_block`), from the
  configuration lemmas of the MPCP reduction (`encodeCfg_after_right_move_eq` and its siblings);
  after halting, the absorb rules and the final rule erase the string (`derives_halted`).
* **Backward** (`halts_of_derives`): a configuration string has exactly one state marker, and the
  left side of every rule contains a marker, so a rewrite happens at the marker (`split_mark`). By
  determinism it is the machine's step, except for an interior right move at the right end, which
  leaves the marker before `#`: a string from which nothing can be rewritten, so the empty string
  is never reached (`not_derives_stuck`), or the halting marker, when the machine has halted.

The reduction `haltToSemiThue` normalises the machine and its input
(`Foundations.Computability.Normalize`), so that both conditions hold, takes `tmRules` of the
normalised machine, and renames its states to their codes, over the fixed alphabet `Alpha ℕ Sym2`.
`halt_iff_derives` and `Codes.derives_mapRules_iff` make it a reduction from `HaltProblem`
(`halt_reducesto_semiThue_spec`). The systems produced have non-empty left sides
(`haltToSemiThue_lhs_ne`), so it is also a reduction to `DecisionProblemPos`
(`halt_reducesto_semiThuePos_spec`). The packaged reductions `SemiThue.synthFromHalt` and
`SemiThue.synthPosFromHalt` are in `SynthHardness.lean`.
-/

namespace DiagonaLean.SemiThue.Reduction

open Cslib.Turing SingleTapeTM DiagonaLean.PCP DiagonaLean.MPCP.Reduction DiagonaLean.Halt
  DiagonaLean.Halt.Encoding DiagonaLean.Foundations.Grammar DiagonaLean.Foundations.Rewriting
  DiagonaLean.Foundations.Computability.Normalize
  DiagonaLean.Synthetic.Definitions Relation

/-! ### Markers -/

section Mark

variable {Q S : Type}

/-- A state symbol or the halting marker. -/
def isMark : Alpha Q S → Bool
  | .state _ => true
  | .halt => true
  | _ => false

/-- **A marker splits a string uniquely**, when one side has no marker before it and none after
it. -/
theorem split_mark {xs ys xs' ys' : List (Alpha Q S)} {m m' : Alpha Q S} (hm : isMark m)
    (hxs' : ∀ x ∈ xs', isMark x = false) (hys' : ∀ x ∈ ys', isMark x = false)
    (h : xs ++ m :: ys = xs' ++ m' :: ys') : xs = xs' ∧ m = m' ∧ ys = ys' := by
  induction xs generalizing xs' with
  | nil =>
    cases xs' with
    | nil => simpa using h
    | cons x' xs'' =>
      obtain ⟨rfl, -⟩ := List.cons.inj h
      simp_all
  | cons x xs ih =>
    cases xs' with
    | nil =>
      obtain ⟨-, rfl⟩ := List.cons.inj h
      simp_all
    | cons x' xs'' =>
      rw [List.cons_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := ih (fun y hy => hxs' y (List.mem_cons_of_mem _ hy)) h
      exact ⟨rfl, rfl, rfl⟩

end Mark

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- No letter of a lifted tape is a marker. -/
theorem isMark_liftTape (tm : SingleTapeTM Symbol) (l : List (Option Symbol)) :
    ∀ x ∈ liftTape tm l, isMark x = false := by
  intro x hx
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
  rfl

/-- The string of a running configuration, split at its state marker. -/
theorem block_running (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    block tm ⟨some q, t⟩ = (# :: liftTape tm t.left.toList.reverse) ++
      ↟ₛq :: (↟ₜt.head :: (liftTape tm t.right.toList ++ [#])) := by
  simp [block, encodeCfg, encodeRunningCfg, liftTape]

/-- The string of a running configuration has no halting marker. -/
theorem halt_not_mem_block_running (tm : SingleTapeTM Symbol) (q : tm.State) (t : BiTape Symbol) :
    (h⊥ : Alpha tm.State Symbol) ∉ block tm ⟨some q, t⟩ := by
  simp [block, encodeCfg, encodeRunningCfg, liftTape]

/-! ### The rewriting system -/

variable [Encodable Symbol]

/-- The rewriting rule of a tile. -/
def tileRule {α : Type} (t : Tile α) : Rule α := ⟨t.top, t.bot⟩

/-- The rewriting system of a machine: its transition tiles and absorb tiles as rules, and the
final rule `# h⊥ # → []`. -/
def tmRules (tm : EncodableTM Symbol) : SRS (Alpha tm.State Symbol) :=
  (transitionTiles tm).map tileRule ++ (absorbTiles tm.toSingleTapeTM).map tileRule ++
    [⟨[#, h⊥, #], []⟩]

variable {tm : EncodableTM Symbol}

/-- The rule of a transition tile is a rule of the system. -/
theorem tileRule_mem {q : tm.State} {a : Option Symbol} {T : Tile (Alpha tm.State Symbol)}
    (hT : T ∈ transitionTilesFor tm.toSingleTapeTM q a) : tileRule T ∈ tmRules tm :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem
    ((MPCP.Reduction.mem_transitionTiles tm T).2 ⟨q, a, hT⟩)))

/-- The rule `a h⊥ → h⊥` is a rule of the system. -/
theorem absorbLeft_mem (a : Option Symbol) :
    (⟨[↟ₜa, h⊥], [h⊥]⟩ : Rule _) ∈ tmRules tm :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2
    ⟨absorbLeftTile tm.toSingleTapeTM a, List.mem_flatMap.2 ⟨a, mem_enumerate a, by
      simp [absorbTilesFor]⟩, rfl⟩))

/-- The rule `h⊥ a → h⊥` is a rule of the system. -/
theorem absorbRight_mem (a : Option Symbol) :
    (⟨[h⊥, ↟ₜa], [h⊥]⟩ : Rule _) ∈ tmRules tm :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2
    ⟨absorbRightTile tm.toSingleTapeTM a, List.mem_flatMap.2 ⟨a, mem_enumerate a, by
      simp [absorbTilesFor]⟩, rfl⟩))

/-- The final rule `# h⊥ # → []` is a rule of the system. -/
theorem final_mem : (⟨[#, h⊥, #], []⟩ : Rule _) ∈ tmRules tm :=
  List.mem_append_right _ (List.mem_singleton.2 rfl)

/-- A rule is a transition tile, or its left side contains the halting marker. -/
theorem mem_tmRules_cases {lr : Rule (Alpha tm.State Symbol)}
    (h : lr ∈ tmRules tm) :
    (∃ q a T, T ∈ transitionTilesFor tm.toSingleTapeTM q a ∧ lr = tileRule T) ∨ h⊥ ∈ lr.lhs := by
  simp only [tmRules, List.mem_append, List.mem_map, List.mem_singleton] at h
  rcases h with (⟨T, hT, rfl⟩ | ⟨T, hT, rfl⟩) | rfl
  · obtain ⟨q, a, hT⟩ := (MPCP.Reduction.mem_transitionTiles tm T).1 hT
    exact Or.inl ⟨q, a, T, hT, rfl⟩
  · right
    obtain ⟨a, -, hT⟩ := List.mem_flatMap.1 hT
    simp only [absorbTilesFor, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl <;> simp [tileRule, absorbLeftTile, absorbRightTile]
  · simp

/-- The top of every transition tile is a window `pre ++ [↟ₛq, ↟ₜa] ++ post`. -/
theorem top_window {q : tm.State} {a : Option Symbol} {T : Tile (Alpha tm.State Symbol)}
    (hT : T ∈ transitionTilesFor tm.toSingleTapeTM q a) :
    ∃ pre post, T.top = pre ++ ↟ₛq :: ↟ₜa :: post := by
  unfold transitionTilesFor at hT
  split at hT
  · obtain rfl := List.mem_singleton.1 hT
    exact ⟨[], [], rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact ⟨[], [], rfl⟩
    · exact ⟨[], [#], rfl⟩
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hT
    exact ⟨[↟ₜb], [], rfl⟩

/-- Every rule has a non-empty left side. -/
theorem tmRules_lhs_ne : ∀ lr ∈ tmRules tm, lr.lhs ≠ [] := by
  intro lr hlr
  rcases mem_tmRules_cases hlr with ⟨q, a, T, hT, rfl⟩ | hh
  · obtain ⟨pre, post, htop⟩ := top_window hT
    simp [tileRule, htop]
  · exact List.ne_nil_of_mem hh

/-! ### Stuck strings -/

/-- **A string whose running marker is followed by `#` is stuck**: no rule applies, so it never
rewrites to the empty string. -/
theorem not_derives_stuck {L : List (Alpha tm.State Symbol)} (hL : ∀ x ∈ L, isMark x = false)
    (q : tm.State) : ¬ L ++ [↟ₛq, #] ↠[tmRules tm] [] := by
  intro h
  rcases h.cases_head with heq | ⟨s₁, hs, -⟩
  · simp at heq
  · obtain ⟨lr, hlr, p, r, hb, -⟩ := SRS.step_iff.1 hs
    rcases mem_tmRules_cases hlr with ⟨q₀, a₀, T, hT, rfl⟩ | hh
    · obtain ⟨pre, post, htop⟩ := top_window hT
      simp only [tileRule, htop] at hb
      have := split_mark (xs := p ++ pre) (ys := ↟ₜa₀ :: post ++ r) (m := ↟ₛq₀)
        (xs' := L) (m' := ↟ₛq) (ys' := [#]) rfl hL (by simp [isMark])
        (by simpa [List.append_assoc] using hb.symm)
      simp at this
    · have : h⊥ ∈ L ++ [↟ₛq, #] := hb ▸ List.mem_append_left _ (List.mem_append_right _ hh)
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at this
      have := hL _ this
      simp [isMark] at this

/-! ### One step -/

omit [Encodable Symbol] in
/-- The configuration after a no-move step. -/
theorem encodeCfg_after_no_move (qNew : Option tm.State) (t : BiTape Symbol) (w : Option Symbol) :
    encodeCfg tm.toSingleTapeTM ⟨qNew, t.write w⟩ =
      liftTape tm.toSingleTapeTM t.left.toList.reverse ++
        [stateMarker tm.toSingleTapeTM qNew, ↟ₜw] ++ liftTape tm.toSingleTapeTM t.right.toList := by
  cases qNew <;> simp [encodeCfg, encodeHaltedCfg, encodeRunningCfg, BiTape.write, liftTape,
    stateMarker]

/-- **Every step of the machine is one rewrite**, for a machine that never writes a blank, unless
it moves left at the left end. -/
theorem step_block (h_nbw : NoBlankWrites tm.toSingleTapeTM) (q : tm.State) (t : BiTape Symbol)
    (hl : (tm.tr q t.head).1.movement = some Turing.Dir.left → t.left.toList ≠ []) :
    block tm.toSingleTapeTM ⟨some q, t⟩ ⭢[tmRules tm]
      block tm.toSingleTapeTM (stepResult tm.toSingleTapeTM q t) := by
  rcases h : tm.tr q t.head with ⟨⟨w, mov⟩, n⟩
  have hw : w ≠ none := by simpa [h] using h_nbw q t.head
  have hres : stepResult tm.toSingleTapeTM q t = ⟨n, (t.write w).optionMove mov⟩ := by
    simp [stepResult, h]
  rw [hres, block_running]
  rcases mov with _ | _ | _
  · refine SRS.step_iff.2 ⟨_, tileRule_mem (q := q) (a := t.head) (T := noMoveTile _ q t.head n w)
      (by simp [transitionTilesFor, h]), # :: liftTape _ t.left.toList.reverse,
      liftTape _ t.right.toList ++ [#], by simp [tileRule, noMoveTile], ?_⟩
    simp [block, BiTape.optionMove, encodeCfg_after_no_move, tileRule, noMoveTile]
  · have hne := hl (by simp [h])
    have hL : t.left.toList = t.left.head :: t.left.tail.toList :=
      (head_cons_tail_toList _ hne).symm
    refine SRS.step_iff.2 ⟨_, tileRule_mem (q := q) (a := t.head)
      (T := leftMoveTile _ q t.head n w t.left.head)
      (by simp [transitionTilesFor, h]),
      # :: liftTape _ t.left.tail.toList.reverse, liftTape _ t.right.toList ++ [#], ?_, ?_⟩
    · rw [hL]; simp [tileRule, leftMoveTile, liftTape]
    · simp [block, BiTape.optionMove, BiTape.move,
        encodeCfg_after_left_move_eq _ _ _ _ (Or.inl hw), tileRule,
        leftMoveTile]
  · cases hr : t.right.toList with
    | nil =>
      refine SRS.step_iff.2 ⟨_, tileRule_mem (q := q) (a := t.head)
        (T := rightMoveBoundaryTile _ q t.head n w) (by simp [transitionTilesFor, h]),
        # :: liftTape _ t.left.toList.reverse, [], by simp [tileRule, rightMoveBoundaryTile], ?_⟩
      simp [block, BiTape.optionMove, BiTape.move,
        encodeCfg_after_right_move_boundary_eq _ _ _ _ (Or.inl hw) hr,
        tileRule, rightMoveBoundaryTile]
    | cons x xs =>
      refine SRS.step_iff.2 ⟨_, tileRule_mem (q := q) (a := t.head)
        (T := rightMoveTile _ q t.head n w) (by simp [transitionTilesFor, h]),
        # :: liftTape _ t.left.toList.reverse, liftTape _ (x :: xs) ++ [#],
        by simp [tileRule, rightMoveTile], ?_⟩
      simp only [block, BiTape.optionMove, BiTape.move]
      rw [encodeCfg_after_right_move_eq _ n t w (Or.inl hw)
        (by rw [hr]; exact List.cons_ne_nil _ _)]
      simp [hr, tileRule, rightMoveTile, liftTape]

/-- **A rewrite of a running configuration is the machine's step**, or the step halts, or the
result is stuck. -/
theorem step_inv (h_nbw : NoBlankWrites tm.toSingleTapeTM) {q : tm.State} {t : BiTape Symbol}
    {s' : List (Alpha tm.State Symbol)}
    (hs : block tm.toSingleTapeTM ⟨some q, t⟩ ⭢[tmRules tm] s') :
    s' = block tm.toSingleTapeTM (stepResult tm.toSingleTapeTM q t) ∨
      (stepResult tm.toSingleTapeTM q t).state = none ∨ ¬ s' ↠[tmRules tm] [] := by
  obtain ⟨lr, hlr, p, r, hb, rfl⟩ := SRS.step_iff.1 hs
  rw [block_running] at hb
  have hxs : ∀ x ∈ # :: liftTape tm.toSingleTapeTM t.left.toList.reverse, isMark x = false := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · rfl
    · exact isMark_liftTape _ _ x hx
  have hys : ∀ x ∈ ↟ₜt.head :: (liftTape tm.toSingleTapeTM t.right.toList ++ [#]),
      isMark x = false := by
    intro x hx
    simp only [List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · rfl
    · exact isMark_liftTape _ _ x hx
    · simp only [List.not_mem_nil, or_false] at hx
      subst hx; rfl
  rcases mem_tmRules_cases hlr with ⟨q₀, a₀, T, hT, rfl⟩ | hh
  swap
  · have : h⊥ ∈ block tm.toSingleTapeTM ⟨some q, t⟩ := by
      rw [block_running, hb]
      exact List.mem_append_left _ (List.mem_append_right _ hh)
    exact absurd this (halt_not_mem_block_running _ q t)
  rcases h₀ : tm.tr q₀ a₀ with ⟨⟨w, mov⟩, n⟩
  have hw : w ≠ none := by simpa [h₀] using h_nbw q₀ a₀
  unfold transitionTilesFor at hT
  rw [h₀] at hT
  -- the window of a rule whose top is `pre ++ [↟ₛq₀, ↟ₜa₀] ++ post`
  have win : ∀ pre post, (tileRule T).lhs = pre ++ ↟ₛq₀ :: ↟ₜa₀ :: post →
      p ++ pre = # :: liftTape tm.toSingleTapeTM t.left.toList.reverse ∧ q₀ = q ∧ a₀ = t.head ∧
        post ++ r = liftTape tm.toSingleTapeTM t.right.toList ++ [#] := by
    intro pre post htop
    rw [htop] at hb
    obtain ⟨h1, h2, h3⟩ := split_mark (xs := p ++ pre) (ys := ↟ₜa₀ :: (post ++ r)) rfl hxs hys
      (by simpa [List.append_assoc] using hb.symm)
    simp only [Alpha.state.injEq] at h2
    simp only [List.cons.injEq, Alpha.tape.injEq] at h3
    exact ⟨h1, h2, h3.1, h3.2⟩
  have hres : ∀ {q₀'}, q₀ = q₀' → ∀ {a₀'}, a₀ = a₀' → tm.tr q₀' a₀' = (⟨w, mov⟩, n) := by
    rintro _ rfl _ rfl; exact h₀
  rcases mov with _ | _ | _
  · -- no move
    obtain rfl := List.mem_singleton.1 hT
    obtain ⟨hp, rfl, rfl, hr⟩ := win [] [] rfl
    left
    simp only [List.append_nil] at hp hr
    simp [stepResult, h₀, block, BiTape.optionMove, encodeCfg_after_no_move, hp, hr.symm,
      tileRule, noMoveTile]
  · -- left move
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hT
    obtain ⟨hp, rfl, rfl, hr⟩ := win [↟ₜb] [] rfl
    simp only [List.nil_append] at hr
    left
    have hne : t.left.toList ≠ [] := by
      intro he
      simp only [he, List.reverse_nil, liftTape_nil] at hp
      have := congrArg List.getLast? hp
      simp at this
    have hL : t.left.toList = t.left.head :: t.left.tail.toList :=
      (head_cons_tail_toList _ hne).symm
    rw [hL] at hp
    simp only [List.reverse_cons, liftTape_append, liftTape_cons, liftTape_nil, ← List.cons_append]
      at hp
    obtain ⟨hp2, hb'⟩ := List.append_inj' hp rfl
    simp only [List.cons.injEq, Alpha.tape.injEq, and_true] at hb'
    subst hb' hp2
    simp [stepResult, h₀, block, BiTape.optionMove, BiTape.move,
      encodeCfg_after_left_move_eq _ _ _ _ (Or.inl hw), hr.symm, tileRule, leftMoveTile]
  · -- right move
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · obtain ⟨hp, rfl, rfl, hr⟩ := win [] [] rfl
      simp only [List.append_nil, List.nil_append] at hp hr
      cases hrt : t.right.toList with
      | cons x xs =>
        left
        simp only [stepResult, h₀, block, BiTape.optionMove, BiTape.move]
        rw [encodeCfg_after_right_move_eq _ n t w (Or.inl hw)
          (by rw [hrt]; exact List.cons_ne_nil _ _)]
        simp [hp, hr, hrt, tileRule, rightMoveTile, liftTape]
      | nil =>
        rw [hrt] at hr
        simp only [liftTape_nil, List.nil_append] at hr
        subst hr
        cases n with
        | none => right; left; simp [stepResult, h₀]
        | some q' =>
          right; right
          have := not_derives_stuck (tm := tm)
            (L := # :: liftTape tm.toSingleTapeTM t.left.toList.reverse ++ [↟ₜw])
            (fun x hx => by
              rcases List.mem_append.1 hx with hx | hx
              · exact hxs x hx
              · rw [List.mem_singleton.1 hx]; rfl) q'
          simpa [hp, tileRule, rightMoveTile, List.append_assoc] using this
    · obtain ⟨hp, rfl, rfl, hr⟩ := win [] [#] rfl
      simp only [List.append_nil] at hp
      have hrt : t.right.toList = [] := by
        cases hrt : t.right.toList with
        | nil => rfl
        | cons x xs => simp [hrt, liftTape] at hr
      rw [hrt] at hr
      simp only [liftTape_nil, List.nil_append, List.cons_append, List.cons.injEq, true_and] at hr
      left
      simp [stepResult, h₀, block, BiTape.optionMove, BiTape.move,
        encodeCfg_after_right_move_boundary_eq _ _ _ _ (Or.inl hw) hrt, hp, hr, tileRule,
        rightMoveBoundaryTile]

/-! ### Erasing a halted configuration -/

/-- The halting marker swallows the tape on its left, up to `#`. -/
theorem derives_absorb_left (l : List (Option Symbol)) (rest : List (Alpha tm.State Symbol)) :
    # :: liftTape tm.toSingleTapeTM l ++ h⊥ :: rest ↠[tmRules tm] # :: h⊥ :: rest := by
  induction l using List.reverseRecOn with
  | nil => exact .refl
  | append_singleton l a ih =>
    refine Relation.ReflTransGen.head ?_ ih
    exact SRS.step_iff.2 ⟨_, absorbLeft_mem a, # :: liftTape tm.toSingleTapeTM l, rest,
      by simp [liftTape], by simp⟩

/-- The halting marker swallows the tape on its right, up to `#`. -/
theorem derives_absorb_right (pre : List (Alpha tm.State Symbol)) (r : List (Option Symbol)) :
    pre ++ h⊥ :: liftTape tm.toSingleTapeTM r ++ [#] ↠[tmRules tm] pre ++ [h⊥, #] := by
  induction r with
  | nil => simpa [liftTape] using (Relation.ReflTransGen.refl :
      pre ++ [h⊥, #] ↠[tmRules tm] pre ++ [h⊥, #])
  | cons a r ih =>
    refine Relation.ReflTransGen.head ?_ ih
    exact SRS.step_iff.2 ⟨_, absorbRight_mem a, pre, liftTape tm.toSingleTapeTM r ++ [#],
      by simp [liftTape], by simp⟩

/-- A halted configuration rewrites to the empty string. -/
theorem derives_halted (t : BiTape Symbol) :
    block tm.toSingleTapeTM ⟨none, t⟩ ↠[tmRules tm] [] := by
  have h₁ := derives_absorb_left (tm := tm) t.left.toList.reverse
    (liftTape tm.toSingleTapeTM (t.head :: t.right.toList) ++ [#])
  have h₂ := derives_absorb_right (tm := tm) [#] (t.head :: t.right.toList)
  have h₃ : [#, h⊥, #] ↠[tmRules tm] [] :=
    .single (SRS.step_iff.2 ⟨_, final_mem, [], [], by simp, by simp⟩)
  have e : block tm.toSingleTapeTM ⟨none, t⟩ =
      # :: liftTape tm.toSingleTapeTM t.left.toList.reverse ++ h⊥ ::
        (liftTape tm.toSingleTapeTM (t.head :: t.right.toList) ++ [#]) := by
    simp [block, encodeCfg, encodeHaltedCfg]
  rw [e]
  exact h₁.trans (by simpa using h₂.trans h₃)

/-! ### The equivalence -/

/-- **If the machine halts, its initial configuration string rewrites to the empty string.** -/
theorem derives_of_halts (h_nbw : NoBlankWrites tm.toSingleTapeTM) (w : List Symbol)
    (h_nlb : NoLeftBoundary tm.toSingleTapeTM w) (h : Halts tm.toSingleTapeTM w) :
    block tm.toSingleTapeTM (initCfg tm.toSingleTapeTM w) ↠[tmRules tm] [] := by
  obtain ⟨tape, htr⟩ := h
  have reach : ∀ c, ReflTransGen tm.toSingleTapeTM.TransitionRelation
      (initCfg tm.toSingleTapeTM w) c →
      block tm.toSingleTapeTM (initCfg tm.toSingleTapeTM w) ↠[tmRules tm]
        block tm.toSingleTapeTM c := by
    intro c hc
    induction hc with
    | refl => exact .refl
    | tail hreach hstep ih =>
      rename_i c c'
      obtain ⟨st, tp⟩ := c
      cases st with
      | none => simp [SingleTapeTM.TransitionRelation, SingleTapeTM.step] at hstep
      | some q =>
        have hc' : c' = stepResult tm.toSingleTapeTM q tp :=
          Option.some.inj (hstep.symm.trans (tm_step_running _ q tp).symm)
        subst hc'
        refine ih.tail (step_block h_nbw q tp fun hmov hleft => ?_)
        exact h_nlb _ hreach q tp rfl hleft hmov
  exact (reach _ htr).trans (derives_halted tape)

/-- **If the initial configuration string rewrites to the empty string, the machine halts.** -/
theorem halts_of_derives (h_nbw : NoBlankWrites tm.toSingleTapeTM) (w : List Symbol)
    (h : block tm.toSingleTapeTM (initCfg tm.toSingleTapeTM w) ↠[tmRules tm] []) :
    Halts tm.toSingleTapeTM w := by
  suffices key : ∀ s, s ↠[tmRules tm] [] → ∀ c,
      ReflTransGen tm.toSingleTapeTM.TransitionRelation (initCfg tm.toSingleTapeTM w) c →
      s = block tm.toSingleTapeTM c → Halts tm.toSingleTapeTM w from
    key _ h _ .refl rfl
  intro s hs
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro c _ hc
    simp [block] at hc
  | head hstep hrest ih =>
    intro c hc hsc
    obtain ⟨st, tp⟩ := c
    cases st with
    | none => exact ⟨tp, hc⟩
    | some q =>
      subst hsc
      have hT : tm.toSingleTapeTM.TransitionRelation ⟨some q, tp⟩
          (stepResult tm.toSingleTapeTM q tp) := (tm_step_running _ q tp).symm
      rcases step_inv h_nbw hstep with heq | hnone | hstuck
      · exact ih _ (hc.tail hT) heq
      · have e : stepResult tm.toSingleTapeTM q tp =
            ⟨none, (stepResult tm.toSingleTapeTM q tp).BiTape⟩ := by rw [← hnone]
        exact ⟨_, e ▸ hc.tail hT⟩
      · exact absurd hrest hstuck

/-- **A machine halts iff its initial configuration string rewrites to the empty string**, for a
machine that never writes a blank and never moves left at the left end on this input. -/
theorem halt_iff_derives (h_nbw : NoBlankWrites tm.toSingleTapeTM) (w : List Symbol)
    (h_nlb : NoLeftBoundary tm.toSingleTapeTM w) :
    Halts tm.toSingleTapeTM w ↔
      block tm.toSingleTapeTM (initCfg tm.toSingleTapeTM w) ↠[tmRules tm] [] :=
  ⟨derives_of_halts h_nbw w h_nlb, halts_of_derives h_nbw w⟩

/-! ### The reduction -/

section Reduction

/-- **The reduction.** The rewriting system of the normalised machine and its start string, with
states renamed to their codes, and the empty string as target. -/
def haltToSemiThue (p : EncodableTM Bool × List Bool) :
    SRS (Alpha ℕ Sym2) × List (Alpha ℕ Sym2) ×
      List (Alpha ℕ Sym2) :=
  letI := (normEnc p.1).stateEncodable
  ((tmRules (normEnc p.1)).mapRules (Alpha.map Encodable.encode),
    (block (normEnc p.1).toSingleTapeTM
      (initCfg (normEnc p.1).toSingleTapeTM (encInput p.2))).map (Alpha.map Encodable.encode),
    [])

/-- `haltToSemiThue` witnesses the reduction from the halting problem to the word problem. -/
theorem halt_reducesto_semiThue_spec : HaltProblem ⪯_s[haltToSemiThue] DecisionProblem := by
  rintro ⟨M, w⟩
  show Halts M.toSingleTapeTM w ↔ _
  let := (normEnc M).stateEncodable
  rw [halts_normTM_iff,
    halt_iff_derives (tm := normEnc M) (normTM_noBlankWrites _) _ (normTM_noLeftBoundary _ _),
    ← Foundations.Codes.derives_mapRules_iff (Alpha.map_injective Encodable.encode_injective)
      tmRules_lhs_ne]
  rfl

/-- Every rule of a system produced by the reduction has a non-empty left side. -/
theorem haltToSemiThue_lhs_ne (p : EncodableTM Bool × List Bool) :
    ∀ lr ∈ (haltToSemiThue p).1, lr.lhs ≠ [] := by
  intro lr hlr
  obtain ⟨lr₀, hlr₀, rfl⟩ := List.mem_map.1 hlr
  simpa using tmRules_lhs_ne lr₀ hlr₀

/-- `haltToSemiThue` witnesses the reduction from the halting problem to the word problem for
systems with non-empty left sides. -/
theorem halt_reducesto_semiThuePos_spec :
    HaltProblem ⪯_s[haltToSemiThue] DecisionProblemPos := fun p =>
  (halt_reducesto_semiThue_spec p).trans (and_iff_right (haltToSemiThue_lhs_ne p)).symm

end Reduction

end DiagonaLean.SemiThue.Reduction
