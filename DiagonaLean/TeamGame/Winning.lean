/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.TeamGame.Correctness

@[expose] public section

/-! # Who wins the game of a list machine

The team wins the reachability variant of the game of a list machine iff the machine halts
(`winReach_iff_halts`), and the safety variant iff it does not halt (`winSafety_iff_not_halts`).

When the machine halts, or does not, the players output the rows of the tableau after a trigger
(`stratOut`, `stratStop`), and every check passes (`check_passes`). In the reachability variant
player 0 stops the waiting one round after the first row with a halting head. Conversely, safe
winning strategies output the rows of the tableau (`rows_of_safe`), so in the reachability variant
the stop check finds a halting head, and in the safety variant no row has one.

## Main statements

* `winReach_iff_halts`, `winSafety_iff_not_halts`: the team wins the reachability variant iff the
  machine halts, and the safety variant iff it does not.
-/

namespace DiagonaLean.TeamGame

open DiagonaLean.Foundations.Computability.ListMachine

variable {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]

/-! ### Plays never return to the start -/

section Start

variable (δ : Q → Γ → Act Q Γ) (bl : Γ) (c₀ : List (Cell Q Γ)) (var : Variant)

/-- A check never moves to the start. -/
theorem chk_ne_start (p : Pos Q Γ) (a₀ a₁ : Move Q Γ) : chk δ bl c₀ p a₀ a₁ ≠ .start := by
  unfold chk
  split <;> (try split_ifs) <;> simp

/-- The start is no successor. -/
theorem start_not_mem_succs (p : Pos Q Γ) (a₀ a₁ : Move Q Γ) :
    (.start : Pos Q Γ) ∉ succs δ bl c₀ var p a₀ a₁ := by
  unfold succs
  split_ifs with h₁ h₂ h₃ h₄
  · rintro hp
    rw [List.mem_singleton] at hp
    rw [← hp] at h₁
    simp [isSink] at h₁
  · simp
  · simp
  · rcases p with _ | b <;> simp [natureMoves]
    cases b <;> simp
  · simpa using (chk_ne_start δ bl c₀ p a₀ a₁).symm

/-- A play is at the start only at round 0. -/
theorem play_ne_start {σ₀ σ₁ : List Bool → Move Q Γ} {f : ℕ → Pos Q Γ}
    (hf : IsPlayA δ bl c₀ var σ₀ σ₁ f) (k : ℕ) : f (k + 1) ≠ .start := fun h =>
  start_not_mem_succs δ bl c₀ var _ _ _ (h ▸ hf.2 k)

omit [DecidableEq Q] [DecidableEq Γ] in
/-- A waiting position is no sink. -/
theorem isSink_of_isWaiting {p : Pos Q Γ} (hp : isWaiting p = true) : isSink p = false := by
  rcases p <;> simp_all [isWaiting, isSink]

omit [DecidableEq Q] [DecidableEq Γ] in
/-- The histories of a play that has waited until round `k` see no trigger. -/
theorem hist_waiting {f : ℕ → Pos Q Γ} {k : ℕ} (hw : ∀ i ≤ k, isWaiting (f i) = true) :
    hist₀ f k = List.replicate (k + 1) false ∧ hist₁ f k = List.replicate (k + 1) false :=
  ⟨range_map_eq_replicate fun i hi => by rw [observe_waiting (hw i hi)],
    range_map_eq_replicate fun i hi => by rw [observe_waiting (hw i hi)]⟩

end Start

/-! ### Strategies that output the tableau -/

section Strategies

variable (δ : Q → Γ → Act Q Γ) (bl : Γ) (k₀ : Cfg Q Γ)

/-- The strategy of player 1: after a trigger at round `m`, output row `m - 1` of the tableau. -/
def stratOut (h : List Bool) : Move Q Γ :=
  match decodeTrig h with
  | some (m, j) => rowMove (rowWord δ bl k₀ (m - 1)) j
  | none => .idle

/-- The strategy of player 0: as player 1, and `stop` at round `n` when `stopAt = some n`. -/
def stratStop (stopAt : Option ℕ) (h : List Bool) : Move Q Γ :=
  match decodeTrig h with
  | some (m, j) => rowMove (rowWord δ bl k₀ (m - 1)) j
  | none => if stopAt.map (fun n => List.replicate (n + 1) false) = some h then .stop else .idle

omit [DecidableEq Q] [DecidableEq Γ] in
/-- After a trigger at round `m`, player 1 outputs row `m - 1`. -/
@[simp]
theorem stratOut_trig (m j : ℕ) :
    stratOut δ bl k₀ (trig m j) = rowMove (rowWord δ bl k₀ (m - 1)) j := by
  simp [stratOut, decodeTrig_trig]

omit [DecidableEq Q] [DecidableEq Γ] in
/-- After a trigger at round `m`, player 0 outputs row `m - 1`. -/
@[simp]
theorem stratStop_trig (stopAt : Option ℕ) (m j : ℕ) :
    stratStop δ bl k₀ stopAt (trig m j) = rowMove (rowWord δ bl k₀ (m - 1)) j := by
  simp [stratStop, decodeTrig_trig]

omit [DecidableEq Q] [DecidableEq Γ] in
/-- Before a trigger, player 1 does nothing. -/
@[simp]
theorem stratOut_replicate (k : ℕ) : stratOut δ bl k₀ (List.replicate k false) = .idle := by
  simp [stratOut, decodeTrig_replicate]

omit [DecidableEq Q] [DecidableEq Γ] in
/-- Before a trigger, player 0 stops at round `n` when `stopAt = some n`, and does nothing
otherwise. -/
theorem stratStop_replicate (stopAt : Option ℕ) (k : ℕ) :
    stratStop δ bl k₀ stopAt (List.replicate k false) =
      if stopAt.map (· + 1) = some k then .stop else .idle := by
  simp only [stratStop, decodeTrig_replicate]
  rcases stopAt with _ | n
  · rfl
  · simp [List.replicate_inj, eq_comm]

omit [DecidableEq Q] [DecidableEq Γ] in
/-- When no row has a halting head, the strategies never output one. -/
theorem haltMove_strat (hno : ∀ t, hasHalt δ (rowWord δ bl k₀ t) = false) (h : List Bool)
    (stopAt : Option ℕ) :
    haltMove δ (stratStop δ bl k₀ stopAt h) = false ∧ haltMove δ (stratOut δ bl k₀ h) = false := by
  constructor
  · unfold stratStop
    split
    · exact haltMove_rowMove δ (hno _) _
    · split_ifs <;> rfl
  · unfold stratOut
    split
    · exact haltMove_rowMove δ (hno _) _
    · rfl

end Strategies

/-! ### Every check passes -/

section Passes

variable {δ : Q → Γ → Act Q Γ} {bl : Γ} {k₀ : Cfg Q Γ} {var : Variant} {stopAt : Option ℕ}
  {f : ℕ → Pos Q Γ}

/-- The conditions on the stop round: none in the safety variant, where no row has a halting
head; and in the reachability variant a stop round `n ≥ 1` whose row has a halting head. -/
def StopOK (δ : Q → Γ → Act Q Γ) (bl : Γ) (k₀ : Cfg Q Γ) (var : Variant) (stopAt : Option ℕ) :
    Prop :=
  (var = .safety → stopAt = none ∧ ∀ t, hasHalt δ (rowWord δ bl k₀ t) = false) ∧
    ∀ n, stopAt = some n → 1 ≤ n ∧ hasHalt δ (rowWord δ bl k₀ n) = true

omit [DecidableEq Q] [DecidableEq Γ] in
/-- Under `StopOK`, the moves of the strategies satisfy the no-halting condition. -/
theorem noHalt_strat (hok : StopOK δ bl k₀ var stopAt) (h h' : List Bool) :
    NoHalt δ var (stratStop δ bl k₀ stopAt h) (stratOut δ bl k₀ h') := fun hv =>
  ⟨(haltMove_strat δ bl k₀ ((hok.1 hv).2) h stopAt).1,
    (haltMove_strat δ bl k₀ ((hok.1 hv).2) h' stopAt).2⟩

omit [DecidableEq Q] [DecidableEq Γ] in
/-- A play that has waited before round `m` sees no trigger before `m`. -/
theorem observe_pre {m : ℕ} (hpre : ∀ i < m, isWaiting (f i) = true) :
    ∀ i < m, observe (f i) = (false, false) := fun i hi => observe_waiting (hpre i hi)

/-- **The Eq check passes** when the players output the rows of the tableau, and the row has a
halting head in stop mode. -/
theorem pass_eq (hok : StopOK δ bl k₀ var stopAt)
    (hf : IsPlayA δ bl (cells k₀) var (stratStop δ bl k₀ stopAt) (stratOut δ bl k₀) f) {m : ℕ}
    {s : Bool} (hfm : f m = .eq true s false) (hpre : ∀ i < m, isWaiting (f i) = true)
    (hs : s = true → hasHalt δ (rowWord δ bl k₀ (m - 1)) = true) : ∃ L, f (m + L) = .ok := by
  have hm : isWaiting (f m) = false := by rw [hfm]; rfl
  have hob := observe_pre hpre
  have h₀ := hist₀_trig hf (fun i hi => by rw [hob i hi]) hm (by rw [hfm]; rfl)
  have h₁ := hist₁_trig hf (fun i hi => by rw [hob i hi]) hm (by rw [hfm]; rfl)
  set w := rowWord δ bl k₀ (m - 1)
  have hA₀ : (fun i => stratStop δ bl k₀ stopAt (hist₀ f (m + i))) = rowMove w :=
    funext fun i => by rw [h₀, stratStop_trig]
  have hA₁ : (fun i => stratOut δ bl k₀ (hist₁ f (m + i))) = rowMove w :=
    funext fun i => by rw [h₁, stratOut_trig]
  refine ⟨w.length + 1, ?_⟩
  rw [play_eq_chkRun hf hm, hfm, hA₀, hA₁]
  exact chkRun_eq_ok δ bl _ var (fun hv => (hok.1 hv).2 _) hs

/-- **The Init check passes** when player 1 outputs the initial row. -/
theorem pass_init (hok : StopOK δ bl k₀ var stopAt)
    (hf : IsPlayA δ bl (cells k₀) var (stratStop δ bl k₀ stopAt) (stratOut δ bl k₀) f)
    (hf1 : f 1 = .init 0 true) : ∃ L, f (1 + L) = .ok := by
  have hm : isWaiting (f 1) = false := by rw [hf1]; rfl
  have h₁ := hist₁_trig hf (fun i hi => by
    rw [show i = 0 by omega, hf.1]; rfl) hm (by rw [hf1]; rfl)
  have hA₁ : (fun i => stratOut δ bl k₀ (hist₁ f (1 + i))) = rowMove (cells k₀) :=
    funext fun i => by rw [h₁, stratOut_trig, Nat.sub_self, rowWord_zero]
  refine ⟨(cells k₀).length + 1, ?_⟩
  rw [play_eq_chkRun hf hm, hf1, hA₁]
  refine chkRun_init_ok δ bl _ var fun j _ hv => ?_
  have := noHalt_strat hok (hist₀ f (1 + j)) (trig 1 j) hv
  rw [stratOut_trig, Nat.sub_self, rowWord_zero] at this
  exact this

/-- **The Succ check passes** when player 0 outputs a row of the tableau and player 1, one round
later, the next row. -/
theorem pass_succ (hok : StopOK δ bl k₀ var stopAt)
    (hf : IsPlayA δ bl (cells k₀) var (stratStop δ bl k₀ stopAt) (stratOut δ bl k₀) f) {m : ℕ}
    (hm1 : 1 ≤ m) (hfm : f m = .succ₀) (hpre : ∀ i < m, isWaiting (f i) = true) :
    ∃ L, f (m + L) = .ok := by
  have hm : isWaiting (f m) = false := by rw [hfm]; rfl
  have hob := observe_pre hpre
  have h₀ := hist₀_trig hf (fun i hi => by rw [hob i hi]) hm (by rw [hfm]; rfl)
  set u := rowWord δ bl k₀ (m - 1)
  have hA₀ : (fun i => stratStop δ bl k₀ stopAt (hist₀ f (m + i))) = rowMove u :=
    funext fun i => by rw [h₀, stratStop_trig]
  set A₁ := fun i => stratOut δ bl k₀ (hist₁ f (m + i)) with hA₁def
  have hm' : isWaiting (f (m + 1)) = false := by
    rw [play_eq_chkRun hf hm 1]
    exact isWaiting_stepC δ bl _ var _ _ hm
  have hf1 : f (m + 1) = chk δ bl (cells k₀) .succ₀ (rowMove u 0) (A₁ 0) := by
    rw [play_eq_chkRun hf hm 1, hfm, hA₀]
    have hn := noHalt_strat hok (trig m 0) (hist₁ f (m + 0))
    rw [stratStop_trig] at hn
    simp only [chkRun, stepC, isSink, Bool.false_eq_true, ↓reduceIte]
    rcases hv : var with _ | _
    · obtain ⟨h1, h2⟩ := hn hv
      simp only [Nat.add_zero] at h2
      simp [A₁, u, h1, h2]
    · rfl
  have h₁ : ∀ j, hist₁ f (m + 1 + j) = trig (m + 1) j := by
    refine hist₁_trig hf (fun i hi => ?_) hm' ?_
    · rcases Nat.lt_or_ge i m with him | him
      · rw [hob i him]
      · rw [show i = m by omega, hfm]; rfl
    · rw [hf1]
      refine observe_chk_succ₀ ?_
      unfold rowMove
      split_ifs
      · simp [chk]
      · simp [chk]
      · omega
  have hA : ∀ j, A₁ (j + 1) = rowMove (succWord δ bl u) j := fun j => by
    simp only [A₁, show m + (j + 1) = m + 1 + j by omega, h₁, stratOut_trig,
      Nat.add_sub_cancel, u, succWord_rowWord, Nat.sub_add_cancel hm1]
  refine ⟨u.length + 3, ?_⟩
  rw [play_eq_chkRun hf hm, hfm, hA₀]
  refine chkRun_succ_ok δ bl _ var hA fun t hv => ?_
  have := noHalt_strat hok (trig m t) (hist₁ f (m + t)) hv
  rw [stratStop_trig] at this
  exact this

/-- **Every check passes**: from the first position of a play that is not waiting, the play
reaches `ok`. -/
theorem check_passes (hok : StopOK δ bl k₀ var stopAt)
    (hf : IsPlayA δ bl (cells k₀) var (stratStop δ bl k₀ stopAt) (stratOut δ bl k₀) f) {m : ℕ}
    (hm : isWaiting (f m) = false) (hpre : ∀ i < m, isWaiting (f i) = true) :
    ∃ L, f (m + L) = .ok := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := by
    rcases m with _ | m
    · rw [hf.1] at hm; exact absurd hm (by simp [isWaiting])
    · exact ⟨m, rfl⟩
  have hw : ∀ i ≤ m, isWaiting (f i) = true := fun i hi => hpre i (by omega)
  obtain ⟨h₀, h₁⟩ := hist_waiting hw
  have hstep := hf.2 m
  rw [h₀, h₁, stratOut_replicate, stratStop_replicate] at hstep
  have hwm := hw m le_rfl
  have hns := isSink_of_isWaiting hwm
  by_cases hst : stopAt.map (· + 1) = some (m + 1)
  · -- player 0 stops: the stop check
    have hn : stopAt = some m := by
      rcases stopAt with _ | n
      · simp at hst
      · simp only [Option.map_some, Option.some.injEq] at hst
        rw [show n = m by omega]
    obtain ⟨hn1, hhalt⟩ := hok.2 m hn
    have hv : var = .reach := by
      rcases hv : var
      · simp [(hok.1 hv).1] at hn
      · rfl
    have hne : f m ≠ .start := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact play_ne_start δ bl _ var hf k
    rw [ite_eq_left hst] at hstep
    unfold succs at hstep
    simp [hns, hv, hwm, hne, haltMove] at hstep
    exact pass_eq hok hf hstep hpre fun _ => by simpa using hhalt
  · rw [ite_eq_right hst] at hstep
    have hmem : f (m + 1) ∈ natureMoves (f m) := by
      unfold succs at hstep
      simpa [hns, hwm, haltMove] using hstep
    rcases hp : f m with _ | b | _ | _ | _ | _ | _ | _ | _ <;> rw [hp] at hmem hwm <;>
      simp [isWaiting] at hwm
    · -- Nature at the start
      obtain rfl : m = 0 := by
        rcases m with _ | m
        · rfl
        · exact absurd hp (play_ne_start δ bl _ var hf m)
      simp only [natureMoves, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h | h <;> rw [h] at hm
      · simp [isWaiting] at hm
      · simp [isWaiting] at hm
      · obtain ⟨L, hL⟩ := pass_init hok hf h
        exact ⟨L, by rw [Nat.zero_add]; exact hL⟩
      · exact pass_eq hok hf h hpre (by simp)
      · exact pass_succ hok hf le_rfl h hpre
    · -- Nature waiting
      cases b <;> simp only [natureMoves, List.mem_cons, List.not_mem_nil, or_false] at hmem <;>
        rcases hmem with h | h <;> rw [h] at hm
      · simp [isWaiting] at hm
      · exact pass_eq hok hf h hpre (by simp)
      · simp [isWaiting] at hm
      · exact pass_succ hok hf (by omega) h hpre

end Passes

/-! ### Safe strategies output the tableau -/

section Rows

variable {δ : Q → Γ → Act Q Γ} {bl : Γ} {k₀ : Cfg Q Γ} {c₀ : List (Cell Q Γ)} {var : Variant}
  {σ₀ σ₁ : List Bool → Move Q Γ}

/-- **Safe strategies output the tableau**: when plays are safe and the waiting moves are harmless
before round `M ≥ 1`, player 1 triggered at round `m ≤ M + 1` outputs row `m - 1`. -/
theorem rows_of_safe (hs : SafePlays δ bl (cells k₀) var σ₀ σ₁) {M : ℕ} (hM : 1 ≤ M)
    (hq : QuietBefore δ var σ₀ σ₁ M) {m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ M + 1) :
    ∀ j ≤ (rowWord δ bl k₀ (m - 1)).length,
      σ₁ (trig m j) = rowMove (rowWord δ bl k₀ (m - 1)) j := by
  induction m, hm1 using Nat.le_induction with
  | base =>
    rw [Nat.sub_self, rowWord_zero]
    exact claim_init hs (hq.mono hM)
  | succ m hm1 ih =>
    have hA₀ := (claim_eq hs hm1 (hq.mono (by omega)) (ih (by omega))).1
    have h := claim_succ hs hm1 (hq.mono (by omega)) hA₀
    rw [succWord_rowWord, Nat.sub_add_cancel hm1] at h
    intro j hj
    rw [Nat.add_sub_cancel] at hj ⊢
    exact h j (by simp only [length_rowWord] at hj ⊢; omega)

/-- In the safety variant, when plays are safe, no waiting move is a halting head. -/
theorem quiet_safety (hs : SafePlays δ bl c₀ .safety σ₀ σ₁) (M : ℕ) :
    QuietBefore δ .safety σ₀ σ₁ M := by
  induction M with
  | zero => intro k hk; omega
  | succ M ih =>
    intro k hk
    rcases Nat.lt_or_ge k M with h | h
    · exact ih k h
    obtain rfl : k = M := by omega
    refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
    by_contra hc
    have hor : (haltMove δ (σ₀ (List.replicate (k + 1) false)) ||
        haltMove δ (σ₁ (List.replicate (k + 1) false))) = true := by
      rcases h₀ : haltMove δ (σ₀ (List.replicate (k + 1) false)) <;>
        rcases h₁ : haltMove δ (σ₁ (List.replicate (k + 1) false)) <;> simp_all
    obtain ⟨-, h1⟩ := waitPol_play (δ := δ) (bl := bl) (c₀ := c₀) (var := .safety) (σ₀ := σ₀)
      (σ₁ := σ₁) (b := false) (m := k + 1) (p := .hlt) (by omega) (by simpa using ih) (by
        have hns : isSink (if k = 0 then (.start : Pos Q Γ) else .wait false) = false :=
          by split_ifs <;> rfl
        simp only [Nat.add_sub_cancel]
        unfold succs
        simp [hns, hor])
    exact (hs _ (buildPlay_isPlay δ bl c₀ .safety σ₀ σ₁ _) (k + 1)).2 h1

end Rows

/-! ### The main theorems -/

section Main

variable {δ : Q → Γ → Act Q Γ} {bl : Γ} {k₀ : Cfg Q Γ}

/-- If the team wins the reachability variant, the machine halts. -/
theorem halts_of_winReach (h : WinReach δ bl (cells k₀)) : Halts δ bl k₀ := by
  obtain ⟨σ₀, σ₁, hw⟩ := h
  have hs := safePlays_of_reach hw
  by_cases hex : ∃ n, 1 ≤ n ∧ σ₀ (List.replicate (n + 1) false) = .stop
  · classical
    obtain ⟨hn1, hstop⟩ := Nat.find_spec hex
    have hq : QuietBefore δ .reach σ₀ σ₁ (Nat.find hex) := fun k hk =>
      ⟨fun h => absurd h (by simp), fun _ hk1 hs' => Nat.find_min hex hk ⟨hk1, hs'⟩⟩
    have hrows := rows_of_safe (k₀ := k₀) hs hn1 hq (m := Nat.find hex + 1) (by omega) le_rfl
    simp only [Nat.add_sub_cancel] at hrows
    obtain ⟨j, hj⟩ := (hasHalt_rowWord δ bl k₀ _).1 (claim_stop hs hn1 hq hstop hrows)
    exact (halts_iff_tab (bl := bl)).2 ⟨_, j, hj⟩
  · push Not at hex
    have hq : ∀ m, QuietBefore δ .reach σ₀ σ₁ m := fun m k _ =>
      ⟨fun h => absurd h (by simp), fun _ hk1 => hex k hk1⟩
    obtain ⟨k, hk⟩ :=
      hw _ (buildPlay_isPlay δ bl (cells k₀) .reach σ₀ σ₁ (waitPol false 1 (.wait false)))
    rw [stay_play hq] at hk
    split_ifs at hk

/-- If the machine halts, the team wins the reachability variant. -/
theorem winReach_of_halts (h : Halts δ bl k₀) : WinReach δ bl (cells k₀) := by
  obtain ⟨t, j, hj⟩ := (halts_iff_tab (bl := bl)).1 h
  have hok : StopOK δ bl k₀ .reach (some (t + 1)) := ⟨fun h => absurd h (by simp), fun n hn => by
    simp only [Option.some.injEq] at hn
    subst hn
    exact ⟨by omega, (hasHalt_rowWord δ bl k₀ _).2 ⟨j, tab_halt_succ δ bl k₀ hj⟩⟩⟩
  refine ⟨stratStop δ bl k₀ (some (t + 1)), stratOut δ bl k₀, fun f hf => ?_⟩
  have hex : ∃ m, isWaiting (f m) = false := by
    by_contra hall
    push Not at hall
    have hw : ∀ i ≤ t + 1, isWaiting (f i) = true := fun i _ => by simpa using hall i
    obtain ⟨h₀, h₁⟩ := hist_waiting hw
    have hstep := hf.2 (t + 1)
    rw [h₀, h₁, stratOut_replicate, stratStop_replicate, ite_eq_left (by simp)] at hstep
    unfold succs at hstep
    simp [isSink_of_isWaiting (hw _ le_rfl), hw _ le_rfl, play_ne_start δ bl _ _ hf t,
      haltMove] at hstep
    have := hall (t + 2)
    rw [hstep] at this
    simp [isWaiting] at this
  classical
  obtain ⟨L, hL⟩ := check_passes hok hf (Nat.find_spec hex) fun i hi => by
    simpa using Nat.find_min hex hi
  exact ⟨_, hL⟩

/-- **The team wins the reachability variant iff the machine halts.** -/
theorem winReach_iff_halts : WinReach δ bl (cells k₀) ↔ Halts δ bl k₀ :=
  ⟨halts_of_winReach, winReach_of_halts⟩

/-- If the machine does not halt, the team wins the safety variant. -/
theorem winSafety_of_not_halts (h : ¬ Halts δ bl k₀) : WinSafety δ bl (cells k₀) := by
  have hno : ∀ t, hasHalt δ (rowWord δ bl k₀ t) = false := fun t => by
    by_contra hc
    obtain ⟨j, hj⟩ := (hasHalt_rowWord δ bl k₀ t).1 (by simpa using hc)
    exact h ((halts_iff_tab (bl := bl)).2 ⟨t, j, hj⟩)
  have hok : StopOK δ bl k₀ .safety none := ⟨fun _ => ⟨rfl, hno⟩, fun n hn => by simp at hn⟩
  refine ⟨stratStop δ bl k₀ none, stratOut δ bl k₀, fun f hf k => ?_⟩
  by_cases hk : isWaiting (f k) = true
  · constructor <;> intro he <;> rw [he] at hk <;> simp [isWaiting] at hk
  · classical
    have hex : ∃ m, isWaiting (f m) = false := ⟨k, by simpa using hk⟩
    have hm := Nat.find_spec hex
    have hmk : Nat.find hex ≤ k := Nat.find_min' hex (by simpa using hk)
    obtain ⟨L, hL⟩ := check_passes hok hf hm fun i hi => by simpa using Nat.find_min hex hi
    have hrun := ne_err_of_ok δ bl (cells k₀) .safety
      (by rw [← play_eq_chkRun hf hm]; exact hL) (k - Nat.find hex)
    rw [← play_eq_chkRun hf hm, Nat.add_sub_cancel' hmk] at hrun
    exact hrun

/-- If the team wins the safety variant, the machine does not halt. -/
theorem not_halts_of_winSafety (h : WinSafety δ bl (cells k₀)) : ¬ Halts δ bl k₀ := by
  obtain ⟨σ₀, σ₁, hw⟩ := h
  have hs : SafePlays δ bl (cells k₀) .safety σ₀ σ₁ := hw
  intro hh
  obtain ⟨t, j, hj⟩ := (halts_iff_tab (bl := bl)).1 hh
  have hq := quiet_safety hs
  have hrows := rows_of_safe (k₀ := k₀) hs (M := t + 1) (by omega) (hq _) (m := t + 1) (by omega)
    (by omega)
  simp only [Nat.add_sub_cancel] at hrows
  have := (claim_eq hs (by omega) (hq _) hrows).2 rfl
  rw [(hasHalt_rowWord δ bl k₀ t).2 ⟨j, hj⟩] at this
  exact absurd this (by simp)

/-- **The team wins the safety variant iff the machine does not halt.** -/
theorem winSafety_iff_not_halts : WinSafety δ bl (cells k₀) ↔ ¬ Halts δ bl k₀ :=
  ⟨not_halts_of_winSafety, winSafety_of_not_halts⟩

end Main

end DiagonaLean.TeamGame
