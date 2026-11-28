/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CFGame.Codes
import DiagonaLean.Synthetic.Tactics.ReductionPath

@[expose] public section

/-! # Halting of list machines reduces to context-free games

An instance of `ListHalt` is a program `p` of a list machine on numeric states, a start state `q₀`
and a tape. Its machine never leaves the finite list `ListHalt.states p q₀`, so it is the renaming
by `Subtype.val` of a machine on the finite type `ProgStates p q₀` of these states (`actOnStates`,
`act_eq_mapAct`). The simulation game of the machine on `ProgStates p q₀` is won iff the machine
halts (`wins_iff_halts`), and renamed to numbers it is the game `listToCFGame bl (p, q₀, tape)`,
built on the numeric states (`rules_mapQ`, `target_mapQ`). So `listToCFGame bl` reduces halting of
list machines to context-free games (`listHalt_reducesto_cfGame_spec`), and it is primitive
recursive (`listToCFGame_prim`), because it is built on codes (`rulesC`, `targetC`, `cfgWordC`).

## Main statements

* `listHalt_reducesto_cfGame_spec`: the machine of an instance halts iff Juliet wins its game.
* `listToCFGame_prim`: the reduction is primitive recursive.
-/

namespace DiagonaLean.CFGame.Reduction

open DiagonaLean.Foundations.Computability DiagonaLean.Foundations.Computability.ListMachine
  DiagonaLean.Foundations.Computability.ListHalt DiagonaLean.CFGame.Simulation

variable {Γ : Type} [DecidableEq Γ]

/-! ### The machine on the states of a program -/

/-- The states of the program `p` and the start state `q₀`, as a type. -/
abbrev ProgStates (p : Program Γ) (q₀ : ℕ) := { q : ℕ // q ∈ states p q₀ }

/-- The state a rule enters is a state of the program. -/
theorem mem_states_of_rule {p : Program Γ} {q : ℕ} {c : Γ} {r : Move × ℕ × Γ}
    (h : rule? p q c = some r) (q₀ : ℕ) : r.2.1 ∈ states p q₀ := by
  unfold rule? at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  exact List.mem_dedup.2 (List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, List.mem_of_find?_eq_some hx,
    rfl⟩))

/-- The transition of a right side of a rule on `ProgStates p q₀`. -/
def toActOnStates {p : Program Γ} {q₀ : ℕ} (r : Move × ℕ × Γ) (hr : r.2.1 ∈ states p q₀) :
    Act (ProgStates p q₀) Γ :=
  if r.1 = .stay then .stay ⟨r.2.1, hr⟩ r.2.2
  else if r.1 = .right then .right ⟨r.2.1, hr⟩ r.2.2
  else .left ⟨r.2.1, hr⟩ r.2.2

/-- The machine of `p` on `ProgStates p q₀`. -/
def actOnStates (p : Program Γ) (q₀ : ℕ) (q : ProgStates p q₀) (c : Γ) : Act (ProgStates p q₀) Γ :=
  match h : rule? p q.1 c with
  | none => .halt
  | some r => toActOnStates r (mem_states_of_rule h q₀)

/-- The machine of `p` is the renaming of the machine on `ProgStates p q₀` by `Subtype.val`. -/
theorem act_eq_mapAct (p : Program Γ) (q₀ : ℕ) (q : ProgStates p q₀) (c : Γ) :
    act p q.1 c = mapAct Subtype.val (actOnStates p q₀ q c) := by
  unfold act actOnStates
  split
  · next h => simp [h, mapAct]
  · next r h =>
    simp only [h, Option.map_some, Option.getD_some, toAct, toActOnStates]
    split_ifs <;> rfl

/-! ### The reduction -/

variable [Fintype Γ] [Primcodable Γ]

/-- **The reduction.** `listToCFGame bl (p, q₀, tape)` is the simulation game of the machine of
`p`, on the states `ListHalt.states p q₀` and every symbol, and the word of its start
configuration, with letters coded as numbers (`natLetterCode`). -/
def listToCFGame (bl : Γ) (x : Program Γ × ℕ × List Γ) : Game ℕ × List ℕ :=
  ((rulesC x.1 (states x.1 x.2.1) (enumAll Γ) bl, targetC (states x.1 x.2.1) (enumAll Γ)),
    cfgWordC x.2.1 [] (x.2.2.headD bl) x.2.2.tail)

derive_primrec listToCFGame

/-- The game of an instance is the coded simulation game of its machine. -/
theorem listToCFGame_eq_map (bl : Γ) (x : Program Γ × ℕ × List Γ) :
    listToCFGame bl x =
      (Game.map natLetterCode (rules (act x.1) (states x.1 x.2.1) (enumAll Γ) bl,
          target (states x.1 x.2.1) (enumAll Γ)),
        (cfgWord (start bl x.2.1 x.2.2)).map natLetterCode) := by
  simp only [listToCFGame, Game.map, rulesC_eq, targetC_eq, ← cfgWordC_eq, start]

omit [DecidableEq Γ] [Fintype Γ] in
/-- The code of a letter on `ProgStates p q₀` is the code of its renaming to numbers. -/
theorem letterCode_val (p : Program Γ) (q₀ : ℕ) :
    letterCode (Subtype.val : ProgStates p q₀ → ℕ) Encodable.encode =
      natLetterCode ∘ Letter.mapQ (Γ := Γ) Subtype.val := by
  funext x
  cases x <;> rfl

/-- The game of an instance is the game of the machine on `ProgStates p q₀`, coded. -/
theorem listToCFGame_eq (bl : Γ) (p : Program Γ) (q₀ : ℕ) (tape : List Γ) :
    listToCFGame bl (p, q₀, tape) =
      (Game.map (letterCode Subtype.val Encodable.encode)
          (rules (actOnStates p q₀) (states p q₀).attach (enumAll Γ) bl,
            target (states p q₀).attach (enumAll Γ)),
        (cfgWord (⟨⟨q₀, mem_states_start p q₀⟩, [], tape.headD bl, tape.tail⟩ :
          Cfg (ProgStates p q₀) Γ)).map (letterCode Subtype.val Encodable.encode)) := by
  have hr := rules_mapQ (Subtype.val : ProgStates p q₀ → ℕ) (act_eq_mapAct p q₀)
    (states p q₀).attach (enumAll Γ) bl
  have ht := target_mapQ (Γ := Γ) Subtype.val_injective (states p q₀).attach (enumAll Γ)
  have hw := cfgWord_mapQ (f := (Subtype.val : ProgStates p q₀ → ℕ))
    (⟨⟨q₀, mem_states_start p q₀⟩, [], tape.headD bl, tape.tail⟩ : Cfg (ProgStates p q₀) Γ)
  rw [List.attach_map_subtype_val] at hr ht
  simp only [listToCFGame_eq_map, letterCode_val, Game.map, ← hr, ← ht, start, List.map_map,
    RegularExpression.map_map]
  refine Prod.ext (Prod.ext (by simp [Function.comp_def]) rfl) ?_
  dsimp only
  rw [← List.map_map, ← hw]
  rfl

/-- `listToCFGame bl` witnesses the reduction from halting of list machines given by a table to
context-free games. -/
theorem listHalt_reducesto_cfGame_spec (bl : Γ) :
    ListHalt.DecisionProblem bl ⪯_s[listToCFGame bl] (@DecisionProblem ℕ) := by
  rintro ⟨p, q₀, tape⟩
  rw [listToCFGame_eq, DecisionProblem]
  simp only
  rw [wins_map_iff (letterCode_injective Subtype.val_injective Encodable.encode_injective),
    wins_iff_halts (List.mem_attach _) mem_enumAll (fun _ => mem_target (List.mem_attach _)
      mem_enumAll)]
  rw [ListHalt.decisionProblem_mk, HaltsOn, start]
  exact (halts_mapCfg_iff (act_eq_mapAct p q₀)
    (⟨⟨q₀, mem_states_start p q₀⟩, [], tape.headD bl, tape.tail⟩ : Cfg (ProgStates p q₀) Γ))

/-- Context-free games are displayed as "Context-free game". -/
instance : Synthetic.ReductionChain.ProblemName (@DecisionProblem ℕ) :=
  ⟨"Context-free game"⟩

end DiagonaLean.CFGame.Reduction
