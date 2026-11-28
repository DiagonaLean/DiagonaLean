/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CFGame.Target
import DiagonaLean.CFGame.Rename
import DiagonaLean.Foundations.Computability.ListHalt
import DiagonaLean.Foundations.Computability.DerivePrimcodable
import DiagonaLean.Foundations.Computability.DerivePrimrec
import DiagonaLean.Foundations.Computability.PrimrecRec

@[expose] public section

/-! # The simulation game on numeric states, coded

Regular expressions over a `Primcodable` alphabet are `Primcodable` (`derive_primcodable`). A
letter of the simulation game on numeric states is coded by a number (`listCode`). The coded
rules, target and configuration words are given directly on codes (`rulesC`, `targetC`,
`cfgWordC`), which are primitive recursive, and they are the codes of the rules, target and words
of the game (`rulesC_eq`, `targetC_eq`, `cfgWordC_eq`).

## Main statements

* `rulesC_eq`, `targetC_eq`, `cfgWordC_eq`: the constructions on codes are the coded
  constructions.
-/

derive_primcodable RegularExpression

namespace DiagonaLean.CFGame.Simulation

open DiagonaLean.Foundations.Computability DiagonaLean.Foundations.Computability.ListMachine
  DiagonaLean.Foundations.Computability.ListHalt RegularExpression

/-! ### Regular expressions -/

section Regex

variable {α β : Type} [Primcodable α] [Primcodable β]

/-- The sum of two expressions is primitive recursive in them. -/
@[fun_prop] theorem prim_reAdd {f g : β → RegularExpression α} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x + g x := by
  change Primrec fun x => (f x).plus (g x)
  fun_prop

/-- The product of two expressions is primitive recursive in them. -/
@[fun_prop] theorem prim_reMul {f g : β → RegularExpression α} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => f x * g x := by
  change Primrec fun x => (f x).comp (g x)
  fun_prop

/-- The empty expression is a primitive recursive constant. -/
@[fun_prop] theorem prim_reZero : Primrec fun _ : β => (0 : RegularExpression α) := Primrec.const _

/-- The expression of the empty word is a primitive recursive constant. -/
@[fun_prop] theorem prim_reOne : Primrec fun _ : β => (1 : RegularExpression α) := Primrec.const _

derive_primrec sumRE [Primcodable α]

derive_primrec anyOf [Primcodable α]

derive_primrec wordRE [Primcodable α]

derive_primrec pattern [Primcodable α]

end Regex

/-! ### Codes of letters -/

variable {Γ : Type} [Primcodable Γ]

/-- The code of the tape letter `c`. -/
def cT (c : Γ) : ℕ := Nat.pair 2 (Encodable.encode c)

/-- The code of the head letter in state `q` on `c`. -/
def cH (q : ℕ) (c : Γ) : ℕ := Nat.pair 3 (Nat.pair q (Encodable.encode c))

/-- The code of the right marker for the state `q` and the symbol `c`. -/
def cR (q : ℕ) (c : Γ) : ℕ := Nat.pair 4 (Nat.pair q (Encodable.encode c))

/-- The code of the left marker for the state `q` and the symbol `c`. -/
def cL (q : ℕ) (c : Γ) : ℕ := Nat.pair 5 (Nat.pair q (Encodable.encode c))

/-- The code of a letter of the game on numeric states. -/
def listCode : Letter ℕ Γ → ℕ
  | .dollar => Nat.pair 0 0
  | .endm => Nat.pair 1 0
  | .tape c => cT c
  | .head q c => cH q c
  | .rmark q c => cR q c
  | .lmark q c => cL q c
  | .halt => Nat.pair 6 0
  | .objTape => Nat.pair 7 0
  | .objHead => Nat.pair 8 0
  | .objR => Nat.pair 9 0
  | .objL => Nat.pair 10 0

/-- `listCode` is injective. -/
theorem listCode_injective : Function.Injective (listCode (Γ := Γ)) := by
  intro x y h
  cases x <;> cases y <;> simp only [listCode, cT, cH, cR, cL, Nat.pair_eq_pair] at h <;>
    first
    | rfl
    | (exfalso; omega)
    | (obtain ⟨-, h⟩ := h; rw [Encodable.encode_injective h])
    | (obtain ⟨-, h₁, h₂⟩ := h; rw [h₁, Encodable.encode_injective h₂])

/-! ### The rules -/

variable [DecidableEq Γ]

/-- The code of the letter after the transition of the program `p` in state `q` on `c`. -/
def actC (p : Program Γ) (q : ℕ) (c : Γ) : ℕ :=
  ((rule? p q c).map fun r =>
    if r.1 = .stay then cH r.2.1 r.2.2 else if r.1 = .right then cR r.2.1 r.2.2
    else cL r.2.1 r.2.2).getD (Nat.pair 6 0)

/-- `actC` codes the letter after the transition. -/
theorem actC_eq (p : Program Γ) (q : ℕ) (c : Γ) :
    actC p q c = listCode (actLetter (act p q c)) := by
  unfold actC act
  cases rule? p q c with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.getD_some, toAct]
    split_ifs <;> rfl

/-- The coded rules of the game of the program `p` on the states `qs` and the symbols `cs`. -/
def rulesC (p : Program Γ) (qs : List ℕ) (cs : List Γ) (bl : Γ) : List (ℕ × ℕ × List ℕ) :=
  (qs.flatMap fun q => cs.flatMap fun c =>
      [(cH q c, actC p q c, []), (cH q c, Nat.pair 8 0, []),
       (cR q c, cT c, []), (cR q c, Nat.pair 9 0, []),
       (cL q c, cT c, []), (cL q c, Nat.pair 10 0, [])]) ++
    (cs.flatMap fun c => (qs.map fun q => (cT c, cH q c, [])) ++ [(cT c, Nat.pair 7 0, [])]) ++
    ((qs.map fun q => (Nat.pair 1 0, cH q bl, [Nat.pair 1 0])) ++
      [(Nat.pair 1 0, Nat.pair 7 0, [])])

/-- `rulesC` is the coded rules. -/
theorem rulesC_eq (p : Program Γ) (qs : List ℕ) (cs : List Γ) (bl : Γ) :
    rulesC p qs cs bl =
      (rules (act p) qs cs bl).map fun r => (listCode r.1, listCode r.2.1, r.2.2.map listCode) := by
  simp [rulesC, rules, List.map_flatMap, actC_eq, listCode, Function.comp_def]

/-! ### The target -/

/-- The codes of the letters that are not objections. -/
def nonObjC (qs : List ℕ) (cs : List Γ) : List ℕ :=
  [Nat.pair 0 0, Nat.pair 1 0, Nat.pair 6 0] ++ cs.map cT ++
    qs.flatMap fun q => cs.flatMap fun c => [cH q c, cR q c, cL q c]

/-- The codes of the letters that are neither objections, heads nor markers. -/
def quietC (cs : List Γ) : List ℕ := [Nat.pair 0 0, Nat.pair 1 0, Nat.pair 6 0] ++ cs.map cT

/-- The codes of the letters that are neither objections nor heads. -/
def headlessC (qs : List ℕ) (cs : List Γ) : List ℕ :=
  [Nat.pair 0 0, Nat.pair 1 0, Nat.pair 6 0] ++ cs.map cT ++
    qs.flatMap fun q => cs.flatMap fun c => [cR q c, cL q c]

/-- The coded target for the states `qs` and the symbols `cs`. -/
def targetC (qs : List ℕ) (cs : List Γ) : RegularExpression ℕ :=
  sumRE (pattern (nonObjC qs cs) [Nat.pair 6 0] ::
    ((qs.flatMap fun q => cs.flatMap fun b => qs.flatMap fun p => cs.flatMap fun c =>
        if p = q then [] else
          [pattern (nonObjC qs cs) [cR q b, cH p c],
            pattern (nonObjC qs cs) [cH p c, cL q b]]) ++
      [pattern (quietC cs) [Nat.pair 8 0]] ++
      (qs.flatMap fun q => cs.flatMap fun b =>
        [pattern (headlessC qs cs) [cR q b, Nat.pair 7 0],
          pattern (headlessC qs cs) [Nat.pair 7 0, cL q b]]) ++
      (qs.flatMap fun p => cs.flatMap fun c =>
        [pattern (nonObjC qs cs) [Nat.pair 9 0, cH p c],
          pattern (nonObjC qs cs) [cH p c, Nat.pair 10 0]])))

omit [DecidableEq Γ] in
/-- `targetC` is the coded target. -/
theorem targetC_eq (qs : List ℕ) (cs : List Γ) :
    targetC qs cs = (target qs cs).map listCode := by
  have hn : (nonObj qs cs).map listCode = nonObjC qs cs := by
    simp [nonObj, nonObjC, letters, List.filter_append, List.filter_flatMap, List.map_flatMap,
      isObjB, Letter.IsObj, listCode, List.filter_map, Function.comp_def]
  have hq : (quiet qs cs).map listCode = quietC cs := by
    simp [quiet, quietC, letters, List.filter_append, List.filter_flatMap, List.map_flatMap,
      isObjB, isActiveB, Letter.IsObj, listCode, List.filter_map, Function.comp_def]
  have hh : (headless qs cs).map listCode = headlessC qs cs := by
    simp [headless, headlessC, letters, List.filter_append, List.filter_flatMap, List.map_flatMap,
      isObjB, isHeadB, Letter.IsObj, listCode, List.filter_map, Function.comp_def]
  simp only [target, targetC, sumRE_map, pattern_map, hn, hq, hh, List.map_cons, List.map_append,
    List.map_flatMap, apply_ite, List.map_nil, listCode]

/-! ### Configuration words -/

/-- The coded word of the configuration `(q, l, c, r)`. -/
def cfgWordC (q : ℕ) (l : List Γ) (c : Γ) (r : List Γ) : List ℕ :=
  Nat.pair 0 0 :: (l.reverse.map cT ++ [cH q c] ++ (r.map cT ++ [Nat.pair 1 0]))

omit [DecidableEq Γ] in
/-- `cfgWordC` is the coded word of a configuration. -/
theorem cfgWordC_eq (k : Cfg ℕ Γ) : cfgWordC k.q k.l k.c k.r = (cfgWord k).map listCode := by
  simp [cfgWordC, cfgWord, frame, listCode, Function.comp_def]

/-! ### Computability -/

derive_primrec cT

derive_primrec cH

derive_primrec cR

derive_primrec cL

derive_primrec actC

derive_primrec rulesC

derive_primrec nonObjC

derive_primrec quietC

derive_primrec headlessC

derive_primrec targetC

derive_primrec cfgWordC

end DiagonaLean.CFGame.Simulation
