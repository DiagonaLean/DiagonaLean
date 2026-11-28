/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CFGame.Target
import DiagonaLean.CFGame.Rename
import DiagonaLean.Foundations.Computability.ListHalt
import DiagonaLean.Foundations.Computability.DerivePrimrec

@[expose] public section

/-! # The simulation game on numeric states, coded

A letter of the simulation game is coded by a number (`letterCode`), and on numeric states by
`natLetterCode`; regular expressions over `ℕ` are `Primcodable`
(`Foundations/Computability/RegularExpression.lean`). The coded
rules, target and configuration words are given directly on codes (`rulesC`, `targetC`,
`cfgWordC`), which are primitive recursive, and they are the codes of the rules, target and words
of the game (`rulesC_eq`, `targetC_eq`, `cfgWordC_eq`).

## Main statements

* `rulesC_eq`, `targetC_eq`, `cfgWordC_eq`: the constructions on codes are the coded
  constructions.
-/

namespace DiagonaLean.CFGame.Simulation

open DiagonaLean.Foundations.Computability DiagonaLean.Foundations.Computability.ListMachine
  DiagonaLean.Foundations.Computability.ListHalt

/-! ### Codes of letters -/

section Code

variable {Q Γ : Type}

/-- The code of the left end `$`. -/
def dollarCode : ℕ := Nat.pair 0 0

/-- The code of the right end `#`. -/
def endCode : ℕ := Nat.pair 1 0

/-- The code of the halt letter. -/
def haltCode : ℕ := Nat.pair 6 0

/-- The code of the objection on a tape cell or on `#`. -/
def objTapeCode : ℕ := Nat.pair 7 0

/-- The code of the objection on the head. -/
def objHeadCode : ℕ := Nat.pair 8 0

/-- The code of the objection on a right marker. -/
def objRCode : ℕ := Nat.pair 9 0

/-- The code of the objection on a left marker. -/
def objLCode : ℕ := Nat.pair 10 0

/-- The code of a letter, from codes `fq` of states and `fc` of tape symbols. -/
def letterCode (fq : Q → ℕ) (fc : Γ → ℕ) : Letter Q Γ → ℕ
  | .dollar => dollarCode
  | .endm => endCode
  | .tape c => Nat.pair 2 (fc c)
  | .head q c => Nat.pair 3 (Nat.pair (fq q) (fc c))
  | .rmark q c => Nat.pair 4 (Nat.pair (fq q) (fc c))
  | .lmark q c => Nat.pair 5 (Nat.pair (fq q) (fc c))
  | .halt => haltCode
  | .objTape => objTapeCode
  | .objHead => objHeadCode
  | .objR => objRCode
  | .objL => objLCode

/-- `letterCode fq fc` is injective when `fq` and `fc` are. -/
theorem letterCode_injective {fq : Q → ℕ} {fc : Γ → ℕ} (hq : Function.Injective fq)
    (hc : Function.Injective fc) : Function.Injective (letterCode fq fc) := by
  intro x y h
  cases x <;> cases y <;>
    simp only [letterCode, dollarCode, endCode, haltCode, objTapeCode, objHeadCode, objRCode,
      objLCode, Nat.pair_eq_pair] at h <;>
    first
    | rfl
    | (exfalso; omega)
    | (obtain ⟨-, h⟩ := h; rw [hc h])
    | (obtain ⟨-, h₁, h₂⟩ := h; rw [hq h₁, hc h₂])

end Code

variable {Γ : Type} [Primcodable Γ]

/-- `tapeCode c` is the code of the tape letter `c`. -/
def tapeCode (c : Γ) : ℕ := Nat.pair 2 (Encodable.encode c)

/-- `headCode q c` is the code of the head letter in state `q` on `c`. -/
def headCode (q : ℕ) (c : Γ) : ℕ := Nat.pair 3 (Nat.pair q (Encodable.encode c))

/-- `rmarkCode q c` is the code of the right marker for the state `q` and the symbol `c`. -/
def rmarkCode (q : ℕ) (c : Γ) : ℕ := Nat.pair 4 (Nat.pair q (Encodable.encode c))

/-- `lmarkCode q c` is the code of the left marker for the state `q` and the symbol `c`. -/
def lmarkCode (q : ℕ) (c : Γ) : ℕ := Nat.pair 5 (Nat.pair q (Encodable.encode c))

/-- `natLetterCode` codes the letters of the game on numeric states. -/
def natLetterCode : Letter ℕ Γ → ℕ
  | .dollar => dollarCode
  | .endm => endCode
  | .tape c => tapeCode c
  | .head q c => headCode q c
  | .rmark q c => rmarkCode q c
  | .lmark q c => lmarkCode q c
  | .halt => haltCode
  | .objTape => objTapeCode
  | .objHead => objHeadCode
  | .objR => objRCode
  | .objL => objLCode

/-- `natLetterCode` is `letterCode` with the identity on states. -/
theorem natLetterCode_eq : natLetterCode (Γ := Γ) = letterCode id Encodable.encode := by
  funext x
  cases x <;> rfl

/-! ### The rules -/

variable [DecidableEq Γ]

/-- The code of the letter after the transition of the program `p` in state `q` on `c`. -/
def actC (p : Program Γ) (q : ℕ) (c : Γ) : ℕ :=
  ((rule? p q c).map fun r =>
    if r.1 = .stay then headCode r.2.1 r.2.2 else if r.1 = .right then rmarkCode r.2.1 r.2.2
    else lmarkCode r.2.1 r.2.2).getD (haltCode)

/-- `actC` codes the letter after the transition. -/
theorem actC_eq (p : Program Γ) (q : ℕ) (c : Γ) :
    actC p q c = natLetterCode (actLetter (act p q c)) := by
  unfold actC act
  cases rule? p q c with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.getD_some, toAct]
    split_ifs <;> rfl

/-- The coded rules of the game of the program `p` on the states `qs` and the symbols `cs`. -/
def rulesC (p : Program Γ) (qs : List ℕ) (cs : List Γ) (bl : Γ) : List (ℕ × ℕ × List ℕ) :=
  (qs.flatMap fun q => cs.flatMap fun c =>
      [(headCode q c, actC p q c, []), (headCode q c, objHeadCode, []),
       (rmarkCode q c, tapeCode c, []), (rmarkCode q c, objRCode, []),
       (lmarkCode q c, tapeCode c, []), (lmarkCode q c, objLCode, [])]) ++
    (cs.flatMap fun c =>
      (qs.map fun q => (tapeCode c, headCode q c, [])) ++ [(tapeCode c, objTapeCode, [])]) ++
    ((qs.map fun q => (endCode, headCode q bl, [endCode])) ++
      [(endCode, objTapeCode, [])])

/-- `rulesC` is the coded rules. -/
theorem rulesC_eq (p : Program Γ) (qs : List ℕ) (cs : List Γ) (bl : Γ) :
    rulesC p qs cs bl =
      (rules (act p) qs cs bl).map fun r =>
        (natLetterCode r.1, natLetterCode r.2.1, r.2.2.map natLetterCode) := by
  simp [rulesC, rules, List.map_flatMap, actC_eq, natLetterCode, Function.comp_def]

/-! ### The target -/

/-- The codes of the letters that are not objections. -/
def nonObjC (qs : List ℕ) (cs : List Γ) : List ℕ :=
  [dollarCode, endCode, haltCode] ++ cs.map tapeCode ++
    qs.flatMap fun q => cs.flatMap fun c => [headCode q c, rmarkCode q c, lmarkCode q c]

/-- The codes of the letters that are neither objections, heads nor markers. -/
def quietC (cs : List Γ) : List ℕ := [dollarCode, endCode, haltCode] ++ cs.map tapeCode

/-- The codes of the letters that are neither objections nor heads. -/
def headlessC (qs : List ℕ) (cs : List Γ) : List ℕ :=
  [dollarCode, endCode, haltCode] ++ cs.map tapeCode ++
    qs.flatMap fun q => cs.flatMap fun c => [rmarkCode q c, lmarkCode q c]

/-- The coded target for the states `qs` and the symbols `cs`. -/
def targetC (qs : List ℕ) (cs : List Γ) : RegularExpression ℕ :=
  sumRE (pattern (nonObjC qs cs) [haltCode] ::
    ((qs.flatMap fun q => cs.flatMap fun b => qs.flatMap fun p => cs.flatMap fun c =>
        if p = q then [] else
          [pattern (nonObjC qs cs) [rmarkCode q b, headCode p c],
            pattern (nonObjC qs cs) [headCode p c, lmarkCode q b]]) ++
      [pattern (quietC cs) [objHeadCode]] ++
      (qs.flatMap fun q => cs.flatMap fun b =>
        [pattern (headlessC qs cs) [rmarkCode q b, objTapeCode],
          pattern (headlessC qs cs) [objTapeCode, lmarkCode q b]]) ++
      (qs.flatMap fun p => cs.flatMap fun c =>
        [pattern (nonObjC qs cs) [objRCode, headCode p c],
          pattern (nonObjC qs cs) [headCode p c, objLCode]])))

omit [DecidableEq Γ] in
/-- `targetC` is the coded target. -/
theorem targetC_eq (qs : List ℕ) (cs : List Γ) :
    targetC qs cs = (target qs cs).map natLetterCode := by
  have hn : (nonObj qs cs).map natLetterCode = nonObjC qs cs := by
    simp [nonObj, nonObjC, letters, List.filter_append, List.filter_flatMap, List.map_flatMap,
      isObjB, Letter.IsObj, natLetterCode, List.filter_map, Function.comp_def]
  have hq : (quiet qs cs).map natLetterCode = quietC cs := by
    simp [quiet, quietC, letters, List.filter_append, List.filter_flatMap, List.map_flatMap,
      isObjB, isActiveB, Letter.IsObj, natLetterCode, List.filter_map, Function.comp_def]
  have hh : (headless qs cs).map natLetterCode = headlessC qs cs := by
    simp [headless, headlessC, letters, List.filter_append, List.filter_flatMap, List.map_flatMap,
      isObjB, isHeadB, Letter.IsObj, natLetterCode, List.filter_map, Function.comp_def]
  simp only [target, targetC, sumRE_map, pattern_map, hn, hq, hh, List.map_cons, List.map_append,
    List.map_flatMap, apply_ite, List.map_nil, natLetterCode]

/-! ### Configuration words -/

/-- The coded word of the configuration `(q, l, c, r)`. -/
def cfgWordC (q : ℕ) (l : List Γ) (c : Γ) (r : List Γ) : List ℕ :=
  dollarCode :: (l.reverse.map tapeCode ++ [headCode q c] ++ (r.map tapeCode ++ [endCode]))

omit [DecidableEq Γ] in
/-- `cfgWordC` is the coded word of a configuration. -/
theorem cfgWordC_eq (k : Cfg ℕ Γ) : cfgWordC k.q k.l k.c k.r = (cfgWord k).map natLetterCode := by
  simp [cfgWordC, cfgWord, frame, natLetterCode, Function.comp_def]

/-! ### Computability -/

derive_primrec tapeCode

derive_primrec headCode

derive_primrec rmarkCode

derive_primrec lmarkCode

derive_primrec actC

derive_primrec rulesC

derive_primrec nonObjC

derive_primrec quietC

derive_primrec headlessC

derive_primrec targetC

derive_primrec cfgWordC

end DiagonaLean.CFGame.Simulation
