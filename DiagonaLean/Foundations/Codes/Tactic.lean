/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Codes.Functor

@[expose] public section

/-! # The `code_lift` tactic

A problem given as a functor on codes (`Foundations.Codes.CodeFunctor`) lifts to every alphabet
with two distinct letters. `code_lift F from h` applies the lifting theorem that matches the goal,
with `h` the result over the source alphabet:

* `Undecidable P`: `CodeFunctor.undecidableOf`, with `h : Undecidable` over the source. Since
  `Undecidable P` is an abbreviation of `HaltProblem ⪯_s P`, `h` may be any reduction from
  `HaltProblem`.
* `¬ ComputablePred P`: `CodeFunctor.not_computablePred_lift`, with `h : ¬ ComputablePred` over
  the source.
* `¬ MachineDecidable enc P`: the above, then `not_machineDecidable_of_not_computablePred`, with
  `h : ¬ ComputablePred` over the source.

`code_lift F`, with no source result, proves `ManyOneEquiv P Q` (`CodeFunctor.manyOneEquiv`).

The theorem is chosen by the head of the goal (`targetHead`), so an error in applying it, such as
a source result `h` of the wrong type, is reported as such. `P` must be the problem of `F` up to
unfolding `F` (an `abbrev`). The side goals are closed when possible, and otherwise left as named
goals, so that what remains to be proved is displayed:

* `Undecidable P`: the two letters and their distinctness come from a hypothesis `hne : b0 ≠ b1`
  in the context (the letters are data, so they cannot come from `Nontrivial`).
* `case map_computable` (and `map_computable_symm` for `ManyOneEquiv`): the function of the lift,
  `F.liftMap b0 b1`, is computable. It is closed by unfolding `liftMap` and `F` and calling
  `fun_prop`, which needs `fun_prop` lemmas for the encodings and the letters of the instance
  (`derive_primrec` generates them, also for a code that depends on the instance).
* `case enc_computable`: the encoding of a `MachineDecidable` goal is computable, closed by
  `assumption`.

`F` must be an identifier, so that it can be unfolded. The good codes of `F` must form a class
with a `LiftableCodes` instance, as `IsCode` and `IsSync` do.
-/

/-- Closes `∀ [DecidableEq α] (b0 b1 : β), Computable (F.liftMap b0 b1)` by unfolding `liftMap`
and `F` and calling `fun_prop`. Used by `code_lift`. -/
syntax "code_lift_computable " ident : tactic

macro_rules
  | `(tactic| code_lift_computable $F:ident) =>
    `(tactic|
        (intros
         refine Primrec.to_comp ?_
         unfold DiagonaLean.Foundations.Codes.CodeFunctor.liftMap
         dsimp only [$F:ident]
         fun_prop))

namespace DiagonaLean.Foundations.Codes.CodeLift

open Lean Meta Elab Tactic

/-- The head constant of `e` and `false`, or, when `e` is a negation `¬ p`, the head constant of
`p` and `true`. `code_lift` chooses the lifting theorem by it. -/
def targetHead (e : Expr) : Name × Bool :=
  let e := e.consumeMData
  if e.isAppOfArity ``Not 1 then (e.appArg!.consumeMData.getAppFn.constName, true)
  else (e.getAppFn.constName, false)

/-- `code_lift F from h` lifts the result `h` about the problem of the functor on codes `F` to the
alphabet of the goal; `code_lift F` proves alphabet invariance. See the module docstring. -/
syntax "code_lift " ident (" from " term)? : tactic

/-- `code_lift` reads the head of the goal, applies the matching lifting theorem, and reports the
errors of that theorem, such as a source result `h` of the wrong type. -/
elab_rules : tactic
  | `(tactic| code_lift $F:ident from $h) => withMainContext do
    match targetHead (← instantiateMVars (← getMainTarget)) with
    | (``DiagonaLean.Synthetic.Notation.Undecidable, false) =>
      evalTactic (← `(tactic|
        exact DiagonaLean.Foundations.Codes.CodeFunctor.undecidableOf $F $h _ _
          (by first
            | assumption
            | fail "code_lift: no hypothesis `hne : b0 ≠ b1` in the context")))
    | (``ComputablePred, true) =>
      evalTactic (← `(tactic|
        (refine DiagonaLean.Foundations.Codes.CodeFunctor.not_computablePred_lift $F
            ?map_computable $h
         try code_lift_computable $F)))
    | (``DiagonaLean.Synthetic.Definitions.MachineDecidable, true) =>
      evalTactic (← `(tactic|
        (refine DiagonaLean.Foundations.Computability.not_machineDecidable_of_not_computablePred
            ?enc_computable
            (DiagonaLean.Foundations.Codes.CodeFunctor.not_computablePred_lift $F
              ?map_computable $h)
         try (case enc_computable => assumption)
         try (case map_computable => code_lift_computable $F))))
    | _ => throwError "code_lift: the goal must be `Undecidable P`, `¬ ComputablePred P` or \
        `¬ MachineDecidable enc P`, with `P` the problem of the functor"
  | `(tactic| code_lift $F:ident) => withMainContext do
    match targetHead (← instantiateMVars (← getMainTarget)) with
    | (``ManyOneEquiv, false) =>
      evalTactic (← `(tactic|
        (refine DiagonaLean.Foundations.Codes.CodeFunctor.manyOneEquiv $F
            ?map_computable ?map_computable_symm
         all_goals try code_lift_computable $F)))
    | _ => throwError "code_lift: without `from`, the goal must be `ManyOneEquiv P Q`, with `P` \
        and `Q` the problem of the functor over two alphabets"

end DiagonaLean.Foundations.Codes.CodeLift
