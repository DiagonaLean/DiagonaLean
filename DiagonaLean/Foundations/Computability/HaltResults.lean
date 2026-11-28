/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Sonnet
-/

import DiagonaLean.Foundations.Computability.Undecidable
import DiagonaLean.Foundations.Computability.ReduceFrom
import DiagonaLean.Foundations.Computability.UndecTransfer
import DiagonaLean.Foundations.Computability.HaltComplete

@[expose] public section

/-! # The `halt_results` command

A reduction from the halting problem proved computable (`HaltReduction P`) is the strongest result
the library states about a problem `P`. `halt_results P from r` states its three consequences as
theorems, under the same names for every problem, in the current namespace:

* `haltHard : HaltHard P`;
* `not_computablePred : Undecidable P`, that is `¬ ComputablePred P`;
* `not_machineDecidable : Computable enc → ¬ MachineDecidable enc P`, for every encoding `enc`.

It also registers the result for the tactics: `not_computablePred` is tagged `@[undecHardness]`,
so the route search of `undec from` starts from `P`, and `instance : HaltHardFact P` lets
`hard_reduce_from` and `reduce_from` take the problem `P` itself as a source.

## Forms

* `halt_results P from r`, with `r : HaltReduction P`, or with `r : HaltHard P` itself: when the
  reduction needs constants that exist only classically (a universal code, a race program from the
  recursion theorem), only its existence can be stated, and its proof obtains them
  (`SKIConv/Undecidable.lean`).
* `halt_results P over_letters from r`, for the statement over every nontrivial alphabet `α`:
  `r b0 b1 hne : HaltReduction P` is a reduction for each pair of distinct letters of `α`
  (such as `MPCP.fromHaltOver`). The letters come from `Nontrivial α` (`HaltHard.of_letters`).
* `halt_results Name for …` puts the three theorems under `Name`, for a second problem in the same
  namespace.

## `re_results`

`re_results P from h`, with `h : REPred P`, after `halt_results` for `P`, states that `P` is
complete for the recursively enumerable problems (`complete : REPred q → ManyOneReducible q P`) and
registers `h` as `instance : REFact P`. Two problems registered by both commands are many-one
equivalent by `manyOneEquiv_of_complete p q`. `re_results Name for …` puts the theorem under
`Name`.

The section's variables, such as `{α : Type} [Primcodable α] [Nontrivial α]`, become arguments of
the theorems as for any theorem: those that `P` mentions.

The command is a macro: it expands to three `theorem` commands, which Lean elaborates and the
kernel checks as if written by hand.

## Main statements

* `HaltHard.of_letters`: halting-hardness over a nontrivial alphabet, from a reduction for each
  pair of distinct letters.
* `manyOneEquiv_of_complete`: two problems registered as halting-hard and recursively enumerable
  are many-one equivalent.
-/

namespace DiagonaLean.Foundations.Computability

/-- **Halting-hardness over a nontrivial alphabet**, from a halting reduction for each pair of
distinct letters. The reduction is data and depends on the letters; that one exists is a
proposition, which needs only `Nontrivial α`. -/
theorem HaltHard.of_letters {α : Type*} [Nontrivial α] {β : Type*} [Primcodable β] {P : β → Prop}
    (r : (b0 b1 : α) → b0 ≠ b1 → HaltReduction P) : HaltHard P :=
  let ⟨b0, b1, hne⟩ := exists_pair_ne α
  ⟨r b0 b1 hne⟩

/-- `P` is recursively enumerable, registered by `re_results` for `manyOneEquiv_of_complete`. -/
class REFact {β : Type*} [Primcodable β] (P : β → Prop) : Prop where
  /-- The fact. -/
  re : REPred P

/-- **Two registered halting-hard r.e. problems are many-one equivalent**: both have the degree of
the halting problem. -/
theorem manyOneEquiv_of_complete {α β : Type*} [Primcodable α] [Primcodable β] (p : α → Prop)
    (q : β → Prop) [HaltHardFact p] [REFact p] [HaltHardFact q] [REFact q] : ManyOneEquiv p q :=
  manyOneEquiv_of_haltHard_of_rePred HaltHardFact.hard REFact.re HaltHardFact.hard REFact.re

end DiagonaLean.Foundations.Computability

/-- The optional `Name for` of `halt_results`. -/
syntax haltResultsName := atomic(ident " for ")

open Lean in
/-- `halt_results P from r` states `haltHard`, `not_computablePred` and `not_machineDecidable` for
the problem `P`, from `r : HaltReduction P` or `r : HaltHard P`. With `over_letters`, `r` takes
two distinct letters of a nontrivial alphabet. `halt_results Name for …` puts the theorems under
`Name`. -/
macro (name := haltResults) "halt_results" pre:(haltResultsName)? p:term
    letters:(" over_letters")? " from " r:term : command => do
  let pre : Option Name := pre.map fun stx => stx.raw[0].getId
  let ref ← getRef
  let name (s : Name) : Ident := mkIdentFrom ref (pre.elim s (· ++ s)) (canonical := true)
  let hard : Term ← match letters with
    | some _ => `(DiagonaLean.Foundations.Computability.HaltHard.of_letters $r)
    -- `r` is a proof of hardness, or a reduction; the reduction is tried last, so that a source
    -- that is neither is reported against `HaltReduction`, the usual form
    | none => `(by first | exact $r | exact ⟨$r⟩)
  let hardName := name `haltHard
  let computableName := name `not_computablePred
  let machineName := name `not_machineDecidable
  `(/-- The problem is halting-hard: the halting problem reduces to it computably. Stated by
    `halt_results`. -/
    theorem $hardName:ident : DiagonaLean.Foundations.Computability.HaltHard $p := $hard
    /-- The problem is undecidable: it is not a computable predicate. Stated by `halt_results`. -/
    @[undecHardness] theorem $computableName:ident :
        DiagonaLean.Foundations.Computability.Undecidable $p :=
      DiagonaLean.Foundations.Computability.HaltHard.not_computablePred (P := $p) $hard
    /-- No Turing machine decides the problem, under any computable encoding of its instances.
    Stated by `halt_results`. -/
    theorem $machineName:ident {enc : _ → List Bool} (henc : Computable enc) :
        ¬ DiagonaLean.Synthetic.Definitions.MachineDecidable enc $p :=
      DiagonaLean.Foundations.Computability.HaltHard.not_machineDecidable (P := $p) $hard henc
    /-- The problem is registered as halting-hard, for the tactics. Stated by `halt_results`. -/
    instance : DiagonaLean.Foundations.Computability.HaltHardFact $p :=
      ⟨$hardName:ident⟩)

open Lean in
/-- `re_results P from h` states `complete` for the problem `P`, from `h : REPred P` and the
halting-hardness that `halt_results` registered, and registers `h` as `REFact P`.
`re_results Name for …` puts the theorem under `Name`. -/
macro (name := reResults) "re_results" pre:(haltResultsName)? p:term " from " h:term :
    command => do
  let pre : Option Name := pre.map fun stx => stx.raw[0].getId
  let ref ← getRef
  let completeName : Ident :=
    mkIdentFrom ref (pre.elim `complete (· ++ `complete)) (canonical := true)
  -- plain binder names, so that the theorem reads as if written by hand
  let β := mkIdent `β
  let q := mkIdent `q
  let hq := mkIdent `hq
  `(/-- The problem is recursively enumerable, registered for `manyOneEquiv_of_complete`. Stated
    by `re_results`. -/
    instance : DiagonaLean.Foundations.Computability.REFact $p := ⟨$h⟩
    /-- The problem is complete for the recursively enumerable problems: every one many-one reduces
    to it. Stated by `re_results`. -/
    theorem $completeName:ident {$β : Type*} [Primcodable $β] {$q : $β → Prop} ($hq : REPred $q) :
        ManyOneReducible $q $p :=
      ManyOneReducible.of_rePred_of_haltHard $hq
        (DiagonaLean.Foundations.Computability.HaltHardFact.hard (P := $p)))
