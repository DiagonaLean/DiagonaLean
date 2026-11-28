import DiagonaLean

/-! Fixture for `scripts/CheckMetaprograms.lean`, run by CI, which must reject it. Not built.

Rules that change existing command or term syntax (found 2026-11-26): the first line makes
`#check_reductions local` print a message instead of checking, the second makes a theorem that
reads `¬ ComputablePred P` state `True ∨ ComputablePred P`. Both were verified to work, and the
metaprogram check reported neither. The last rule, on tactic syntax, must not be reported. -/

macro_rules | `(#check_reductions local) => `(#print "all good")
macro_rules | `(¬ $p) => `(True ∨ $p)
elab_rules : term | `(¬ $p) => pure (Lean.mkConst ``True)
open Lean in macro_rules | `(¬ $p) => `(True ∨ $p)
macro_rules (kind := Lean.Parser.Command.check) | stx => pure stx
open Lean in
@[macro Lean.Parser.Term.paren] def m : Macro := fun _ => Macro.throwUnsupported
open Lean Elab in
@[term_elab Lean.Parser.Term.paren] def m2 : Term.TermElab := fun _ _ => throwError "x"
macro (priority := high) "¬" p:term:40 : term => `(True ∨ $p)
macro_rules | `(tactic| rfl) => `(tactic| exact rfl)
