/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean
import DiagonaLean.Synthetic.MetaprogramCheck

/-! # Tests for the metaprogram check

Run by CI with `lake env lean scripts/CheckMetaprogramsTest.lean`. Each test runs
`violationsInSource` on a small source text, as the file `T.lean` unless stated, and compares its
report lines with `#guard_msgs`. The sources are only parsed, never elaborated, so the forbidden
commands in them do not run.
-/

open Lean Elab Command DiagonaLean.Synthetic.MetaprogramCheck

/-- Logs the report lines for the source `src`, checked as the file `rel`, or `clean` if there are
none. -/
def report (src : String) (rel : String := "T.lean") : CommandElabM Unit := do
  let lines ← violationsInSource (← getEnv) rel src
  logInfo (if lines.isEmpty then "clean" else "\n".intercalate lines.toList)

/-! ### Comments, strings and character literals never count -/

/-- info: clean -/
#guard_msgs in
#eval report "-- run_cmd\n/- addDecl /- nested unsafe -/ still a comment -/\n\
  /-- A docstring that mentions `#eval` and `modifyEnv`. -/\ntheorem t : True := trivial"

/-- info: clean -/
#guard_msgs in
#eval report "def s := \"run_cmd addDecl unsafe debug.skipKernelTC\""

-- An opening comment token inside a string does not open a comment that hides the next line.
/-- info: T.lean:2: `run_cmd` runs code at elaboration time -/
#guard_msgs in
#eval report "def s := \"/-\"\nrun_cmd pure ()\n-- -/"

-- A character literal `'\"'` does not start a string.
/-- info: T.lean:3: `run_cmd` runs code at elaboration time -/
#guard_msgs in
#eval report "def c := '\"'\ndef s := \"/-\"\nrun_cmd pure ()\n-- -/"

/-! ### Identifiers are matched exactly, by component -/

/-- info:
T.lean:1: `addDecl` adds a declaration from a metaprogram
T.lean:2: `declMapExt` changes an environment extension
T.lean:2: `addEntry` changes an environment extension
T.lean:3: `addDecl` adds a declaration from a metaprogram
T.lean:4: `addDecl'` adds a declaration from a metaprogram
T.lean:5: `evalConst` runs code at elaboration time -/
#guard_msgs in
#eval report "def a := Lean.addDecl\ndef b := IR.declMapExt.addEntry\ndef c := «addDecl»\n\
  def d := x.addDecl'\ndef e := evalConst"

-- A longer identifier, or one that runs into a non-ASCII letter, is a different name.
/-- info: clean -/
#guard_msgs in
#eval report "def myaddDecl := 1\ndef τaddDecl := 2\ndef debug := 3\ndef x := debug"

/-! ### Each rule -/

/-- info:
T.lean:1: `#eval` runs code at elaboration time
T.lean:2: `run_elab` runs code at elaboration time
T.lean:3: `initialize` runs code when the module is loaded
T.lean:4: `debug.` sets a debug option, such as `debug.skipKernelTC`
T.lean:5: `unsafe` is `unsafe` code
T.lean:6: `implemented_by` replaces compiled code
T.lean:7: `CommandElab` defines a command, which can change the environment
T.lean:8: `modifyEnv` changes the environment from a metaprogram -/
#guard_msgs in
#eval report "#eval 1\nrun_elab pure ()\ninitialize foo : Nat ← pure 1\n\
  set_option debug.skipKernelTC true in theorem t : True := trivial\nunsafe def u := 1\n\
  @[implemented_by u] def v := 1\ndef w : CommandElab := fun _ => pure ()\ndef m := modifyEnv"

-- Commands that expand to `initialize` count as `initialize`.
/-- info:
T.lean:1: `register_label_attr` runs code when the module is loaded
T.lean:2: `register_option` runs code when the module is loaded -/
#guard_msgs in
#eval report "register_label_attr foo\nregister_option bar : Bool := { defValue := false }"

-- A new command is reported at its `:`, also when `command` is on the next line.
/-- info:
T.lean:1: `: command` defines a command, which can change the environment
T.lean:2: `: command` defines a command, which can change the environment -/
#guard_msgs in
#eval report "elab \"foo\" : command => pure ()\nelab \"bar\" :\n  command => pure ()"

-- A new tactic is not a command.
/-- info: clean -/
#guard_msgs in
#eval report "macro \"foo\" : tactic => `(tactic| rfl)"

/-! ### Parsing follows the file's scopes -/

-- Scoped notation parses after `open scoped`.
/-- info: clean -/
#guard_msgs in
#eval report "open scoped Computability\ndef x (L : Language Bool) : Language Bool := L∗"

-- Without the `open`, the file does not parse, and that is reported.
/-- info: T.lean:1: does not parse: expected token -/
#guard_msgs in
#eval report "def x (L : Language Bool) : Language Bool := L∗"

-- An `import` after the header is reported, with the parse error on the module name after it, and
-- the rest of the file is still checked.
/-- info:
T.lean:2: does not parse: `import` after the header
T.lean:2: does not parse: unexpected identifier; expected command
T.lean:3: `run_cmd` runs code at elaboration time -/
#guard_msgs in
#eval report "def a := 1\nimport Lean\nrun_cmd pure ()"

/-! ### The allowlist -/

/-- info: clean -/
#guard_msgs in
#eval report "#eval 1" (rel := "DiagonaLean/Synthetic/EvalExample.lean")

-- The allowlist is per rule: the same file may not use `run_cmd`.
/-- info: DiagonaLean/Synthetic/EvalExample.lean:1: `run_cmd` runs code at elaboration time -/
#guard_msgs in
#eval report "run_cmd pure ()" (rel := "DiagonaLean/Synthetic/EvalExample.lean")

/-! ### Commands are allowed per declaration -/

-- The named command of an allowlisted file and its helper are allowed.
/-- info: clean -/
#guard_msgs in
#eval report "def readArgs : CommandElabM Unit := pure ()\n\
  elab (name := derivePrimrec) \"derive_primrec\" : command => pure ()"
  (rel := "DiagonaLean/Foundations/Computability/DerivePrimrec.lean")

-- A second command in the same file is reported, named or not.
/-- info:
DiagonaLean/Foundations/Computability/DerivePrimrec.lean:2: `: command` defines a command, which can change the environment
DiagonaLean/Foundations/Computability/DerivePrimrec.lean:3: `: command` defines a command, which can change the environment -/
#guard_msgs in
#eval report "elab (name := derivePrimrec) \"derive_primrec\" : command => pure ()\n\
  elab (name := evil) \"evil\" s:str : command => pure ()\nelab \"evil2\" : command => pure ()"
  (rel := "DiagonaLean/Foundations/Computability/DerivePrimrec.lean")

-- Reusing an allowed name, here in another namespace, is reported.
/-- info: DiagonaLean/Foundations/Computability/DerivePrimrec.lean:3: `: command` defines a command, which can change the environment -/
#guard_msgs in
#eval report "elab (name := derivePrimrec) \"a\" : command => pure ()\nnamespace X\n\
  elab (name := derivePrimrec) \"b\" : command => pure ()\nend X"
  (rel := "DiagonaLean/Foundations/Computability/DerivePrimrec.lean")

-- An allowed declaration may define a command, but the other rules still apply inside it.
/-- info: DiagonaLean/Foundations/Computability/DerivePrimrec.lean:1: `modifyEnv` changes the environment from a metaprogram -/
#guard_msgs in
#eval report "elab (name := derivePrimrec) \"a\" : command => modifyEnv id"
  (rel := "DiagonaLean/Foundations/Computability/DerivePrimrec.lean")

-- A declaration allowed in one file is not allowed in another.
/-- info: T.lean:1: `: command` defines a command, which can change the environment -/
#guard_msgs in
#eval report "elab (name := derivePrimrec) \"a\" : command => pure ()"

/-! ### Rules for existing command or term syntax (the `expander` rule)

A `macro_rules` on `#check_reductions local` silenced the check, and one on `¬` made a theorem
that reads `¬ ComputablePred P` state `True ∨ ComputablePred P`; neither was reported before
2026-11-26. Rules on tactic syntax stay allowed: the kernel checks every proof. -/

/-- info:
T.lean:1: `macro_rules` changes what existing command or term syntax means, which can silence a check or change what a statement says; only tactic syntax may get new rules or a priority
T.lean:2: `macro_rules` changes what existing command or term syntax means, which can silence a check or change what a statement says; only tactic syntax may get new rules or a priority
T.lean:3: `elab_rules` changes what existing command or term syntax means, which can silence a check or change what a statement says; only tactic syntax may get new rules or a priority -/
#guard_msgs in
#eval report "macro_rules | `(#check_reductions local) => `(#print \"x\")\n\
  macro_rules | `(¬ $p) => `(True ∨ $p)\n\
  elab_rules : term | `(¬ $p) => pure (Lean.mkConst ``True)"

-- Wrapped in `open … in` or `set_option … in`, `local`, or as the second pattern of an alternative.
/-- info:
T.lean:1: `macro_rules` changes what existing command or term syntax means, which can silence a check or change what a statement says; only tactic syntax may get new rules or a priority
T.lean:2: `macro_rules` changes what existing command or term syntax means, which can silence a check or change what a statement says; only tactic syntax may get new rules or a priority
T.lean:3: `macro_rules` changes what existing command or term syntax means, which can silence a check or change what a statement says; only tactic syntax may get new rules or a priority
T.lean:4: `macro_rules` changes what existing command or term syntax means, which can silence a check or change what a statement says; only tactic syntax may get new rules or a priority -/
#guard_msgs in
#eval report "open Lean in macro_rules | `(¬ $p) => `(True ∨ $p)\n\
  set_option hygiene false in macro_rules | `(¬ $p) => `(True ∨ $p)\n\
  local macro_rules | `(¬ $p) => `(True ∨ $p)\n\
  macro_rules | `(tactic| rfl), `(¬ $p) => `(tactic| rfl)"

-- A bare variable as the pattern matches any syntax of the `kind`.
/-- info: T.lean:1: `macro_rules` changes what existing command or term syntax means, which can silence a check or change what a statement says; only tactic syntax may get new rules or a priority -/
#guard_msgs in
#eval report "macro_rules (kind := Lean.Parser.Command.check) | stx => pure stx"

-- The `macro` and `term_elab` attributes, also through the `attribute` command.
/-- info:
T.lean:1: `@[macro]` changes what existing command or term syntax means, which can silence a check or change what a statement says; only tactic syntax may get new rules or a priority
T.lean:2: `term_elab` changes what existing command or term syntax means, which can silence a check or change what a statement says; only tactic syntax may get new rules or a priority
T.lean:3: `@[macro]` changes what existing command or term syntax means, which can silence a check or change what a statement says; only tactic syntax may get new rules or a priority -/
#guard_msgs in
#eval report "@[macro Lean.Parser.Term.paren] def m : Lean.Macro := fun _ => Lean.Macro.throwUnsupported\n\
  @[term_elab Lean.Parser.Term.paren] def m2 : Lean.Elab.Term.TermElab := fun _ _ => throwError \"x\"\n\
  attribute [macro Lean.Parser.Term.paren] m"

-- New term syntax with a priority wins over existing syntax with the same tokens.
/-- info:
T.lean:1: `priority` changes what existing command or term syntax means, which can silence a check or change what a statement says; only tactic syntax may get new rules or a priority
T.lean:2: `priority` changes what existing command or term syntax means, which can silence a check or change what a statement says; only tactic syntax may get new rules or a priority -/
#guard_msgs in
#eval report "macro (priority := high) \"¬\" p:term:40 : term => `(True ∨ $p)\n\
  notation (priority := high) \"¬\" p:40 => True ∨ p"

-- Rules and priorities on tactic syntax, and new term syntax without a priority, are allowed.
/-- info: clean -/
#guard_msgs in
#eval report "macro_rules | `(tactic| rfl) => `(tactic| exact rfl)\n\
  syntax (priority := high) \"my_tac\" : tactic\n\
  notation:50 a \" ≈≈ \" b => a = b"
