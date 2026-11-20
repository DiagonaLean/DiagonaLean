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
