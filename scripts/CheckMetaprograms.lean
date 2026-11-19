/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

/-! # Checking that no metaprogram changes the environment

Run by CI as `lake env lean --run scripts/CheckMetaprograms.lean [ROOT]`, where `ROOT` is the
repository root and defaults to the current directory.

`#check_reductions` reads the environment, and a metaprogram can write it: add a declaration that
the kernel never checked (`debug.skipKernelTC`), or copy the compiled code of an honest stub onto a
classical definition (`run_cmd` with `addDecl` and `IR.declMapExt.addEntry`), which the kernel and
`lean4checker` accept. Such a metaprogram leaves no trace in the environment that tells it apart, so
this check reads the sources: it forbids, outside comments, the commands that run code at
elaboration time and the functions that change the environment (`rules`), except where
`allowances` permits them. A word counts when it is not part of a longer run of ASCII letters,
digits and underscores. It is a check against mistakes and casual tricks, not a sandbox: a tactic
written with `elab` runs arbitrary code, so the library's `elab` tactics are reviewed by hand.

The sources are scanned, not parsed: Lean's parser needs the scoped notation of each file, which
only elaborating the file activates, and elaborating would run the metaprograms the check is for.

The fixture `scripts/metaprogram-fixture` must be rejected.
-/

open System

/-- How a forbidden word is recognized. -/
inductive Context where
  /-- The word on its own. -/
  | plain
  /-- The word right after `#`, as in `#eval`. -/
  | afterHash
  /-- The word right before `.`, as in `debug.skipKernelTC`. -/
  | beforeDot
  /-- The word after `:` and whitespace, as in `elab : command`. -/
  | afterColon

/-- A forbidden use: its name, the words that trigger it, how they are recognized, and what such a
use does. -/
structure Rule where
  /-- The name that `allowances` refers to. -/
  name : String
  /-- The words that trigger the rule. -/
  words : List String
  /-- How the words are recognized. -/
  context : Context := .plain
  /-- What a use does. -/
  why : String

/-- The forbidden uses. -/
def rules : List Rule := [
  { name := "run", words := ["run_cmd", "run_elab", "run_meta"],
    why := "runs code at elaboration time" },
  { name := "eval", words := ["eval"], context := .afterHash,
    why := "runs code at elaboration time" },
  { name := "initialize", words := ["initialize", "builtin_initialize"],
    why := "runs code when the module is loaded" },
  { name := "command", words := ["command"], context := .afterColon,
    why := "defines a command, which can change the environment" },
  { name := "command", words := ["CommandElab", "CommandElabM", "command_elab"],
    why := "defines a command, which can change the environment" },
  { name := "debug", words := ["debug"], context := .beforeDot,
    why := "sets a debug option, such as `debug.skipKernelTC`" },
  { name := "unsafe", words := ["unsafe"], why := "is `unsafe` code" },
  { name := "implemented_by", words := ["implemented_by", "extern"],
    why := "replaces compiled code" },
  { name := "addDecl", words := ["addDecl", "addAndCompile", "compileDecl", "compileDecls"],
    why := "adds a declaration from a metaprogram" },
  { name := "modifyEnv", words := ["modifyEnv", "setEnv"],
    why := "changes the environment from a metaprogram" },
  { name := "extension", words := ["addEntry", "modifyState", "setState", "declMapExt"],
    why := "changes an environment extension" },
  { name := "evalConst", words := ["evalConst", "evalExpr"],
    why := "runs code at elaboration time" }]

/-- The files, relative to the root, and the rules that they may break. -/
def allowances : List (String × List String) := [
  -- defines `#check_reductions`, whose messages name the escape hatches it reports
  ("DiagonaLean/Synthetic/ReductionCheck.lean", ["command", "unsafe", "implemented_by"]),
  -- not imported by `DiagonaLean.lean`; evaluates a reduction to show that it runs
  ("DiagonaLean/Synthetic/EvalExample.lean", ["eval"])]

/-- The rules that the file at `rel` may break. -/
def allowedRules (rel : String) : List String :=
  ((allowances.find? (·.1 == rel)).map (·.2)).getD []

/-- The characters left after skipping the rest of a `--` comment, with a space for each skipped
character; the line break that ends the comment is kept. -/
def skipLineComment : List Char → List Char × List Char
  | [] => ([], [])
  | '\n' :: rest => ([], '\n' :: rest)
  | _ :: rest => let (spaces, rest') := skipLineComment rest; (' ' :: spaces, rest')

/-- Skipping a `--` comment does not make the list longer. -/
theorem skipLineComment_length (cs : List Char) : (skipLineComment cs).2.length ≤ cs.length := by
  induction cs with
  | nil => simp [skipLineComment]
  | cons c rest ih =>
    by_cases h : c = '\n'
    · subst h; simp [skipLineComment]
    · simp [skipLineComment]; omega

/-- `cs` with `--` comments and nested `/- -/` comments, docstrings included, blanked out, given
the current comment depth and whether the scan is inside a string literal. Line breaks are kept, so
line numbers do not change. String literals are kept. -/
def stripAux : List Char → Nat → Bool → List Char
  | [], _, _ => []
  | '\\' :: c :: rest, 0, true => '\\' :: c :: stripAux rest 0 true
  | '"' :: rest, 0, true => '"' :: stripAux rest 0 false
  | c :: rest, 0, true => c :: stripAux rest 0 true
  | '"' :: rest, 0, false => '"' :: stripAux rest 0 true
  | '/' :: '-' :: rest, d, false => ' ' :: ' ' :: stripAux rest (d + 1) false
  | '-' :: '/' :: rest, d + 1, false => ' ' :: ' ' :: stripAux rest d false
  | c :: rest, d + 1, false => (if c == '\n' then '\n' else ' ') :: stripAux rest (d + 1) false
  | '-' :: '-' :: rest, 0, false =>
    ' ' :: ' ' :: (skipLineComment rest).1 ++ stripAux (skipLineComment rest).2 0 false
  | c :: rest, d, s => c :: stripAux rest d s
termination_by cs => cs.length
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have := skipLineComment_length rest; simp_all; omega

/-- `src` with comments blanked out (see `stripAux`). -/
def stripComments (src : String) : Array Char :=
  (stripAux src.toList 0 false).toArray

/-- Whether `c` is part of a word: an ASCII letter, digit or underscore. -/
def isWordChar (c : Char) : Bool :=
  c.isAlphanum || c == '_'

/-- The last character before position `i` of `cs` that is not whitespace, if `i` is preceded by
whitespace and then that character. Returns `none` if there is no whitespace before `i`. -/
def charBeforeSpace (cs : Array Char) (i : Nat) : Option Char := Id.run do
  let mut j := i
  while j > 0 && cs[j - 1]!.isWhitespace do
    j := j - 1
  if j == i || j == 0 then return none
  return some cs[j - 1]!

/-- Whether the word `cs[i:k]` occurs in the context `ctx`. -/
def inContext (cs : Array Char) (i k : Nat) : Context → Bool
  | .plain => true
  | .afterHash => i > 0 && cs[i - 1]! == '#'
  | .beforeDot => k < cs.size && cs[k]! == '.'
  | .afterColon => charBeforeSpace cs i == some ':'

/-- How a match of `rule` on the word `w` is shown in a report. -/
def shown (rule : Rule) (w : String) : String :=
  match rule.context with
  | .plain => w
  | .afterHash => "#" ++ w
  | .beforeDot => w ++ "."
  | .afterColon => ": " ++ w

/-- The words of `cs`, each with its start, its end and its line, numbered from `1`. -/
def words (cs : Array Char) : Array (String × Nat × Nat × Nat) := Id.run do
  let mut out := #[]
  let mut i := 0
  let mut line := 1
  while i < cs.size do
    let c := cs[i]!
    if isWordChar c then
      let mut k := i
      while k < cs.size && isWordChar cs[k]! do
        k := k + 1
      out := out.push (String.ofList (cs.extract i k).toList, i, k, line)
      i := k
    else
      if c == '\n' then line := line + 1
      i := i + 1
  return out

/-- The report lines for the forbidden uses in the file at `rel` with contents `src`. -/
def violations (rel src : String) : Array String := Id.run do
  let cs := stripComments src
  let allowed := allowedRules rel
  let mut out := #[]
  for (w, i, k, line) in words cs do
    for rule in rules do
      if !allowed.contains rule.name && rule.words.contains w && inContext cs i k rule.context then
        out := out.push s!"{rel}:{line}: `{shown rule w}` {rule.why}"
  return out

/-- `path` with the directory `root` removed from its front. -/
def relativeTo (root path : FilePath) : String :=
  (path.toString.drop (root.toString.length + 1)).toString

/-- The files checked: the `.lean` files under `ROOT/DiagonaLean/`, and `ROOT/DiagonaLean.lean`. -/
def checkedFiles (root : FilePath) : IO (Array FilePath) := do
  let paths ← (root / "DiagonaLean").walkDir
  let files := (paths.filter (·.extension == some "lean")).qsort (·.toString < ·.toString)
  return files.push (root / "DiagonaLean.lean")

/-- Checks the repository at the root given as the first argument, prints every forbidden use,
and returns `1` if there is one. -/
def main (args : List String) : IO UInt32 := do
  let root : FilePath := args.headD "."
  let files ← checkedFiles root
  let mut failures := 0
  for path in files do
    for msg in violations (relativeTo root path) (← IO.FS.readFile path) do
      IO.println msg
      failures := failures + 1
  if failures == 0 then
    IO.println s!"check_metaprograms: {files.size} files checked, no forbidden uses"
    return 0
  IO.println s!"check_metaprograms: {failures} forbidden uses; see the module docstring of \
    scripts/CheckMetaprograms.lean"
  return 1
