/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Lean

@[expose] public section

/-! # Checking that no metaprogram changes the environment

`#check_reductions` reads the environment, and a metaprogram can write it: add a declaration that
the kernel never checked (`debug.skipKernelTC`), or copy the compiled code of an honest stub onto a
classical definition (`run_cmd` with `addDecl` and `IR.declMapExt.addEntry`), which the kernel and
`lean4checker` accept. Such a metaprogram leaves nothing in the environment that tells it apart, so
this check reads the sources. It forbids the commands that run code at elaboration time and the
functions that change the environment (`ruleOf`), except where `allowances` permits them.
`scripts/CheckMetaprograms.lean` runs it over the library in CI.

Each file is parsed by Lean's own parser (`parseFile`), not scanned as text, so comments, string
and character literals never count, and identifiers are matched exactly, components included
(`IR.declMapExt.addEntry` is a use of `declMapExt` and of `addEntry`). Parsing needs the notation
that is active at each point of the file, which depends on its `open` commands, so the file is
parsed in the environment of the built library, and the commands `open`, `namespace`, `section`
and `end` are elaborated, which runs no code of the file. No other command is elaborated, so a
`run_cmd` in the file is parsed and reported, never run. A file that does not parse is reported
too.

It is a check against mistakes and casual tricks, not a sandbox: a tactic written with `elab` runs
arbitrary code, and so can a command defined in an imported library, so the library's `elab`
tactics and its dependencies are reviewed by hand.

## Main declarations

* `ruleOf`: the rule, if any, that a token of the syntax tree breaks.
* `violationsInSource`: the report lines for one file's source, given an environment.
* `checkFiles`: the check over a list of files, as CI runs it.
-/

namespace DiagonaLean.Synthetic.MetaprogramCheck

open Lean Elab

/-- A forbidden use: the name that `allowances` refers to, and what such a use does. -/
structure Rule where
  /-- The name that `allowances` refers to. -/
  name : String
  /-- What a use does. -/
  why : String

/-- `run_cmd`, `run_elab`, `run_meta` and `#eval` run code at elaboration time. -/
def runRule : Rule := ⟨"run", "runs code at elaboration time"⟩

/-- `#eval` runs code at elaboration time. -/
def evalRule : Rule := ⟨"eval", "runs code at elaboration time"⟩

/-- `initialize` runs code when the module is loaded. -/
def initializeRule : Rule := ⟨"initialize", "runs code when the module is loaded"⟩

/-- A new command can change the environment. -/
def commandRule : Rule := ⟨"command", "defines a command, which can change the environment"⟩

/-- A `debug.` option, such as `debug.skipKernelTC`, can switch off checks. -/
def debugRule : Rule := ⟨"debug", "sets a debug option, such as `debug.skipKernelTC`"⟩

/-- `unsafe` code escapes the kernel. -/
def unsafeRule : Rule := ⟨"unsafe", "is `unsafe` code"⟩

/-- `implemented_by` and `extern` replace compiled code. -/
def implementedByRule : Rule := ⟨"implemented_by", "replaces compiled code"⟩

/-- `addDecl` and its relatives add a declaration from a metaprogram. -/
def addDeclRule : Rule := ⟨"addDecl", "adds a declaration from a metaprogram"⟩

/-- `modifyEnv` and `setEnv` change the environment from a metaprogram. -/
def modifyEnvRule : Rule := ⟨"modifyEnv", "changes the environment from a metaprogram"⟩

/-- `addEntry`, `modifyState`, `setState` and `declMapExt` change an environment extension. -/
def extensionRule : Rule := ⟨"extension", "changes an environment extension"⟩

/-- `evalConst` and `evalExpr` run code at elaboration time. -/
def evalConstRule : Rule := ⟨"evalConst", "runs code at elaboration time"⟩

/-- The rule that a keyword token breaks, if any. -/
def ruleOfAtom : String → Option Rule
  | "run_cmd" | "run_elab" | "run_meta" => some runRule
  | "#eval" | "#eval!" => some evalRule
  | "initialize" | "builtin_initialize" => some initializeRule
  | "unsafe" => some unsafeRule
  | "implemented_by" | "extern" => some implementedByRule
  | _ => none

/-- The rule that one component of an identifier breaks, if any. Trailing primes are ignored, so
`addDecl'` counts as `addDecl`. -/
def ruleOfComponent (c : String) : Option Rule :=
  match String.ofList (c.toList.reverse.dropWhile (· == '\'')).reverse with
  | "CommandElab" | "CommandElabM" | "command_elab" => some commandRule
  | "implemented_by" | "extern" => some implementedByRule
  | "addDecl" | "addAndCompile" | "compileDecl" | "compileDecls" => some addDeclRule
  | "modifyEnv" | "setEnv" => some modifyEnvRule
  | "addEntry" | "modifyState" | "setState" | "declMapExt" => some extensionRule
  | "evalConst" | "evalExpr" => some evalConstRule
  | _ => none

/-- The string components of a name, outermost first. -/
def nameComponents (n : Name) : List String :=
  n.components.filterMap fun c => match c with
    | .str _ s => some s
    | _ => none

/-- A finding: the rule broken, how the use is shown in the report, and where it starts. -/
structure Finding where
  /-- The rule that is broken. -/
  rule : Rule
  /-- The use, as shown in the report. -/
  shown : String
  /-- The position where the use starts. -/
  pos : String.Pos.Raw

/-- The findings for the identifier `n` at position `pos`: one for each component that breaks a
rule, and one for a dotted name whose first component is `debug`, such as `debug.skipKernelTC`. -/
def findingsOfIdent (n : Name) (pos : String.Pos.Raw) : List Finding :=
  let cs := nameComponents n
  let option := if cs.head? == some "debug" && cs.length > 1 then [⟨debugRule, "debug.", pos⟩]
    else []
  option ++ cs.filterMap fun c => (ruleOfComponent c).map fun r => ⟨r, c, pos⟩

/-- `acc` followed by the atoms and identifiers of `stx`, in source order. -/
partial def leavesAux (acc : Array Syntax) (stx : Syntax) : Array Syntax :=
  match stx with
  | .node _ _ args => args.foldl leavesAux acc
  | .atom .. | .ident .. => acc.push stx
  | .missing => acc

/-- The atoms and identifiers of `stx`, in source order. String, character, number and name
literals are atoms whose text starts with a quote, a digit or a backquote, so they match no rule. -/
def leaves (stx : Syntax) : Array Syntax :=
  leavesAux #[] stx

/-- The findings in the token at index `i` of `ls`: a keyword, an identifier, or a `:` followed by
the identifier `command` (a declaration of new syntax in the command category, reported at the
`:`). -/
def findingsAt (ls : Array Syntax) (i : Nat) : List Finding :=
  let pos := (ls[i]!.getPos? (canonicalOnly := true)).getD 0
  match ls[i]! with
  | .atom _ ":" =>
    match ls[i + 1]? with
    | some (.ident _ _ `command _) => [⟨commandRule, ": command", pos⟩]
    | _ => []
  | .atom _ a => ((ruleOfAtom a).map fun r => ⟨r, a, pos⟩).toList
  | .ident _ _ n _ => findingsOfIdent n pos
  | _ => []

/-- The findings in a syntax tree. -/
def findings (stx : Syntax) : Array Finding :=
  let ls := leaves stx
  (List.range ls.size).foldl (fun acc i => acc ++ (findingsAt ls i).toArray) #[]

/-- The commands that are elaborated while parsing, because they change which notation is active
or which namespace is current. They run no code of the file. -/
def scopeCommands : List Name :=
  [``Parser.Command.open, ``Parser.Command.namespace, ``Parser.Command.section,
    ``Parser.Command.end]

/-- Elaborates the scope command `cmd` in the command state `s`, returning the new state. -/
def elabScopeCommand (inputCtx : Parser.InputContext) (s : Command.State) (cmd : Syntax) :
    IO Command.State := do
  let ctx : Command.Context :=
    { fileName := inputCtx.fileName, fileMap := inputCtx.fileMap, snap? := none, cancelTk? := none }
  match ← ((Command.elabCommand cmd).run ctx |>.run s).toBaseIO with
  | .ok (_, s') => return s'
  | .error e =>
    let msg : Message :=
      { fileName := inputCtx.fileName, pos := inputCtx.fileMap.toPosition (cmd.getPos?.getD 0),
        severity := .error, data := ← e.toMessageData.toString }
    return { s with messages := s.messages.add msg }

/-- The header and commands of `src`, parsed in the environment `env`, with the scope commands
elaborated as they come (`scopeCommands`), and the messages of parsing and of those commands.
Parsing stops at the end of the file or at `#exit`, after which Lean ignores the rest too. An
`import` after the header is an error, and parsing goes on past it, so it cannot hide the rest of
the file. -/
def parseFile (env : Environment) (fileName src : String) : IO (Array Syntax × MessageLog) := do
  let inputCtx := Parser.mkInputContext src fileName
  let (header, mps₀, msgs₀) ← Parser.parseHeader inputCtx
  let mut s := Command.mkState env msgs₀ {}
  let mut mps := mps₀
  let mut cmds := #[header.raw]
  repeat
    let scope := s.scopes.head!
    let pmctx : Parser.ParserModuleContext :=
      { env := s.env, options := scope.opts, currNamespace := scope.currNamespace,
        openDecls := scope.openDecls }
    let (cmd, mps', msgs') := Parser.parseCommand inputCtx pmctx mps s.messages
    mps := mps'
    s := { s with messages := msgs' }
    if cmd.isOfKind ``Parser.Command.eoi || cmd.isOfKind ``Parser.Command.exit then break
    cmds := cmds.push cmd
    if cmd.isOfKind ``Parser.Command.import then
      let msg : Message :=
        { fileName := inputCtx.fileName, severity := .error, data := "`import` after the header",
          pos := inputCtx.fileMap.toPosition (cmd.getPos?.getD 0) }
      s := { s with messages := s.messages.add msg }
    if scopeCommands.contains cmd.getKind then
      s ← elabScopeCommand inputCtx s cmd
  return (cmds, s.messages)

/-- The files, relative to the root, and the rules that they may break. -/
def allowances : List (String × List String) := [
  -- defines `#check_reductions`, whose messages name the escape hatches it reports
  ("DiagonaLean/Synthetic/ReductionCheck.lean", ["command", "unsafe", "implemented_by"]),
  -- not imported by `DiagonaLean.lean`; evaluates a reduction to show that it runs
  ("DiagonaLean/Synthetic/EvalExample.lean", ["eval"]),
  -- defines `derive_primcodable`, which only parses and elaborates generated source text as
  -- ordinary commands; the functions that change the environment directly stay forbidden here
  ("DiagonaLean/Foundations/Computability/DerivePrimcodable.lean", ["command"])]

/-- The rules that the file at `rel` may break. -/
def allowedRules (rel : String) : List String :=
  ((allowances.find? (·.1 == rel)).map (·.2)).getD []

/-- The report lines for the file at `rel` with contents `src`, parsed in the environment `env`:
one line per forbidden use, and one per error from parsing the file. -/
def violationsInSource (env : Environment) (rel src : String) : IO (Array String) := do
  let (cmds, msgs) ← parseFile env rel src
  let fileMap := FileMap.ofString src
  let allowed := allowedRules rel
  let mut out := #[]
  for msg in msgs.toList do
    if msg.severity == .error then
      out := out.push s!"{rel}:{msg.pos.line}: does not parse: {(← msg.data.toString).trimAscii}"
  for cmd in cmds do
    for f in findings cmd do
      if !allowed.contains f.rule.name then
        out := out.push s!"{rel}:{(fileMap.toPosition f.pos).line}: `{f.shown}` {f.rule.why}"
  return out

/-- Checks the files at `paths`, named in reports by their paths relative to the root `root`, in
the environment `env`. Prints every finding and a summary, and returns the number of findings. -/
def checkFiles (env : Environment) (root : System.FilePath) (paths : Array System.FilePath) :
    IO Nat := do
  let mut failures := 0
  for path in paths do
    let rel := (path.toString.drop (root.toString.length + 1)).toString
    for line in ← violationsInSource env rel (← IO.FS.readFile path) do
      IO.println line
      failures := failures + 1
  return failures

end DiagonaLean.Synthetic.MetaprogramCheck
