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
functions that change the environment (`ruleOf`), except where `allowances` permits them. A new
command is permitted only in the declarations that `commandAllowances` names, file by file, so an
allowlisted file cannot gain a second command unnoticed. Rules for existing syntax are forbidden
outside the tactic category (`expanderRule`): a `macro_rules` on `#check_reductions` silences the
check, and one on `¬` changes what every statement written with it says. A library proof also
names its route instead of searching the reduction graph (`searchRule`), so that it does not
depend on what is imported.
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

/-- `macro_rules`, `elab_rules` and the attributes `macro` and `term_elab` add an expansion to
syntax, including syntax declared elsewhere, and an added macro runs before the syntax's own
elaborator; new syntax with a priority wins over existing syntax with the same tokens. On command
syntax this silences a check (`macro_rules | `(#check_reductions local) => `(#print "")`); on term
syntax it changes what a statement says (`macro_rules | `(¬ $p) => `(True ∨ $p)` makes a theorem
that reads `¬ ComputablePred P` state `True ∨ ComputablePred P`). Tactic syntax is not affected:
a proof is checked by the kernel whatever the tactic does. -/
def expanderRule : Rule :=
  ⟨"expander", "changes what existing command or term syntax means, which can silence a check or \
    change what a statement says; only tactic syntax may get new rules or a priority"⟩

/-- The rule that a keyword token breaks, if any. -/
def ruleOfAtom : String → Option Rule
  | "run_cmd" | "run_elab" | "run_meta" => some runRule
  | "#eval" | "#eval!" => some evalRule
  | "initialize" | "builtin_initialize" => some initializeRule
  -- these commands expand to `initialize`
  | "register_label_attr" | "register_simp_attr" | "register_option" => some initializeRule
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
  | "term_elab" | "builtin_term_elab" | "builtin_macro" | "builtin_command_elab" =>
    some expanderRule
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

/-- `undec from P`, `undec from P via?`, `undec?` and `reduction_path` search the reduction graph
when the proof is elaborated, and the graph depends on what is imported and tagged: an import can
change the route a proof takes, or which goals it leaves. A library proof names its route, with
`reduce_from h via r₁, via r₂, …` (or `undec from h via r₁, …`), which `undec?` suggests. Not a
soundness rule: whatever route is found, the kernel checks the proof. -/
def searchRule : Rule :=
  ⟨"search", "searches the reduction graph, so the route depends on the imports; name the route \
    with `reduce_from h via r₁, via r₂, …`, which `undec?` suggests"⟩

/-- The tactics that search the reduction graph, by syntax kind, with the name shown in a report;
`undec from h via r₁, …` (`undecFromVia`) follows a given route and is not one of them. -/
def searchKinds : List (Name × String) :=
  [(`DiagonaLean.Synthetic.Notation.undecFrom, "undec from"),
    (`DiagonaLean.Synthetic.Notation.undecSuggest, "undec?"),
    (`DiagonaLean.Synthetic.ReductionChain.reductionPath, "reduction_path")]

/-- The findings of the `search` rule in `cmd`: each use of a tactic of `searchKinds`. -/
partial def searchFindings (cmd : Syntax) : Array Finding :=
  match cmd with
  | .node _ k args =>
    let here := match searchKinds.lookup k with
      | some shown => #[⟨searchRule, shown, (cmd.getPos? (canonicalOnly := true)).getD 0⟩]
      | none => #[]
    args.foldl (fun acc a => acc ++ searchFindings a) here
  | _ => #[]

/-- The quotations that a `macro_rules` or `elab_rules` pattern may be: tactic syntax only. -/
def tacticQuotKinds : List Name := [``Parser.Tactic.quot, ``Parser.Tactic.quotSeq]

/-- The commands that declare new syntax. With a `(priority := …)`, new term or command syntax
wins over existing syntax with the same tokens, as `macro (priority := high) "¬" p:term:40 : term`
does over `¬`, which is the same hijack as a `macro_rules` (without a priority, the two parses are
ambiguous, which is an error). -/
def syntaxCommandKinds : List Name :=
  [``Parser.Command.syntax, ``Parser.Command.macro, ``Parser.Command.elab,
    ``Parser.Command.notation, ``Parser.Command.mixfix]

/-- The category that the syntax command `s` declares into: the identifier after its last `:`,
or `term` for `notation` and the `infix` family, which have none. -/
def syntaxCategory (s : Syntax) : Name := Id.run do
  let ls := leaves s
  let mut cat := `term
  for h : i in [0:ls.size] do
    if let .atom _ ":" := ls[i] then
      if let some (.ident _ _ n _) := ls[i + 1]? then cat := n
  return cat

/-- The findings of the `expander` rule in the command `cmd`, at any depth, so a command wrapped in
`open … in` or `set_option … in` is seen: each pattern of a `macro_rules` or `elab_rules` that is
not a tactic quotation (a term or command quotation, or a bare variable, which matches any syntax
of its `kind`); each `@[macro k]` attribute, also in an `attribute` command; and each new syntax
outside the tactic category declared with a priority (`syntaxCommandKinds`). Only the match
alternatives of a rules command are read, not a `match` inside a right-hand side. -/
partial def expanderFindings (cmd : Syntax) : Array Finding :=
  go cmd
where
  /-- The position where `s` starts. -/
  pos (s : Syntax) : String.Pos.Raw := (s.getPos? (canonicalOnly := true)).getD 0
  /-- The patterns of an alternative, under the null nodes of `sepBy`, without the commas. -/
  patterns (s : Syntax) : Array Syntax :=
    if s.isOfKind nullKind then s.getArgs.foldl (fun acc a => acc ++ patterns a) #[]
    else if s.isAtom then #[] else #[s]
  /-- The findings in `s` and below. -/
  go (s : Syntax) : Array Finding := Id.run do
    let .node _ k args := s | return #[]
    let mut out := #[]
    let shown? := if k == ``Parser.Command.macro_rules then some "macro_rules"
      else if k == ``Parser.Command.elab_rules then some "elab_rules" else none
    if let some shown := shown? then
      if let some alts := args.find? (·.isOfKind ``Parser.Term.matchAlts) then
        for alt in alts[0].getArgs do
          for pat in patterns alt[1] do
            if !tacticQuotKinds.contains pat.getKind then
              out := out.push ⟨expanderRule, shown, pos pat⟩
    if k == ``Parser.Attr.macro then out := out.push ⟨expanderRule, "@[macro]", pos s⟩
    if syntaxCommandKinds.contains k && syntaxCategory s != `tactic then
      if let some p := s.find? (·.isOfKind ``Parser.Command.namedPrio) then
        out := out.push ⟨expanderRule, "priority", pos p⟩
    for a in args do out := out ++ go a
    return out

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

/-- The files, relative to the root, and the rules that they may break anywhere in the file. The
`command` rule is never allowed for a whole file; see `commandAllowances`. -/
def allowances : List (String × List String) := [
  -- defines `#check_reductions`, whose messages name the escape hatches it reports
  ("DiagonaLean/Synthetic/ReductionCheck.lean", ["unsafe", "implemented_by"]),
  -- not imported by `DiagonaLean.lean`; evaluates a reduction to show that it runs
  ("DiagonaLean/Synthetic/EvalExample.lean", ["eval"]),
  -- `register_label_attr undecReduction` and `register_option undec.showRoute`, which register a
  -- tag and an option and add no declarations
  ("DiagonaLean/Synthetic/Tactics/ReductionPath.lean", ["initialize", "search"]),
  -- `register_label_attr undecHardness`, likewise; and the search tactics are defined here and in
  -- `UndecFrom.lean`, whose elaborators match their syntax
  ("DiagonaLean/Foundations/Computability/UndecTransfer.lean", ["initialize", "search"]),
  ("DiagonaLean/Synthetic/Tactics/UndecFrom.lean", ["search"])]

/-- The files, relative to the root, and the top-level declarations in each that may break the
`command` rule: the command itself and the helpers typed in `CommandElabM`. Each name may be
declared once in its file, so a second declaration with the same name, in another namespace for
instance, is still reported, and so is a command with no name. What these declarations do is not
checked; changes to them are reviewed by hand. -/
def commandAllowances : List (String × List String) := [
  -- `#check_reductions`
  ("DiagonaLean/Synthetic/ReductionCheck.lean", ["checkReductions", "elabCheckReductions"]),
  -- `derive_primcodable`, which only parses and elaborates generated source text as ordinary
  -- commands
  ("DiagonaLean/Foundations/Computability/DerivePrimcodable.lean",
    ["readCtors", "derivePrimcodable"]),
  -- `derive_primrec`, under the same discipline: it elaborates one generated theorem
  ("DiagonaLean/Foundations/Computability/DerivePrimrec.lean", ["readArgs", "derivePrimrec"]),
  -- `halt_results` and `re_results`, macros that expand to theorem and instance commands
  ("DiagonaLean/Foundations/Computability/HaltResults.lean", ["haltResults", "reResults"])]

/-- The rules that the file at `rel` may break anywhere. -/
def allowedRules (rel : String) : List String :=
  ((allowances.find? (·.1 == rel)).map (·.2)).getD []

/-- The declarations of the file at `rel` that may break the `command` rule. -/
def allowedCommandDecls (rel : String) : List String :=
  ((commandAllowances.find? (·.1 == rel)).map (·.2)).getD []

/-- The name that the top-level command `stx` declares, if any: the identifier of a declaration
(`def`, `theorem`, …) or the `(name := …)` of a syntax, `elab` or `macro` command. The first one in
the tree is taken, since both come before the body. -/
partial def declName? (stx : Syntax) : Option String :=
  match stx with
  | .node _ k args =>
    if k == ``Parser.Command.declId || k == ``Parser.Command.namedName then
      args.findSome? fun a => match a with
        | .ident _ _ n _ => some n.toString
        | _ => none
    else args.findSome? declName?
  | _ => none

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
  let commandDecls := allowedCommandDecls rel
  let mut seen : List String := []
  for cmd in cmds do
    let name? := declName? cmd
    let commandOk := match name? with
      | some n => commandDecls.contains n && !seen.contains n
      | none => false
    if let some n := name? then seen := n :: seen
    for f in findings cmd ++ expanderFindings cmd ++ searchFindings cmd do
      let ok := if f.rule.name == commandRule.name then commandOk
        else allowed.contains f.rule.name
      if !ok then
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
