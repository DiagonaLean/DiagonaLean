import DiagonaLean

/-! # The library makes no new keyword by accident

Run by CI with `lake env lean scripts/ReservedWordsTest.lean`. A word in a `syntax`, `macro`,
`elab` or `notation` declaration, such as `" unfold"`, becomes a *reserved* keyword: no file that
imports the library can then use it as a name, so `fun unfold => …` or `| unfold =>` fails to
parse far from the cause (this broke a `match` in `KAComm` once). A word that should stay usable
as a name is written as a non-reserved token, `&"unfold"`. (Lean does this itself for the first
word of a tactic, which is why `reduce_from` is not reported.)

The check reads every symbol of the library's syntax declarations (their `ParserDescr` values),
keeps the word-like ones, and reports each that no longer parses as an identifier and is not in
`knownKeywords`.
-/

open Lean Parser

/-- The word-like keywords that the library's syntax may use: Lean's own, the names of the
library's commands (a command's first word is always reserved), and two tactic words reviewed on
2026-11-26. `via` and `over_letters` stay reserved because making them non-reserved changes how
`halt_results … over_letters` and the `reduceLink` category parse; no file uses them as names. -/
def knownKeywords : List String :=
  ["for", "from", "local", "using", "with",
    "derive_primcodable", "derive_primrec", "halt_results", "re_results",
    "via", "over_letters"]

/-- The symbols of a `ParserDescr` term, each with whether it is reserved. -/
partial def descrSymbols (e : Expr) : List (String × Bool) :=
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``ParserDescr.symbol, #[.lit (.strVal s)] => [(s.trimAscii.toString, true)]
  | some ``ParserDescr.nonReservedSymbol, #[.lit (.strVal s), _] =>
    [(s.trimAscii.toString, false)]
  | some ``ParserDescr.unicodeSymbol, #[.lit (.strVal s), _, _] => [(s.trimAscii.toString, true)]
  | _, args => args.toList.flatMap descrSymbols

/-- `s` looks like an identifier: a letter, then letters, digits and underscores. -/
def wordLike (s : String) : Bool :=
  match s.toList with
  | c :: cs => c.isAlpha && cs.all fun c => c.isAlphanum || c == '_'
  | [] => false

/-- The reserved words of the syntax declared by the library's modules, and by the current file
if `includeLocal`, that do not parse as identifiers and are not in `knownKeywords`, each with a
declaration that uses it. -/
def newKeywords (env : Environment) (includeLocal : Bool) : List (String × Name) := Id.run do
  let mods := env.allImportedModuleNames
  let mut words : Std.HashMap String Name := {}
  for (n, ci) in env.constants.toList do
    let fromLibrary := match env.getModuleIdxFor? n with
      | some i => (`DiagonaLean).isPrefixOf (mods[i.toNat]?.getD .anonymous)
      | none => includeLocal
    unless fromLibrary do continue
    let .defnInfo d := ci | continue
    unless d.type.isConstOf ``ParserDescr || d.type.isConstOf ``TrailingParserDescr do continue
    for (s, reserved) in descrSymbols d.value do
      if reserved && wordLike s && !knownKeywords.contains s && !words.contains s then
        words := words.insert s n
  return words.toList.filter (fun (w, _) => !(runParserCategory env `term s!"fun {w} => {w}").isOk)
    |>.mergeSort (·.1 < ·.1)

/-- Logs the new keywords, or `clean`. -/
def reportKeywords (includeLocal : Bool) : Elab.Command.CommandElabM Unit := do
  let ws := newKeywords (← getEnv) includeLocal
  logInfo (if ws.isEmpty then "clean" else "\n".intercalate (ws.map fun (w, n) =>
    s!"`{w}` (in `{n}`) is now a reserved keyword, so no importing file can use it as a name; \
      write it as `&\"{w}\"` in the syntax, or add it to `knownKeywords` after review"))

/-! ### The library -/

/-- info: clean -/
#guard_msgs in
#eval reportKeywords false

/-! ### The check sees a new reserved word

The second word of this tactic is reserved; the first is not, since Lean makes the first word of
a tactic non-reserved. -/

syntax "frob_lead" "frob_inner" term : tactic
syntax "frob_ok" &"frob_nonreserved" term : tactic

/-- info: `frob_inner` (in `tacticFrob_leadFrob_inner_`) is now a reserved keyword, so no importing file can use it as a name; write it as `&"frob_inner"` in the syntax, or add it to `knownKeywords` after review -/
#guard_msgs in
#eval reportKeywords true
