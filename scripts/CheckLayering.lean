/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Lean

/-! # Checking that `Foundations` depends on no problem folder

Run by CI as `lake env lean --run scripts/CheckLayering.lean [ROOT]`, where `ROOT` is the
repository root and defaults to the current directory.

`DiagonaLean/Foundations/` holds general results that problem folders build on, so it may depend
only on itself and on the base the problem folders share: `Synthetic` (the notions of reduction and
undecidability) and `Halt` (the source problem). The check reads the imports of every file under
`ROOT/DiagonaLean/` with Lean's header parser (`Lean.parseImports`) and follows them transitively,
so importing a `Synthetic` module that imports `PCP` also fails. Code that only one problem uses
belongs in that problem's folder, as `KAComm/KleeneAlgebra/` does.

The source files are read, not the built modules, so the check needs no build and also runs on the
fixture `scripts/layering-fixture`, which it must reject.
-/

open Lean System

/-- The layer that is checked. -/
def layer : Name := `DiagonaLean.Foundations

/-- The top-level folders that `layer` may depend on, besides itself. -/
def allowedFolders : List Name :=
  [`DiagonaLean.Foundations, `DiagonaLean.Synthetic, `DiagonaLean.Halt]

/-- The top-level folder of a module: its first two name components. -/
def folder (m : Name) : Name :=
  match m.components with
  | a :: b :: _ => a ++ b
  | _ => m

/-- The module name of a file, given its path relative to the root, such as
`DiagonaLean/Halt/Basic.lean` for `DiagonaLean.Halt.Basic`. -/
def moduleOf (rel : FilePath) : Name :=
  (rel.withExtension "").components.foldl Name.str .anonymous

/-- `path` with the directory `root` removed from its front. -/
def relativeTo (root path : FilePath) : FilePath :=
  ⟨(path.toString.drop (root.toString.length + 1)).toString⟩

/-- The `.lean` files under `ROOT/DiagonaLean/`, each with its module name. -/
def leanFiles (root : FilePath) : IO (Array (Name × FilePath)) := do
  let paths ← (root / "DiagonaLean").walkDir
  let files := paths.filter (·.extension == some "lean")
  return files.map fun p => (moduleOf (relativeTo root p), p)

/-- The `DiagonaLean` modules that the file at `path` imports. Fails if the header does not
parse. -/
def importsOf (path : FilePath) : IO (Array Name) := do
  let (imports, _, log) ← Elab.parseImports (← IO.FS.readFile path) path.toString
  if log.hasErrors then
    throw <| IO.userError s!"{path}: the header does not parse"
  return (imports.map (·.module)).filter (·.getRoot == `DiagonaLean)

/-- The chain of imports from `start` to `m`, read off the map `parent` from each module reached
to the module it was reached from. -/
partial def chainTo (parent : Std.HashMap Name Name) (start m : Name) : List Name :=
  if m == start then [start]
  else match parent[m]? with
    | some p => chainTo parent start p ++ [m]
    | none => [m]

/-- The forbidden dependencies of `start`: for each module outside `allowedFolders` that `start`
reaches through modules inside them, the chain of imports that reaches it. The search is
breadth-first, so each chain is a shortest one. -/
def violations (graph : Std.HashMap Name (Array Name)) (start : Name) : Array (List Name) :=
  Id.run do
    let mut parent : Std.HashMap Name Name := {}
    let mut seen : Std.HashSet Name := ({} : Std.HashSet Name).insert start
    let mut queue : Array Name := #[start]
    let mut next := 0
    let mut found : Array (List Name) := #[]
    while next < queue.size do
      let m := queue[next]!
      next := next + 1
      for dep in graph.getD m #[] do
        if seen.contains dep then continue
        seen := seen.insert dep
        parent := parent.insert dep m
        if allowedFolders.contains (folder dep) then
          queue := queue.push dep
        else
          found := found.push (chainTo parent start dep)
    return found

/-- The report line for a forbidden chain of imports from `start`. -/
def report (start : Name) (chain : List Name) : String :=
  let dep := chain.getLastD start
  s!"{start} depends on {folder dep}: " ++ " -> ".intercalate (chain.map toString)

/-- Checks the repository at the root given as the first argument, prints every forbidden
dependency, and returns `1` if there is one. -/
def main (args : List String) : IO UInt32 := do
  let root : FilePath := args.headD "."
  let files ← leanFiles root
  let mut graph : Std.HashMap Name (Array Name) := {}
  for (m, path) in files do
    graph := graph.insert m (← importsOf path)
  let starts := ((files.map (·.1)).filter (folder · == layer)).qsort (·.toString < ·.toString)
  let mut errors : Array String := #[]
  for start in starts do
    for chain in violations graph start do
      errors := errors.push (report start chain)
  for e in errors do
    IO.println e
  if errors.isEmpty then
    IO.println s!"check_layering: {starts.size} modules in {layer} checked, no forbidden \
      dependencies"
    return 0
  let noun := if errors.size == 1 then "dependency" else "dependencies"
  let folders := ", ".intercalate ((allowedFolders.map toString).mergeSort (· < ·))
  IO.println s!"check_layering: {errors.size} forbidden {noun}; {layer} may depend only on \
    {folders}"
  return 1
