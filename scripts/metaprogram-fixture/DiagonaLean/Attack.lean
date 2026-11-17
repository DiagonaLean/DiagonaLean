/-! Fixture for `scripts/check_metaprograms.py`, run by CI, which must reject it. Not built.

A classical reduction that `#check_reductions` accepts: `run_cmd` adds it with `addDecl`, which
the kernel checks, and copies the compiled code of an honest stub to it, so it is safe, not
`noncomputable` and compiled. `lean4checker` accepts it too. And a theorem the kernel never checks.
Mentions in comments, such as run_cmd, addDecl or unsafe here, must not be reported. -/

import DiagonaLean.Synthetic.Undecidability

open DiagonaLean.Halt DiagonaLean.Halt.Encoding DiagonaLean.Synthetic.Definitions
  DiagonaLean.Synthetic.Notation Lean Elab Command

theorem classicalFn : ∃ f : EncodableTM Bool × List Bool → ℕ, HaltProblem ⪯ₘ[f] fun n => Even n := by
  classical
  exact ⟨fun p => if HaltProblem p then 0 else 1, fun p => by
    by_cases h : HaltProblem p <;> simp [h, Nat.not_even_one]⟩

/-- The code that runs in place of the reduction. -/
def stubFn : EncodableTM Bool × List Bool → ℕ := fun _ => 0

run_cmd do
  let ty ← liftTermElabM do
    instantiateMVars (← Term.elabTermAndSynthesize (← `(Undecidable fun n : ℕ => Even n)) none)
  let val ← liftTermElabM do
    instantiateMVars
      (← Term.elabTermAndSynthesize (← `(⟨classicalFn.choose, classicalFn.choose_spec⟩)) ty)
  liftCoreM <| addDecl <| .defnDecl
    { name := `injected, levelParams := [], type := ty, value := val,
      hints := .abbrev, safety := .safe }
  let some d := IR.findEnvDecl (← getEnv) ``stubFn | throwError "no IR"
  let d' : IR.Decl := match d with
    | .fdecl _ xs t b i => .fdecl `injected xs t b i
    | e => e
  modifyEnv (IR.declMapExt.addEntry · d')

set_option debug.skipKernelTC true in
theorem unchecked : False := sorry
