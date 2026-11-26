import DiagonaLean.Foundations.Computability.Upgrade
import DiagonaLean.MPCP.Hardness
import DiagonaLean.PCP.Primrec
import DiagonaLean.PCP.Undecidable
import DiagonaLean.MatMort.MachineLevel
import DiagonaLean.MatMort.Undecidable
import DiagonaLean.SKIConv.Undecidable

/-! Tests for `upgrade`, run by CI: the cut by name, by hypothesis and by `HaltSource`, the goals
left on the links after the cut, and the errors. -/

open DiagonaLean.Foundations.Computability DiagonaLean.Synthetic.Definitions
  DiagonaLean.PCP.Reduction DiagonaLean.MPCP.Reduction DiagonaLean.PCP.AlphabetLift
  DiagonaLean.MatMort.Reduction

/-- The alphabet of the MPCP and PCP instances built from machines. -/
abbrev A := Alpha ℕ DiagonaLean.Foundations.Computability.Normalize.Sym2

/-- PCP over `S23`, which has no `HaltSource`. -/
abbrev PCPS23 := @DiagonaLean.PCP.DecisionProblem S23

/-- A bundled link from MPCP to PCP. -/
def mpcpLink :
    @DiagonaLean.MPCP.DecisionProblem A ⪯_s @DiagonaLean.PCP.DecisionProblem (Ext A) :=
  ⟨fun x => mpcpToPcp x.1 x.2, mpcp_reducesto_pcp_spec⟩

/-! ### The whole reduction has a proved counterpart: `MatMort.fromHalt`, no goal -/

example : HaltReduction DiagonaLean.MatMort.DecisionProblem := by
  upgrade DiagonaLean.MatMort.synthFromHalt

example : ¬ ComputablePred DiagonaLean.MatMort.DecisionProblem := by
  upgrade DiagonaLean.MatMort.synthFromHalt

/-- By name, with the same explicit arguments: `PCP.fromHaltOver 0 1 _`. -/
example : HaltHard PCPS23 := by
  upgrade (DiagonaLean.PCP.synthFromHaltOver (0 : S23) 1 (by decide))

/-! ### A chain with no counterpart: cut at `MPCP.fromHalt`, two links upgraded by `fun_prop` -/

/-- MPCP, then a bundled link, then the change of alphabet. -/
def synthChain : SynthHaltReduction PCPS23 := by
  synth_reduce_from DiagonaLean.MPCP.synthFromHalt via mpcpLink,
    with (liftInstance (0 : S23) 1) using (pcp_alphabet_lift_spec 0 1 (by decide))

example : HaltReduction PCPS23 := by
  upgrade synthChain

example {enc : DiagonaLean.PCP.Stack S23 → List Bool} (henc : Computable enc) :
    ¬ MachineDecidable enc PCPS23 := by
  upgrade synthChain

/-- A hypothesis cuts the chain later: only the change of alphabet is upgraded. -/
example (h : HaltReduction (@DiagonaLean.PCP.DecisionProblem (Ext A))) :
    HaltReduction PCPS23 := by
  upgrade synthChain

/-! ### A goal left open, tagged after the function -/

/-- The change of alphabet under a name without a `fun_prop` lemma. -/
def plainL : DiagonaLean.PCP.Stack (Ext A) → DiagonaLean.PCP.Stack S23 := liftInstance 0 1

/-- The chain of `synthChain`, through `plainL`. -/
def synthPlain : SynthHaltReduction PCPS23 := by
  synth_reduce_from DiagonaLean.MPCP.synthFromHalt via mpcpLink,
    with plainL using (pcp_alphabet_lift_spec 0 1 (by decide))

example : HaltReduction PCPS23 := by
  upgrade synthPlain
  case computable_plainL => exact (liftInstance_primrec (0 : S23) 1).to_comp

/-! ### Errors -/

/-- Mortality with a trivial conjunct: a problem with no proved halting reduction. -/
def MortT (x : Finset (Matrix (Fin 3) (Fin 3) ℤ)) : Prop :=
  DiagonaLean.MatMort.DecisionProblem x ∧ True

/-- Mortality of the value at `0` of a function on `ℕ`: a type with no `Primcodable` instance. -/
def MortFn (g : ℕ → Finset (Matrix (Fin 3) (Fin 3) ℤ)) : Prop :=
  DiagonaLean.MatMort.DecisionProblem (g 0)

/-- A matrix set as a constant function on `ℕ`. -/
def toFn (x : Finset (Matrix (Fin 3) (Fin 3) ℤ)) : ℕ → Finset (Matrix (Fin 3) (Fin 3) ℤ) :=
  fun _ => x

/-- The value at `0`. -/
def atZero (g : ℕ → Finset (Matrix (Fin 3) (Fin 3) ℤ)) : Finset (Matrix (Fin 3) (Fin 3) ℤ) := g 0

/-- `toFn` reduces mortality to `MortFn`. -/
theorem toFn_spec : DiagonaLean.MatMort.DecisionProblem ⪯_s[toFn] MortFn := fun _ => Iff.rfl

/-- `atZero` reduces `MortFn` to `MortT`. -/
theorem atZero_spec : MortFn ⪯_s[atZero] MortT :=
  fun _ => ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩

/-- Mortality, through functions on `ℕ`, to `MortT`. -/
def synthThroughFn : SynthHaltReduction MortT := by
  synth_reduce_from DiagonaLean.MatMort.synthFromHalt with toFn using toFn_spec,
    with atZero using atZero_spec

/--
error: upgrade: the synthetic link from
  DiagonaLean.MatMort.DecisionProblem
to
  MortFn
cannot be made proved: its types need a `Primcodable` instance for `Computable` to be stated.
failed to synthesize
  Primcodable (ℕ → Finset (Matrix (Fin 3) (Fin 3) ℤ))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example : HaltReduction MortT := by
  upgrade synthThroughFn

/--
error: upgrade: no problem of the chain of `(h.comp ⟨atZero, atZero_spec⟩)` has a proved halting reduction. The chain:
  HaltProblem ⪯_s MortFn ⪯_s MortT
Looked for, at each problem `p`: the proved counterpart by name (`foo` for `synthFoo`), a hypothesis `HaltReduction p`, and an instance `HaltSource p`. Give one of these for some problem of the chain.
-/
#guard_msgs in
example (h : SynthHaltReduction MortFn) : HaltReduction MortT := by
  upgrade (h.comp ⟨atZero, atZero_spec⟩)

/--
error: upgrade: no problem of the chain of `(DiagonaLean.SKIConv.synthFromHalt C hu
  hr)` has a proved halting reduction. The chain:
  HaltProblem ⪯_s DiagonaLean.SKIConv.SKIConvProblem
Looked for, at each problem `p`: the proved counterpart by name (`foo` for `synthFoo`), a hypothesis `HaltReduction p`, and an instance `HaltSource p`. Give one of these for some problem of the chain.
-/
#guard_msgs in
example {u : Nat.Partrec.Code} (C : Nat.Partrec.Code)
    (hu : DiagonaLean.Foundations.CombinatoryLogic.IsUniversal u)
    (hr : DiagonaLean.Foundations.CombinatoryLogic.RaceProg u.toSKI C) :
    HaltReduction DiagonaLean.SKIConv.SKIConvProblem := by
  upgrade (DiagonaLean.SKIConv.synthFromHalt C hu hr)

/--
error: upgrade: the goal
  SynthHaltReduction DiagonaLean.MatMort.DecisionProblem
is synthetic; `upgrade` proves the proved goals from a synthetic reduction.
-/
#guard_msgs in
example : SynthHaltReduction DiagonaLean.MatMort.DecisionProblem := by
  upgrade DiagonaLean.MatMort.synthFromHalt

/--
error: upgrade: `DiagonaLean.MatMort.synthFromHalt` does not reduce to the problem of the goal.
Type mismatch
  DiagonaLean.MatMort.fromHalt
has type
  HaltReduction DiagonaLean.MatMort.DecisionProblem
but is expected to have type
  HaltReduction PCPS23
-/
#guard_msgs in
example : HaltReduction PCPS23 := by
  upgrade DiagonaLean.MatMort.synthFromHalt
