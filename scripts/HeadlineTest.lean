import DiagonaLean

/-! # The headline statements, pinned

Run by CI with `lake env lean scripts/HeadlineTest.lean`. Each `example` states a headline result
of the library with its exact statement, and proves it by the theorem itself. A change that weakens
a headline (an extra hypothesis, a weaker conclusion, a different problem or encoding) makes the
`example` fail, although every other check would still pass. A deliberate change of a headline
updates its `example` here, in the same commit.

The statements were generated on 2026-11-27 from the theorems' types, with full names.
-/

example :
    ¬∃ (D : Cslib.Turing.SingleTapeTM Bool), DiagonaLean.Halt.IsSelfHaltDecider D :=
  @DiagonaLean.Halt.Undecidable.self_halt_undecidable

example :
    ¬∃ (D : Cslib.Turing.SingleTapeTM Bool), DiagonaLean.Halt.IsHaltDecider D :=
  @DiagonaLean.Halt.Undecidable.halt_undecidable

example :
    ¬DiagonaLean.Synthetic.Definitions.MachineDecidable
        DiagonaLean.Halt.Undecidable.haltInputEncoding
        DiagonaLean.Halt.HaltProblem :=
  @DiagonaLean.Halt.Undecidable.halt_not_machinedecidable

example :
    ¬ComputablePred DiagonaLean.Foundations.Computability.HaltCanon :=
  @DiagonaLean.Foundations.Computability.not_computablePred_haltCanon

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α],
      DiagonaLean.Foundations.Computability.HaltHard (β := DiagonaLean.PCP.Tile α ×
          DiagonaLean.PCP.Stack α)
        DiagonaLean.MPCP.DecisionProblem :=
  @DiagonaLean.MPCP.haltHard

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α],
      ¬ComputablePred (α := DiagonaLean.PCP.Tile α × DiagonaLean.PCP.Stack α)
          DiagonaLean.MPCP.DecisionProblem :=
  @DiagonaLean.MPCP.not_computablePred

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α] {enc : DiagonaLean.PCP.Tile α ×
        DiagonaLean.PCP.Stack α → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.MPCP.DecisionProblem :=
  @DiagonaLean.MPCP.not_machineDecidable

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α],
      DiagonaLean.Foundations.Computability.HaltHard (β := DiagonaLean.PCP.Stack α)
          DiagonaLean.PCP.DecisionProblem :=
  @DiagonaLean.PCP.haltHard

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α],
      ¬ComputablePred (α := DiagonaLean.PCP.Stack α) DiagonaLean.PCP.DecisionProblem :=
  @DiagonaLean.PCP.not_computablePred

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α] {enc : DiagonaLean.PCP.Stack α → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.PCP.DecisionProblem :=
  @DiagonaLean.PCP.not_machineDecidable

example :
    DiagonaLean.Foundations.Computability.HaltHard DiagonaLean.MatMort.DecisionProblem :=
  @DiagonaLean.MatMort.haltHard

example :
    ¬ComputablePred DiagonaLean.MatMort.DecisionProblem :=
  @DiagonaLean.MatMort.not_computablePred

example :
    ∀ {enc : Finset (Matrix (Fin 3) (Fin 3) ℤ) → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.MatMort.DecisionProblem :=
  @DiagonaLean.MatMort.not_machineDecidable

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α],
      DiagonaLean.Foundations.Computability.HaltHard (β := DiagonaLean.Foundations.Grammar.SRS α ×
          List α × List α)
        DiagonaLean.SemiThue.DecisionProblem :=
  @DiagonaLean.SemiThue.haltHard

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α],
      ¬ComputablePred (α := DiagonaLean.Foundations.Grammar.SRS α × List α × List α)
          DiagonaLean.SemiThue.DecisionProblem :=
  @DiagonaLean.SemiThue.not_computablePred

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α]
      {enc : DiagonaLean.Foundations.Grammar.SRS α × List α × List α → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.SemiThue.DecisionProblem :=
  @DiagonaLean.SemiThue.not_machineDecidable

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α],
      DiagonaLean.Foundations.Computability.HaltHard (β := DiagonaLean.Foundations.Grammar.SRS α ×
          List α × List α)
        DiagonaLean.SemiThue.DecisionProblemPos :=
  @DiagonaLean.SemiThue.Pos.haltHard

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α],
      ¬ComputablePred (α := DiagonaLean.Foundations.Grammar.SRS α × List α × List α)
          DiagonaLean.SemiThue.DecisionProblemPos :=
  @DiagonaLean.SemiThue.Pos.not_computablePred

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α]
      {enc : DiagonaLean.Foundations.Grammar.SRS α × List α × List α → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.SemiThue.DecisionProblemPos :=
  @DiagonaLean.SemiThue.Pos.not_machineDecidable

example :
    DiagonaLean.Foundations.Computability.HaltHard (β :=
      DiagonaLean.Foundations.Grammar.SRS
          (DiagonaLean.MPCP.Reduction.Alpha ℕ DiagonaLean.Foundations.Computability.Normalize.Sym2)
              ×
        List (DiagonaLean.MPCP.Reduction.Alpha ℕ
            DiagonaLean.Foundations.Computability.Normalize.Sym2))
      DiagonaLean.SemiThue.ToEmptyProblem :=
  @DiagonaLean.SemiThue.ToEmpty.haltHard

example :
    ¬ComputablePred (α :=
        DiagonaLean.Foundations.Grammar.SRS
            (DiagonaLean.MPCP.Reduction.Alpha ℕ
                DiagonaLean.Foundations.Computability.Normalize.Sym2) ×
          List (DiagonaLean.MPCP.Reduction.Alpha ℕ
              DiagonaLean.Foundations.Computability.Normalize.Sym2))
        DiagonaLean.SemiThue.ToEmptyProblem :=
  @DiagonaLean.SemiThue.ToEmpty.not_computablePred

example :
    ∀
      {enc :
        DiagonaLean.Foundations.Grammar.SRS
              (DiagonaLean.MPCP.Reduction.Alpha ℕ
                  DiagonaLean.Foundations.Computability.Normalize.Sym2) ×
            List (DiagonaLean.MPCP.Reduction.Alpha ℕ
                DiagonaLean.Foundations.Computability.Normalize.Sym2) →
          List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.SemiThue.ToEmptyProblem :=
  @DiagonaLean.SemiThue.ToEmpty.not_machineDecidable

example :
    ∀ {T : Type} [Primcodable T],
      DiagonaLean.Foundations.Computability.HaltHard (β := DiagonaLean.GrammarMem.GrammarCode T ×
          List T)
        DiagonaLean.GrammarMem.DecisionProblem :=
  @DiagonaLean.GrammarMem.haltHard

example :
    ∀ {T : Type} [Primcodable T],
      ¬ComputablePred (α := DiagonaLean.GrammarMem.GrammarCode T × List T)
          DiagonaLean.GrammarMem.DecisionProblem :=
  @DiagonaLean.GrammarMem.not_computablePred

example :
    ∀ {T : Type} [Primcodable T] {enc : DiagonaLean.GrammarMem.GrammarCode T × List T → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.GrammarMem.DecisionProblem :=
  @DiagonaLean.GrammarMem.not_machineDecidable

example :
    ∀ {T : Type} [Primcodable T],
      DiagonaLean.Foundations.Computability.HaltHard
        fun (g : { g : DiagonaLean.GrammarMem.GrammarCode T // DiagonaLean.GrammarMem.IsType0 g })
            =>
        DiagonaLean.GrammarMem.EmptyWordProblem g.1 :=
  @DiagonaLean.GrammarMem.EmptyWord.haltHard

example :
    ∀ {T : Type} [Primcodable T],
      ¬ComputablePred fun (g : { g : DiagonaLean.GrammarMem.GrammarCode T //
          DiagonaLean.GrammarMem.IsType0 g }) =>
          DiagonaLean.GrammarMem.EmptyWordProblem g.1 :=
  @DiagonaLean.GrammarMem.EmptyWord.not_computablePred

example :
    ∀ {T : Type} [Primcodable T]
      {enc : { g : DiagonaLean.GrammarMem.GrammarCode T // DiagonaLean.GrammarMem.IsType0 g } →
          List Bool},
      Computable enc →
        ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
            fun (g : { g : DiagonaLean.GrammarMem.GrammarCode T // DiagonaLean.GrammarMem.IsType0 g
                }) =>
            DiagonaLean.GrammarMem.EmptyWordProblem g.1 :=
  @DiagonaLean.GrammarMem.EmptyWord.not_machineDecidable

example :
    ∀ {α : Type} [Primcodable α] [DecidableEq α] [Nontrivial α],
      DiagonaLean.Foundations.Computability.HaltHard
        fun (c : DiagonaLean.Foundations.Grammar.CFGCode α ×
            DiagonaLean.Foundations.Grammar.CFGCode α) =>
        DiagonaLean.EmpCFG.IntersectionNonempty (DiagonaLean.Foundations.Grammar.GrammarPres.toCFG
            c.1)
          (DiagonaLean.Foundations.Grammar.GrammarPres.toCFG c.2) :=
  @DiagonaLean.EmpCFG.Code.haltHard

example :
    ∀ {α : Type} [Primcodable α] [DecidableEq α] [Nontrivial α],
      ¬ComputablePred fun (c : DiagonaLean.Foundations.Grammar.CFGCode α ×
          DiagonaLean.Foundations.Grammar.CFGCode α) =>
          DiagonaLean.EmpCFG.IntersectionNonempty
              (DiagonaLean.Foundations.Grammar.GrammarPres.toCFG c.1)
            (DiagonaLean.Foundations.Grammar.GrammarPres.toCFG c.2) :=
  @DiagonaLean.EmpCFG.Code.not_computablePred

example :
    ∀ {α : Type} [Primcodable α] [DecidableEq α] [Nontrivial α]
      {enc : DiagonaLean.Foundations.Grammar.CFGCode α × DiagonaLean.Foundations.Grammar.CFGCode α
          → List Bool},
      Computable enc →
        ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
            fun (c : DiagonaLean.Foundations.Grammar.CFGCode α ×
                DiagonaLean.Foundations.Grammar.CFGCode α) =>
            DiagonaLean.EmpCFG.IntersectionNonempty
                (DiagonaLean.Foundations.Grammar.GrammarPres.toCFG c.1)
              (DiagonaLean.Foundations.Grammar.GrammarPres.toCFG c.2) :=
  @DiagonaLean.EmpCFG.Code.not_machineDecidable

example :
    ∀ {α : Type} [Primcodable α] [DecidableEq α] [Nontrivial α],
      DiagonaLean.Foundations.Computability.HaltHard fun (c :
          DiagonaLean.Foundations.Grammar.CFGCode α) =>
        DiagonaLean.AmbigCFG.DecisionProblem (DiagonaLean.Foundations.Grammar.GrammarPres.toCFG c)
            :=
  @DiagonaLean.AmbigCFG.Code.haltHard

example :
    ∀ {α : Type} [Primcodable α] [DecidableEq α] [Nontrivial α],
      ¬ComputablePred fun (c : DiagonaLean.Foundations.Grammar.CFGCode α) =>
          DiagonaLean.AmbigCFG.DecisionProblem (DiagonaLean.Foundations.Grammar.GrammarPres.toCFG
              c) :=
  @DiagonaLean.AmbigCFG.Code.not_computablePred

example :
    ∀ {α : Type} [Primcodable α] [DecidableEq α] [Nontrivial α]
      {enc : DiagonaLean.Foundations.Grammar.CFGCode α → List Bool},
      Computable enc →
        ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc fun (c :
            DiagonaLean.Foundations.Grammar.CFGCode α) =>
            DiagonaLean.AmbigCFG.DecisionProblem (DiagonaLean.Foundations.Grammar.GrammarPres.toCFG
                c) :=
  @DiagonaLean.AmbigCFG.Code.not_machineDecidable

example :
    DiagonaLean.Foundations.Computability.HaltHard DiagonaLean.SKIConv.SKIConvProblem :=
  @DiagonaLean.SKIConv.haltHard

example :
    ¬ComputablePred DiagonaLean.SKIConv.SKIConvProblem :=
  @DiagonaLean.SKIConv.not_computablePred

example :
    ∀ {enc : Cslib.SKI × Cslib.SKI → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.SKIConv.SKIConvProblem :=
  @DiagonaLean.SKIConv.not_machineDecidable

example :
    DiagonaLean.Foundations.Computability.HaltHard DiagonaLean.BetaConv.BetaConvProblem :=
  @DiagonaLean.BetaConv.haltHard

example :
    ¬ComputablePred DiagonaLean.BetaConv.BetaConvProblem :=
  @DiagonaLean.BetaConv.not_computablePred

example :
    ∀
      {enc :
        Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ ×
            Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ →
          List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.BetaConv.BetaConvProblem :=
  @DiagonaLean.BetaConv.not_machineDecidable

example :
    DiagonaLean.Foundations.Computability.HaltHard DiagonaLean.KAComm.KATermEq.KATermEqProblem :=
  @DiagonaLean.KAComm.KATermEq.haltHard

example :
    ¬ComputablePred DiagonaLean.KAComm.KATermEq.KATermEqProblem :=
  @DiagonaLean.KAComm.KATermEq.not_computablePred

example :
    ∀ {enc : DiagonaLean.KAComm.KleeneAlgebra.Inst → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.KAComm.KATermEq.KATermEqProblem :=
  @DiagonaLean.KAComm.KATermEq.not_machineDecidable

example :
    DiagonaLean.Foundations.Computability.HaltHard
        DiagonaLean.KAComm.KATermEqBool.KATermEqBoolProblem :=
  @DiagonaLean.KAComm.KATermEqBool.haltHard

example :
    ¬ComputablePred DiagonaLean.KAComm.KATermEqBool.KATermEqBoolProblem :=
  @DiagonaLean.KAComm.KATermEqBool.not_computablePred

example :
    ∀ {enc : DiagonaLean.KAComm.KleeneAlgebra.InstB → List Bool},
      Computable enc →
        ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
            DiagonaLean.KAComm.KATermEqBool.KATermEqBoolProblem :=
  @DiagonaLean.KAComm.KATermEqBool.not_machineDecidable

example :
    DiagonaLean.Foundations.Computability.HaltHard DiagonaLean.KAComm.TermEq.TermEqProblem :=
  @DiagonaLean.KAComm.TermEq.haltHard

example :
    ¬ComputablePred DiagonaLean.KAComm.TermEq.TermEqProblem :=
  @DiagonaLean.KAComm.TermEq.not_computablePred

example :
    ∀ {enc : DiagonaLean.KAComm.KleeneAlgebra.Inst → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.KAComm.TermEq.TermEqProblem :=
  @DiagonaLean.KAComm.TermEq.not_machineDecidable

example :
    DiagonaLean.Foundations.Computability.HaltHard DiagonaLean.KAComm.TermEqBool.TermEqBoolProblem
        :=
  @DiagonaLean.KAComm.TermEqBool.haltHard

example :
    ¬ComputablePred DiagonaLean.KAComm.TermEqBool.TermEqBoolProblem :=
  @DiagonaLean.KAComm.TermEqBool.not_computablePred

example :
    ∀ {enc : DiagonaLean.KAComm.KleeneAlgebra.InstB → List Bool},
      Computable enc →
        ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
            DiagonaLean.KAComm.TermEqBool.TermEqBoolProblem :=
  @DiagonaLean.KAComm.TermEqBool.not_machineDecidable

example :
    ¬ComputablePred DiagonaLean.KAComm.LangEq.LangEqProblem :=
  @DiagonaLean.KAComm.LangEq.not_computablePred

example :
    ∀ {enc : DiagonaLean.KAComm.KleeneAlgebra.Inst → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.KAComm.LangEq.LangEqProblem :=
  @DiagonaLean.KAComm.LangEq.not_machineDecidable

example :
    ¬ComputablePred DiagonaLean.KAComm.LangEqBool.LangEqBoolProblem :=
  @DiagonaLean.KAComm.LangEqBool.not_computablePred

example :
    ∀ {enc : DiagonaLean.KAComm.KleeneAlgebra.InstB → List Bool},
      Computable enc →
        ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
            DiagonaLean.KAComm.LangEqBool.LangEqBoolProblem :=
  @DiagonaLean.KAComm.LangEqBool.not_machineDecidable

example :
    ¬ComputablePred DiagonaLean.KAComm.ModelLe.ModelLeProblem :=
  @DiagonaLean.KAComm.ModelLe.not_computablePred

example :
    ∀ {enc : DiagonaLean.KAComm.KleeneAlgebra.Inst → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.KAComm.ModelLe.ModelLeProblem :=
  @DiagonaLean.KAComm.ModelLe.not_machineDecidable

example :
    ¬ComputablePred DiagonaLean.KAComm.ModelLeBool.ModelLeBoolProblem :=
  @DiagonaLean.KAComm.ModelLeBool.not_computablePred

example :
    ∀ {enc : DiagonaLean.KAComm.KleeneAlgebra.InstB → List Bool},
      Computable enc →
        ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
            DiagonaLean.KAComm.ModelLeBool.ModelLeBoolProblem :=
  @DiagonaLean.KAComm.ModelLeBool.not_machineDecidable

example :
    ∀ {C : Set (ℕ →. ℕ)}, DiagonaLean.Rice.IsNontrivial C → ¬ComputablePred
        (DiagonaLean.Rice.RiceProblem C) :=
  @DiagonaLean.Rice.not_computablePred

example :
    ∀ {C : Set (ℕ →. ℕ)},
      DiagonaLean.Rice.IsNontrivial C →
        ∀ {enc : Nat.Partrec.Code → List Bool},
          Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
              (DiagonaLean.Rice.RiceProblem C) :=
  @DiagonaLean.Rice.not_machineDecidable
