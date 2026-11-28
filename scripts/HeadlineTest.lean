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
      DiagonaLean.Foundations.Computability.HaltHard (β := DiagonaLean.Foundations.Rewriting.SRS α ×
          List α × List α)
        DiagonaLean.SemiThue.DecisionProblem :=
  @DiagonaLean.SemiThue.haltHard

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α],
      ¬ComputablePred (α := DiagonaLean.Foundations.Rewriting.SRS α × List α × List α)
          DiagonaLean.SemiThue.DecisionProblem :=
  @DiagonaLean.SemiThue.not_computablePred

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α]
      {enc : DiagonaLean.Foundations.Rewriting.SRS α × List α × List α → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.SemiThue.DecisionProblem :=
  @DiagonaLean.SemiThue.not_machineDecidable

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α],
      DiagonaLean.Foundations.Computability.HaltHard (β := DiagonaLean.Foundations.Rewriting.SRS α ×
          List α × List α)
        DiagonaLean.SemiThue.DecisionProblemPos :=
  @DiagonaLean.SemiThue.Pos.haltHard

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α],
      ¬ComputablePred (α := DiagonaLean.Foundations.Rewriting.SRS α × List α × List α)
          DiagonaLean.SemiThue.DecisionProblemPos :=
  @DiagonaLean.SemiThue.Pos.not_computablePred

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α]
      {enc : DiagonaLean.Foundations.Rewriting.SRS α × List α × List α → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.SemiThue.DecisionProblemPos :=
  @DiagonaLean.SemiThue.Pos.not_machineDecidable

example :
    DiagonaLean.Foundations.Computability.HaltHard (β :=
      DiagonaLean.Foundations.Rewriting.SRS
          (DiagonaLean.MPCP.Reduction.Alpha ℕ DiagonaLean.Foundations.Computability.Normalize.Sym2)
              ×
        List (DiagonaLean.MPCP.Reduction.Alpha ℕ
            DiagonaLean.Foundations.Computability.Normalize.Sym2))
      DiagonaLean.SemiThue.ToEmptyProblem :=
  @DiagonaLean.SemiThue.ToEmpty.haltHard

example :
    ¬ComputablePred (α :=
        DiagonaLean.Foundations.Rewriting.SRS
            (DiagonaLean.MPCP.Reduction.Alpha ℕ
                DiagonaLean.Foundations.Computability.Normalize.Sym2) ×
          List (DiagonaLean.MPCP.Reduction.Alpha ℕ
              DiagonaLean.Foundations.Computability.Normalize.Sym2))
        DiagonaLean.SemiThue.ToEmptyProblem :=
  @DiagonaLean.SemiThue.ToEmpty.not_computablePred

example :
    ∀
      {enc :
        DiagonaLean.Foundations.Rewriting.SRS
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

example :
    DiagonaLean.Foundations.Computability.HaltHard DiagonaLean.MatrixGame.DecisionProblem :=
  @DiagonaLean.MatrixGame.haltHard

example :
    ¬ComputablePred DiagonaLean.MatrixGame.DecisionProblem :=
  @DiagonaLean.MatrixGame.not_computablePred

example :
    ∀ {enc : DiagonaLean.MatrixGame.Arena → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.MatrixGame.DecisionProblem :=
  @DiagonaLean.MatrixGame.not_machineDecidable

example :
    ∀ {enc : Finset DiagonaLean.MatrixGame.Position → List Bool},
      Computable enc →
        ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc fun moves =>
          DiagonaLean.MatrixGame.DecisionProblem (DiagonaLean.MatrixGame.Reduction.signGame moves) :=
  @DiagonaLean.MatrixGame.not_machineDecidable_signGame

example :
    ¬ComputablePred DiagonaLean.Rabin.DecisionProblem :=
  @DiagonaLean.Rabin.not_computablePred

example :
    ∀ {enc : DiagonaLean.Rabin.PayoffCode → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.Rabin.DecisionProblem :=
  @DiagonaLean.Rabin.not_machineDecidable

example :
    DiagonaLean.Foundations.Computability.HaltHard
      (DiagonaLean.Foundations.Computability.ListHalt.DecisionProblem
        (none : Option DiagonaLean.Foundations.Computability.Normalize.Sym2)) :=
  @DiagonaLean.Foundations.Computability.ListHalt.haltHard

example :
    ¬ComputablePred
      (DiagonaLean.Foundations.Computability.ListHalt.DecisionProblem
        (none : Option DiagonaLean.Foundations.Computability.Normalize.Sym2)) :=
  @DiagonaLean.Foundations.Computability.ListHalt.not_computablePred

example :
    DiagonaLean.Foundations.Computability.HaltHard DiagonaLean.CM2.DecisionProblem :=
  @DiagonaLean.CM2.haltHard

example :
    ¬ComputablePred DiagonaLean.CM2.DecisionProblem :=
  @DiagonaLean.CM2.not_computablePred

example :
    ∀ {enc : List DiagonaLean.CM2.Instr → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          DiagonaLean.CM2.DecisionProblem :=
  @DiagonaLean.CM2.not_machineDecidable

example :
    DiagonaLean.Foundations.Computability.HaltHard (@DiagonaLean.CFGame.DecisionProblem ℕ) :=
  @DiagonaLean.CFGame.haltHard

example :
    ¬ComputablePred (@DiagonaLean.CFGame.DecisionProblem ℕ) :=
  @DiagonaLean.CFGame.not_computablePred

example :
    ∀ {enc : DiagonaLean.CFGame.Game ℕ × List ℕ → List Bool},
      Computable enc → ¬DiagonaLean.Synthetic.Definitions.MachineDecidable enc
          (@DiagonaLean.CFGame.DecisionProblem ℕ) :=
  @DiagonaLean.CFGame.not_machineDecidable

example :
    DiagonaLean.Halt.HaltProblem ⪯_s @DiagonaLean.TeamGame.DecisionProblem ℕ _ :=
  DiagonaLean.TeamGame.synthFromHalt

example :
    DiagonaLean.Halt.HaltProblem ⪯_s
      DiagonaLean.Synthetic.Definitions.Complement (@DiagonaLean.TeamGame.DecisionProblemSafety ℕ _) :=
  DiagonaLean.TeamGame.synthComplFromHalt

/-! ## Recursive enumerability

The three rewriting problems, PCP, MPCP, matrix mortality, the four KAComm equality problems,
membership for grammar codes, intersection of grammar codes, two-counter machines and list
machines are recursively enumerable, so with their halting-hardness above they are exactly as
hard as the halting problem. Generated on 2026-11-27; extended on 2026-11-28. -/

example :
    ∀ {T : Type} [Primcodable T] [DecidableEq T],
      REPred (@DiagonaLean.SemiThue.DecisionProblem T) :=
  @DiagonaLean.SemiThue.rePred

example :
    REPred DiagonaLean.SKIConv.DecisionProblem :=
  @DiagonaLean.SKIConv.rePred

example :
    REPred DiagonaLean.BetaConv.DecisionProblem :=
  @DiagonaLean.BetaConv.rePred

example :
    ∀ {α : Type} [Primcodable α], REPred (@DiagonaLean.PCP.DecisionProblem α) :=
  @DiagonaLean.PCP.rePred

example :
    ∀ {α : Type} [Primcodable α], REPred (@DiagonaLean.MPCP.DecisionProblem α) :=
  @DiagonaLean.MPCP.rePred

example :
    REPred DiagonaLean.MatMort.DecisionProblem :=
  @DiagonaLean.MatMort.rePred

example :
    REPred DiagonaLean.KAComm.TermEq.DecisionProblem :=
  @DiagonaLean.KAComm.TermEq.rePred

example :
    REPred DiagonaLean.KAComm.KATermEq.DecisionProblem :=
  @DiagonaLean.KAComm.KATermEq.rePred

example :
    REPred DiagonaLean.KAComm.TermEqBool.DecisionProblem :=
  @DiagonaLean.KAComm.TermEqBool.rePred

example :
    REPred DiagonaLean.KAComm.KATermEqBool.DecisionProblem :=
  @DiagonaLean.KAComm.KATermEqBool.rePred

example :
    ∀ {T : Type} [Primcodable T],
      REPred (@DiagonaLean.GrammarMem.DecisionProblem T) :=
  @DiagonaLean.GrammarMem.rePred

example :
    ∀ {T : Type} [Primcodable T],
      REPred fun g : { g : DiagonaLean.GrammarMem.GrammarCode T //
          DiagonaLean.GrammarMem.IsType0 g } =>
        DiagonaLean.GrammarMem.EmptyWordProblem g.1 :=
  @DiagonaLean.GrammarMem.EmptyWord.rePred

example :
    ∀ {α : Type} [Primcodable α] [DecidableEq α],
      REPred fun c : DiagonaLean.Foundations.Grammar.CFGCode α ×
          DiagonaLean.Foundations.Grammar.CFGCode α =>
        DiagonaLean.EmpCFG.IntersectionNonempty c.1.toCFG c.2.toCFG :=
  @DiagonaLean.EmpCFG.Code.rePred

example :
    REPred DiagonaLean.CM2.DecisionProblem :=
  @DiagonaLean.CM2.rePred

example :
    ∀ {Γ : Type} [DecidableEq Γ] [Primcodable Γ] (bl : Γ),
      REPred (DiagonaLean.Foundations.Computability.ListHalt.DecisionProblem bl) :=
  @DiagonaLean.Foundations.Computability.ListHalt.rePred

/-! ## Co-halting-hardness

The complement of the halting problem is not recursively enumerable, so neither is a
co-halting-hard predicate; emptiness of the intersection of grammar codes is one. Generated on
2026-11-28. -/

example :
    ¬REPred fun x => ¬DiagonaLean.Foundations.Computability.HaltCanon x :=
  @DiagonaLean.Foundations.Computability.not_rePred_compl_haltCanon

example :
    ∀ {α : Type} [Primcodable α] [DecidableEq α] [Nontrivial α],
      DiagonaLean.Foundations.Computability.CoHaltHard
        fun (c : DiagonaLean.Foundations.Grammar.CFGCode α ×
            DiagonaLean.Foundations.Grammar.CFGCode α) =>
        DiagonaLean.EmpCFG.IntersectionEmpty (DiagonaLean.Foundations.Grammar.GrammarPres.toCFG
            c.1)
          (DiagonaLean.Foundations.Grammar.GrammarPres.toCFG c.2) :=
  @DiagonaLean.EmpCFG.Code.empty_coHaltHard

example :
    ∀ {α : Type} [Primcodable α] [DecidableEq α] [Nontrivial α],
      ¬REPred fun (c : DiagonaLean.Foundations.Grammar.CFGCode α ×
            DiagonaLean.Foundations.Grammar.CFGCode α) =>
        DiagonaLean.EmpCFG.IntersectionEmpty (DiagonaLean.Foundations.Grammar.GrammarPres.toCFG
            c.1)
          (DiagonaLean.Foundations.Grammar.GrammarPres.toCFG c.2) :=
  @DiagonaLean.EmpCFG.Code.empty_not_rePred

/-! ## Completeness and degrees

The halting problem is complete for the recursively enumerable problems, and the three rewriting
problems, halting-hard and recursively enumerable, have its degree. Generated on 2026-11-27. -/

universe u

example :
    ∀ {α : Type u} [Primcodable α] {p : α → Prop},
      REPred p → p ≤₀ DiagonaLean.Foundations.Computability.HaltCanon :=
  @DiagonaLean.Foundations.Computability.manyOneReducible_haltCanon_of_rePred

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α] {β : Type u}
      [Primcodable β] {p : β → Prop}, REPred p → p ≤₀ (@DiagonaLean.SemiThue.DecisionProblem α) :=
  @DiagonaLean.SemiThue.complete

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α] {β : Type u}
      [Primcodable β] {p : β → Prop}, REPred p → p ≤₀ (@DiagonaLean.MPCP.DecisionProblem α) :=
  @DiagonaLean.MPCP.complete

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α] {β : Type u}
      [Primcodable β] {p : β → Prop}, REPred p → p ≤₀ (@DiagonaLean.PCP.DecisionProblem α) :=
  @DiagonaLean.PCP.complete

example :
    ∀ {β : Type u} [Primcodable β] {p : β → Prop},
      REPred p → p ≤₀ DiagonaLean.MatMort.DecisionProblem :=
  @DiagonaLean.MatMort.complete

example :
    ∀ {β : Type u} [Primcodable β] {p : β → Prop},
      REPred p → p ≤₀ DiagonaLean.KAComm.TermEq.DecisionProblem :=
  @DiagonaLean.KAComm.TermEq.complete

example :
    ∀ {β : Type u} [Primcodable β] {p : β → Prop},
      REPred p → p ≤₀ DiagonaLean.KAComm.KATermEq.DecisionProblem :=
  @DiagonaLean.KAComm.KATermEq.complete

example :
    ∀ {β : Type u} [Primcodable β] {p : β → Prop},
      REPred p → p ≤₀ DiagonaLean.KAComm.TermEqBool.DecisionProblem :=
  @DiagonaLean.KAComm.TermEqBool.complete

example :
    ∀ {β : Type u} [Primcodable β] {p : β → Prop},
      REPred p → p ≤₀ DiagonaLean.KAComm.KATermEqBool.DecisionProblem :=
  @DiagonaLean.KAComm.KATermEqBool.complete

example :
    ∀ {T : Type} [Primcodable T] {β : Type u} [Primcodable β] {p : β → Prop},
      REPred p → p ≤₀ (@DiagonaLean.GrammarMem.DecisionProblem T) :=
  @DiagonaLean.GrammarMem.complete

example :
    ∀ {β : Type u} [Primcodable β] {p : β → Prop},
      REPred p → p ≤₀ DiagonaLean.CM2.DecisionProblem :=
  @DiagonaLean.CM2.complete

example :
    ∀ {β : Type u} [Primcodable β] {p : β → Prop},
      REPred p → p ≤₀ DiagonaLean.Foundations.Computability.ListHalt.DecisionProblem
        (none : Option DiagonaLean.Foundations.Computability.Normalize.Sym2) :=
  @DiagonaLean.Foundations.Computability.ListHalt.complete

example :
    ∀ {β : Type u} [Primcodable β] {p : β → Prop},
      REPred p → p ≤₀ DiagonaLean.SKIConv.DecisionProblem :=
  @DiagonaLean.SKIConv.complete

example :
    ∀ {β : Type u} [Primcodable β] {p : β → Prop},
      REPred p → p ≤₀ DiagonaLean.BetaConv.DecisionProblem :=
  @DiagonaLean.BetaConv.complete

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α],
      ManyOneEquiv (@DiagonaLean.SemiThue.DecisionProblem α) DiagonaLean.SKIConv.DecisionProblem :=
  @DiagonaLean.Degrees.semiThue_equiv_skiConv

example :
    ManyOneEquiv DiagonaLean.SKIConv.DecisionProblem DiagonaLean.BetaConv.DecisionProblem :=
  @DiagonaLean.Degrees.skiConv_equiv_betaConv

example :
    ∀ {α : Type} [Primcodable α] [Nontrivial α],
      ManyOneEquiv (@DiagonaLean.SemiThue.DecisionProblem α) DiagonaLean.BetaConv.DecisionProblem :=
  @DiagonaLean.Degrees.semiThue_equiv_betaConv

/-! ## The problems, pinned

Each problem's one-argument `DecisionProblem` unfolds, by `Iff.rfl`, to its curried form
(`decisionProblem_mk`), and the curried forms of the rewriting problems unfold to Mathlib's and
Cslib's relations (`wordProblem_iff`, `convertible_iff`). A change to the definition of a problem
makes one of these `example`s fail, as a weakened headline does above. Generated on 2026-11-27 from
the theorems' types, with full names. -/

example :
    ∀ {T : Type} (R : DiagonaLean.Foundations.Rewriting.SRS T)
      (u v : DiagonaLean.Foundations.Rewriting.Word T),
      DiagonaLean.SemiThue.WordProblem R u v ↔ Relation.ReflTransGen R.Step u v :=
  @DiagonaLean.SemiThue.wordProblem_iff

example :
    ∀ {T : Type} (R : DiagonaLean.Foundations.Rewriting.SRS T)
      (u v : DiagonaLean.Foundations.Rewriting.Word T),
      DiagonaLean.SemiThue.DecisionProblem (R, u, v) ↔ DiagonaLean.SemiThue.WordProblem R u v :=
  @DiagonaLean.SemiThue.decisionProblem_mk

example :
    ∀ {T : Type} (R : DiagonaLean.Foundations.Rewriting.SRS T)
      (u v : DiagonaLean.Foundations.Rewriting.Word T),
      DiagonaLean.SemiThue.DecisionProblemPos (R, u, v) ↔
        DiagonaLean.SemiThue.PosWordProblem R u v :=
  @DiagonaLean.SemiThue.decisionProblemPos_mk

example :
    ∀ {T : Type} (R : DiagonaLean.Foundations.Rewriting.SRS T)
      (u : DiagonaLean.Foundations.Rewriting.Word T),
      DiagonaLean.SemiThue.ToEmptyProblem (R, u) ↔ DiagonaLean.SemiThue.ToEmpty R u :=
  @DiagonaLean.SemiThue.toEmptyProblem_mk

example :
    ∀ (x y : Cslib.SKI),
      DiagonaLean.SKIConv.Convertible x y ↔
        ∃ z, Relation.ReflTransGen Cslib.SKI.Red x z ∧ Relation.ReflTransGen Cslib.SKI.Red y z :=
  @DiagonaLean.SKIConv.convertible_iff

example :
    ∀ (x y : Cslib.SKI),
      DiagonaLean.SKIConv.DecisionProblem (x, y) ↔ DiagonaLean.SKIConv.Convertible x y :=
  @DiagonaLean.SKIConv.decisionProblem_mk

example :
    ∀ (M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ),
      DiagonaLean.BetaConv.Convertible M N ↔
        ∃ P,
          Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta M P ∧
            Relation.ReflTransGen Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta N P :=
  @DiagonaLean.BetaConv.convertible_iff

example :
    ∀ (M N : Cslib.LambdaCalculus.LocallyNameless.Untyped.Term ℕ),
      DiagonaLean.BetaConv.DecisionProblem (M, N) ↔ DiagonaLean.BetaConv.Convertible M N :=
  @DiagonaLean.BetaConv.decisionProblem_mk

example :
    ∀ {α : Type} (c : DiagonaLean.PCP.Tile α) (P : DiagonaLean.PCP.Stack α),
      DiagonaLean.MPCP.DecisionProblem (c, P) ↔ DiagonaLean.MPCP.Solvable c P :=
  @DiagonaLean.MPCP.decisionProblem_mk

example :
    ∀ {T : Type} (G₁ G₂ : ContextFreeGrammar T),
      DiagonaLean.EmpCFG.DecisionProblem (G₁, G₂) ↔ DiagonaLean.EmpCFG.IntersectionNonempty G₁ G₂ :=
  @DiagonaLean.EmpCFG.decisionProblem_mk

example :
    ∀ {T : Type} (g : DiagonaLean.GrammarMem.GrammarCode T) (w : List T),
      DiagonaLean.GrammarMem.DecisionProblem (g, w) ↔ w ∈ g.language :=
  @DiagonaLean.GrammarMem.decisionProblem_mk

example :
    ∀ (e f : DiagonaLean.KAComm.KleeneAlgebra.RExp (ℕ ⊕ ℕ)),
      DiagonaLean.KAComm.TermEq.DecisionProblem (e, f) ↔
        DiagonaLean.KAComm.KleeneAlgebra.RExp.Equiv DiagonaLean.KAComm.KleeneAlgebra.DComm e f :=
  @DiagonaLean.KAComm.TermEq.decisionProblem_mk

example :
    ∀ (e f : DiagonaLean.KAComm.KleeneAlgebra.RExp (Bool ⊕ Bool)),
      DiagonaLean.KAComm.TermEqBool.DecisionProblem (e, f) ↔
        DiagonaLean.KAComm.KleeneAlgebra.RExp.Equiv DiagonaLean.KAComm.KleeneAlgebra.DComm e f :=
  @DiagonaLean.KAComm.TermEqBool.decisionProblem_mk

example :
    ∀ (e f : DiagonaLean.KAComm.KleeneAlgebra.RExp (ℕ ⊕ ℕ)),
      DiagonaLean.KAComm.KATermEq.DecisionProblem (e, f) ↔
        DiagonaLean.KAComm.KleeneAlgebra.RExp.KAEquiv DiagonaLean.KAComm.KleeneAlgebra.DComm e f :=
  @DiagonaLean.KAComm.KATermEq.decisionProblem_mk

example :
    ∀ (e f : DiagonaLean.KAComm.KleeneAlgebra.RExp (Bool ⊕ Bool)),
      DiagonaLean.KAComm.KATermEqBool.DecisionProblem (e, f) ↔
        DiagonaLean.KAComm.KleeneAlgebra.RExp.KAEquiv DiagonaLean.KAComm.KleeneAlgebra.DComm e f :=
  @DiagonaLean.KAComm.KATermEqBool.decisionProblem_mk

example :
    ∀ (e f : DiagonaLean.KAComm.KleeneAlgebra.RExp (ℕ ⊕ ℕ)),
      DiagonaLean.KAComm.LangEq.DecisionProblem (e, f) ↔
        DiagonaLean.KAComm.KleeneAlgebra.TD.pl (DiagonaLean.KAComm.KleeneAlgebra.FreePreKA.mk e) =
          DiagonaLean.KAComm.KleeneAlgebra.TD.pl
            (DiagonaLean.KAComm.KleeneAlgebra.FreePreKA.mk f) :=
  @DiagonaLean.KAComm.LangEq.decisionProblem_mk

example :
    ∀ (e f : DiagonaLean.KAComm.KleeneAlgebra.RExp (Bool ⊕ Bool)),
      DiagonaLean.KAComm.LangEqBool.DecisionProblem (e, f) ↔
        DiagonaLean.KAComm.KleeneAlgebra.TD.pl (DiagonaLean.KAComm.KleeneAlgebra.FreePreKA.mk e) =
          DiagonaLean.KAComm.KleeneAlgebra.TD.pl
            (DiagonaLean.KAComm.KleeneAlgebra.FreePreKA.mk f) :=
  @DiagonaLean.KAComm.LangEqBool.decisionProblem_mk

example :
    ∀ (e f : DiagonaLean.KAComm.KleeneAlgebra.RExp (ℕ ⊕ ℕ)),
      DiagonaLean.KAComm.ModelLe.DecisionProblem (e, f) ↔
        DiagonaLean.KAComm.KleeneAlgebra.TD.pl (DiagonaLean.KAComm.KleeneAlgebra.FreePreKA.mk e) ≤
          DiagonaLean.KAComm.KleeneAlgebra.TD.pl
            (DiagonaLean.KAComm.KleeneAlgebra.FreePreKA.mk f) :=
  @DiagonaLean.KAComm.ModelLe.decisionProblem_mk

example :
    ∀ (e f : DiagonaLean.KAComm.KleeneAlgebra.RExp (Bool ⊕ Bool)),
      DiagonaLean.KAComm.ModelLeBool.DecisionProblem (e, f) ↔
        DiagonaLean.KAComm.KleeneAlgebra.TD.pl (DiagonaLean.KAComm.KleeneAlgebra.FreePreKA.mk e) ≤
          DiagonaLean.KAComm.KleeneAlgebra.TD.pl
            (DiagonaLean.KAComm.KleeneAlgebra.FreePreKA.mk f) :=
  @DiagonaLean.KAComm.ModelLeBool.decisionProblem_mk

example :
    ∀ (eve adam : Finset DiagonaLean.MatrixGame.Position),
      DiagonaLean.MatrixGame.DecisionProblem (eve, adam) ↔
        DiagonaLean.MatrixGame.EveForcesZero eve adam :=
  @DiagonaLean.MatrixGame.decisionProblem_mk

example :
    ∀ {α : Type} (G : DiagonaLean.CFGame.Game α) (w : List α),
      DiagonaLean.CFGame.DecisionProblem (G, w) ↔ DiagonaLean.CFGame.Wins G w :=
  @DiagonaLean.CFGame.decisionProblem_mk

example :
    ∀ {α : Type} [DecidableEq α] (G : DiagonaLean.TeamGame.Game α) (d : α),
      DiagonaLean.TeamGame.DecisionProblem (G, d) ↔ DiagonaLean.TeamGame.TeamWinsReach G d :=
  @DiagonaLean.TeamGame.decisionProblem_mk

example :
    ∀ {α : Type} [DecidableEq α] (G : DiagonaLean.TeamGame.Game α) (d : α),
      DiagonaLean.TeamGame.DecisionProblemSafety (G, d) ↔
        DiagonaLean.TeamGame.TeamWinsSafety G d :=
  @DiagonaLean.TeamGame.decisionProblemSafety_mk
