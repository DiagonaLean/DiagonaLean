/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji, Prathamesh Turaga
-/

import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

@[expose] public section

/-! # Two conditions on Turing machines

`NoBlankWrites tm`: the machine never writes a blank. `NoLeftBoundary tm w`: on input `w`, no
reachable configuration moves left at the left end of the tape. Reductions that encode
configurations as strings (MPCP, string rewriting) assume both, and `Normalize.normTM` turns any
machine over `Bool` into one satisfying them (`normTM_noBlankWrites`, `normTM_noLeftBoundary`).
-/

namespace DiagonaLean.Foundations.Normalize

open Cslib.Turing SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- `tm` is blank-write free: the transition function never writes the blank symbol. -/
def NoBlankWrites (tm : SingleTapeTM Symbol) : Prop :=
  ∀ q : tm.State, ∀ a : Option Symbol, ((tm.tr q a).1).symbol ≠ none

/-- `tm` satisfies the no-left-boundary condition on input `w`: no reachable configuration invokes a
  left-move at the left tape boundary. -/
def NoLeftBoundary (tm : SingleTapeTM Symbol) (w : List Symbol) : Prop :=
  ∀ (cfg : tm.Cfg), Relation.ReflTransGen tm.TransitionRelation
      (SingleTapeTM.initCfg tm w) cfg →
    ∀ (q : tm.State) (t : BiTape Symbol),
      cfg = ⟨some q, t⟩ → t.left.toList = [] →
      (tm.tr q t.head).1.movement ≠ some Turing.Dir.left

end DiagonaLean.Foundations.Normalize
