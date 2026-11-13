/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhilesh Balaji
-/

import DiagonaLean.AmbigCFG.Reductions.PCP_to_AmbigCFG

@[expose] public section

/-! # Undecidability of CFG ambiguity

CFG ambiguity is undecidable over any alphabet with two distinct letters (`ambigcfg_undecidable`).
An instance bundles the grammar with the number of tiles of the PCP instance it came from
(`AmbigCFGInstance`), so that all instances share one type.
-/

variable {α : Type} [DecidableEq α]

namespace DiagonaLean.AmbigCFG.Reduction

open DiagonaLean.PCP DiagonaLean.AmbigCFG DiagonaLean.Synthetic.Notation

/-- A context-free grammar over `PCPAlpha` for *some* tile-count `n`, bundled into one
  fixed type. `Stack.toGrammar P`'s own alphabet `PCPAlpha P = Sum α (Fin P.length)`
  depends on `P.length`, so it can't itself be the codomain of a many-one reduction
  `Stack α → Y` for a single fixed `Y` — `Undecidable`/`ManyOneReduces` need that.
  Bundling the length alongside the grammar is the standard way to state "CFG
  ambiguity is undecidable" once instances don't all share one alphabet. -/
abbrev AmbigCFGInstance (α : Type) : Type 1 :=
  Σ n : ℕ, ContextFreeGrammar (Sum α (Fin n))

/-- CFG ambiguity is undecidable: via `reduceFromPCP`, reduced from PCP over the same
  alphabet `α`, using `P ↦ ⟨P.length, Stack.toGrammar P⟩` as the reduction function
  (see `AmbigCFGInstance`) and `ambiguous_if_pcp`/`pcp_if_ambiguous` as the two
  correctness directions. -/
theorem ambigcfg_undecidable [Nontrivial α] :
    Undecidable (fun G : AmbigCFGInstance α => G.2.DecisionProblem) := by
  reduceFromPCP over_type α
    with_red_function (fun P : Stack α => (⟨P.length, Stack.toGrammar P⟩ : AmbigCFGInstance α))
    using_lemmas ambiguous_if_pcp pcp_if_ambiguous

end DiagonaLean.AmbigCFG.Reduction
