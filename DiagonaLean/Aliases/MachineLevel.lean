/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.AmbigCFG.AlphabetLift
import DiagonaLean.AmbigCFG.Reductions.PCP_to_AmbigCFGCode
import DiagonaLean.EmpCFG.AlphabetLift
import DiagonaLean.EmpCFG.Reductions.PCP_to_EmpCFGCode
import DiagonaLean.EmpCFG.Undecidable
import DiagonaLean.GrammarMem.Reductions.HaltCanon_to_GrammarMem
import DiagonaLean.GrammarMem.Reductions.SemiThue_to_GrammarMem
import DiagonaLean.MPCP.Reductions.HaltCanon_to_MPCP
import DiagonaLean.MPCP.Undecidable
import DiagonaLean.SemiThue.AlphabetLift
import DiagonaLean.SemiThue.Reductions.HaltCanon_to_SemiThue

@[expose] public section

/-! # Deprecated names: the `MachineLevel` namespaces

The files `X/MachineLevel.lean` and `X/Hardness.lean` were split on 2026-11-27: constructions moved
to `X/Reductions/`, results to `X/Undecidable.lean`, alphabet lifts stayed in `X/AlphabetLift.lean`.
Their namespaces `DiagonaLean.X.MachineLevel` followed, as `X.Reduction`, `X` and `X.AlphabetLift`.
The old names are kept here as deprecated aliases, so that a branch started before the split
builds with warnings that name the new declaration. Delete this file, and its import in
`DiagonaLean.lean`, once no active branch uses the old names.

## Main statements

* One deprecated alias for each declaration of the former `MachineLevel` namespaces, except the
  automatically named `Primcodable` instance of type 0 grammar codes, which is found by its type.
-/

namespace DiagonaLean.AmbigCFG.MachineLevel

-- from `DiagonaLean.AmbigCFG.AlphabetLift`
@[deprecated AmbigCFG.AlphabetLift.CodeProblem (since := "2026-11-27")]
alias CodeProblem := AmbigCFG.AlphabetLift.CodeProblem
@[deprecated AmbigCFG.AlphabetLift.ambCodeFunctor (since := "2026-11-27")]
alias ambCodeFunctor := AmbigCFG.AlphabetLift.ambCodeFunctor
@[deprecated AmbigCFG.AlphabetLift.ambigCFGCode_manyOneEquiv (since := "2026-11-27")]
alias ambigCFGCode_manyOneEquiv := AmbigCFG.AlphabetLift.ambigCFGCode_manyOneEquiv
@[deprecated AmbigCFG.AlphabetLift.codeProblemReduces (since := "2026-11-27")]
alias codeProblemReduces := AmbigCFG.AlphabetLift.codeProblemReduces
@[deprecated AmbigCFG.AlphabetLift.codeProblemReduces' (since := "2026-11-27")]
alias codeProblemReduces' := AmbigCFG.AlphabetLift.codeProblemReduces'
@[deprecated AmbigCFG.AlphabetLift.codeProblem_eq (since := "2026-11-27")]
alias codeProblem_eq := AmbigCFG.AlphabetLift.codeProblem_eq
@[deprecated AmbigCFG.AlphabetLift.codeProblem_iff (since := "2026-11-27")]
alias codeProblem_iff := AmbigCFG.AlphabetLift.codeProblem_iff
-- from `DiagonaLean.AmbigCFG.Reductions.PCP_to_AmbigCFGCode`
@[deprecated AmbigCFG.Reduction.absTs (since := "2026-11-27")]
alias absTs := AmbigCFG.Reduction.absTs
@[deprecated AmbigCFG.Reduction.absTs_map_val (since := "2026-11-27")]
alias absTs_map_val := AmbigCFG.Reduction.absTs_map_val
@[deprecated AmbigCFG.Reduction.ambCode (since := "2026-11-27")]
alias ambCode := AmbigCFG.Reduction.ambCode
@[deprecated AmbigCFG.Reduction.ambCode_eq_map (since := "2026-11-27")]
alias ambCode_eq_map := AmbigCFG.Reduction.ambCode_eq_map
@[deprecated AmbigCFG.Reduction.ambCode_prim (since := "2026-11-27")]
alias ambCode_prim := AmbigCFG.Reduction.ambCode_prim
@[deprecated AmbigCFG.Reduction.ambPres (since := "2026-11-27")]
alias ambPres := AmbigCFG.Reduction.ambPres
@[deprecated AmbigCFG.Reduction.ambPres_map (since := "2026-11-27")]
alias ambPres_map := AmbigCFG.Reduction.ambPres_map
@[deprecated AmbigCFG.Reduction.codeTs (since := "2026-11-27")]
alias codeTs := AmbigCFG.Reduction.codeTs
@[deprecated AmbigCFG.Reduction.ntIdx (since := "2026-11-27")]
alias ntIdx := AmbigCFG.Reduction.ntIdx
@[deprecated AmbigCFG.Reduction.ntIdx_injective (since := "2026-11-27")]
alias ntIdx_injective := AmbigCFG.Reduction.ntIdx_injective
@[deprecated AmbigCFG.Reduction.pcp_reducesto_ambigCFGCode_spec (since := "2026-11-27")]
alias pcp_reducesto_ambigCFGCode_spec := AmbigCFG.Reduction.pcp_reducesto_ambigCFGCode_spec
@[deprecated AmbigCFG.Reduction.toCFG_ambPres_abs (since := "2026-11-27")]
alias toCFG_ambPres_abs := AmbigCFG.Reduction.toCFG_ambPres_abs

end DiagonaLean.AmbigCFG.MachineLevel

namespace DiagonaLean.EmpCFG.MachineLevel

-- from `DiagonaLean.EmpCFG.AlphabetLift`
@[deprecated EmpCFG.AlphabetLift.CodeProblem (since := "2026-11-27")]
alias CodeProblem := EmpCFG.AlphabetLift.CodeProblem
@[deprecated EmpCFG.AlphabetLift.codeProblem_eq (since := "2026-11-27")]
alias codeProblem_eq := EmpCFG.AlphabetLift.codeProblem_eq
@[deprecated EmpCFG.AlphabetLift.codeProblem_iff (since := "2026-11-27")]
alias codeProblem_iff := EmpCFG.AlphabetLift.codeProblem_iff
@[deprecated EmpCFG.AlphabetLift.empCFGCode_manyOneEquiv (since := "2026-11-27")]
alias empCFGCode_manyOneEquiv := EmpCFG.AlphabetLift.empCFGCode_manyOneEquiv
@[deprecated EmpCFG.AlphabetLift.empCodeFunctor (since := "2026-11-27")]
alias empCodeFunctor := EmpCFG.AlphabetLift.empCodeFunctor
-- from `DiagonaLean.EmpCFG.Reductions.PCP_to_EmpCFGCode`
@[deprecated EmpCFG.Reduction.empCode (since := "2026-11-27")]
alias empCode := EmpCFG.Reduction.empCode
@[deprecated EmpCFG.Reduction.empCode_prim (since := "2026-11-27")]
alias empCode_prim := EmpCFG.Reduction.empCode_prim
@[deprecated EmpCFG.Reduction.genPres (since := "2026-11-27")]
alias genPres := EmpCFG.Reduction.genPres
@[deprecated EmpCFG.Reduction.genPres_zero (since := "2026-11-27")]
alias genPres_zero := EmpCFG.Reduction.genPres_zero
@[deprecated EmpCFG.Reduction.language_toCFG_genPres_zero (since := "2026-11-27")]
alias language_toCFG_genPres_zero := EmpCFG.Reduction.language_toCFG_genPres_zero
@[deprecated EmpCFG.Reduction.pcp_reducesto_empCFGCode_spec (since := "2026-11-27")]
alias pcp_reducesto_empCFGCode_spec := EmpCFG.Reduction.pcp_reducesto_empCFGCode_spec
@[deprecated EmpCFG.Reduction.toCFG_genPres_unit (since := "2026-11-27")]
alias toCFG_genPres_unit := EmpCFG.Reduction.toCFG_genPres_unit
-- from `DiagonaLean.EmpCFG.Undecidable`
@[deprecated EmpCFG.not_computablePred_empCFGCode_empty (since := "2026-11-27")]
alias not_computablePred_empCFGCode_empty := EmpCFG.not_computablePred_empCFGCode_empty
@[deprecated EmpCFG.not_machineDecidable_empCFGCode_empty (since := "2026-11-27")]
alias not_machineDecidable_empCFGCode_empty := EmpCFG.not_machineDecidable_empCFGCode_empty

end DiagonaLean.EmpCFG.MachineLevel

namespace DiagonaLean.GrammarMem.MachineLevel

-- from `DiagonaLean.GrammarMem.Reductions.HaltCanon_to_GrammarMem`
@[deprecated GrammarMem.Reduction.canonGCode (since := "2026-11-27")]
alias canonGCode := GrammarMem.Reduction.canonGCode
@[deprecated GrammarMem.Reduction.canonGCode_prim (since := "2026-11-27")]
alias canonGCode_prim := GrammarMem.Reduction.canonGCode_prim
@[deprecated GrammarMem.Reduction.haltCanon_iff_emptyWord (since := "2026-11-27")]
alias haltCanon_iff_emptyWord := GrammarMem.Reduction.haltCanon_iff_emptyWord
@[deprecated GrammarMem.Reduction.isType0_canonGCode (since := "2026-11-27")]
alias isType0_canonGCode := GrammarMem.Reduction.isType0_canonGCode
-- from `DiagonaLean.GrammarMem.Reductions.SemiThue_to_GrammarMem`
@[deprecated GrammarMem.Reduction.emptyWord_ofSRS_iff (since := "2026-11-27")]
alias emptyWord_ofSRS_iff := GrammarMem.Reduction.emptyWord_ofSRS_iff
@[deprecated GrammarMem.Reduction.gSym (since := "2026-11-27")]
alias gSym := GrammarMem.Reduction.gSym
@[deprecated GrammarMem.Reduction.gSym_injective (since := "2026-11-27")]
alias gSym_injective := GrammarMem.Reduction.gSym_injective
@[deprecated GrammarMem.Reduction.gSym_ne_start (since := "2026-11-27")]
alias gSym_ne_start := GrammarMem.Reduction.gSym_ne_start
@[deprecated GrammarMem.Reduction.gSym_prim (since := "2026-11-27")]
alias gSym_prim := GrammarMem.Reduction.gSym_prim
@[deprecated GrammarMem.Reduction.isType0_ofSRS (since := "2026-11-27")]
alias isType0_ofSRS := GrammarMem.Reduction.isType0_ofSRS
@[deprecated GrammarMem.Reduction.isType0_prim (since := "2026-11-27")]
alias isType0_prim := GrammarMem.Reduction.isType0_prim
@[deprecated GrammarMem.Reduction.ofSRS (since := "2026-11-27")]
alias ofSRS := GrammarMem.Reduction.ofSRS
@[deprecated GrammarMem.Reduction.ofSRS_prim (since := "2026-11-27")]
alias ofSRS_prim := GrammarMem.Reduction.ofSRS_prim

end DiagonaLean.GrammarMem.MachineLevel

namespace DiagonaLean.MPCP.MachineLevel

-- from `DiagonaLean.MPCP.Reductions.HaltCanon_to_MPCP`
@[deprecated MPCP.Reduction.CanonTM.sameTable (since := "2026-11-27")]
alias CanonTM.sameTable := MPCP.Reduction.CanonTM.sameTable
@[deprecated MPCP.Reduction.SameTable (since := "2026-11-27")]
alias SameTable := MPCP.Reduction.SameTable
@[deprecated MPCP.Reduction.canonInst (since := "2026-11-27")]
alias canonInst := MPCP.Reduction.canonInst
@[deprecated MPCP.Reduction.canonInst_prim (since := "2026-11-27")]
alias canonInst_prim := MPCP.Reduction.canonInst_prim
@[deprecated MPCP.Reduction.codeOf (since := "2026-11-27")]
alias codeOf := MPCP.Reduction.codeOf
@[deprecated MPCP.Reduction.haltCanon_iff_mpcp (since := "2026-11-27")]
alias haltCanon_iff_mpcp := MPCP.Reduction.haltCanon_iff_mpcp
@[deprecated MPCP.Reduction.halts_iff_mpcpN (since := "2026-11-27")]
alias halts_iff_mpcpN := MPCP.Reduction.halts_iff_mpcpN
@[deprecated MPCP.Reduction.markerN (since := "2026-11-27")]
alias markerN := MPCP.Reduction.markerN
@[deprecated MPCP.Reduction.markerN_prim (since := "2026-11-27")]
alias markerN_prim := MPCP.Reduction.markerN_prim
@[deprecated MPCP.Reduction.mem_idx (since := "2026-11-27")]
alias mem_idx := MPCP.Reduction.mem_idx
@[deprecated MPCP.Reduction.mem_range_eight (since := "2026-11-27")]
alias mem_range_eight := MPCP.Reduction.mem_range_eight
@[deprecated MPCP.Reduction.mem_stackN (since := "2026-11-27")]
alias mem_stackN := MPCP.Reduction.mem_stackN
@[deprecated MPCP.Reduction.mem_stackN_congr (since := "2026-11-27")]
alias mem_stackN_congr := MPCP.Reduction.mem_stackN_congr
@[deprecated MPCP.Reduction.mem_transN (since := "2026-11-27")]
alias mem_transN := MPCP.Reduction.mem_transN
@[deprecated MPCP.Reduction.mem_transN_congr (since := "2026-11-27")]
alias mem_transN_congr := MPCP.Reduction.mem_transN_congr
@[deprecated MPCP.Reduction.normTrN (since := "2026-11-27")]
alias normTrN := MPCP.Reduction.normTrN
@[deprecated MPCP.Reduction.normTrN_congr (since := "2026-11-27")]
alias normTrN_congr := MPCP.Reduction.normTrN_congr
@[deprecated MPCP.Reduction.normTrN_eq (since := "2026-11-27")]
alias normTrN_eq := MPCP.Reduction.normTrN_eq
@[deprecated MPCP.Reduction.normTrN_prim (since := "2026-11-27")]
alias normTrN_prim := MPCP.Reduction.normTrN_prim
@[deprecated MPCP.Reduction.ren (since := "2026-11-27")]
alias ren := MPCP.Reduction.ren
@[deprecated MPCP.Reduction.simN (since := "2026-11-27")]
alias simN := MPCP.Reduction.simN
@[deprecated MPCP.Reduction.simN_eq (since := "2026-11-27")]
alias simN_eq := MPCP.Reduction.simN_eq
@[deprecated MPCP.Reduction.simN_prim (since := "2026-11-27")]
alias simN_prim := MPCP.Reduction.simN_prim
@[deprecated MPCP.Reduction.stIdx (since := "2026-11-27")]
alias stIdx := MPCP.Reduction.stIdx
@[deprecated MPCP.Reduction.stIdx_injective (since := "2026-11-27")]
alias stIdx_injective := MPCP.Reduction.stIdx_injective
@[deprecated MPCP.Reduction.stackN (since := "2026-11-27")]
alias stackN := MPCP.Reduction.stackN
@[deprecated MPCP.Reduction.stackN_prim (since := "2026-11-27")]
alias stackN_prim := MPCP.Reduction.stackN_prim
@[deprecated MPCP.Reduction.startN (since := "2026-11-27")]
alias startN := MPCP.Reduction.startN
@[deprecated MPCP.Reduction.startN_prim (since := "2026-11-27")]
alias startN_prim := MPCP.Reduction.startN_prim
@[deprecated MPCP.Reduction.startTile_ren (since := "2026-11-27")]
alias startTile_ren := MPCP.Reduction.startTile_ren
@[deprecated MPCP.Reduction.syms2 (since := "2026-11-27")]
alias syms2 := MPCP.Reduction.syms2
@[deprecated MPCP.Reduction.trTilesN (since := "2026-11-27")]
alias trTilesN := MPCP.Reduction.trTilesN
@[deprecated MPCP.Reduction.trTilesN_prim (since := "2026-11-27")]
alias trTilesN_prim := MPCP.Reduction.trTilesN_prim
@[deprecated MPCP.Reduction.transN (since := "2026-11-27")]
alias transN := MPCP.Reduction.transN
@[deprecated MPCP.Reduction.transN_prim (since := "2026-11-27")]
alias transN_prim := MPCP.Reduction.transN_prim
@[deprecated MPCP.Reduction.transitionTilesFor_ren (since := "2026-11-27")]
alias transitionTilesFor_ren := MPCP.Reduction.transitionTilesFor_ren
-- from `DiagonaLean.MPCP.Undecidable`
@[deprecated MPCP.mpcp_manyOneEquiv (since := "2026-11-27")]
alias mpcp_manyOneEquiv := MPCP.mpcp_manyOneEquiv

end DiagonaLean.MPCP.MachineLevel

namespace DiagonaLean.SemiThue.MachineLevel

-- from `DiagonaLean.SemiThue.AlphabetLift`
@[deprecated SemiThue.AlphabetLift.semiThuePos_manyOneEquiv (since := "2026-11-27")]
alias semiThuePos_manyOneEquiv := SemiThue.AlphabetLift.semiThuePos_manyOneEquiv
-- from `DiagonaLean.SemiThue.Reductions.HaltCanon_to_SemiThue`
@[deprecated SemiThue.Reduction.canonToEmpty (since := "2026-11-27")]
alias canonToEmpty := SemiThue.Reduction.canonToEmpty
@[deprecated SemiThue.Reduction.canonToEmpty_prim (since := "2026-11-27")]
alias canonToEmpty_prim := SemiThue.Reduction.canonToEmpty_prim
@[deprecated SemiThue.Reduction.canonWord (since := "2026-11-27")]
alias canonWord := SemiThue.Reduction.canonWord
@[deprecated SemiThue.Reduction.canonWord_prim (since := "2026-11-27")]
alias canonWord_prim := SemiThue.Reduction.canonWord_prim
@[deprecated SemiThue.Reduction.codeRules (since := "2026-11-27")]
alias codeRules := SemiThue.Reduction.codeRules
@[deprecated SemiThue.Reduction.codeRules_lhs_ne (since := "2026-11-27")]
alias codeRules_lhs_ne := SemiThue.Reduction.codeRules_lhs_ne
@[deprecated SemiThue.Reduction.codeRules_prim (since := "2026-11-27")]
alias codeRules_prim := SemiThue.Reduction.codeRules_prim
@[deprecated SemiThue.Reduction.haltCanon_iff_toEmpty (since := "2026-11-27")]
alias haltCanon_iff_toEmpty := SemiThue.Reduction.haltCanon_iff_toEmpty
@[deprecated SemiThue.Reduction.haltRules (since := "2026-11-27")]
alias haltRules := SemiThue.Reduction.haltRules
@[deprecated SemiThue.Reduction.halts_iff_toEmptyN (since := "2026-11-27")]
alias halts_iff_toEmptyN := SemiThue.Reduction.halts_iff_toEmptyN
@[deprecated SemiThue.Reduction.mem_codeRules (since := "2026-11-27")]
alias mem_codeRules := SemiThue.Reduction.mem_codeRules
@[deprecated SemiThue.Reduction.mem_codeRules_congr (since := "2026-11-27")]
alias mem_codeRules_congr := SemiThue.Reduction.mem_codeRules_congr
@[deprecated SemiThue.Reduction.toEmptyOf (since := "2026-11-27")]
alias toEmptyOf := SemiThue.Reduction.toEmptyOf
@[deprecated SemiThue.Reduction.toEmptyOf_prim (since := "2026-11-27")]
alias toEmptyOf_prim := SemiThue.Reduction.toEmptyOf_prim

end DiagonaLean.SemiThue.MachineLevel
