/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Tactic.DeriveFintype
import DiagonaLean.Foundations.Computability.ListConfig

@[expose] public section

/-! # Turing machine configurations as words

A configuration of a Cslib single-tape Turing machine with state `q`, head symbol `h`, and tape
halves `l` and `r` (each listed nearest cell first) is encoded as the word `⊢ rev(l) [q, h] r ⊣`
over the alphabet `Letter`. These machines replace the two-counter machines of the paper
(Definitions 10–11). The encoding is injective and prefix-free.
-/
namespace DiagonaLean.Foundations.KleeneAlgebra.Enc

open Cslib.Turing

export DiagonaLean.Foundations.Computability (Data Data.Running dstep stk stk_nil stk_cons cfgOf
  nil_head nil_tail step_cfgOf step_cfgOf_halted dstep_halted iterate_halted
  exists_iterate_of_reflTransGen initData stk_map_some cfgOf_initData)

/-- The alphabet `Σ` of configuration words. -/
inductive Letter (Sym St : Type) where
  /-- The left end marker `⊢`. -/
  | lend
  /-- The right end marker `⊣`. -/
  | rend
  /-- A tape cell holding `o` (`none` is blank). -/
  | cell (o : Option Sym)
  /-- The head letter `[q, o]`: state `q` (`none` means halted) scanning symbol `o`. -/
  | head (q : Option St) (o : Option Sym)
  deriving DecidableEq, Fintype

variable {Sym : Type} [Inhabited Sym] [Fintype Sym] {M : SingleTapeTM Sym}

/-- A list of tape cells as a list of `cell` letters. -/
def cells {St : Type} (a : List (Option Sym)) : List (Letter Sym St) := a.map Letter.cell

/-- The configuration word `⊢ rev(l) [q, h] r ⊣` of `d`. -/
def wd (d : Data M) : List (Letter Sym M.State) :=
  Letter.lend :: (cells d.l.reverse ++ Letter.head d.state d.h :: (cells d.r ++ [Letter.rend]))

/-- The configuration word `wd d` as an element of the free monoid. -/
def wdF (d : Data M) : FreeMonoid (Letter Sym M.State) := FreeMonoid.ofList (wd d)

omit [Inhabited Sym] [Fintype Sym] in
/-- `cells` is injective. -/
theorem cells_injective {St : Type} :
    Function.Injective (cells : List (Option Sym) → List (Letter Sym St)) :=
  List.map_injective_iff.2 fun _ _ h => Letter.cell.inj h

/-- A head letter does not occur in a list of cell letters. -/
theorem head_notMem_cells (q : Option M.State) (o : Option Sym) (a : List (Option Sym)) :
    Letter.head q o ∉ cells (St := M.State) a := by
  simp [cells]

/-- The right end marker does not occur in a list of cell letters. -/
theorem rend_notMem_cells (a : List (Option Sym)) : Letter.rend ∉ cells (St := M.State) a := by
  simp [cells]

/-- Two words of the form `cells a ++ head q o :: t` are equal only if all their parts are. -/
theorem cells_append_head_inj {a a' : List (Option Sym)} {q q' : Option M.State} {o o' : Option Sym}
    {t t' : List (Letter Sym M.State)}
    (h : cells a ++ Letter.head q o :: t = cells a' ++ Letter.head q' o' :: t') :
    a = a' ∧ q = q' ∧ o = o' ∧ t = t' := by
  induction a generalizing a' with
  | nil =>
    cases a' with
    | nil => simp only [cells, List.map_nil, List.nil_append, List.cons.injEq,
        Letter.head.injEq] at h; exact ⟨rfl, h.1.1, h.1.2, h.2⟩
    | cons b a' => simp [cells] at h
  | cons x a ih =>
    cases a' with
    | nil => simp [cells] at h
    | cons b a' =>
      simp only [cells, List.map_cons, List.cons_append, List.cons.injEq, Letter.cell.injEq] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨by rw [(ih h).1], (ih h).2⟩

/-- Distinct configurations have distinct words. -/
theorem wd_injective : Function.Injective (wd : Data M → List (Letter Sym M.State)) := by
  rintro ⟨q, l, h, r⟩ ⟨q', l', h', r'⟩ he
  simp only [wd, List.cons.injEq, true_and] at he
  obtain ⟨hl, rfl, rfl, hr⟩ := cells_append_head_inj he
  rw [List.append_cancel_right_eq] at hr
  rw [List.reverse_inj.1 hl, cells_injective hr]

/-- Every configuration word ends in `⊣` and has no other `⊣`. -/
theorem wd_eq (d : Data M) : ∃ x, wd d = x ++ [Letter.rend] ∧ Letter.rend ∉ x :=
  ⟨Letter.lend :: (cells d.l.reverse ++ Letter.head d.state d.h :: cells d.r), by simp [wd],
    by simp [cells]⟩

/-- Configuration words form a prefix-free set: `⊣` occurs only at the end. -/
theorem prefixFree {d d' : Data M} (h : wd d <+: wd d') : d = d' := by
  apply wd_injective
  obtain ⟨t, ht⟩ := h
  obtain ⟨x, hx, hxr⟩ := wd_eq d
  obtain ⟨x', hx', hxr'⟩ := wd_eq d'
  by_cases h0 : t = []
  · subst h0; simpa using ht
  · exfalso
    have h1 := congrArg List.dropLast ht
    rw [hx, hx', List.dropLast_append_of_ne_nil h0, List.dropLast_concat] at h1
    exact hxr' (h1 ▸ by simp)

/-- The word of `d` has length `|l| + |r| + 3`. -/
theorem length_wd (d : Data M) : (wd d).length = d.l.length + d.r.length + 3 := by
  simp [wd, cells]; omega

/-- One step makes the configuration word at most one letter longer. -/
theorem length_wd_dstep (d : Data M) : (wd (dstep M d)).length ≤ (wd d).length + 1 := by
  obtain ⟨_ | q, l, h, r⟩ := d
  · simp [dstep]
  · simp only [length_wd, dstep]
    rcases M.tr q h with ⟨⟨wr, _ | _ | _⟩, q'⟩
    · simp
    · cases l <;> (simp; try omega)
    · cases r <;> (simp; try omega)

end DiagonaLean.Foundations.KleeneAlgebra.Enc
