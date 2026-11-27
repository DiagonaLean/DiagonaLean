/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import Mathlib.Data.List.Palindrome
import DiagonaLean.PCP.MachineLevel

/-! # Does a linear grammar generate a palindrome?

A grammar has one nonterminal, ground rules `S → w`, and wrapping rules `S → u S v`.
Its alphabet consists of two letters and a separator. Run this example with
`lake env lean examples/PalindromeGrammar.lean`.
-/

namespace PalindromeGrammar

open DiagonaLean DiagonaLean.Synthetic.Definitions DiagonaLean.Foundations.Computability

/-- A word over two letters and a separator (`none`). -/
abbrev Word := List (Option Bool)
/-- Ground rules `S → w` and wrapping rules `S → u S v`. -/
abbrev Grammar := List Word × List (Word × Word)

/-- A finite derivation from the single nonterminal. -/
inductive Generates (g : Grammar) : Word → Prop where
  | ground {w} : w ∈ g.1 → Generates g w
  | wrap {u v w} : (u, v) ∈ g.2 → Generates g w → Generates g (u ++ w ++ v)

/-- Some terminal derivation of `g` yields a palindrome. -/
def HasPalindrome (g : Grammar) : Prop := ∃ w, Generates g w ∧ List.Palindrome w

private def wrapTile (t : PCP.Tile Bool) : Word × Word :=
  (t.top.map some, t.bot.reverse.map some)

private def marked (u v : List Bool) : Word :=
  u.map some ++ [none] ++ v.reverse.map some

/-- Ground rules choose the innermost tile. Each outer rule adds one more tile. -/
def ofPCP (p : PCP.Stack Bool) : Grammar :=
  (p.map (fun t => marked t.top t.bot), p.map wrapTile)

private theorem wrap_marked (t : PCP.Tile Bool) (u v : List Bool) :
    (wrapTile t).1 ++ marked u v ++ (wrapTile t).2 = marked (t.top ++ u) (t.bot ++ v) := by
  simp [wrapTile, marked, List.reverse_append, List.map_append, List.append_assoc]

private theorem generates_iff (p : PCP.Stack Bool) (w : Word) :
    Generates (ofPCP p) w ↔ ∃ ts : PCP.Stack Bool,
      ts ≠ [] ∧ (∀ t ∈ ts, t ∈ p) ∧ w = marked (PCP.τ1 ts) (PCP.τ2 ts) := by
  constructor
  · intro h
    induction h with
    | ground hm =>
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
      exact ⟨[t], by simp, by simpa, by simp⟩
    | wrap hm _ ih =>
      obtain ⟨t, ht, heq⟩ := List.mem_map.mp hm
      cases heq
      obtain ⟨ts, _, hs, rfl⟩ := ih
      exact ⟨t :: ts, by simp, by simpa using And.intro ht hs, wrap_marked t _ _⟩
  · rintro ⟨ts, hn, hs, rfl⟩
    induction ts with
    | nil => contradiction
    | cons t ts ih =>
      have ht := hs t (by simp)
      cases ts with
      | nil =>
        simpa using Generates.ground (g := ofPCP p) (List.mem_map_of_mem ht :
          marked t.top t.bot ∈ p.map (fun x => marked x.top x.bot))
      | cons u us =>
        rw [PCP.τ1_cons, PCP.τ2_cons, ← wrap_marked]
        apply Generates.wrap (List.mem_map_of_mem (f := wrapTile) ht)
        exact ih (by simp) (fun x hx => hs x (List.mem_cons_of_mem _ hx))

private def beforeMarker : Word → List Bool
  | some a :: w => a :: beforeMarker w
  | _ => []

private theorem before_marked (u v : List Bool) : beforeMarker (marked u v) = u := by
  induction u with
  | nil => rfl
  | cons a u ih => exact congrArg (a :: ·) ih

private theorem marked_palindrome (u v : List Bool) :
    List.Palindrome (marked u v) ↔ u = v := by
  have hrev : (marked u v).reverse = marked v u := by
    simp [marked, List.reverse_append, List.map_reverse, List.append_assoc]
  rw [List.Palindrome.iff_reverse_eq, hrev]
  exact ⟨fun h => by simpa only [before_marked] using (congrArg beforeMarker h).symm,
    fun h => h ▸ rfl⟩

private theorem correct (p : PCP.Stack Bool) : PCP.PCProblem p ↔ HasPalindrome (ofPCP p) := by
  constructor
  · rintro ⟨ts, hn, hs, he⟩
    exact ⟨_, (generates_iff _ _).2 ⟨ts, hn, hs, rfl⟩, (marked_palindrome _ _).2 he⟩
  · rintro ⟨w, hw, hp⟩
    obtain ⟨ts, hn, hs, rfl⟩ := (generates_iff _ _).1 hw
    exact ⟨ts, hn, hs, (marked_palindrome _ _).1 hp⟩

/-- PCP over `Bool` reduces to palindrome existence through `ofPCP`. -/
def fromPCP : PCP.PCProblem ⪯_s HasPalindrome := ⟨ofPCP, correct⟩

/-- `ofPCP` is computable. -/
@[fun_prop] theorem computable_ofPCP : Computable ofPCP := by
  apply Primrec.to_comp
  unfold ofPCP marked wrapTile
  fun_prop

/-- Palindrome existence for these one-nonterminal grammars is not a computable predicate. -/
theorem not_computablePred_hasPalindrome : ¬ ComputablePred HasPalindrome := by
  undec from PCP.PCProblem

end PalindromeGrammar
