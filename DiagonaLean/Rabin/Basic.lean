/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.Foundations.Computability.Prim
import DiagonaLean.Foundations.Computability.DerivePrimcodable
import DiagonaLean.Foundations.Computability.OutputSearch

@[expose] public section

/-! # Winner determination for Rabin's three-move game

Players I, II, I successively choose natural numbers `i`, `j`, `k`, seeing all earlier moves.
Player I wins exactly when `g k = i + j` (`PlayerIWins`). A finite payoff program (`PayoffCode`)
describes `g`. Its constructors give the primitive recursive schemes and an instruction that runs
a bounded simulation of a Turing machine, and the programs compute exactly the primitive recursive
functions
(`PayoffCode.eval_primrec`, `exists_payoffCode`). The problem (`DecisionProblem`) asks whether
Player I has a winning strategy for the payoff of a program.

## References

* [M. O. Rabin, *Effective computability of winning strategies*][Rabin1957]
-/

namespace DiagonaLean.Rabin

open DiagonaLean.Foundations.Computability

/-- Player I wins the play `i`, `j`, `k` when `g k = i + j`. -/
def PlayerIWins (g : ℕ → ℕ) (i j k : ℕ) : Prop := g k = i + j

/-- A strategy for Player II chooses a reply to the opening and wins against every last move. -/
def WinningII (g strategy : ℕ → ℕ) : Prop :=
  ∀ i k, ¬ PlayerIWins g i (strategy i) k

/-- Player I can choose an opening and a final move as a function of Player II's reply. -/
def HasWinningI (g : ℕ → ℕ) : Prop :=
  ∃ (i : ℕ) (last : ℕ → ℕ), ∀ j, PlayerIWins g i j (last j)

/-- A `PayoffCode` is a finite program for a primitive recursive payoff. The bounded instruction
returns its input when the supplied simulation has halted within that many steps, and zero
otherwise. -/
inductive PayoffCode where
  | zero | succ | left | right
  | pair (f g : PayoffCode)
  | comp (f g : PayoffCode)
  | prec (base step : PayoffCode)
  | bounded (data : List (ℕ × ℕ) × SC)

end DiagonaLean.Rabin

derive_primcodable DiagonaLean.Rabin.PayoffCode

namespace DiagonaLean.Rabin

open DiagonaLean.Foundations.Computability

/-- `c.eval` is the payoff function computed by the program `c`. -/
def PayoffCode.eval : PayoffCode → ℕ → ℕ
  | .zero => fun _ => 0
  | .succ => Nat.succ
  | .left => fun n => n.unpair.1
  | .right => fun n => n.unpair.2
  | .pair f g => fun n => Nat.pair (f.eval n) (g.eval n)
  | .comp f g => fun n => f.eval (g.eval n)
  | .prec f g => Nat.unpaired fun z n =>
      n.rec (f.eval z) fun y acc => g.eval (Nat.pair z (Nat.pair y acc))
  | .bounded d => fun k => if Test d k then k else 0

/-- Every payoff program computes a primitive recursive function. -/
theorem PayoffCode.eval_primrec (c : PayoffCode) : Primrec c.eval := by
  apply Primrec.nat_iff.mpr
  induction c with
  | zero => exact .zero
  | succ => exact .succ
  | left => exact .left
  | right => exact .right
  | pair _ _ hf hg => exact .pair hf hg
  | comp f g hf hg => exact Nat.Primrec.comp (f := f.eval) (g := g.eval) hf hg
  | prec _ _ hf hg => exact .prec hf hg
  | bounded d =>
    have ht := test_prim.comp (f := fun k : ℕ => (d, k)) ((Primrec.const d).pair Primrec.id)
    apply Primrec.nat_iff.mp
    change Primrec (fun k => if Test d k then k else 0)
    exact Primrec.ite ht Primrec.id (Primrec.const 0)

/-- Every primitive recursive payoff has a program using the ordinary recursion schemes. -/
theorem exists_payoffCode {g : ℕ → ℕ} (hg : Primrec g) : ∃ c : PayoffCode, c.eval = g := by
  replace hg := Primrec.nat_iff.mp hg
  induction hg with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | pair _ _ hf hg =>
    obtain ⟨f, rfl⟩ := hf
    obtain ⟨g, rfl⟩ := hg
    exact ⟨.pair f g, rfl⟩
  | comp _ _ hf hg =>
    obtain ⟨f, rfl⟩ := hf
    obtain ⟨g, rfl⟩ := hg
    exact ⟨.comp f g, rfl⟩
  | prec _ _ hf hg =>
    obtain ⟨f, rfl⟩ := hf
    obtain ⟨g, rfl⟩ := hg
    exact ⟨.prec f g, rfl⟩

/-- Player I has a winning strategy for the payoff computed by `c`. -/
def DecisionProblem (c : PayoffCode) : Prop := HasWinningI c.eval

end DiagonaLean.Rabin
