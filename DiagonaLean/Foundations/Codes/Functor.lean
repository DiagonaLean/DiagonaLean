/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Codes.Unary
import DiagonaLean.Foundations.Computability.MachineBridge
import DiagonaLean.Foundations.Computability.Prim
import DiagonaLean.Synthetic.Undecidability

@[expose] public section

/-! # Problems as functors on codes, and lifting them to every alphabet

Alphabets with letterwise codes `c : α → List β` as morphisms form a category (the Kleisli
category of `List`, restricted to a class `Good` of codes such as `IsCode` or `IsSync`). A problem
over every alphabet is a `CodeFunctor Good`: a type of instances `Inst α` for each alphabet, the
action `map c` of a code on instances (encode every word of the instance), and a predicate `Prob`
that every good code preserves and reflects (`natural`). In other words `Prob` is a natural
transformation from `Inst` to the constant functor `Prop`: the square

```
          map c
  Inst α ──────► Inst β
     Prob ╲      ╱ Prob
           Prop
```
commutes.

The lifting is proved once for every such problem:

* `CodeFunctor.undecidableOf`: undecidability over a countable alphabet transfers to every
  alphabet with two distinct letters, along `bitCode`.
* `CodeFunctor.not_computablePred_of`: so does `¬ ComputablePred`, once `map (bitCode b0 b1)` is
  computable. Instances are built from words by products and lists, so `map c` applies `encode c`
  to each word, and `encode_primrec` (proved once) with `fun_prop` gives its computability.

`Inst` is a functor on all codes, good or not (`map_unit`, `map_kcomp`): encoding by the
one-letter code `unit` changes nothing, and encoding by `c₁` then `c₂` is encoding by their
composite `kcomp c₂ c₁`. The lifting theorems do not use the laws; they record that `map` is the
action of codes and nothing else.
-/

namespace DiagonaLean.Foundations.Codes

open DiagonaLean.Synthetic.Notation DiagonaLean.Foundations.Computability

/-! ### The shared computability proof -/

section Prim

variable {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]

theorem encode_primrec {c : α → List β} (hc : Primrec c) : Primrec (encode c) :=
  Primrec.list_flatMap Primrec.id (hc.comp Primrec.snd).to₂

@[fun_prop] theorem prim_encode {c : α → List β} (hc : Primrec c) {f : γ → List α}
    (hf : Primrec f) : Primrec fun x => encode c (f x) :=
  (encode_primrec hc).comp hf

theorem unary_primrec : Primrec unary := by
  unfold unary
  fun_prop

theorem bitCode_primrec (b0 b1 : β) : Primrec (bitCode (α := α) b0 b1) := by
  unfold bitCode ofEncodable bit
  have := unary_primrec
  fun_prop

end Prim

/-! ### Problems as functors -/

/-- A problem over every alphabet, natural with respect to the codes in `Good`. -/
structure CodeFunctor (Good : ∀ {α β : Type}, (α → List β) → Prop) where
  /-- The instances over an alphabet. -/
  Inst : Type → Type
  /-- A code acts on instances by encoding their words. -/
  map : ∀ {α β : Type}, (α → List β) → Inst α → Inst β
  /-- The problem. -/
  Prob : ∀ {α : Type}, Inst α → Prop
  /-- Functor law: the identity code acts as the identity. -/
  map_unit : ∀ {α : Type} (x : Inst α), map unit x = x
  /-- Functor law: the composite of two codes acts as the composite of their actions. -/
  map_kcomp : ∀ {α β γ : Type} (c₁ : α → List β) (c₂ : β → List γ) (x : Inst α),
    map c₂ (map c₁ x) = map (kcomp c₂ c₁) x
  /-- Good codes preserve and reflect the problem. -/
  natural : ∀ {α β : Type} {c : α → List β}, Good c → ∀ x, Prob (map c x) ↔ Prob x

variable {Good : ∀ {α β : Type}, (α → List β) → Prop} (F : CodeFunctor Good) {α β : Type}

/-- A good code is a many-one reduction between the problem over its two alphabets. -/
def CodeFunctor.reduces (c : α → List β) (hc : Good c) : @F.Prob α ⪯ₘ @F.Prob β :=
  ⟨F.map c, fun x => (F.natural hc x).symm⟩

/-- **The lifting.** Undecidability over a countable alphabet transfers to every alphabet with two
distinct letters, when `bitCode` is good (it is synchronizing, `isSync_bitCode`). -/
def CodeFunctor.undecidableOf [Encodable α] (u : Undecidable (@F.Prob α)) (b0 b1 : β)
    (hc : Good (bitCode (α := α) b0 b1)) : Undecidable (@F.Prob β) :=
  undecidabilityFromReducibility u (F.reduces _ hc)

/-- **The lifting at machine level.** `¬ ComputablePred` transfers along a good code whose action on
instances is computable. -/
theorem CodeFunctor.not_computablePred_of [Primcodable (F.Inst α)] [Primcodable (F.Inst β)]
    {c : α → List β} (hc : Good c) (hmap : Computable (F.map c))
    (h : ¬ ComputablePred (@F.Prob α)) : ¬ ComputablePred (@F.Prob β) :=
  not_computablePred_of_reduces (F.reduces c hc) hmap h

/-- **The lifting at machine level, to every nontrivial alphabet.** -/
theorem CodeFunctor.not_computablePred_lift [Encodable α] [Nontrivial β]
    [Primcodable (F.Inst α)] [Primcodable (F.Inst β)]
    (hc : ∀ {b0 b1 : β}, b0 ≠ b1 → Good (bitCode (α := α) b0 b1))
    (hmap : ∀ b0 b1 : β, Computable (F.map (bitCode (α := α) b0 b1)))
    (h : ¬ ComputablePred (@F.Prob α)) : ¬ ComputablePred (@F.Prob β) := by
  obtain ⟨b0, b1, hne⟩ := exists_pair_ne β
  exact F.not_computablePred_of (hc hne) (hmap b0 b1) h

end DiagonaLean.Foundations.Codes
