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

Over two countable alphabets with two letters each, there are good codes both ways, so the
problem is many-one equivalent over the two (`CodeFunctor.manyOneEquiv`): its many-one degree does
not depend on the alphabet. The reductions themselves are data, `F.reduces (bitCode b0 b1)`; with
a computable action they give Mathlib's `ManyOneReducible` (`ManyOneReduces.toManyOneReducible`).
Every property closed under computable many-one reductions transports in both directions, for
instance being a computable predicate (`computablePred_iff_of_equiv`) or recursively enumerable
(`rePred_iff_of_equiv`). For a single reduction as data, `computablePred_of_reduces` and
`REPred.of_reduces` take `p ⪯ₘ q` with a computable function directly.

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

/-! ### The lift from the letters an instance uses

The lifting above needs a code good on the whole source alphabet, so the alphabet must be
countable. An instance uses finitely many letters, so a code built for each instance from the
letters it uses (`localCode`: the unary code of a letter's position among them) lifts from any
alphabet with decidable equality. Such a code is good only on those letters, which is enough when
codes that agree on them act alike on the instance (`Support.map_congr`): naturality for codes
good on the letters of an instance follows from naturality for good codes and the functor laws
(`Support.natural_on`). -/

/-- The closure properties of a class of good codes that the lift from the letters used needs. -/
structure GoodClass (Good : ∀ {α β : Type}, (α → List β) → Prop) : Prop where
  /-- Precomposing with an injective renaming of letters keeps a code good. -/
  comp_inj : ∀ {α β γ : Type} {c : β → List γ} {f : α → β}, Good c → Function.Injective f →
    Good (c ∘ f)
  /-- The identity code is good. -/
  unit_good : ∀ {α : Type}, Good (unit (α := α))
  /-- The unary code of the natural numbers, in two distinct letters, is good. -/
  bitCode_good : ∀ {β : Type} {b0 b1 : β}, b0 ≠ b1 → Good (bitCode (α := ℕ) b0 b1)

theorem goodClass_isCode : GoodClass IsCode :=
  ⟨fun hc hf => hc.comp hf, @fun _ => isCode_unit, fun hne => (isSync_bitCode hne).isCode⟩

theorem goodClass_isSync : GoodClass IsSync :=
  ⟨fun hc hf => hc.comp hf, isSync_unit, fun hne => isSync_bitCode hne⟩

/-- The letters an instance uses: codes that agree on them act alike on it. -/
structure CodeFunctor.Support where
  /-- The letters of an instance. -/
  supp : ∀ {α : Type}, F.Inst α → List α
  /-- Codes that agree on the letters of an instance act alike on it. -/
  map_congr : ∀ {α β : Type} {c c' : α → List β} (x : F.Inst α),
    (∀ a ∈ supp x, c a = c' a) → F.map c x = F.map c' x

/-- **Naturality on the letters used.** A code whose restriction to the letters of an instance is
good preserves and reflects the problem on that instance. The instance is moved to the subtype of
its letters by a code (`a ↦ [⟨a, h⟩]` on its letters), where the global naturality applies. -/
theorem CodeFunctor.Support.natural_on {F : CodeFunctor Good} (σ : F.Support) (G : GoodClass Good)
    [DecidableEq α] {c : α → List β} (x : F.Inst α)
    (hc : Good fun a : {a // a ∈ σ.supp x} => c a.1) : F.Prob (F.map c x) ↔ F.Prob x := by
  let ρ : α → List {a // a ∈ σ.supp x} := fun a => if h : a ∈ σ.supp x then [⟨a, h⟩] else []
  have hval : Good fun a : {a // a ∈ σ.supp x} => unit a.1 :=
    G.comp_inj G.unit_good Subtype.val_injective
  have e₁ : F.map (fun a : {a // a ∈ σ.supp x} => unit a.1) (F.map ρ x) = x :=
    calc _ = F.map (kcomp _ ρ) x := F.map_kcomp _ _ _
      _ = F.map unit x := σ.map_congr x fun a ha => by simp [kcomp, ρ, ha, unit]
      _ = x := F.map_unit x
  have e₂ : F.map (fun a : {a // a ∈ σ.supp x} => c a.1) (F.map ρ x) = F.map c x :=
    (F.map_kcomp _ _ _).trans (σ.map_congr x fun a ha => by simp [kcomp, ρ, ha])
  rw [← e₂, F.natural hc, ← F.natural hval (F.map ρ x), e₁]

/-- The code of a letter from its position among the letters `S`: the unary code of the position,
in the letters `b0`, `b1`. -/
def localCode [DecidableEq α] (b0 b1 : β) (S : List α) (a : α) : List β :=
  bitCode (α := ℕ) b0 b1 (S.idxOf a)

/-- `localCode` is good on the letters `S`: positions of distinct members of `S` differ. -/
theorem good_localCode (G : GoodClass Good) [DecidableEq α] {b0 b1 : β} (hne : b0 ≠ b1)
    (S : List α) : Good fun a : {a // a ∈ S} => localCode b0 b1 S a.1 :=
  G.comp_inj (f := fun a : {a // a ∈ S} => S.idxOf a.1) (G.bitCode_good hne)
    fun a _ h => Subtype.ext ((List.idxOf_inj a.2).1 h)

/-- **The lift from the letters used.** The problem over an alphabet with decidable equality
many-one reduces to it over any alphabet with two distinct letters, by encoding each instance with
the code of its own letters. -/
def CodeFunctor.Support.reduces {F : CodeFunctor Good} (σ : F.Support) (G : GoodClass Good)
    [DecidableEq α] (b0 b1 : β) (hne : b0 ≠ b1) : @F.Prob α ⪯ₘ @F.Prob β :=
  ⟨fun x => F.map (localCode b0 b1 (σ.supp x)) x,
    fun x => (σ.natural_on G x (good_localCode G hne _)).symm⟩

/-- **The lifting, from any alphabet with decidable equality.** -/
def CodeFunctor.Support.undecidableOf {F : CodeFunctor Good} (σ : F.Support) (G : GoodClass Good)
    [DecidableEq α] (u : Undecidable (@F.Prob α)) (b0 b1 : β) (hne : b0 ≠ b1) :
    Undecidable (@F.Prob β) :=
  undecidabilityFromReducibility u (σ.reduces G b0 b1 hne)

/-! ### Alphabet invariance -/

/-- A good code with a computable action is a computable many-one reduction. -/
theorem CodeFunctor.manyOneReducible [Primcodable (F.Inst α)] [Primcodable (F.Inst β)]
    {c : α → List β} (hc : Good c) (hmap : Computable (F.map c)) :
    ManyOneReducible (@F.Prob α) (@F.Prob β) :=
  (F.reduces c hc).toManyOneReducible hmap

/-- **Alphabet invariance.** Over two countable alphabets with two distinct letters each, the
problem is many-one equivalent, by `bitCode` both ways. -/
theorem CodeFunctor.manyOneEquiv [Encodable α] [Encodable β] [Nontrivial α] [Nontrivial β]
    [Primcodable (F.Inst α)] [Primcodable (F.Inst β)]
    (hcα : ∀ {b0 b1 : β}, b0 ≠ b1 → Good (bitCode (α := α) b0 b1))
    (hcβ : ∀ {b0 b1 : α}, b0 ≠ b1 → Good (bitCode (α := β) b0 b1))
    (hmapα : ∀ b0 b1 : β, Computable (F.map (bitCode (α := α) b0 b1)))
    (hmapβ : ∀ b0 b1 : α, Computable (F.map (bitCode (α := β) b0 b1))) :
    ManyOneEquiv (@F.Prob α) (@F.Prob β) := by
  obtain ⟨a0, a1, ha⟩ := exists_pair_ne α
  obtain ⟨b0, b1, hb⟩ := exists_pair_ne β
  exact ⟨F.manyOneReducible (hcα hb) (hmapα b0 b1), F.manyOneReducible (hcβ ha) (hmapβ a0 a1)⟩

section Transport

variable {X Y : Type} [Primcodable X] [Primcodable Y] {p : X → Prop} {q : Y → Prop}

/-- Being a computable predicate transfers back along a reduction (`⪯ₘ`) with a computable
function. -/
theorem computablePred_of_reduces (r : p ⪯ₘ q) (hr : Computable r.f) (hq : ComputablePred q) :
    ComputablePred p :=
  ComputablePred.computable_of_manyOneReducible (r.toManyOneReducible hr) hq

/-- Recursive enumerability transfers back along a reduction (`⪯ₘ`) with a computable function. -/
theorem REPred.of_reduces (r : p ⪯ₘ q) (hr : Computable r.f) (hq : REPred q) : REPred p :=
  REPred.of_eq (hq.comp hr) fun x => (r.hf x).symm

/-- Recursive enumerability transfers back along a computable many-one reduction. -/
theorem REPred.of_manyOneReducible (h : ManyOneReducible p q) (hq : REPred q) : REPred p := by
  obtain ⟨f, hf, hpq⟩ := h
  exact REPred.of_reduces (q := q) ⟨f, hpq⟩ hf hq

/-- Many-one equivalent predicates are computable together. -/
theorem computablePred_iff_of_equiv (h : ManyOneEquiv p q) : ComputablePred p ↔ ComputablePred q :=
  ⟨fun hp => ComputablePred.computable_of_manyOneReducible h.2 hp,
    fun hq => ComputablePred.computable_of_manyOneReducible h.1 hq⟩

/-- Many-one equivalent predicates are recursively enumerable together. -/
theorem rePred_iff_of_equiv (h : ManyOneEquiv p q) : REPred p ↔ REPred q :=
  ⟨fun hp => REPred.of_manyOneReducible h.2 hp, fun hq => REPred.of_manyOneReducible h.1 hq⟩

end Transport

end DiagonaLean.Foundations.Codes
