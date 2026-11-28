/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.Foundations.Computability.HaltCanon
import DiagonaLean.Foundations.Computability.Interpreter
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # The halting problem is complete for the recursively enumerable problems

Every recursively enumerable predicate many-one reduces to the halting problem on canonical
machines (`manyOneReducible_haltCanon_of_rePred`). Its semi-decision procedure is a partial
recursive function `g` with `p a ↔ (g (encode a)).Dom`, and the compiler `exists_machine` turns `g`
into one fixed machine `W` that halts on the tape of `n` exactly when `g n` is defined. `W` is a
finite constant, obtained classically, so its canonical form is a constant too, and the reduction
`a ↦ (canonical form of W, tape of encode a)` is computable.

A halting-hard problem is therefore at least as hard as every recursively enumerable problem
(`ManyOneReducible.of_rePred_of_haltHard`), and two problems that are both halting-hard and
recursively enumerable are many-one equivalent (`manyOneEquiv_of_haltHard_of_rePred`): they have
the same many-one degree, the degree of the halting problem.

## Main statements

* `manyOneReducible_haltCanon_of_rePred`: `HaltCanon` is complete for the r.e. predicates.
* `ManyOneReducible.of_rePred_of_haltHard`: an r.e. predicate reduces to every halting-hard one.
* `manyOneEquiv_of_haltHard_of_rePred`: halting-hard r.e. predicates are many-one equivalent.

## References

* H. Rogers, *Theory of Recursive Functions and Effective Computability* (1967), Section 7.2
-/

namespace DiagonaLean.Foundations.Computability

open Cslib.Turing Turing Nat.Partrec DiagonaLean.Halt DiagonaLean.Halt.Encoding

variable {α : Type*} [Primcodable α]

/-- **The halting problem on canonical machines is complete for the r.e. predicates**: every
recursively enumerable predicate many-one reduces to it, computably. -/
theorem manyOneReducible_haltCanon_of_rePred {p : α → Prop} (hp : REPred p) :
    ManyOneReducible p HaltCanon := by
  classical
  -- the semi-decision procedure, on numbers
  let g : ℕ →. ℕ := fun n =>
    (Part.ofOption (Encodable.decode (α := α) n)).bind fun a =>
      (Part.assert (p a) fun _ => Part.some ()).map fun _ => 0
  have hg : Partrec g :=
    Computable.decode.ofOption.bind ((hp.comp Computable.snd).map (Computable.const 0).to₂)
  have hdom : ∀ a, (g (Encodable.encode a)).Dom ↔ p a := fun a => by
    simp only [g, Encodable.encodek, Part.coe_some, Part.bind_some, Part.map_Dom]
    exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩
  -- the compiled machine, which halts exactly when `g` converges
  obtain ⟨W, e₀, e, hout, hhalt⟩ := exists_machine g hg
  let M : EncodableTM Bool :=
    { W with stateEncodable := Encodable.ofEquiv _ (Fintype.equivFin W.State) }
  let tape : ℕ → List Bool := fun n => e₀ ++ (bitsOf n).reverse.flatMap fun b => e (bitG b)
  have htape : ∀ n, e₀ ++ (PartrecToTM2.trNat n).reverse.flatMap e = tape n := fun n => by
    simp only [tape, ← bitsOf_map, ← List.map_reverse, List.flatMap_map]
  -- the tape is primitive recursive: `e` is a function on a finite alphabet
  have he : Primrec fun b : Bool => e (bitG b) := Primrec.dom_bool _
  have ht : Primrec fun a : α => tape (Encodable.encode a) :=
    Primrec.list_append.comp (Primrec.const e₀)
      (Primrec.list_flatMap (Primrec.list_reverse.comp (bitsOf_prim.comp Primrec.encode))
        (he.comp Primrec.snd).to₂)
  refine ⟨fun a => (parse (encodeBoolTM M), tape (Encodable.encode a)),
    (Computable.const _).pair ht.to_comp, fun a => ?_⟩
  show p a ↔ Halts (parse (encodeBoolTM M)).toTM.toSingleTapeTM (tape (Encodable.encode a))
  rw [halts_parse_code M, ← hdom, ← htape]
  constructor
  · intro hd
    obtain ⟨m, hm⟩ := Part.dom_iff_mem.1 hd
    exact ⟨_, hout _ m hm⟩
  · rintro ⟨t, ht⟩
    exact hhalt _ ((SingleTapeTM.eval_dom_iff W _).2 ⟨t, ht⟩)

variable {β : Type*} [Primcodable β]

/-- **An r.e. predicate reduces to every halting-hard predicate**: through the halting problem. -/
theorem _root_.ManyOneReducible.of_rePred_of_haltHard {p : α → Prop} {q : β → Prop} (hp : REPred p)
    (hq : HaltHard q) : ManyOneReducible p q :=
  (manyOneReducible_haltCanon_of_rePred hp).trans (haltHard_iff.1 hq)

/-- **Halting-hard r.e. predicates are many-one equivalent**: both have the degree of the halting
problem. -/
theorem manyOneEquiv_of_haltHard_of_rePred {p : α → Prop} {q : β → Prop} (hp : HaltHard p)
    (hp' : REPred p) (hq : HaltHard q) (hq' : REPred q) : ManyOneEquiv p q :=
  ⟨.of_rePred_of_haltHard hp' hq, .of_rePred_of_haltHard hq' hp⟩

end DiagonaLean.Foundations.Computability
