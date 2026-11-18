/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.PrimrecRec

@[expose] public section

/-! # Finitely branching trees are `Primcodable`

`PTree α ar` is the type of trees whose nodes carry a shape `a : α` and exactly `ar a` children:
the W-type of the polynomial with shapes `α` and arities `ar`. Almost every inductive type is of
this form. When `α` is `Primcodable` and `ar` is primitive recursive, `PTree α ar` is `Primcodable`
(Theorem A of `AUTOMATION.md`).

The encoding sends `node a cs` to `Nat.pair (encode a) (encode [encode (cs 0), …])`. A child's code
is smaller than its parent's (`encode_child_lt`), so decoding is a recursion on the code. Because
the encoding is canonical, `encode (decode n)` is `n + 1` when `n` is the code of a tree and `0`
otherwise, so the decoder is primitive recursive as soon as the set of codes is
(`valid_primrec`), which is a course-of-values recursion.

Building a node (`mkOpt`) and taking one apart (`shape`, `children`) are primitive recursive
(`mkOpt_primrec`, `shape_primrec`, `children_primrec`). A fold with a primitive recursive step is
primitive recursive (`fold_primrec`, Theorem B), and so is a paramorphism, whose step also sees the
children (`para_primrec`). The fold is mirrored on codes (`codeFold`), which satisfies a
course-of-values equation (`codeFold_eq`) and agrees with the fold on codes of trees
(`codeFold_code`).

`PTree` is its own inductive type rather than Mathlib's `WType`, which already has a different
`Encodable` instance.
-/

namespace DiagonaLean.Foundations.Computability

open Encodable

/-- Trees whose nodes carry a shape `a : α` and `ar a` children. -/
inductive PTree (α : Type) (ar : α → ℕ) : Type where
  /-- A node with shape `a` and children `cs`. -/
  | node (a : α) (cs : Fin (ar a) → PTree α ar)

namespace PTree

variable {α : Type} {ar : α → ℕ}

section Encode

variable [Encodable α]

/-- The code of a tree. -/
def code : PTree α ar → ℕ
  | node a cs => Nat.pair (encode a) (encode (List.ofFn fun i => code (cs i)))

/-- An element of a list of numbers is smaller than the list's code. -/
theorem lt_encode_of_mem {c : ℕ} : ∀ {l : List ℕ}, c ∈ l → c < encode l
  | x :: l, h => by
    rw [encode_list_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.lt_succ_of_le (Nat.left_le_pair _ _)
    · exact Nat.lt_succ_of_le ((lt_encode_of_mem h).le.trans (Nat.right_le_pair _ _))

/-- A child's code is smaller than its parent's. -/
theorem code_child_lt (a : α) (cs : Fin (ar a) → PTree α ar) (i : Fin (ar a)) :
    code (cs i) < code (node a cs) := by
  rw [code]
  have h : code (cs i) ∈ List.ofFn fun j => code (cs j) := List.mem_ofFn.2 ⟨i, rfl⟩
  exact (lt_encode_of_mem h).trans_le (Nat.right_le_pair _ _)

/-- Decoding: a node is decoded when its shape decodes (with `decode₂`, so that decoding is
canonical), its list of child codes has length
`ar a` and only smaller entries, and every child decodes. -/
def decodeT (n : ℕ) : Option (PTree α ar) :=
  match decode₂ α n.unpair.1, decode₂ (List ℕ) n.unpair.2 with
  | some a, some l =>
    if hl : l.length = ar a ∧ ∀ c ∈ l, c < n then
      let cs : Fin (ar a) → Option (PTree α ar) := fun i =>
        have : l[i.val] < n := hl.2 _ (List.getElem_mem _)
        decodeT l[i.val]
      if hall : ∀ i, (cs i).isSome then some (node a fun i => (cs i).get (hall i)) else none
    else none
  | _, _ => none
termination_by n

/-- Decoding inverts the code. -/
theorem decodeT_code (t : PTree α ar) : decodeT (code t) = some t := by
  induction t with
  | node a cs ih =>
    rw [decodeT, code, Nat.unpair_pair, encodek₂, encodek₂]
    simp only
    have hl : (List.ofFn fun i => code (cs i)).length = ar a ∧
        ∀ c ∈ List.ofFn (fun i => code (cs i)), c < Nat.pair (encode a)
          (encode (List.ofFn fun i => code (cs i))) := by
      refine ⟨List.length_ofFn, fun c hc => ?_⟩
      exact (lt_encode_of_mem hc).trans_le (Nat.right_le_pair _ _)
    rw [dite_eq_left_of_eq_true (eq_true hl)]
    have hc : ∀ i : Fin (ar a), decodeT (α := α) (ar := ar)
        (List.ofFn fun j => code (cs j))[i.val] = some (cs i) := fun i => by
      simp only [List.getElem_ofFn]
      exact ih i
    have hall : ∀ i : Fin (ar a), (decodeT (α := α) (ar := ar)
        (List.ofFn fun j => code (cs j))[i.val]).isSome := fun i => by rw [hc i]; rfl
    rw [dite_eq_left_of_eq_true (eq_true hall)]
    congr 2
    funext i
    simp only [hc i, Option.get_some]

/-- Decoding is canonical: a decoded tree has the code it was decoded from. -/
theorem code_of_decodeT : ∀ (n : ℕ) {t : PTree α ar}, decodeT n = some t → code t = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t ht
    rw [decodeT] at ht
    split at ht
    · rename_i a l ha hl'
      split at ht
      · rename_i hl
        dsimp only at ht
        split at ht
        · cases ht
          rw [code, (decode₂_eq_some.1 ha)]
          conv_rhs => rw [← Nat.pair_unpair n]
          congr 1
          conv_rhs => rw [← decode₂_eq_some.1 hl']
          congr 1
          apply List.ext_getElem (by simp [hl.1])
          intro j hj₁ hj₂
          simp only [List.getElem_ofFn]
          exact ih _ (hl.2 _ (List.getElem_mem _)) (Option.get_mem _)
        · cases ht
      · cases ht
    · cases ht

/-- One step of the test for codes: `n` is a code, given the table `T` of answers below `n`. -/
def validStep (n : ℕ) (T : List Bool) : Bool :=
  (decode₂ α n.unpair.1).elim false fun a =>
    (decode₂ (List ℕ) n.unpair.2).elim false fun l =>
      decide (l.length = ar a) && l.all fun c => decide (c < n) && T.getD c false

/-- Whether `n` is a code satisfies the course-of-values equation of `validStep`. -/
theorem isSome_decodeT (n : ℕ) : (decodeT (α := α) (ar := ar) n).isSome =
    validStep (α := α) (ar := ar) n ((List.range n).map fun m => (decodeT (α := α) (ar := ar) m).isSome) := by
  rw [decodeT, validStep]
  split
  · rename_i a l ha hl'
    rw [ha, hl']
    simp only [Option.elim]
    by_cases hl : l.length = ar a ∧ ∀ c ∈ l, c < n
    · rw [dite_eq_left_of_eq_true (eq_true hl)]
      have hlook : ∀ c ∈ l, (decide (c < n) && ((List.range n).map fun m =>
          (decodeT (α := α) (ar := ar) m).isSome).getD c false) =
          (decodeT (α := α) (ar := ar) c).isSome := fun c hc => by
        rw [getD_map_range_of_lt _ (hl.2 c hc)]
        simp [hl.2 c hc]
      have hall' : (l.all fun c => decide (c < n) && ((List.range n).map fun m =>
          (decodeT (α := α) (ar := ar) m).isSome).getD c false) =
          l.all fun c => (decodeT (α := α) (ar := ar) c).isSome := by
        rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
        exact ⟨fun h c hc => hlook c hc ▸ h c hc, fun h c hc => (hlook c hc).symm ▸ h c hc⟩
      rw [hall']
      by_cases hall : ∀ i : Fin (ar a), (decodeT (α := α) (ar := ar) l[i.val]).isSome
      · rw [dite_eq_left_of_eq_true (eq_true hall)]
        simp only [Option.isSome_some, hl.1, decide_true, Bool.true_and]
        symm
        rw [List.all_eq_true]
        intro c hc
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
        exact hall ⟨j, hl.1 ▸ hj⟩
      · rw [dite_eq_right_of_eq_false (eq_false hall)]
        simp only [Option.isSome_none, hl.1, decide_true, Bool.true_and]
        symm
        rw [Bool.eq_false_iff, ne_eq, List.all_eq_true]
        intro h
        exact hall fun i => h _ (List.getElem_mem _)
    · rw [dite_eq_right_of_eq_false (eq_false hl)]
      simp only [Option.isSome_none]
      symm
      rw [Bool.eq_false_iff, ne_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      rintro ⟨hlen, h⟩
      refine hl ⟨hlen, fun c hc => ?_⟩
      have := h c hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
  · rename_i x y hxy
    simp only [Option.isSome_none]
    cases ha : decode₂ α n.unpair.1 <;> cases hl' : decode₂ (List ℕ) n.unpair.2 <;>
      simp_all [Option.elim]

/-- The node with shape `a` and children `l`, when `l` has `ar a` entries. -/
def mkOpt (a : α) (l : List (PTree α ar)) : Option (PTree α ar) :=
  if h : l.length = ar a then some (node a fun i => l[i.val]'(by have := i.isLt; omega)) else none

/-- The shape of a node. -/
def shape : PTree α ar → α
  | node a _ => a

/-- The children of a node, in order. -/
def children : PTree α ar → List (PTree α ar)
  | node _ cs => List.ofFn cs

/-- `mkOpt` decodes the code it would have. -/
theorem mkOpt_eq_decodeT (a : α) (l : List (PTree α ar)) :
    mkOpt a l = decodeT (Nat.pair (encode a) (encode (l.map code))) := by
  rw [mkOpt]
  by_cases h : l.length = ar a
  · rw [dite_eq_left_of_eq_true (eq_true h), ← decodeT_code, code]
    congr 3
    apply List.ext_getElem (by simp [h])
    intro j hj₁ hj₂
    simp
  · rw [dite_eq_right_of_eq_false (eq_false h), decodeT, Nat.unpair_pair, encodek₂, encodek₂]
    simp only
    rw [dite_eq_right_of_eq_false (eq_false fun hl => h (by simpa using hl.1))]

omit [Encodable α] in
/-- Building a node from the list of its children. -/
theorem mkOpt_ofFn (a : α) (cs : Fin (ar a) → PTree α ar) : mkOpt a (List.ofFn cs) = some (node a cs) := by
  rw [mkOpt, dite_eq_left_of_eq_true (eq_true (List.length_ofFn))]
  simp

/-- Trees are `Encodable`, through `code` and `decodeT`. -/
instance : Encodable (PTree α ar) where
  encode := code
  decode := decodeT
  encodek := decodeT_code

/-- The code of a decoded number: `n + 1` for a code, `0` otherwise. -/
theorem encode_decodeT (n : ℕ) :
    encode (decodeT (α := α) (ar := ar) n) = if (decodeT (α := α) (ar := ar) n).isSome then n + 1
      else 0 := by
  cases h : decodeT (α := α) (ar := ar) n with
  | none => rfl
  | some t =>
    show code t + 1 = _
    rw [code_of_decodeT n h]
    rfl

end Encode

section Prim

variable [Primcodable α]

/-- The test step is primitive recursive. -/
theorem validStep_primrec (hAr : Primrec ar) :
    Primrec fun q : ℕ × List Bool => validStep (α := α) (ar := ar) q.1 q.2 := by
  unfold validStep
  fun_prop

/-- **The codes of trees form a primitive recursive set.** -/
theorem valid_primrec (hAr : Primrec ar) :
    Primrec fun n => (decodeT (α := α) (ar := ar) n).isSome := by
  have h := Primrec.nat_strong_rec (fun (_ : Unit) n => (decodeT (α := α) (ar := ar) n).isSome)
    (g := fun _ T => some (validStep (α := α) (ar := ar) T.length T))
    (Primrec.option_some.comp ((validStep_primrec hAr).comp
      ((prim_length Primrec.snd).pair Primrec.snd)))
    (fun _ n => by rw [List.length_map, List.length_range, isSome_decodeT n])
  exact h.comp (Primrec.const ()) Primrec.id

/-- **Theorem A.** Finitely branching trees with `Primcodable` shapes and primitive recursive
arities are `Primcodable`. -/
instance primcodable [Fact (Primrec ar)] : Primcodable (PTree α ar) where
  prim := by
    have hv := valid_primrec (α := α) (Fact.out : Primrec ar)
    have h : Primrec fun n => if (decodeT (α := α) (ar := ar) n).isSome then n + 1 else 0 := by
      fun_prop
    exact (Primrec.nat_iff.1 h).of_eq fun n => (encode_decodeT n).symm

/-- **Building a node is primitive recursive.** -/
theorem mkOpt_primrec [Fact (Primrec ar)] :
    Primrec₂ (mkOpt (α := α) (ar := ar)) := by
  have h : Primrec fun q : α × List (PTree α ar) =>
      decode (α := PTree α ar) (Nat.pair (encode q.1) (encode (q.2.map encode))) := by fun_prop
  exact h.of_eq fun q => (mkOpt_eq_decodeT q.1 q.2).symm

/-- `mkOpt` applied to primitive recursive functions is primitive recursive. -/
@[fun_prop] theorem prim_mkOpt [Fact (Primrec ar)] {β : Type} [Primcodable β] {f : β → α}
    {g : β → List (PTree α ar)} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => mkOpt (f x) (g x) := mkOpt_primrec.comp hf hg

/-- **The shape of a node is primitive recursive.** -/
theorem shape_primrec [Fact (Primrec ar)] : Primrec (shape (α := α) (ar := ar)) := by
  have h : Primrec fun t : PTree α ar => decode₂ α (encode t).unpair.1 := by fun_prop
  refine (Primrec.option_get (h := fun t => ?_) h).of_eq fun t => ?_
  · cases t; simp [encode, code]
  · cases t; simp [encode, code, shape]

/-- **The children of a node are primitive recursive.** -/
theorem children_primrec [Fact (Primrec ar)] : Primrec (children (α := α) (ar := ar)) := by
  have h : Primrec fun t : PTree α ar =>
      ((decode₂ (List ℕ) (encode t).unpair.2).getD []).filterMap (decode (α := PTree α ar)) :=
    Primrec.listFilterMap (by fun_prop) (Primrec.decode.comp Primrec.snd).to₂
  refine h.of_eq fun t => ?_
  cases t with
  | node a cs =>
    show ((decode₂ (List ℕ) (code (node a cs)).unpair.2).getD []).filterMap decodeT = _
    simp only [code, Nat.unpair_pair, encodek₂, Option.getD_some, children]
    have hc : (fun i => code (cs i)) = code ∘ cs := rfl
    rw [hc, ← List.map_ofFn, List.filterMap_map]
    have hd : (decodeT (α := α) (ar := ar) ∘ code) = some := funext decodeT_code
    rw [hd, List.filterMap_some]

end Prim

section Fold

variable {P σ : Type}

/-- The fold of a tree with parameter `p`: a node with shape `a` gets `step p a` of the results
on its children, in order. -/
def fold (step : P → α → List σ → σ) (p : P) : PTree α ar → σ
  | node a cs => step p a (List.ofFn fun i => fold step p (cs i))

/-- The paramorphism: like `fold`, but the step also sees the children themselves. -/
def para (step : P → α → List (PTree α ar) → List σ → σ) (p : P) : PTree α ar → σ
  | node a cs => step p a (List.ofFn cs) (List.ofFn fun i => para step p (cs i))

variable [Encodable α] [Inhabited σ]

/-- The fold on codes: `default` on a number that is not a code. -/
def codeFold (step : P → α → List σ → σ) (p : P) (n : ℕ) : σ :=
  match decode₂ α n.unpair.1, decode₂ (List ℕ) n.unpair.2 with
  | some a, some l =>
    if hl : ∀ c ∈ l, c < n then
      step p a (l.attach.map fun (c : {c // c ∈ l}) =>
        have : c.val < n := hl _ c.property
        codeFold step p c.val)
    else default
  | _, _ => default
termination_by n

/-- On the code of a tree, the fold on codes is the fold. -/
theorem codeFold_code (step : P → α → List σ → σ) (p : P) (t : PTree α ar) :
    codeFold step p (code t) = fold step p t := by
  induction t with
  | node a cs ih =>
    rw [codeFold, code, Nat.unpair_pair, encodek₂, encodek₂]
    simp only
    have hl : ∀ c ∈ List.ofFn (fun i => code (cs i)), c < Nat.pair (encode a)
        (encode (List.ofFn fun i => code (cs i))) := fun c hc =>
      (lt_encode_of_mem hc).trans_le (Nat.right_le_pair _ _)
    rw [dite_eq_left_of_eq_true (eq_true hl), fold]
    congr 1
    rw [List.attach_map_val (f := fun c => codeFold step p c), List.map_ofFn]
    congr 1
    funext i
    exact ih i

/-- One step of the fold on codes, given the table `T` of its values below `n`. -/
def foldStep (step : P → α → List σ → σ) (p : P) (n : ℕ) (T : List σ) : σ :=
  (decode₂ α n.unpair.1).elim default fun a =>
    (decode₂ (List ℕ) n.unpair.2).elim default fun l =>
      if l.all fun c => decide (c < n) then step p a (l.map fun c => T.getD c default)
      else default

/-- The fold on codes satisfies the course-of-values equation of `foldStep`. -/
theorem codeFold_eq (step : P → α → List σ → σ) (p : P) (n : ℕ) :
    codeFold step p n = foldStep step p n ((List.range n).map (codeFold step p)) := by
  rw [codeFold, foldStep]
  split
  · rename_i a l ha hl'
    rw [ha, hl']
    simp only [Option.elim]
    by_cases hl : ∀ c ∈ l, c < n
    · have hall : (l.all fun c => decide (c < n)) = true := List.all_eq_true.2 fun c hc =>
        decide_eq_true (hl c hc)
      rw [dite_eq_left_of_eq_true (eq_true hl), ite_eq_left hall]
      congr 1
      rw [List.attach_map_val (f := fun c => codeFold step p c)]
      exact List.map_congr_left fun c hc => (getD_map_range_of_lt _ (hl c hc)).symm
    · have hall : ¬ (l.all fun c => decide (c < n)) = true := fun h =>
        hl fun c hc => of_decide_eq_true (List.all_eq_true.1 h c hc)
      rw [dite_eq_right_of_eq_false (eq_false hl), ite_eq_right hall]
  · rename_i x y hxy
    cases ha : decode₂ α n.unpair.1 <;> cases hl' : decode₂ (List ℕ) n.unpair.2 <;>
      simp_all [Option.elim]

end Fold

section FoldPrim

variable {P σ : Type} [Primcodable α] [Fact (Primrec ar)] [Primcodable P] [Primcodable σ]
  [Inhabited σ]

/-- **Theorem B.** A fold with a primitive recursive step is primitive recursive, in the
parameter and the tree. -/
theorem fold_primrec
    {step : P → α → List σ → σ}
    (hstep : Primrec fun q : P × (α × List σ) => step q.1 q.2.1 q.2.2) :
    Primrec₂ (fold (ar := ar) step) := by
  have hst : Primrec fun q : P × (ℕ × List σ) => foldStep step q.1 q.2.1 q.2.2 := by
    unfold foldStep
    have hm : Primrec fun z : ((P × (ℕ × List σ)) × α) × List ℕ =>
        z.2.map fun c => z.1.1.2.2.getD c default := by fun_prop
    have hs : Primrec fun z : ((P × (ℕ × List σ)) × α) × List ℕ =>
        step z.1.1.1 z.1.2 (z.2.map fun c => z.1.1.2.2.getD c default) :=
      hstep.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.snd.comp Primrec.fst).pair hm))
    have hc : PrimrecPred fun z : ((P × (ℕ × List σ)) × α) × List ℕ =>
        (z.2.all fun c => decide (c < z.1.1.2.1)) = true := by fun_prop
    have hi := prim_ite hc hs (Primrec.const default)
    have ho := prim_elim (o := fun y : (P × (ℕ × List σ)) × α => decode₂ (List ℕ) y.1.2.1.unpair.2)
      (g := fun y (l : List ℕ) => if (l.all fun c => decide (c < y.1.2.1)) = true then
        step y.1.1 y.2 (l.map fun c => y.1.2.2.getD c default) else default)
      (by fun_prop) (Primrec.const default) hi
    exact prim_elim (o := fun q : P × (ℕ × List σ) => decode₂ α q.2.1.unpair.1)
      (g := fun q a => (decode₂ (List ℕ) q.2.1.unpair.2).elim default fun l =>
        if (l.all fun c => decide (c < q.2.1)) = true then
          step q.1 a (l.map fun c => q.2.2.getD c default) else default)
      (by fun_prop) (Primrec.const default) ho
  have hc : Primrec₂ (codeFold step) := Primrec.nat_strong_rec _
    (g := fun p T => some (foldStep step p T.length T))
    (Primrec.option_some.comp (hst.comp (Primrec.fst.pair
      ((prim_length Primrec.snd).pair Primrec.snd))))
    (fun p n => by rw [List.length_map, List.length_range, ← codeFold_eq])
  exact (hc.comp Primrec.fst (Primrec.encode.comp Primrec.snd)).of_eq fun q =>
    codeFold_code step q.1 q.2

/-- The fold that computes each subtree together with the paramorphism on it. -/
def paraPair (step : P → α → List (PTree α ar) → List σ → σ) (p : P) (a : α)
    (rs : List (Option (PTree α ar) × σ)) : Option (PTree α ar) × σ :=
  (mkOpt a (rs.filterMap Prod.fst), step p a (rs.filterMap Prod.fst) (rs.map Prod.snd))

omit [Primcodable α] [Fact (Primrec ar)] [Primcodable P] [Primcodable σ] [Inhabited σ] in
/-- `fold (paraPair step)` returns the tree and the paramorphism on it. -/
theorem fold_paraPair (step : P → α → List (PTree α ar) → List σ → σ) (p : P) (t : PTree α ar) :
    fold (paraPair step) p t = (some t, para step p t) := by
  induction t with
  | node a cs ih =>
    rw [fold, para]
    simp only [ih]
    have h₁ : (List.ofFn fun i => ((some (cs i), para step p (cs i)) :
        Option (PTree α ar) × σ)).filterMap Prod.fst = List.ofFn cs := by
      rw [show (List.ofFn fun i => ((some (cs i), para step p (cs i)) : Option (PTree α ar) × σ)) =
          (List.ofFn cs).map (fun t => ((some t, para step p t) : Option (PTree α ar) × σ)) by
        rw [List.map_ofFn]; rfl, List.filterMap_map]
      exact List.filterMap_some
    have h₂ : (List.ofFn fun i => ((some (cs i), para step p (cs i)) :
        Option (PTree α ar) × σ)).map Prod.snd = List.ofFn fun i => para step p (cs i) := by
      rw [List.map_ofFn]; rfl
    rw [paraPair, h₁, h₂, mkOpt_ofFn]

/-- **Theorem B for the paramorphism.** A paramorphism with a primitive recursive step is
primitive recursive, in the parameter and the tree. -/
theorem para_primrec {step : P → α → List (PTree α ar) → List σ → σ}
    (hstep : Primrec fun q : P × (α × (List (PTree α ar) × List σ)) =>
      step q.1 q.2.1 q.2.2.1 q.2.2.2) :
    Primrec₂ (para (ar := ar) step) := by
  have hf : Primrec fun q : P × (α × List (Option (PTree α ar) × σ)) =>
      q.2.2.filterMap Prod.fst :=
    Primrec.listFilterMap (by fun_prop) (Primrec.fst.comp Primrec.snd).to₂
  have hs : Primrec fun q : P × (α × List (Option (PTree α ar) × σ)) =>
      paraPair step q.1 q.2.1 q.2.2 := by
    unfold paraPair
    refine Primrec.pair (mkOpt_primrec.comp (Primrec.fst.comp Primrec.snd) hf) ?_
    have hm : Primrec fun q : P × (α × List (Option (PTree α ar) × σ)) =>
        q.2.2.map Prod.snd := by fun_prop
    exact hstep.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair (hf.pair hm)))
  exact (Primrec.snd.comp (fold_primrec hs)).of_eq fun q => by
    simp only [fold_paraPair]

end FoldPrim

end PTree

end DiagonaLean.Foundations.Computability
