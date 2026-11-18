/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh TVH, Claude Opus
-/

import DiagonaLean.Foundations.Computability.PrimrecRec

@[expose] public section

/-! # Decoding hand-made codes

A hand-made code `c : T → ℕ` of a tree-like type, such as `rc` for regular expressions, packs the
codes of a node's children into the node's own code, each smaller than it. Such a code is a
correct encoding as soon as one decoding step is primitive recursive:

* `kids n` lists the child codes packed into `n`, each smaller than `n` (`hk`);
* `step n ts` rebuilds the node of code `n` from its decoded children `ts`;
* every `t` has subterms `ts` with `kids (c t) = ts.map c` and `step (c t) ts = some t`
  (`hspec`).

Then `decode` inverts `c` (`decode_code`), is primitive recursive when `kids` and `step` are
(`decode_primrec`), and, when `c` is primitive recursive, primitive recursion through `c` is
primitive recursion (`primrec_iff`). The proof is a course-of-values recursion on the code
(`Primrec.nat_strong_rec`), done here once for every such code.
-/

namespace DiagonaLean.Foundations.Computability.TaggedCode

/-- The payload of a code with a positive tag is smaller than the code. -/
theorem unpair_snd_lt {n : ℕ} (h : n.unpair.1 ≠ 0) : n.unpair.2 < n := by
  have := lt_of_le_of_lt (Nat.right_le_pair 0 n.unpair.2)
    (Nat.pair_lt_pair_left n.unpair.2 (Nat.pos_of_ne_zero h))
  rwa [Nat.pair_unpair] at this

variable {T : Type} (kids : ℕ → List ℕ) (hk : ∀ n, ∀ m ∈ kids n, m < n)
  (step : ℕ → List T → Option T)

/-- The decoder: decode the children, then rebuild the node. -/
def decode (n : ℕ) : Option T :=
  let ds := (kids n).attach.map fun (m : {m // m ∈ kids n}) =>
    have : m.val < n := hk n m.val m.property
    decode m.val
  if ds.all Option.isSome then step n (ds.filterMap id) else none
termination_by n

/-- One step of the decoder, with the children looked up in the table `D` of earlier values. -/
def decodeStep (n : ℕ) (D : List (Option T)) : Option T :=
  let ds := (kids n).map fun m => D.getD m none
  if ds.all Option.isSome then step n (ds.filterMap id) else none

/-- The decoder satisfies the course-of-values equation of `decodeStep`. -/
theorem decode_eq (n : ℕ) :
    decode kids hk step n = decodeStep kids step n ((List.range n).map (decode kids hk step)) := by
  rw [decode, decodeStep]
  have h : ((kids n).attach.map fun m => decode kids hk step m.val) =
      (kids n).map fun m => ((List.range n).map (decode kids hk step)).getD m none := by
    rw [List.attach_map_val (f := decode kids hk step)]
    exact List.map_congr_left fun m hm => (getD_map_range_of_lt _ (hk n m hm)).symm
  simp only [h]

/-- **The decoder inverts the code.** -/
theorem decode_code {c : T → ℕ}
    (hspec : ∀ t, ∃ ts : List T, kids (c t) = ts.map c ∧ step (c t) ts = some t) (t : T) :
    decode kids hk step (c t) = some t := by
  suffices h : ∀ n, ∀ t, c t = n → decode kids hk step n = some t from h _ t rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t ht
    obtain ⟨ts, hks, hst⟩ := hspec t
    rw [ht] at hks hst
    rw [decode_eq, decodeStep]
    have hd : ((kids n).map fun m => ((List.range n).map (decode kids hk step)).getD m none) =
        ts.map some := by
      rw [hks, List.map_map]
      refine List.map_congr_left fun t' ht' => ?_
      have hlt : c t' < n := hk n _ (hks ▸ List.mem_map_of_mem ht')
      simp only [Function.comp, getD_map_range_of_lt _ hlt]
      exact ih _ hlt t' rfl
    rw [hd]
    simp [hst, List.filterMap_map]

section Prim

variable [Primcodable T]

/-- One step of the decoder is primitive recursive when `kids` and `step` are. -/
theorem decodeStep_primrec (hkids : Primrec kids)
    (hstep : Primrec fun q : ℕ × List T => step q.1 q.2) :
    Primrec fun q : ℕ × List (Option T) => decodeStep kids step q.1 q.2 := by
  unfold decodeStep
  have hds : Primrec fun q : ℕ × List (Option T) => (kids q.1).map fun m => q.2.getD m none := by
    fun_prop
  have hall : PrimrecPred fun q : ℕ × List (Option T) =>
      (((kids q.1).map fun m => q.2.getD m none).all Option.isSome) = true :=
    pred_eq (prim_all hds (Primrec.option_isSome.comp Primrec.snd)) (Primrec.const true)
  have hfm : Primrec fun q : ℕ × List (Option T) =>
      ((kids q.1).map fun m => q.2.getD m none).filterMap id :=
    Primrec.listFilterMap hds (Primrec.snd).to₂
  exact prim_ite hall (hstep.comp (Primrec.fst.pair hfm)) (Primrec.const none)

/-- **The decoder is primitive recursive** when `kids` and `step` are. -/
theorem decode_primrec (hkids : Primrec kids)
    (hstep : Primrec fun q : ℕ × List T => step q.1 q.2) : Primrec (decode kids hk step) := by
  have h := Primrec.nat_strong_rec (fun (_ : Unit) n => decode kids hk step n)
    (g := fun _ D => some (decodeStep kids step D.length D))
    (Primrec.option_some.comp ((decodeStep_primrec kids step hkids hstep).comp
      ((prim_length Primrec.snd).pair Primrec.snd)))
    (fun _ n => by rw [List.length_map, List.length_range, ← decode_eq])
  exact h.comp (Primrec.const ()) Primrec.id

include hk in
/-- **A primitive recursive hand-made code with a primitive recursive decoding step is a correct
encoding:** primitive recursion through `c` is primitive recursion. -/
theorem primrec_iff {c : T → ℕ}
    (hspec : ∀ t, ∃ ts : List T, kids (c t) = ts.map c ∧ step (c t) ts = some t)
    (hc : Primrec c) (hkids : Primrec kids)
    (hstep : Primrec fun q : ℕ × List T => step q.1 q.2)
    {β : Type} [Primcodable β] {f : β → T} : Primrec f ↔ Primrec fun b => c (f b) := by
  refine ⟨fun h => hc.comp h, fun h => ?_⟩
  have hs : ∀ b, (decode kids hk step (c (f b))).isSome := fun b => by
    rw [decode_code kids hk step hspec]; rfl
  exact (Primrec.option_get (h := hs) ((decode_primrec kids hk step hkids hstep).comp h)).of_eq
    fun b => by simp [decode_code kids hk step hspec]

end Prim

end DiagonaLean.Foundations.Computability.TaggedCode
