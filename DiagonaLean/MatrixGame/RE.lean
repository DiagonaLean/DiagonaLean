/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prathamesh Turaga, Claude Opus
-/

import DiagonaLean.MatrixGame.Search
import DiagonaLean.Foundations.Computability.FinsetPrim
import DiagonaLean.Foundations.Computability.MatrixPrim
import DiagonaLean.Foundations.Computability.IntPrim
import DiagonaLean.Foundations.Computability.PolyTree
import DiagonaLean.Foundations.Computability.PrimrecRec
import DiagonaLean.Foundations.Computability.MachineBridge

@[expose] public section

/-! # Whether Eve has a winning strategy is recursively enumerable

The move sets are finite, so Eve has a winning strategy iff she can force zero within some number
of rounds `n` (`decisionProblem_iff_forceZero`, `forceZero_iff_exists_bound`), and for each `n`
that is a finite search, `winsWithin G n 1`. The search is primitive recursive in the arena and
`n`, which makes the problem recursively enumerable (`MatrixGame.rePred`); with
`MatrixGame.haltHard` it is exactly as hard as the halting problem.

`winsWithin` recurses on `n` but calls itself at many positions, `p * a * b` for each move `a` of
Eve and `b` of Adam, which `primrec_rec` does not handle. So the search is run on a whole list of
positions at once (`winsList`): one level of the game tree is the list of all children of the
previous one (`children`), the single recursive call is on that list, and the value of each node
is read off its block of children (`evalNode`, cut by `chunks`). That is recursion on `ℕ` with one
changing argument, which `primrec_rec` proves primitive recursive (`winsList_primrec`), and
`winsList n (G, l)` is `winsWithin G n` on each position of `l` (`winsList_eq`). The move sets are
read as the lists their codes decode to (`moves`, `mem_moves`).

## Main statements

* `MatrixGame.rePred`: whether Eve has a winning strategy is recursively enumerable.
* `RE.winsList_eq`: the search on a list of positions is `winsWithin` on each.

## References

* [M. S. Paterson, *Unsolvability in 3 × 3 Matrices*][Paterson1970]
-/

open Encodable DiagonaLean.Foundations.Computability

namespace DiagonaLean.MatrixGame.RE

/-- The moves of a finite set, as the list its code decodes to. -/
def moves (s : Finset Position) : List Position :=
  (decode (α := List Position) (encode s)).getD []

/-- The list of moves has the moves of the set. -/
theorem mem_moves {s : Finset Position} {a : Position} : a ∈ moves s ↔ a ∈ s :=
  (mem_iff_mem_decode_encode s a).symm

/-- `moves` is primitive recursive. -/
@[fun_prop] theorem moves_primrec : Primrec moves :=
  Primrec.option_getD.comp (Primrec.decode.comp Primrec.encode) (Primrec.const [])

/-- The positions after one round from `q`, Eve's moves outside, Adam's inside. -/
def children (G : Arena) (q : Position) : List Position :=
  (moves G.1).flatMap fun a => (moves G.2).map fun b => q * a * b

/-- `children` is primitive recursive. -/
@[fun_prop] theorem children_primrec : Primrec fun x : Arena × Position => children x.1 x.2 := by
  unfold children; fun_prop

/-- A node of the search: `q` is zero, or for some move of Eve the values of all of Adam's
replies, a block of `na` consecutive values among `ne` blocks, are true. -/
def evalNode (q : Position) (ne na : ℕ) (vals : List Bool) : Bool :=
  decide (q = 0) || (chunks (List.replicate ne na) vals).any fun c => c.all id

/-- `evalNode` is primitive recursive. -/
@[fun_prop] theorem evalNode_primrec :
    Primrec fun x : Position × ℕ × ℕ × List Bool => evalNode x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  unfold evalNode; fun_prop

/-- `winsWithin G n` on every position of a list at once, by recursion on `n` with one recursive
call, on the list of all children. -/
def winsList : ℕ → Arena × List Position → List Bool
  | 0, x => x.2.map fun q => decide (q = 0)
  | n + 1, x =>
    List.zipWith (fun q v => evalNode q (moves x.1.1).length (moves x.1.2).length v) x.2
      (chunks (x.2.map fun _ => (moves x.1.1).length * (moves x.1.2).length)
        (winsList n (x.1, x.2.flatMap (children x.1))))

/-- **The search on lists is primitive recursive**, by `primrec_rec`. -/
theorem winsList_primrec : Primrec₂ winsList := by primrec_rec


/-- Cutting the concatenation of pieces of one length `k` gives the pieces back. -/
theorem chunks_flatMap {α β : Type*} (l : List α) (g : α → List β) (k : ℕ)
    (hk : ∀ a ∈ l, (g a).length = k) : chunks (l.map fun _ => k) (l.flatMap g) = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.flatMap_cons, chunks_cons_append _ _ _ _ (hk a (by simp)),
      ih fun b hb => hk b (by simp [hb]), List.map_cons]

/-- Every position has one child for each pair of moves. -/
theorem length_children (G : Arena) (q : Position) :
    (children G q).length = (moves G.1).length * (moves G.2).length := by
  simp [children, List.length_flatMap, List.sum_replicate, List.map_const']

/-- One node of the search is one step of `winsWithin`. -/
theorem evalNode_children (G : Arena) (n : ℕ) (q : Position) :
    evalNode q (moves G.1).length (moves G.2).length ((children G q).map (winsWithin G n)) =
      winsWithin G (n + 1) q := by
  have hc : chunks (List.replicate (moves G.1).length (moves G.2).length)
      ((children G q).map (winsWithin G n)) =
      (moves G.1).map fun a => (moves G.2).map fun b => winsWithin G n (q * a * b) := by
    rw [← List.map_const', children, List.map_flatMap,
      chunks_flatMap _ _ (moves G.2).length fun a _ => by simp]
    simp [List.map_map, Function.comp_def]
  rw [evalNode, hc, winsWithin, Bool.decide_or]
  congr 1
  rw [Bool.eq_iff_iff]
  simp [mem_moves]

/-- **`winsList` is `winsWithin` on every position of the list.** -/
theorem winsList_eq (n : ℕ) (G : Arena) (l : List Position) :
    winsList n (G, l) = l.map (winsWithin G n) := by
  induction n generalizing l with
  | zero => simp [winsList, winsWithin]
  | succ n ih =>
    rw [winsList, ih, List.map_flatMap,
      chunks_flatMap _ _ _ fun q _ => by rw [List.length_map, length_children],
      List.zipWith_map_right, List.zipWith_self]
    exact List.map_congr_left fun q _ => evalNode_children G n q

/-- Eve has a winning strategy iff the bounded search succeeds for some number of rounds. -/
theorem decisionProblem_iff_exists_winsList (G : Arena) :
    DecisionProblem G ↔ ∃ n, winsList n (G, [1]) = [true] := by
  simp [decisionProblem_iff_forceZero, forceZero_iff_exists_bound, winsList_eq]

end DiagonaLean.MatrixGame.RE

namespace DiagonaLean.MatrixGame

/-- **Whether Eve has a winning strategy is recursively enumerable**: search for a number of rounds
within which she can force zero. -/
theorem rePred : REPred DecisionProblem :=
  REPred.of_exists_primrecPred (q := fun G n => RE.winsList n (G, [1]) = [true])
    (Primrec.eq.comp (RE.winsList_primrec.comp Primrec.snd (Primrec.fst.pair (Primrec.const [1])))
      (Primrec.const [true]))
    RE.decisionProblem_iff_exists_winsList

end DiagonaLean.MatrixGame
