import DiagonaLean

/-! Run by CI: `derive_primcodable` and `primrec_rec` on nested types (fields of type `List T` and
`Option T`). Split from `scripts/FunPropTest.lean` (2026-11-26) so that CI can run the slow
sections in parallel; the sections do not depend on each other. -/

open DiagonaLean.Foundations.Computability

/-! ### `derive_primcodable` and `primrec_rec` on nested types (fields of type `List T`) -/

section Nested

inductive Rose where
  | node (a : ℕ) (cs : List Rose)
  deriving Inhabited
derive_primcodable Rose

inductive Mix where
  | leaf (n : ℕ)
  | bin (l : Mix) (b : Bool) (cs : List Mix) (r : Mix)
  deriving Inhabited
derive_primcodable Mix

inductive Three where
  | nil
  | one (k : ℕ) (t : Three)
  | two (xs : List Three) (b : Bool) (ys : List Three)
derive_primcodable Three

inductive PRose (α : Type) where
  | node (a : α) (cs : List (PRose α))
derive_primcodable PRose

example : Primrec fun n : ℕ => Rose.node n [Rose.node (n + 1) [], Rose.node 0 []] := by fun_prop

def Rose.size : Rose → ℕ
  | .node a cs => a + (cs.map Rose.size).sum
example : Primrec Rose.size := by primrec_rec

def Rose.depth : Rose → ℕ
  | .node _ cs => (cs.map fun c => c.depth + 1).foldr max 0
example : Primrec Rose.depth := by primrec_rec

def Rose.mirror : Rose → Rose
  | .node a cs => .node a (cs.map Rose.mirror).reverse
example : Primrec Rose.mirror := by primrec_rec

def Rose.width : Rose → ℕ
  | .node _ cs => cs.length + (cs.map Rose.width).foldr max 0
example : Primrec Rose.width := by primrec_rec

def Rose.scale (k : ℕ) : Rose → Rose
  | .node a cs => .node (a * k) (cs.map (Rose.scale k))
example : Primrec₂ Rose.scale := by primrec_rec

def Mix.total : Mix → ℕ
  | .leaf n => n
  | .bin l b cs r => l.total + (if b then (cs.map Mix.total).sum else cs.length) + r.total
@[fun_prop] theorem Mix.total_primrec : Primrec Mix.total := by primrec_rec

def Three.count : Three → ℕ
  | .nil => 1
  | .one k t => k + t.count
  | .two xs _ ys => (xs.map Three.count).sum * (ys.map Three.count).sum
example : Primrec Three.count := by primrec_rec

def PRose.flat {α : Type} : PRose α → List α
  | .node a cs => a :: (cs.map PRose.flat).flatten
example {α : Type} [Primcodable α] : Primrec (@PRose.flat α) := by primrec_rec

/-! Paramorphisms on nested types: the right-hand side uses the subterms themselves. -/

def Rose.label : Rose → ℕ
  | .node a _ => a
@[fun_prop] theorem Rose.label_primrec : Primrec Rose.label := by primrec_rec

def Rose.kids : Rose → ℕ
  | .node _ cs => (cs.map Rose.label).sum + (cs.map Rose.kids).sum
example : Primrec Rose.kids := by primrec_rec

/-- Recursion through a `filter` first: rejected, with a message. -/
def Rose.prune (k : ℕ) : Rose → Rose
  | .node a cs => .node a ((cs.filter fun c => c.label < k).map (Rose.prune k))
example : True := by
  fail_if_success (have : Primrec₂ Rose.prune := by primrec_rec)
  trivial

def Mix.leftSize : Mix → ℕ
  | .leaf n => n
  | .bin l _ cs r => (if l.total < r.total then l.leftSize else r.leftSize) + cs.length
example : Primrec Mix.leftSize := by primrec_rec

def Rose.firstKids : Rose → List Rose
  | .node _ cs => cs.take 1 ++ (cs.map Rose.firstKids).flatten
example : Primrec Rose.firstKids := by primrec_rec

/-! Option fields: Lean splits the equations by `none` and `some`. -/

inductive OTree where
  | leaf (n : ℕ)
  | node (l : Option OTree) (k : ℕ) (r : Option OTree)
  deriving Inhabited
derive_primcodable OTree

inductive OT where
  | leaf (n : ℕ)
  | node (l : Option OT) (cs : List OT) (r : Option OT)
derive_primcodable OT

example : Primrec fun n : ℕ => OTree.node (some (.leaf n)) n none := by fun_prop

def OTree.sum : OTree → ℕ
  | .leaf n => n
  | .node l k r =>
    (match l with | none => 0 | some t => t.sum) + k + (match r with | none => 0 | some t => t.sum)
example : Primrec OTree.sum := by primrec_rec

def OTree.sum3 : OTree → ℕ
  | .leaf n => n
  | .node none k none => k
  | .node (some l) k none => l.sum3 + k
  | .node none k (some r) => k + r.sum3
  | .node (some l) k (some r) => l.sum3 + k + r.sum3
@[fun_prop] theorem OTree.sum3_primrec : Primrec OTree.sum3 := by primrec_rec

def OTree.leftOnly : OTree → ℕ
  | .leaf n => n
  | .node none k _ => k
  | .node (some l) _ _ => l.leftOnly
example : Primrec OTree.leftOnly := by primrec_rec

def OTree.mirror : OTree → OTree
  | .leaf n => .leaf n
  | .node none k none => .node none k none
  | .node (some l) k none => .node none k (some l.mirror)
  | .node none k (some r) => .node (some r.mirror) k none
  | .node (some l) k (some r) => .node (some r.mirror) k (some l.mirror)
example : Primrec OTree.mirror := by primrec_rec

def OT.size : OT → ℕ
  | .leaf n => n
  | .node l cs r => (match l with | none => 0 | some c => c.size + 1) + (cs.map OT.size).sum +
      (match r with | none => 1 | some c => c.size)
example : Primrec OT.size := by primrec_rec

/-- A paramorphism through an option field: it uses the subtree itself. -/
def OTree.bigLeft : OTree → ℕ
  | .leaf n => n
  | .node none k _ => k
  | .node (some l) k _ => if k < l.sum3 then l.bigLeft else k
example : Primrec OTree.bigLeft := by primrec_rec

end Nested
