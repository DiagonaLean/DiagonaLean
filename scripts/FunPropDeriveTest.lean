import DiagonaLean

/-! Run by CI: `derive_primcodable` and `primrec_rec` on inductive types, including
paramorphisms. Split from `scripts/FunPropTest.lean` (2026-11-26) so that CI can run the slow
sections in parallel; the sections do not depend on each other. -/

open DiagonaLean.Foundations.Computability

/-! ### `derive_primcodable` -/

section Derive

inductive Tree2 | leaf | node (l r : Tree2)
derive_primcodable Tree2
def tsize : Tree2 → ℕ
  | .leaf => 1
  | .node l r => tsize l + tsize r + 1
example : Primrec tsize := by primrec_rec

inductive Expr2
  | lit (n : ℕ)
  | var (x : ℕ ⊕ Bool)
  | neg (e : Expr2)
  | add (a : Expr2) (k : ℕ) (b : Expr2)
derive_primcodable Expr2
def eval2 (v : ℕ) : Expr2 → ℕ
  | .lit n => n
  | .var x => x.elim (fun _ => v) (fun _ => 0)
  | .neg e => eval2 v e
  | .add a k b => eval2 v a + k * eval2 v b
example : Primrec₂ eval2 := by primrec_rec

inductive Pt | mk (x y : ℕ) (b : Bool)
derive_primcodable Pt
def ptSum : Pt → ℕ | .mk x y _ => x + y
example : Primrec ptSum := by primrec_rec

inductive Color | red | green | blue
derive_primcodable Color
def colorN : Color → ℕ | .red => 0 | .green => 1 | .blue => 2
example : Primrec colorN := by primrec_rec

inductive NSeq | nil | cons (a b : ℕ) (rest : NSeq)
derive_primcodable NSeq
def seqSum : NSeq → ℕ | .nil => 0 | .cons a b r => a * b + seqSum r
example : Primrec seqSum := by primrec_rec
example : Primrec fun n : ℕ => NSeq.cons n (n + 1) .nil := by fun_prop

-- parameters of sort `Type`
inductive Tr (α : Type) | leaf (a : α) | node (l r : Tr α)
derive_primcodable Tr
example : Primcodable (Tr (ℕ ⊕ Bool)) := inferInstance
def trSum : Tr ℕ → ℕ
  | .leaf a => a
  | .node l r => trSum l + trSum r
example : Primrec trSum := by primrec_rec
example : Primrec fun n : ℕ => Tr.node (.leaf n) (.leaf (n + 1)) := by fun_prop

inductive Two (α β' : Type) | a (x : α) | b (y : β') | both (l r : Two α β')
derive_primcodable Two
def twoCount : Two ℕ Bool → ℕ
  | .a x => x
  | .b y => if y then 1 else 0
  | .both l r => twoCount l + twoCount r
example : Primrec twoCount := by primrec_rec

-- universe polymorphic: parameters in any universe, two sharing one, and a nested one
universe u v
inductive UExp (X : Type u) where
  | zero | one
  | sym (x : X)
  | plus (e f : UExp X)
  | star (e : UExp X)
derive_primcodable UExp
def UExp.size {X : Type u} : UExp X → ℕ
  | .zero | .one | .sym _ => 1
  | .plus e f => e.size + f.size + 1
  | .star e => e.size + 1
example {X : Type u} [Primcodable X] : Primrec (@UExp.size X) := by primrec_rec
example : Primrec fun n : ℕ => UExp.plus (.sym n) .one := by fun_prop

inductive Pair2 (X Y : Type u) where
  | mk (x : X) (y : Y)
  | more (p : Pair2 X Y)
derive_primcodable Pair2

inductive URose (X : Type u) (Y : Type v) where
  | node (x : X) (y : Y) (cs : List (URose X Y))
derive_primcodable URose
def URose.count {X : Type u} {Y : Type v} : URose X Y → ℕ
  | .node _ _ cs => 1 + (cs.map URose.count).sum
example {X : Type u} {Y : Type v} [Primcodable X] [Primcodable Y] : Primrec (@URose.count X Y) := by
  primrec_rec

-- rejected

inductive Idx : ℕ → Type | z : Idx 0
/-- error: derive_primcodable: `Idx` has indices, which are not supported -/
#guard_msgs in
derive_primcodable Idx

inductive Clash (σ : Type) | mk (v : σ)
/-- error: derive_primcodable: rename the parameter `σ` of `Clash`; the generated code uses that name -/
#guard_msgs in
derive_primcodable Clash

/-! ### Paramorphisms: right-hand sides that use the subterms themselves -/

instance : Inhabited Cslib.SKI := ⟨.S⟩
def sameSides : Cslib.SKI → ℕ
  | .S => 0
  | .K => 0
  | .I => 0
  | .app x y => if x = y then 1 else sameSides x + sameSides y
example : Primrec sameSides := by primrec_rec

inductive Tree3 | leaf (n : ℕ) | node (l r : Tree3)
  deriving DecidableEq
derive_primcodable Tree3
instance : Inhabited Tree3 := ⟨.leaf 0⟩
def leftmost : Tree3 → Tree3
  | .leaf n => .leaf n
  | .node l _ => leftmost l
example : Primrec leftmost := by primrec_rec
def countEq (k : ℕ) : Tree3 → ℕ
  | .leaf n => if n = k then 1 else 0
  | .node l r => (if l = r then 1 else 0) + countEq k l + countEq k r
example : Primrec₂ countEq := by primrec_rec

-- projections of a structure
structure P3 (α : Type) where
  a : ℕ
  b : List α
  c : Bool
derive_primcodable P3
example : Primrec fun x : P3 ℕ => x.a + x.b.length + (if x.c then 1 else 0) := by fun_prop

end Derive
