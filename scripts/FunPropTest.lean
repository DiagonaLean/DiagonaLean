import DiagonaLean

/-! Run by CI: `fun_prop` proves `Primrec` and `Computable` goals.
See `DiagonaLean.Foundations.Computability.Prim` for the setup. -/

open DiagonaLean.Foundations.Computability

/-! ### `Primrec` -/

example : Primrec fun n : ℕ => n * n + 3 := by fun_prop
example : Primrec fun p : ℕ × ℕ => (p.2 + 1, p.1 * p.2) := by fun_prop
example : Primrec fun l : List ℕ => (0 :: l) ++ l.reverse := by fun_prop
example : Primrec fun l : List ℕ => l.map (· * 2) ++ l := by fun_prop
example : Primrec fun p : ℕ × List ℕ => p.2.map (· + p.1) := by fun_prop
example : Primrec fun p : ℕ × List ℕ => p.2.foldr (fun a s => a + s) p.1 := by fun_prop
example : Primrec fun n : ℕ => if n < 5 then n else Nat.pair n (n / 2) := by fun_prop
example : PrimrecPred fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ p.1 ≠ p.2 := by fun_prop
example (f : ℕ → ℕ) (hf : Primrec f) : Primrec fun n => f (f n + n) := by fun_prop

/-! ### `Computable` -/

example : Computable fun n : ℕ => n * n + 3 := by fun_prop
example : Computable fun x : ℕ × List ℕ => some (Nat.pair x.1 (x.1 + 1), x.2 ++ [x.1]) := by
  fun_prop
example (f : ℕ → ℕ) (hf : Computable f) : Computable fun n => f (f n + n) := by fun_prop
example (f : ℕ → ℕ) (hf : Computable f) : Computable fun n => (f n, n.unpair.1 - f n) := by
  fun_prop
example (b : ℕ → Bool) (hb : Computable b) : Computable fun n => cond (b n) n (n * 2) := by
  fun_prop
example (f : ℕ → ℕ) (hf : Computable f) : Computable fun n => if n < 5 then f n else n := by
  fun_prop
example : Computable fun p : ℕ × List ℕ => p.2.map (· + p.1) := by fun_prop
example (f : ℕ → Option ℕ) (hf : Computable f) : Computable fun n => (f n).getD n := by fun_prop

/-! ### Definitions registered with `@[fun_prop]` compose -/

def double (n : ℕ) : ℕ := n + n
@[fun_prop] theorem primrec_double : Primrec double := by unfold double; fun_prop
example : Computable fun n => double (double n) + 1 := by fun_prop

/-! ### Library definitions -/

example : Primrec DiagonaLean.KACommUndecidable.KleeneAlgebra.subC :=
  DiagonaLean.KACommUndecidable.KleeneAlgebra.subC_prim
example : Primrec fun n => (DiagonaLean.KACommUndecidable.KleeneAlgebra.subC n, n + 1) := by
  fun_prop

/-! ### `primrec_rec`: structural recursion from equation lemmas -/

def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumTo n + n
@[fun_prop] theorem primrec_sumTo : Primrec sumTo := by primrec_rec
example : Primrec fun n => sumTo (sumTo n) + 1 := by fun_prop

def lenPlus : List ℕ → ℕ
  | [] => 1
  | a :: l => lenPlus l + a
example : Primrec lenPlus := by primrec_rec

def powAdd (a : ℕ) : ℕ → ℕ
  | 0 => a
  | n + 1 => powAdd a n * 2 + a
example : Primrec₂ powAdd := by primrec_rec

def scale (k : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: l => (a * k) :: scale k l
example : Primrec₂ scale := by primrec_rec

def twice : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 => (if (twice n).1 < n then (twice n).2 else n, Nat.pair (twice n).1 n)
example : Primrec twice := by primrec_rec

def sumSums : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumSums n + sumTo n
example : Primrec sumSums := by primrec_rec

-- several parameters, packed into a product
def addMul (a b : ℕ) : ℕ → ℕ
  | 0 => a
  | n + 1 => addMul a b n * b + a
example : Primrec₂ fun (p : ℕ × ℕ) n => addMul p.1 p.2 n := by primrec_rec

def three (a b c : ℕ) : List ℕ → ℕ
  | [] => a
  | x :: l => three a b c l + x * b + c
example : Primrec₂ fun (p : ℕ × ℕ × ℕ) l => three p.1 p.2.1 p.2.2 l := by primrec_rec

-- course-of-values recursion
def halfSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => halfSum ((n + 1) / 2) + n
example : Primrec halfSum := by primrec_rec

def back3 (a : ℕ) : ℕ → ℕ
  | 0 => a
  | n + 1 => back3 a (n - 2) + back3 a n + 1
example : Primrec₂ back3 := by primrec_rec

-- nested patterns
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
example : Primrec fib := by primrec_rec

def iterTwice : ℕ → ℕ
  | 0 => 0
  | n + 1 => match n with
    | 0 => 1
    | k + 1 => iterTwice (k + 1) + 2
example : Primrec iterTwice := by primrec_rec

def tri : ℕ → ℕ
  | 0 => 5
  | 1 => 7
  | 2 => 9
  | n + 3 => tri n * tri (n + 2)
example : Primrec tri := by primrec_rec

-- rejected: several parameters must be packed into a product in the goal
set_option linter.unreachableTactic false in
example : True := by
  fail_if_success (have : Primrec₂ (three 1) := by primrec_rec)
  trivial

/-! ### `tm_computer`, `tm_computes`: machines from `fun_prop` -/

open Cslib.Turing in
example : ∃ R : SingleTapeTM Bool, ∀ l, R.Outputs l (l ++ l.reverse) := by
  tm_computer fun l => l ++ l.reverse

def countTrue : List Bool → ℕ
  | [] => 0
  | b :: l => countTrue l + b.toNat
@[fun_prop] theorem primrec_countTrue : Primrec countTrue := by primrec_rec

open Cslib.Turing in
example : ∃ R : SingleTapeTM Bool,
    DiagonaLean.Halt.Undecidable.ComputesReduction R id bitsOf countTrue := by
  tm_computes fun w => bitsOf (countTrue w)
  intro l
  rfl

/-! ### Theorem A: finitely branching trees are `Primcodable` -/

section PTree

open DiagonaLean.Foundations.Computability.PTree

/-- Binary trees: shape `true` has two children, `false` none. -/
def binAr (b : Bool) : ℕ := if b then 2 else 0
instance : Fact (Primrec binAr) := ⟨by unfold binAr; fun_prop⟩
example : Primcodable (PTree Bool binAr) := inferInstance
example : Primrec fun t : PTree Bool binAr => Encodable.encode t := Primrec.encode
example : Primrec (Encodable.decode (α := PTree Bool binAr)) := Primrec.decode

/-- The shapes of regular expressions over `ℕ ⊕ ℕ`: `0`, `1`, a letter, `+`, `·`, `∗`. -/
def rexpAr : Fin 6 ⊕ (ℕ ⊕ ℕ) → ℕ
  | .inl i => if i.val = 3 ∨ i.val = 4 then 2 else if i.val = 5 then 1 else 0
  | .inr _ => 0
instance : Fact (Primrec rexpAr) := ⟨(Primrec.sumCasesOn Primrec.id
  ((Primrec.dom_finite fun i : Fin 6 =>
    if i.val = 3 ∨ i.val = 4 then 2 else if i.val = 5 then 1 else 0).comp₂ Primrec₂.right)
  ((Primrec.const 0).comp₂ Primrec₂.right)).of_eq fun x => by cases x <;> rfl⟩
example : Primcodable (PTree (Fin 6 ⊕ (ℕ ⊕ ℕ)) rexpAr) := inferInstance

/-! ### Theorem B: folds with a primitive recursive step are primitive recursive -/

/-- The number of nodes of a binary tree. -/
def size : PTree Bool binAr → ℕ := fold (fun (_ : Unit) _ rs => rs.foldr (· + ·) 1) ()
example : size (.node false Fin.elim0) = 1 := rfl
example : Primrec size := (fold_primrec (by fun_prop)).comp (Primrec.const ()) Primrec.id

/-- With a parameter: the sum of `k` over the leaves. -/
example : Primrec₂ (fold (ar := binAr) fun (k : ℕ) b rs => if b then rs.foldr (· + ·) 0 else k) :=
  fold_primrec (by fun_prop)

/-! ### Sanity check: `ℕ` and unary trees are primitive recursively isomorphic -/

/-- Unary trees: shape `true` has one child, `false` none. -/
def natAr (b : Bool) : ℕ := if b then 1 else 0
instance : Fact (Primrec natAr) := ⟨by unfold natAr; fun_prop⟩

/-- The leaf, `0`. -/
def leafN : PTree Bool natAr := .node false Fin.elim0
/-- A tree to a number. -/
def toN : PTree Bool natAr → ℕ := fold (fun (_ : Unit) b rs => if b then rs.headI + 1 else 0) ()
/-- A number to a tree. -/
def ofN (n : ℕ) : PTree Bool natAr := (fun t => (mkOpt true [t]).getD leafN)^[n] leafN

theorem step_eq (t : PTree Bool natAr) : (mkOpt true [t]).getD leafN = .node true fun _ => t := by
  have h : [t].length = natAr true := rfl
  rw [mkOpt, dite_eq_left_of_eq_true (eq_true h), Option.getD_some]
  congr 1
  funext i
  have : i.val = 0 := by have := i.isLt; simp [natAr] at this; omega
  simp [this]

theorem toN_node (t : PTree Bool natAr) : toN (.node true fun _ => t) = toN t + 1 := by
  rw [toN, fold]
  simp [List.ofFn, natAr]
  rfl

/-- The round trip `ℕ → tree → ℕ` is the identity. -/
theorem toN_ofN (n : ℕ) : toN (ofN n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ofN, Function.iterate_succ_apply', ← ofN, step_eq, toN_node, ih]

/-- The round trip `tree → ℕ → tree` is the identity. -/
theorem ofN_toN (t : PTree Bool natAr) : ofN (toN t) = t := by
  induction t with
  | node b cs ih =>
    cases b with
    | false =>
      show ofN (toN (.node false cs)) = _
      have hcs : cs = Fin.elim0 := funext fun i => (Fin.elim0 (i : Fin 0))
      subst hcs
      rfl
    | true =>
      have h0 : 0 < natAr true := by decide
      have hcs : cs = fun _ => cs ⟨0, h0⟩ := funext fun i => by
        congr 1; ext; have := i.isLt; simp [natAr] at this; omega
      rw [hcs, toN_node, ofN, Function.iterate_succ_apply', ← ofN, ih ⟨0, h0⟩, step_eq]

-- both directions are primitive recursive: the encodings agree up to a primitive recursive
-- isomorphism
example : Primrec toN := (fold_primrec (by fun_prop)).comp (Primrec.const ()) Primrec.id
example : Primrec ofN := by unfold ofN; fun_prop

/-! ### The paramorphism -/

/-- The number of leaves, computed from the children themselves. -/
example : Primrec₂ (para (ar := binAr) fun (_ : Unit) _ cs (_ : List ℕ) => cs.length) :=
  para_primrec (by fun_prop)

end PTree

/-! ### `primrec_rec` on inductive types with a `primrec_of_eqns` lemma (M7) -/

section M7

open Cslib DiagonaLean.KACommUndecidable.KleeneAlgebra

def skiSize : SKI → ℕ
  | .S => 1
  | .K => 1
  | .I => 1
  | .app x y => skiSize x + skiSize y + 1
example : Primrec skiSize := by primrec_rec

open LambdaCalculus.LocallyNameless.Untyped in
def fvCount (k : ℕ) : Term ℕ → ℕ
  | .bvar _ => 0
  | .fvar x => if x = k then 1 else 0
  | .abs M => fvCount k M
  | .app M N => fvCount k M + fvCount k N
example : Primrec₂ fvCount := by primrec_rec

def starDepth : RExp (ℕ ⊕ ℕ) → ℕ
  | .zero => 0
  | .one => 0
  | .sym _ => 0
  | .plus e f => max (starDepth e) (starDepth f)
  | .mul e f => max (starDepth e) (starDepth f)
  | .star e => starDepth e + 1
example : Primrec starDepth := by primrec_rec

instance : Inhabited (RExp (ℕ ⊕ ℕ)) := ⟨.zero⟩

def swapPlus : RExp (ℕ ⊕ ℕ) → RExp (ℕ ⊕ ℕ)
  | .zero => .zero
  | .one => .one
  | .sym x => .sym x
  | .plus e f => .plus (swapPlus f) (swapPlus e)
  | .mul e f => .mul (swapPlus e) (swapPlus f)
  | .star e => .star (swapPlus e)
example : Primrec swapPlus := by primrec_rec

end M7

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

-- rejected
universe u
inductive PolyT (α : Type u) | mk (v : α)
/-- error: derive_primcodable: `PolyT` is universe polymorphic; state its parameters as `Type` -/
#guard_msgs in
derive_primcodable PolyT

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
