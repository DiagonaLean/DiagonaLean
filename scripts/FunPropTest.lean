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

/-! ### Functions out of finite types (`Primrec.dom_finite`) -/

def finDec : Option (Bool × Bool) → Option Bool
  | some (b, true) => some b
  | _ => none

example : Primrec finDec := by fun_prop
example : Primrec fun x : ℕ × Option (Bool × Bool) =>
    x.1 + (match finDec x.2 with | none => 0 | some false => 1 | some true => 2) := by fun_prop

/-! ### `derive_primrec` -/

namespace DerivePrimrecTest

def f3 (a : ℕ) (l : List ℕ) (b : Bool) : ℕ := if b then a + l.length else a
derive_primrec f3
example : Primrec fun x : ℕ × ℕ => f3 (x.1 + 1) [x.2] (x.1 = 0) := by fun_prop

def gen {α : Type} [DecidableEq α] (a b : α) (l : List α) : List α := if a = b then l else a :: l
derive_primrec gen [Primcodable α]
example {β : Type} [Primcodable β] [DecidableEq β] (c : β) :
    Primrec fun l : List β => gen c c (l ++ l) := by fun_prop

/-- A function argument: the lemma is compositional, with the function depending on the input. -/
def mapAdd (g : ℕ → ℕ) (l : List ℕ) (k : ℕ) : List ℕ := l.map fun n => g n + k
derive_primrec mapAdd
example : Primrec fun l : List ℕ => mapAdd (fun n => n * l.length) l (l.length + 1) := by fun_prop
example (h : ℕ → ℕ) (hh : Primrec h) : Primrec fun l : List ℕ => mapAdd h l 0 := by fun_prop

-- rejected

def hoArg (c : (ℕ → ℕ) → ℕ) (n : ℕ) : ℕ := c id + n
/-- error: derive_primrec: the function argument `c` of `DerivePrimrecTest.hoArg` must
have a type `A → B` with `A` not a function type -/
#guard_msgs (whitespace := lax) in
derive_primrec hoArg

def curArg (c : ℕ → ℕ → ℕ) (n : ℕ) : ℕ := c n n
/-- error: derive_primrec: the function argument `c` of `DerivePrimrecTest.curArg` must
have a type `A → B` with `B` not a function type -/
#guard_msgs (whitespace := lax) in
derive_primrec curArg

def clashArg {X_dp : Type} [Primcodable X_dp] (c : ℕ → ℕ) (n : ℕ) : ℕ := c n
/-- error: derive_primrec: rename the argument `X_dp` of `DerivePrimrecTest.clashArg`; the
generated code uses that name -/
#guard_msgs (whitespace := lax) in
derive_primrec clashArg

end DerivePrimrecTest

/-! ### `code_lift` leaves the computability of the lift as a named goal when `fun_prop` fails -/

namespace CodeLiftTest

open DiagonaLean.Foundations.Codes

/-- An encoding with no `fun_prop` lemma. -/
def myEnc {α β : Type} (c : α → List β) (w : List α) : List β := encode c w

abbrev toy : CodeFunctor IsCode where
  Inst α := List α
  map c w := myEnc c w
  Prob w := w = []
  map_unit w := by simp [myEnc]
  map_kcomp c₁ c₂ w := by simp [myEnc, encode_kcomp]
  natural hc w := by
    simp only [myEnc]
    exact ⟨fun h => hc (h.trans (encode_nil _).symm), by rintro rfl; rfl⟩
  supp w := w
  map_congr _ h := encode_congr h

example {β : Type} [Primcodable β] [Nontrivial β] (h : ¬ ComputablePred (toy.Prob (α := ℕ))) :
    ¬ ComputablePred (toy.Prob (α := β)) := by
  code_lift toy from h
  case map_computable =>
    intros
    refine Primrec.to_comp ?_
    unfold CodeFunctor.liftMap
    dsimp only [toy, myEnc]
    fun_prop

end CodeLiftTest

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

example : Primrec DiagonaLean.KAComm.KleeneAlgebra.subC :=
  DiagonaLean.KAComm.KleeneAlgebra.subC_prim
example : Primrec fun n => (DiagonaLean.KAComm.KleeneAlgebra.subC n, n + 1) := by
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

open Cslib DiagonaLean.KAComm.KleeneAlgebra

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

/-! ### `primrec_rec` on polymorphic definitions -/

section Poly

def hashL' {α : Type} : List α → List (Option α)
  | [] => []
  | a :: x => none :: some a :: hashL' x
example {α : Type} [Primcodable α] : Primrec (@hashL' α) := by primrec_rec

def countIn {α : Type} [DecidableEq α] (a : α) : List α → ℕ
  | [] => 0
  | b :: l => (if b = a then 1 else 0) + countIn a l
example {α : Type} [Primcodable α] [DecidableEq α] : Primrec₂ (@countIn α _) := by primrec_rec

def repl {α : Type} (a : α) : ℕ → List α
  | 0 => []
  | n + 1 => a :: repl a n
example {α : Type} [Primcodable α] : Primrec₂ (@repl α) := by primrec_rec

end Poly

/-! ### `primrec_rec`: recursion on the first argument while the other one changes -/

section Changing

def toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n => decide (n % 2 = 1) :: toBits k (n / 2)
example : Primrec₂ toBits := by primrec_rec

def revDigits : ℕ → ℕ → ℕ
  | 0, acc => acc
  | k + 1, acc => revDigits k (acc * 10 + k % 10)
example : Primrec₂ revDigits := by primrec_rec

def stepAcc : ℕ → List ℕ → List ℕ
  | 0, l => l
  | k + 1, l => k :: stepAcc k (l.map (· + k))
example : Primrec₂ stepAcc := by primrec_rec

end Changing

/-! ### Integers, matrices, and further list and `ℕ` operations -/

example : Primrec fun p : ℤ × ℤ => p.1 * p.2 - 3 * p.1 ^ 2 + (p.2).natAbs := by fun_prop
example : PrimrecPred fun p : ℤ × ℤ => p.1 < p.2 ∧ p.2 ≤ 7 := by fun_prop
example : Primrec fun z : ℤ => (z.toNat, ((z.natAbs : ℕ) : ℤ)) := by fun_prop

example : Primrec fun p : ℤ × ℤ => (!![p.1, 0; p.2, p.1 * p.2] : Matrix (Fin 2) (Fin 2) ℤ) := by
  fun_prop
example : Primrec fun n : ℕ => (Matrix.of fun (i j : Fin 3) => n * i + j) := by fun_prop
example : Primrec fun n : ℕ => List.ofFn fun i : Fin 4 => n + i := by fun_prop

example : Primrec fun n : ℕ => (List.range n).zip (List.range (n+1)) := by fun_prop
example : Primrec fun n : ℕ => (List.range n).zipWith (· + ·) (List.range n) := by fun_prop
example : Primrec fun n : ℕ => (List.range n).erase 3 := by fun_prop
example : Primrec fun n : ℕ => (List.range n).max? := by fun_prop
example : Primrec fun n : ℕ => (List.range n).min? := by fun_prop
example : Primrec fun n : ℕ => Nat.gcd n 6 + Nat.lcm n 6 := by fun_prop
example : Primrec fun n : ℕ => Nat.log 2 n + Nat.sqrt n := by fun_prop
example : Primrec fun n : ℕ => (List.range n).getLast? := by fun_prop
example : Primrec fun n : ℕ => (List.range n).insert 3 := by fun_prop
example : Primrec fun n : ℕ => (List.range n).zipIdx := by fun_prop
example : Primrec fun n : ℕ => (List.range n) ×ˢ (List.range n) := by fun_prop
example : Primrec fun n : ℕ => (List.range n).foldl max 0 := by fun_prop

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
