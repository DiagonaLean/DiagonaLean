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

end PTree
