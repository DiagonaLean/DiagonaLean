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

/-- Rejected: a nested pattern gives three equation lemmas. -/
def iterTwice : ℕ → ℕ
  | 0 => 0
  | n + 1 => match n with
    | 0 => 1
    | k + 1 => iterTwice (k + 1) + 2
example : True := by
  fail_if_success (have : Primrec iterTwice := by primrec_rec)
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
