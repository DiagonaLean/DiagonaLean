import DiagonaLean

/-! # Proving functions primitive recursive, computable, and machine computable, automatically

A guided tour of the automation in `DiagonaLean.Foundations.Computability` (see `AUTOMATION.md`
there). Every proof below is one tactic call, apart from the one-line wrappers that two-argument
functions need (section 2). Run it with

    lake env lean scripts/AutomationDemo.lean

The tactics:

* `fun_prop` proves `Primrec f` and `Computable f` for `f` built by composition from known
  pieces (arithmetic, lists, options, sums, integers, matrices, and anything tagged `@[fun_prop]`);
* `primrec_rec` proves `Primrec f` or `Primrec₂ f` for `f` defined by recursion: on `ℕ`
  (structural, course-of-values, with a changing argument), on lists, and on any inductive type
  given `derive_primcodable`, including nested ones (fields `List T`, `Option T`);
* `derive_primcodable T` makes an inductive type `Primcodable`, with `fun_prop` lemmas for its
  constructors and the recursion principle `primrec_rec` uses;
* `tm_computer F` produces a single-tape Turing machine (Cslib's `SingleTapeTM Bool`) that computes
  a function `F : List Bool → List Bool` shown computable by `fun_prop`.

Tag a result `@[fun_prop]`, and later proofs use it automatically: that is how the sections below
build on one another. `fun_prop` takes a lemma about a function of one argument as it is
(`Primrec f`); for two arguments, prove `Primrec₂ f` and add the one-line compositional form
`Primrec fun x => f (g x) (h x)` from `Primrec g` and `Primrec h`, as in section 2.
-/

open DiagonaLean.Foundations.Computability

/-! ## 1. Composition: `fun_prop` -/

example : Primrec fun n : ℕ => n * n + 3 * n + 1 := by fun_prop
example : Primrec fun p : ℕ × ℕ => if p.1 < p.2 then p.2 - p.1 else Nat.gcd p.1 p.2 := by fun_prop
example : Primrec fun l : List ℕ => (l.filter (· % 2 = 0)).map (· * 3) |>.sum := by fun_prop
example : Primrec fun l : List ℕ => (l.zip l.reverse).map fun q => q.1 * q.2 := by fun_prop
example : Primrec fun n : ℕ => (List.range n).foldl (fun acc i => acc + i * i) 0 := by fun_prop
example : PrimrecPred fun l : List ℕ => ∀ x ∈ l, x < 10 := by fun_prop
-- integers and matrices
example : Primrec fun z : ℤ => z * z - 4 * z + 4 := by fun_prop
example : Primrec fun p : ℤ × ℤ => (!![p.1, p.2; -p.2, p.1] : Matrix (Fin 2) (Fin 2) ℤ) := by
  fun_prop

/-! ## 2. Recursion on `ℕ`: `primrec_rec` -/

/-- Structural recursion with a parameter. -/
def powSum (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => powSum b n * b + 1
theorem powSum_primrec : Primrec₂ powSum := by primrec_rec
-- the compositional form, which `fun_prop` uses
@[fun_prop] theorem prim_powSum {α : Type} [Primcodable α] {f g : α → ℕ} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => powSum (f x) (g x) := powSum_primrec.comp hf hg

/-- Course-of-values recursion: calls on any smaller argument. -/
def bits : ℕ → ℕ
  | 0 => 0
  | n + 1 => bits ((n + 1) / 2) + (n + 1) % 2
@[fun_prop] theorem bits_primrec : Primrec bits := by primrec_rec

/-- Nested patterns. -/
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
@[fun_prop] theorem fib_primrec : Primrec fib := by primrec_rec

/-- Recursion on the first argument while the second changes. -/
def toDigits : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, n => n % 10 :: toDigits k (n / 10)
theorem toDigits_primrec : Primrec₂ toDigits := by primrec_rec
@[fun_prop] theorem prim_toDigits {α : Type} [Primcodable α] {f g : α → ℕ} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun x => toDigits (f x) (g x) := toDigits_primrec.comp hf hg

-- the lemmas compose: no further work for a function that uses them
example : Primrec fun n : ℕ => fib (bits n) + (toDigits 5 n).sum + powSum 2 n := by fun_prop

/-! ## 3. Recursion on lists, and polymorphic definitions -/

/-- Interleaving a separator, for any element type. -/
def interleave {α : Type} (sep : α) : List α → List α
  | [] => []
  | a :: l => a :: sep :: interleave sep l
example {α : Type} [Primcodable α] : Primrec₂ (@interleave α) := by primrec_rec

/-- Running maxima. -/
def runMax : List ℕ → List ℕ
  | [] => []
  | a :: l => a :: (runMax l).map (max a)
@[fun_prop] theorem runMax_primrec : Primrec runMax := by primrec_rec

/-! ## 4. Your own inductive types: `derive_primcodable` -/

/-- Arithmetic expressions over variables `x₀, x₁, …`. -/
inductive Expr where
  | lit (n : ℕ)
  | var (i : ℕ)
  | add (a b : Expr)
  | mul (a b : Expr)
  deriving Inhabited
derive_primcodable Expr

/-- Evaluation, in an environment given as a list. -/
def Expr.eval (env : List ℕ) : Expr → ℕ
  | .lit n => n
  | .var i => env.getD i 0
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
theorem Expr.eval_primrec : Primrec₂ Expr.eval := by primrec_rec
@[fun_prop] theorem Expr.prim_eval {α : Type} [Primcodable α] {f : α → List ℕ} {g : α → Expr}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun x => (g x).eval (f x) :=
  Expr.eval_primrec.comp hf hg

/-- Substituting `e` for the variable `x₀`: a parameter, and a result that is again an
expression. -/
def Expr.subst0 (e : Expr) : Expr → Expr
  | .lit n => .lit n
  | .var i => if i = 0 then e else .var i
  | .add a b => .add (Expr.subst0 e a) (Expr.subst0 e b)
  | .mul a b => .mul (Expr.subst0 e a) (Expr.subst0 e b)
example : Primrec₂ Expr.subst0 := by primrec_rec

/-- The constructors are primitive recursive, so building expressions is too. -/
example : Primrec fun n : ℕ => Expr.add (.var n) (.mul (.lit n) (.lit 2)) := by fun_prop

/-- Composition again: the value of a generated expression. -/
example : Primrec fun n : ℕ => (Expr.add (.var 0) (.lit n)).eval [n, n] := by fun_prop

/-! ## 5. Nested types: children in a `List` or an `Option` -/

/-- Rose trees. -/
inductive Rose where
  | node (label : ℕ) (kids : List Rose)
  deriving Inhabited
derive_primcodable Rose

/-- The sum of the labels: the recursive call is mapped over the children. -/
def Rose.total : Rose → ℕ
  | .node a cs => a + (cs.map Rose.total).sum
@[fun_prop] theorem Rose.total_primrec : Primrec Rose.total := by primrec_rec

/-- The height. -/
def Rose.height : Rose → ℕ
  | .node _ cs => ((cs.map fun c => c.height + 1).foldr max 0)
example : Primrec Rose.height := by primrec_rec

/-- Mirroring: the result is again a tree. -/
def Rose.mirror : Rose → Rose
  | .node a cs => .node a (cs.map Rose.mirror).reverse
example : Primrec Rose.mirror := by primrec_rec

/-- Binary trees with optional children. -/
inductive OTree where
  | leaf (n : ℕ)
  | node (l : Option OTree) (k : ℕ) (r : Option OTree)
  deriving Inhabited
derive_primcodable OTree

/-- Written with `match` on the options (Lean splits the equations; `primrec_rec` recombines
them). -/
def OTree.sum : OTree → ℕ
  | .leaf n => n
  | .node l k r =>
    (match l with | none => 0 | some t => t.sum) + k + (match r with | none => 0 | some t => t.sum)
example : Primrec OTree.sum := by primrec_rec

/-! ## 6. Paramorphisms: using the subterms themselves -/

/-- The label of the root. -/
def Rose.label' : Rose → ℕ
  | .node a _ => a
@[fun_prop] theorem Rose.label'_primrec : Primrec Rose.label' := by primrec_rec

/-- The labels of the children, at every node: the right-hand side looks at the children, not
only at the results on them. -/
def Rose.childLabels : Rose → ℕ
  | .node _ cs => (cs.map Rose.label').sum + (cs.map Rose.childLabels).sum
example : Primrec Rose.childLabels := by primrec_rec

/-! ## 7. Universe-polymorphic types -/

universe u

/-- Lists whose entries carry a tag, over a type in any universe. -/
inductive Tagged (X : Type u) where
  | nil
  | cons (x : X) (tag : ℕ) (rest : Tagged X)
derive_primcodable Tagged

/-- The sum of the tags. -/
def Tagged.tags {X : Type u} : Tagged X → ℕ
  | .nil => 0
  | .cons _ t r => t + r.tags
example {X : Type u} [Primcodable X] : Primrec (@Tagged.tags X) := by primrec_rec

/-! ## 8. `Computable`

`Primrec` implies `Computable` (`Primrec.to_comp`), and `fun_prop` proves `Computable` goals
directly, using that transition. -/

example : Computable fun n : ℕ => fib n + bits n := by fun_prop
example : Computable fun e : Expr => e.eval [1, 2, 3] := by fun_prop
example : Computable Rose.total := Rose.total_primrec.to_comp

/-! ## 9. Turing machines: `tm_computer`

A function on bit strings that `fun_prop` proves computable is computed by a single-tape Turing
machine over `Bool`: `R.Outputs l (F l)` says that, started on `l`, the machine stops with exactly
`F l` on its tape. -/

/-- Complement every bit and append a parity bit. -/
def parityFlip (l : List Bool) : List Bool := l.map (!·) ++ [decide (l.count true % 2 = 1)]
@[fun_prop] theorem parityFlip_primrec : Primrec parityFlip := by unfold parityFlip; fun_prop

open Cslib.Turing in
example : ∃ R : SingleTapeTM Bool, ∀ l, R.Outputs l (parityFlip l) := by
  tm_computer parityFlip

/-! ## 10. What is not automatic

The tactics are sound but incomplete: they fail, with a message, outside the supported shapes. -/

/-- The Ackermann function is computable but not primitive recursive, so no tactic can prove it
`Primrec`; `primrec_rec` refuses its nested recursive call. -/
def ack : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
example : True := by
  fail_if_success (have : Primrec₂ ack := by primrec_rec)
  trivial

/-- Recursion through a `filter` before the recursive `map`. -/
def Rose.prune (k : ℕ) : Rose → Rose
  | .node a cs => .node a ((cs.filter fun c => c.label' < k).map (Rose.prune k))
example : True := by
  fail_if_success (have : Primrec₂ Rose.prune := by primrec_rec)
  trivial
