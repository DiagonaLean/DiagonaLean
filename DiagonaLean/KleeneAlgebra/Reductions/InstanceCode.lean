/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.KleeneAlgebra.Reductions.Instance

@[expose] public section

/-! # Computing the instance

`instCode K l` computes the codes of `rInst K l` by plain arithmetic on row codes, and
`instCode_prim` shows that it is primitive recursive in `l`.

The term `rhsN` contains `bnd (rmS _)`, which is defined by recursion on syntax. To avoid recursion
on codes, the builders run on two tracks: `pcode e` is the pair of the codes of `e` and of `bnd e`,
and each constructor of `RExp` acts on such pairs directly.

## Main statements

* `instCode_eq`: `instCode K l` is the pair of codes of `rInst K l`.
* `instCode_prim`: it is primitive recursive.
-/

namespace DiagonaLean.KAComm.Reduction

open Cslib.Turing Enc RExp TD DiagonaLean.Foundations.Computability

attribute [local irreducible] Nat.pair

/-! ### Two-track builders -/

/-- A pair of codes: of an expression, and of its `bnd`. -/
abbrev P := ℕ × ℕ

/-- `zero`. -/
abbrev pz : P := (cz, co)
/-- `one`. -/
abbrev po : P := (co, co)
/-- `sym`. -/
abbrev ps (s : ℕ) : P := (cs s, cp co (cs s))
/-- `plus`. -/
abbrev pp (x y : P) : P := (cp x.1 y.1, cp co (cp x.2 y.2))
/-- `mul`. -/
abbrev pm (x y : P) : P := (cm x.1 y.1, cp co (cm x.2 y.2))
/-- `star`. -/
abbrev pt (x : P) : P := (ct x.1, cp co (cm x.2 (ct x.1)))

/-- `sumL`. -/
def psum (L : List P) : P := L.foldr pp pz
/-- `prodL`. -/
def pprod (L : List P) : P := L.foldr pm po

/-- The codes of `e` and of `bnd e`. -/
def pcode (e : RExp (ℕ ⊕ ℕ)) : P := (rc e, rc (bnd e))

theorem pcode_plus (e f : RExp (ℕ ⊕ ℕ)) : pcode (plus e f) = pp (pcode e) (pcode f) := rfl

theorem pcode_mul (e f : RExp (ℕ ⊕ ℕ)) : pcode (mul e f) = pm (pcode e) (pcode f) := rfl

theorem pcode_star (e : RExp (ℕ ⊕ ℕ)) : pcode (RExp.star e) = pt (pcode e) := rfl

theorem pcode_sumL (L : List (RExp (ℕ ⊕ ℕ))) : pcode (sumL L) = psum (L.map pcode) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    have : pcode (sumL (e :: L)) = pp (pcode e) (pcode (sumL L)) := rfl
    rw [this, ih]
    rfl

theorem pcode_prodL (L : List (RExp (ℕ ⊕ ℕ))) : pcode (prodL L) = pprod (L.map pcode) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    have : pcode (prodL (e :: L)) = pm (pcode e) (pcode (prodL L)) := rfl
    rw [this, ih]
    rfl

theorem map_sumL {X Y : Type*} (φ : X → Y) (L : List (RExp X)) :
    (sumL L).map φ = sumL (L.map (RExp.map φ)) := by
  induction L with
  | nil => rfl
  | cons e L ih => simp [sumL, RExp.map, ih]

theorem map_prodL {X Y : Type*} (φ : X → Y) (L : List (RExp X)) :
    (prodL L).map φ = prodL (L.map (RExp.map φ)) := by
  induction L with
  | nil => rfl
  | cons e L ih => simp [prodL, RExp.map, ih]

theorem map_bnd {X Y : Type*} (φ : X → Y) (e : RExp X) : (bnd e).map φ = bnd (e.map φ) := by
  induction e with
  | zero => rfl
  | one => rfl
  | sym x => rfl
  | plus e f ihe ihf => simp [bnd, RExp.map, ihe, ihf]
  | mul e f ihe ihf => simp [bnd, RExp.map, ihe, ihf]
  | star e ih => simp [bnd, RExp.map, ih]

/-! ### Words -/

/-- The left copy of a word of codes. -/
abbrev lw (u : List ℕ) : P := pprod (u.map fun a => ps (2 * a))
/-- The right copy of a word of codes. -/
abbrev rw' (u : List ℕ) : P := pprod (u.map fun a => ps (2 * a + 1))
/-- `pairS`. -/
abbrev pairC (u v : List ℕ) : P := pm (lw u) (rw' v)

/-- The code of `lend`. -/
abbrev lendC : ℕ := Nat.pair 0 0
/-- The code of `rend`. -/
abbrev rendC : ℕ := Nat.pair 1 0
/-- The code of a cell. -/
abbrev cellC (o : ℕ) : ℕ := Nat.pair 2 o
/-- The code of a head letter. -/
abbrev headC (q o : ℕ) : ℕ := Nat.pair 3 (Nat.pair q o)

section words

variable {St : Type} [Encodable St]

/-- The renaming. -/
abbrev phi : Letter Bool St ⊕ Letter Bool St → ℕ ⊕ ℕ := dmap letC

theorem pcode_lS (u : List (Letter Bool St)) :
    pcode ((lS u).map phi) = lw (u.map letC) := by
  simp only [lS, map_prodL, pcode_prodL, List.map_map, lw]
  rfl

theorem pcode_rS (u : List (Letter Bool St)) :
    pcode ((rS u).map phi) = rw' (u.map letC) := by
  simp only [rS, map_prodL, pcode_prodL, List.map_map, rw']
  rfl

theorem pcode_pairS (u v : List (Letter Bool St)) :
    pcode ((pairS u v).map phi) = pairC (u.map letC) (v.map letC) := by
  have : pcode ((pairS u v).map phi) = pm (pcode ((lS u).map phi)) (pcode ((rS v).map phi)) := rfl
  rw [this, pcode_lS, pcode_rS]

end words

/-! ### The context terms -/

/-- `C`. -/
def cC : P := psum ([0, 1, 2].map fun o => pairC [cellC o] [cellC o])
/-- `⊢ C∗ (u, v) C∗ ⊣`. -/
abbrev ctxC (u v : List ℕ) : P :=
  pm (pm (pm (pm (pairC [lendC] [lendC]) (pt cC)) (pairC u v)) (pt cC)) (pairC [rendC] [rendC])
/-- `⊢ C∗ (u, v)`. -/
abbrev ctxRC (u v : List ℕ) : P := pm (pm (pairC [lendC] [lendC]) (pt cC)) (pairC u v)
/-- `(u, v) C∗ ⊣`. -/
abbrev ctxLC (u v : List ℕ) : P := pm (pm (pairC u v) (pt cC)) (pairC [rendC] [rendC])

/-- The rule for state code `q` and symbol code `h`, written symbol `a`, next state code `qn`, and
movement `m`. -/
def ruleOf (q h a qn m : ℕ) : P :=
  if m = 0 then ctxC [headC (q + 1) h] [headC qn a]
  else if m = 1 then
    pp (psum ([0, 1, 2].map fun x => ctxC [cellC x, headC (q + 1) h] [headC qn x, cellC a]))
      (ctxLC [lendC, headC (q + 1) h] [lendC, headC qn 0, cellC a])
  else
    pp (psum ([0, 1, 2].map fun x => ctxC [headC (q + 1) h, cellC x] [cellC a, headC qn x]))
      (ctxRC [headC (q + 1) h, rendC] [cellC a, headC qn 0, rendC])

section generic

variable {M : SingleTapeTM Bool} [Encodable M.State]

theorem enumL_opt : enumL (Option Bool) = syms := by decide

theorem pcode_cS : pcode ((cS M).map phi) = cC := by
  simp only [cS, enumL_opt]
  rfl

theorem pcode_ctxS (u v : List (Letter Bool M.State)) :
    pcode ((ctxS M u v).map phi) = ctxC (u.map letC) (v.map letC) := by
  have : pcode ((ctxS M u v).map phi) =
      pm (pm (pm (pm (pcode ((pairS [.lend] [.lend] : Ex M).map phi))
        (pt (pcode ((cS M).map phi)))) (pcode ((pairS u v).map phi)))
        (pt (pcode ((cS M).map phi)))) (pcode ((pairS [.rend] [.rend] : Ex M).map phi)) := rfl
  rw [this, pcode_cS, pcode_pairS, pcode_pairS, pcode_pairS]
  rfl

theorem pcode_ctxRS (u v : List (Letter Bool M.State)) :
    pcode ((ctxRS M u v).map phi) = ctxRC (u.map letC) (v.map letC) := by
  have : pcode ((ctxRS M u v).map phi) =
      pm (pm (pcode ((pairS [.lend] [.lend] : Ex M).map phi))
        (pt (pcode ((cS M).map phi)))) (pcode ((pairS u v).map phi)) := rfl
  rw [this, pcode_cS, pcode_pairS, pcode_pairS]
  rfl

theorem pcode_ctxLS (u v : List (Letter Bool M.State)) :
    pcode ((ctxLS M u v).map phi) = ctxLC (u.map letC) (v.map letC) := by
  have : pcode ((ctxLS M u v).map phi) =
      pm (pm (pcode ((pairS u v).map phi)) (pt (pcode ((cS M).map phi))))
        (pcode ((pairS [.rend] [.rend] : Ex M).map phi)) := rfl
  rw [this, pcode_cS, pcode_pairS, pcode_pairS]
  rfl

/-- The rule of `M`, as codes. -/
theorem pcode_ruleS (q : M.State) (h : Option Bool) :
    pcode ((ruleS M q h).map phi) =
      ruleOf (Encodable.encode q) (hc h) (hc (M.tr q h).1.symbol) (qc (M.tr q h).2)
        (mvc (M.tr q h).1.movement) := by
  rcases htr : M.tr q h with ⟨⟨wr, _ | _ | _⟩, q'⟩
  · simp only [ruleS, htr, pcode_ctxS]
    rfl
  · have e1 : pcode ((ruleS M q h).map phi) =
        pp (psum ((enumL (Option Bool)).map fun x =>
            pcode ((ctxS M [.cell x, .head (some q) h] [.head q' x, .cell wr]).map phi)))
          (pcode ((ctxLS M [.lend, .head (some q) h] [.lend, .head q' none, .cell wr]).map phi)) := by
      simp only [ruleS, htr, RExp.map, map_sumL, List.map_map]
      rw [pcode_plus, pcode_sumL, List.map_map]
      rfl
    rw [e1, enumL_opt]
    simp only [pcode_ctxS, pcode_ctxLS]
    rfl
  · have e1 : pcode ((ruleS M q h).map phi) =
        pp (psum ((enumL (Option Bool)).map fun x =>
            pcode ((ctxS M [.head (some q) h, .cell x] [.cell wr, .head q' x]).map phi)))
          (pcode ((ctxRS M [.head (some q) h, .rend] [.cell wr, .head q' none, .rend]).map phi)) := by
      simp only [ruleS, htr, RExp.map, map_sumL, List.map_map]
      rw [pcode_plus, pcode_sumL, List.map_map]
      rfl
    rw [e1, enumL_opt]
    simp only [pcode_ctxS, pcode_ctxRS]
    rfl

end generic

/-! ### The keys and letters of `NM K l` -/

/-- Filter a list, in a form that is primitive recursive in parameters of the predicate. -/
theorem flatMap_filter {α : Type*} (L : List α) (p : α → Prop) [DecidablePred p] :
    (L.flatMap fun k => if p k then [k] else []) = L.filter (fun k => decide (p k)) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    by_cases h : p a <;> simp [List.flatMap_cons, h, List.filter_cons, ih]

/-- The codes of `Fin (N + 1) × Option Bool`, in the order of `enumL`. -/
abbrev keys (N : ℕ) : List ℕ :=
  (List.range (Nat.pair N 2 + 1)).flatMap fun k =>
    if k.unpair.1 ≤ N ∧ k.unpair.2 ≤ 2 then [k] else []

theorem map_encode_filterMap {α : Type*} [Encodable α] (L : List ℕ) :
    (L.filterMap (Encodable.decode₂ α)).map Encodable.encode =
      L.filter fun k => (Encodable.decode₂ α k).isSome := by
  induction L with
  | nil => rfl
  | cons k L ih =>
    rcases h : Encodable.decode₂ α k with _ | a
    · simp [List.filterMap_cons, List.filter_cons, h, ih]
    · have hk : Encodable.encode a = k := Encodable.mem_decode₂.1 h
      simp [List.filterMap_cons, List.filter_cons, h, ih, hk]

theorem sorted_filter_range (B : ℕ) (p : ℕ → Bool) :
    ((List.range B).filter p).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

theorem enumL_codes (α : Type*) [Fintype α] [Encodable α] (B : ℕ) (p : ℕ → Prop)
    [DecidablePred p] (hp : ∀ k, p k ↔ ∃ a : α, Encodable.encode a = k)
    (hB : ∀ a : α, Encodable.encode a < B) :
    (enumL α).map Encodable.encode = (List.range B).filter fun k => decide (p k) := by
  have hlhs : (enumL α).map Encodable.encode =
      (List.range (Finset.univ.sup (Encodable.encode : α → ℕ) + 1)).filter
        fun k => (Encodable.decode₂ α k).isSome := map_encode_filterMap _
  have hiff : ∀ k, (Encodable.decode₂ α k).isSome = true ↔ ∃ a : α, Encodable.encode a = k := by
    intro k
    constructor
    · intro h
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h
      exact ⟨a, Encodable.mem_decode₂.1 ha⟩
    · rintro ⟨a, rfl⟩
      simp [Encodable.encodek₂]
  rw [hlhs]
  refine List.Perm.eq_of_pairwise (le := (· < ·)) (fun _ _ _ _ h₁ h₂ => absurd h₁ (Nat.lt_asymm h₂))
    (sorted_filter_range _ _) (sorted_filter_range _ _) ?_
  refine (List.perm_ext_iff_of_nodup ?_ ?_).2 fun k => ?_
  · exact (List.nodup_range).filter _
  · exact (List.nodup_range).filter _
  · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, hp, hiff]
    constructor
    · rintro ⟨-, a, rfl⟩
      exact ⟨hB a, a, rfl⟩
    · rintro ⟨-, a, rfl⟩
      exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := (Encodable.encode : α → ℕ))
        (Finset.mem_univ a)), a, rfl⟩

variable (K : UConst) (l : List Bool)

theorem encode_state (q : (NM K l).State) : Encodable.encode q = q.val := rfl

theorem encode_opt (o : Option Bool) : Encodable.encode o = hc o := by
  rcases o with _ | _ | _ <;> rfl

theorem encode_key (p : (NM K l).State × Option Bool) :
    Encodable.encode p = Nat.pair p.1.val (hc p.2) := by
  obtain ⟨q, o⟩ := p
  rw [Encodable.encode_prod_val]
  simp only [encode_opt, encode_state]

theorem pair_le_pair {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) : Nat.pair a b ≤ Nat.pair c d :=
  calc Nat.pair a b ≤ Nat.pair c b := by
        rcases hac.eq_or_lt with rfl | h
        · exact le_rfl
        · exact (Nat.pair_lt_pair_left b h).le
    _ ≤ Nat.pair c d := by
        rcases hbd.eq_or_lt with rfl | h
        · exact le_rfl
        · exact (Nat.pair_lt_pair_right c h).le

theorem hc_optOf {x : ℕ} (hx : x ≤ 2) : hc (optOf x) = x := by
  match x, hx with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

theorem keys_eq :
    (enumL ((NM K l).State × Option Bool)).map Encodable.encode = keys (NN K l) := by
  rw [keys, flatMap_filter]
  refine enumL_codes _ _ _ (fun k => ?_) (fun p => ?_)
  · constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨(⟨k.unpair.1, Nat.lt_succ_of_le h₁⟩, optOf k.unpair.2), ?_⟩
      rw [encode_key]
      simp only [hc_optOf h₂, Nat.pair_unpair]
    · rintro ⟨p, rfl⟩
      rw [encode_key, Nat.unpair_pair]
      exact ⟨Nat.le_of_lt_succ p.1.2, Nat.le_of_lt_succ (hc_lt p.2)⟩
  · rw [encode_key]
    exact Nat.lt_succ_of_le (pair_le_pair (Nat.le_of_lt_succ p.1.2) (Nat.le_of_lt_succ (hc_lt p.2)))

/-- Normalize a symbol or movement code. -/
abbrev norm (a : ℕ) : ℕ := if a = 0 then 0 else if a = 1 then 1 else 2

/-- The code of the next state. -/
abbrev nxC (N x : ℕ) : ℕ := if x = 0 then 0 else (x - 1) % (N + 1) + 1

theorem hc_optOf' (a : ℕ) : hc (optOf a) = norm a := by
  match a with
  | 0 => rfl
  | 1 => rfl
  | a + 2 => simp [optOf, hc, norm]

theorem mvc_mvOf (a : ℕ) : mvc (mvOf a) = norm a := by
  match a with
  | 0 => rfl
  | 1 => rfl
  | a + 2 => simp [mvOf, mvc, norm]

theorem qc_nxOf (x : ℕ) : qc (nxOf (NN K l) x : Option (NM K l).State) = nxC (NN K l) x := by
  match x with
  | 0 => rfl
  | x + 1 =>
    show (Fin.ofNat (NN K l + 1) x).val + 1 = _
    simp [Fin.ofNat, nxC]

/-- The rule for a state and a symbol code. -/
abbrev ruleC (q h : ℕ) : P :=
  ruleOf q h (norm (rowA (rowFn K l q h))) (nxC (NN K l) (rowX (rowFn K l q h)))
    (norm (rowM (rowFn K l q h)))

/-- `R_M`. -/
abbrev rmP : P := psum ((keys (NN K l)).map fun k => ruleC K l k.unpair.1 k.unpair.2)

theorem pcode_ruleS_nm (q : (NM K l).State) (h : Option Bool) :
    pcode ((ruleS (NM K l) q h).map phi) = ruleC K l q.val (hc h) := by
  rw [pcode_ruleS]
  have ha : hc ((NM K l).tr q h).1.symbol = norm (rowA (rowFn K l q.val (hc h))) := hc_optOf' _
  have hm : mvc ((NM K l).tr q h).1.movement = norm (rowM (rowFn K l q.val (hc h))) := mvc_mvOf _
  have hq : qc ((NM K l).tr q h).2 = nxC (NN K l) (rowX (rowFn K l q.val (hc h))) := qc_nxOf K l _
  rw [ha, hm, hq, encode_state]

theorem pcode_rmS : pcode ((rmS (NM K l)).map phi) = rmP K l := by
  rw [rmS, map_sumL, List.map_map, pcode_sumL, List.map_map, rmP, ← keys_eq, List.map_map]
  refine congrArg psum (List.map_congr_left fun p _ => ?_)
  simp only [Function.comp, encode_key, Nat.unpair_pair, pcode_ruleS_nm]

/-! ### The other sums -/

/-- `Cr`. -/
abbrev crP : P := psum ([0, 1, 2].map fun o => rw' [cellC o])

theorem pcode_crS : pcode ((crS (NM K l)).map phi) = crP := by
  simp only [crS, enumL_opt, syms, map_sumL, List.map_map, pcode_sumL, List.map_cons, List.map_nil,
    Function.comp, pcode_rS]
  rfl

/-- `Hr`. -/
abbrev hrP : P := psum ((keys (NN K l)).map fun k => rw' [headC (k.unpair.1 + 1) k.unpair.2])

theorem pcode_hrS : pcode ((hrS (NM K l)).map phi) = hrP K l := by
  rw [hrS, map_sumL, List.map_map, pcode_sumL, List.map_map, hrP, ← keys_eq, List.map_map]
  refine congrArg psum (List.map_congr_left fun p _ => ?_)
  simp only [Function.comp, encode_key, Nat.unpair_pair, pcode_rS]
  rfl

/-- `(C_M)_r`. -/
abbrev crunP : P :=
  pm (pm (pm (pm (rw' [lendC]) (pt crP)) (hrP K l)) (pt crP)) (rw' [rendC])

theorem pcode_crunS : pcode ((crunS (NM K l)).map phi) = crunP K l := by
  have : pcode ((crunS (NM K l)).map phi) =
      pm (pm (pm (pm (pcode ((rS [.lend] : Ex (NM K l)).map phi))
        (pt (pcode ((crS (NM K l)).map phi)))) (pcode ((hrS (NM K l)).map phi)))
        (pt (pcode ((crS (NM K l)).map phi)))) (pcode ((rS [.rend] : Ex (NM K l)).map phi)) := rfl
  rw [this, pcode_crS, pcode_hrS, pcode_rS, pcode_rS]
  rfl

/-- `T_true`. -/
abbrev haltP : P :=
  pm (pm (pm (pm (rw' [lendC]) (pt (rw' [cellC 0]))) (rw' [headC 0 2])) (pt (rw' [cellC 0])))
    (rw' [rendC])

theorem pcode_haltS : pcode ((haltS (NM K l) true).map phi) = haltP := by
  have : pcode ((haltS (NM K l) true).map phi) =
      pm (pm (pm (pm (pcode ((rS [.lend] : Ex (NM K l)).map phi))
        (pt (pcode ((rS [.cell none] : Ex (NM K l)).map phi))))
        (pcode ((rS [.head none (some true)] : Ex (NM K l)).map phi)))
        (pt (pcode ((rS [.cell none] : Ex (NM K l)).map phi))))
        (pcode ((rS [.rend] : Ex (NM K l)).map phi)) := rfl
  rw [this]
  simp only [pcode_rS]
  rfl

/-- The codes of all letters. -/
abbrev lettersC (N : ℕ) : List ℕ :=
  [lendC, rendC] ++ [0, 1, 2].map cellC ++
    (List.range (N + 2)).flatMap fun q => [0, 1, 2].map (headC q)

theorem optStates_codes : (optStates K l).map qc = List.range (NN K l + 2) := by
  have hL : ∀ L : List (Fin (NN K l + 1)),
      (L.map (fun q => (some q : Option (NM K l).State))).map qc = L.map (fun q => q.val + 1) := by
    intro L
    induction L with
    | nil => rfl
    | cons q L ih => exact congrArg (List.cons (q.val + 1)) ih
  have h : (List.finRange (NN K l + 1)).map Fin.val = List.range (NN K l + 1) :=
    List.map_coe_finRange_eq_range
  rw [List.range_succ_eq_map, ← h, List.map_map]
  exact congrArg (List.cons 0) (hL _)

theorem letters_codes : (letters K l).map letC = lettersC (NN K l) := by
  rw [letters, lettersC, List.map_append, List.map_append, List.map_flatMap, ← optStates_codes,
    List.flatMap_map]
  rfl

/-- `Σ`. -/
abbrev sigP (N : ℕ) : P := psum ((lettersC N).map fun a => pairC [a] [a])

theorem pcode_sigN : pcode ((sigN K l).map phi) = sigP (NN K l) := by
  rw [sigN, map_sumL, List.map_map, pcode_sumL, List.map_map, sigP, ← letters_codes, List.map_map]
  refine congrArg psum (List.map_congr_left fun a _ => ?_)
  simp only [Function.comp, pcode_pairS]
  rfl

/-- `Σ̈`. -/
abbrev sigAllP (N : ℕ) : P :=
  psum ((lettersC N).map (fun a => ps (2 * a)) ++ (lettersC N).map fun a => ps (2 * a + 1))

theorem pcode_sigAllN : pcode ((sigAllN K l).map phi) = sigAllP (NN K l) := by
  rw [sigAllN, map_sumL, List.map_map, pcode_sumL, List.map_map, sigAllP, ← letters_codes,
    lettersD, List.map_append, List.map_map, List.map_map, List.map_map, List.map_map]
  rfl

/-- `Σ^≠`. -/
abbrev sigNeP (N : ℕ) : P :=
  psum ((lettersC N).map fun a =>
    psum (((lettersC N).flatMap fun b => if b ≠ a then [b] else []).map fun b =>
      pm (ps (2 * a)) (ps (2 * b + 1))))

theorem filter_codes (a : Letter Bool (NM K l).State) :
    ((letters K l).filter (· ≠ a)).map letC =
      ((letters K l).map letC).flatMap fun b => if b ≠ letC a then [b] else [] := by
  rw [flatMap_filter, List.filter_map]
  congr 1
  refine List.filter_congr fun b _ => ?_
  simp [letC_injective.eq_iff]

theorem pcode_sigNeN : pcode ((sigNeN K l).map phi) = sigNeP (NN K l) := by
  rw [sigNeN, map_sumL, List.map_map, pcode_sumL, List.map_map, sigNeP, ← letters_codes,
    List.map_map]
  refine congrArg psum (List.map_congr_left fun a _ => ?_)
  simp only [Function.comp]
  rw [map_sumL, pcode_sumL, List.map_map, List.map_map, ← filter_codes, List.map_map]
  rfl

/-! ### The instance -/

/-- The code of the right-hand side. -/
abbrev instB : ℕ :=
  cp (cm (ct (sigP (NN K l)).1) (cp (crunP K l).1 haltP.1))
    (cm (ct (sigP (NN K l)).1) (cm (sigNeP (NN K l)).1
      (cm (cm (ct (sigAllP (NN K l)).1) (rmP K l).2) (ct (rmP K l).1))))

/-- The code of the left-hand side. -/
abbrev instA : ℕ := cm (rw' [lendC, headC 1 0, rendC]).1 (ct (rmP K l).1)

/-- The codes of `rInst K l`. -/
abbrev instCode : ℕ × ℕ := (cp (instA K l) (instB K l), instB K l)

theorem rc_redB : rc (redB K l) = instB K l := by
  have h : rc (redB K l) =
      cp (cm (ct (pcode ((sigN K l).map phi)).1)
          (cp (pcode ((crunS (NM K l)).map phi)).1 (pcode ((haltS (NM K l) true).map phi)).1))
        (cm (ct (pcode ((sigN K l).map phi)).1) (cm (pcode ((sigNeN K l).map phi)).1
          (cm (cm (ct (pcode ((sigAllN K l).map phi)).1) (rc ((bnd (rmS (NM K l))).map phi)))
            (ct (pcode ((rmS (NM K l)).map phi)).1)))) := rfl
  rw [h, map_bnd]
  have h₂ : rc (bnd ((rmS (NM K l)).map phi)) = (pcode ((rmS (NM K l)).map phi)).2 := rfl
  rw [h₂, pcode_sigN, pcode_crunS, pcode_haltS, pcode_sigNeN, pcode_sigAllN, pcode_rmS]

theorem rc_redA : rc (redA K l) = instA K l := by
  have h : rc (redA K l) =
      cm (pcode ((rS (wd (initData [] : Data (NM K l)))).map phi)).1
        (ct (pcode ((rmS (NM K l)).map phi)).1) := rfl
  rw [h, pcode_rS, pcode_rmS]
  rfl

/-- **`instCode` computes `rInst`.** -/
theorem instCode_eq : (rc (rInst K l).1, rc (rInst K l).2) = instCode K l := by
  have : rc (rInst K l).1 = cp (rc (redA K l)) (rc (redB K l)) := rfl
  rw [this, show rc (rInst K l).2 = rc (redB K l) from rfl, rc_redA, rc_redB]

/-! ### Primitive recursiveness -/

section Prim

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

theorem prim_pp {f g : α → P} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => pp (f x) (g x) :=
  prim_pair (prim_cp (prim_fst hf) (prim_fst hg))
    (prim_cp (Primrec.const _) (prim_cp (prim_snd hf) (prim_snd hg)))

theorem prim_pm {f g : α → P} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => pm (f x) (g x) :=
  prim_pair (prim_cm (prim_fst hf) (prim_fst hg))
    (prim_cp (Primrec.const _) (prim_cm (prim_snd hf) (prim_snd hg)))

theorem prim_pt {f : α → P} (hf : Primrec f) : Primrec fun x => pt (f x) :=
  prim_pair (prim_ct (prim_fst hf))
    (prim_cp (Primrec.const _) (prim_cm (prim_snd hf) (prim_ct (prim_fst hf))))

theorem prim_ps {f : α → ℕ} (hf : Primrec f) : Primrec fun x => ps (f x) :=
  prim_pair (prim_cs hf) (prim_cp (Primrec.const _) (prim_cs hf))

theorem prim_psum {f : α → List P} (hf : Primrec f) : Primrec fun x => psum (f x) :=
  Primrec.list_foldr (h := fun _ y => pp y.1 y.2) hf (Primrec.const pz)
    (Primrec₂.mk (prim_pp (prim_fst Primrec.snd) (prim_snd Primrec.snd)))

theorem prim_pprod {f : α → List P} (hf : Primrec f) : Primrec fun x => pprod (f x) :=
  Primrec.list_foldr (h := fun _ y => pm y.1 y.2) hf (Primrec.const po)
    (Primrec₂.mk (prim_pm (prim_fst Primrec.snd) (prim_snd Primrec.snd)))

theorem prim_lw {f : α → List ℕ} (hf : Primrec f) : Primrec fun x => lw (f x) :=
  prim_pprod (prim_map hf (prim_ps (prim_mul (Primrec.const 2) Primrec.snd)))

theorem prim_rw' {f : α → List ℕ} (hf : Primrec f) : Primrec fun x => rw' (f x) :=
  prim_pprod (prim_map hf
    (prim_ps (prim_add (prim_mul (Primrec.const 2) Primrec.snd) (Primrec.const 1))))

theorem prim_pairC {f g : α → List ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => pairC (f x) (g x) := prim_pm (prim_lw hf) (prim_rw' hg)

theorem prim_ctxC {f g : α → List ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => ctxC (f x) (g x) :=
  prim_pm (prim_pm (prim_pm (prim_pm (Primrec.const _) (Primrec.const _)) (prim_pairC hf hg))
    (Primrec.const _)) (Primrec.const _)

theorem prim_ctxRC {f g : α → List ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => ctxRC (f x) (g x) :=
  prim_pm (Primrec.const _) (prim_pairC hf hg)

theorem prim_ctxLC {f g : α → List ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun x => ctxLC (f x) (g x) :=
  prim_pm (prim_pm (prim_pairC hf hg) (Primrec.const _)) (Primrec.const _)

end Prim

macro_rules
  | `(tactic| prim_step) => `(tactic| with_reducible first
    | apply prim_ctxC
    | apply prim_ctxRC
    | apply prim_ctxLC
    | apply prim_pairC
    | apply prim_lw
    | apply prim_rw'
    | apply prim_psum
    | apply prim_pprod
    | apply prim_pp
    | apply prim_pm
    | apply prim_pt
    | apply prim_ps)

section Prim

variable {α : Type*} [Primcodable α]

theorem ruleOf_prim : Primrec fun y : ℕ × ℕ × ℕ × ℕ × ℕ =>
    ruleOf y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2 := by
  unfold ruleOf
  prim

theorem prim_ruleOf {q h a qn m : α → ℕ} (hq : Primrec q) (hh : Primrec h) (ha : Primrec a)
    (hn : Primrec qn) (hm : Primrec m) :
    Primrec fun x => ruleOf (q x) (h x) (a x) (qn x) (m x) :=
  ruleOf_prim.comp (hq.pair (hh.pair (ha.pair (hn.pair hm))))

end Prim

macro_rules
  | `(tactic| prim_step) => `(tactic| with_reducible apply prim_ruleOf)

/-- **`instCode` is primitive recursive.** -/
theorem instCode_prim (K : UConst) : Primrec fun l : List Bool => instCode K l := by
  show Primrec fun l : List Bool => (cp (instA K l) (instB K l), instB K l)
  prim

end DiagonaLean.KAComm.Reduction
