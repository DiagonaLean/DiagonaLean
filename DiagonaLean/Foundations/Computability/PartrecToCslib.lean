/-
Copyright (c) 2026 Anonymous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymous
-/

import DiagonaLean.Foundations.Computability.TM0ToCslib
import Mathlib.Computability.PartrecBasis

@[expose] public section

/-! # A partial recursive function, as a fixed Cslib machine

`exists_machine` compiles a partial recursive `g : ℕ →. ℕ` to one `SingleTapeTM Bool`, through
Mathlib's chain `ToPartrec.Code → TM2 → TM1 → TM1 over Bool → TM0`, followed by `wrap`.

The machine is a *finite constant*: it is obtained classically, once, for the fixed `g`. Mathlib's
chain is `noncomputable` because of its supports, so a reduction may not call the compiler on data
that depends on its input. It may use the machine, because one finite constant cannot hide
infinitely many answers (see the convention on `ManyOneReduces`).

## The result bit

The machine only reports whether the value of `g` is zero. Mathlib's translations all preserve the
local variable `σ`, so this bit can be carried there and read from the final `TM0` state. `tr2` is
Mathlib's `PartrecToTM2.tr` with the halting statement redirected to one extra label, which copies
the top of the main stack to `σ` and then halts.

## Main statements

* `exists_machine`: on input `e₀ ++ (trNat n).reverse.flatMap e`, the machine outputs
  `[decide (m ≠ 0)]` for every `m ∈ g n`.
-/

namespace DiagonaLean.Foundations.Computability

open Turing PartrecToTM2 ToPartrec StateTransition Function

/-! ### Reporting the result in the local variable -/

/-- Mathlib's labels, plus one label that reads the result. -/
inductive L2 (uc : Code) where
  | orig (q : Λ')
  | check

instance (uc : Code) : Inhabited (L2 uc) := ⟨.orig (trNormal uc Cont'.halt)⟩

/-- Statements of the TM2 machine, over labels `Λ`. -/
abbrev St2 (Λ : Type) := TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ')

/-- Configurations of the TM2 machine, over labels `Λ`. -/
abbrev Cf2 (Λ : Type) := TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')

variable (uc : Code)

/-- Redirect `halt` to `check`. -/
def rwS : St2 Λ' → St2 (L2 uc)
  | .push k f q => .push k f (rwS q)
  | .peek k f q => .peek k f (rwS q)
  | .pop k f q => .pop k f (rwS q)
  | .load a q => .load a (rwS q)
  | .branch p q₁ q₂ => .branch p (rwS q₁) (rwS q₂)
  | .goto l => .goto fun v => .orig (l v)
  | .halt => .goto fun _ => .check

/-- The machine with the extra label. -/
def tr2 : L2 uc → St2 (L2 uc)
  | .orig q => rwS uc (tr q)
  | .check => .peek K'.main (fun _ top => top) .halt

/-- The configuration of `tr2` for a configuration of `tr`. -/
def lift (c : Cf2 Λ') : Cf2 (L2 uc) :=
  ⟨some (match c.l with
    | some q => .orig q
    | none => .check), c.var, c.stk⟩

theorem stepAux_rwS (s : St2 Λ') (v : Option Γ') (S : K' → List Γ') :
    TM2.stepAux (rwS uc s) v S = lift uc (TM2.stepAux s v S) := by
  induction s generalizing v S with
  | push k f q ih => exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => exact ih _ _
  | load a q ih => exact ih _ _
  | branch p q₁ q₂ ih₁ ih₂ =>
    simp only [rwS, TM2.stepAux]
    cases p v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto l => rfl
  | halt => rfl

theorem reaches_lift {a b : Cf2 Λ'} (h : Reaches (TM2.step tr) a b) :
    Reaches (TM2.step (tr2 uc)) (lift uc a) (lift uc b) := by
  induction h with
  | refl => exact .refl
  | @tail c d _ hcd ih =>
    refine ih.tail ?_
    obtain ⟨_ | q, v, S⟩ := c
    · simp [TM2.step] at hcd
    · have hd : d = TM2.stepAux (tr q) v S := by
        simpa [TM2.step] using (Option.mem_def.1 hcd).symm
      subst hd
      exact Option.mem_def.2 (congrArg some (stepAux_rwS uc (tr q) v S))

theorem supports_rwS {S : Finset Λ'} {T : Finset (L2 uc)} (hT : ∀ q ∈ S, L2.orig q ∈ T)
    (hc : L2.check ∈ T) (s : St2 Λ') (hs : TM2.SupportsStmt S s) :
    TM2.SupportsStmt T (rwS uc s) := by
  induction s with
  | push k f q ih => exact ih hs
  | peek k f q ih => exact ih hs
  | pop k f q ih => exact ih hs
  | load a q ih => exact ih hs
  | branch p q₁ q₂ ih₁ ih₂ => exact ⟨ih₁ hs.1, ih₂ hs.2⟩
  | goto l => exact fun v => hT _ (hs v)
  | halt => exact fun _ => hc

open scoped Classical in
/-- The support of `tr2`. -/
noncomputable def supp2 : Finset (L2 uc) :=
  insert .check ((codeSupp uc Cont'.halt).image .orig)

theorem supports2 : TM2.Supports (tr2 uc) (supp2 uc) := by
  classical
  have hs := tr_supports uc Cont'.halt
  have hT : ∀ q ∈ codeSupp uc Cont'.halt, L2.orig (uc := uc) q ∈ supp2 uc := fun q hq =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hq)
  have hc : L2.check ∈ supp2 uc := Finset.mem_insert_self _ _
  refine ⟨hT _ hs.1, fun q hq => ?_⟩
  rcases Finset.mem_insert.1 hq with rfl | hq
  · exact trivial
  · obtain ⟨q', hq', rfl⟩ := Finset.mem_image.1 hq
    exact supports_rwS uc hT hc _ (hs.2 q' hq')

/-- `tr2` stops with the top of the main stack in the local variable. -/
theorem tr2_eval {n m : ℕ} (hm : [m] ∈ uc.eval [n]) :
    (⟨none, (trList [m]).head?, K'.elim (trList [m]) [] [] []⟩ : Cf2 (L2 uc)) ∈
      StateTransition.eval (TM2.step (tr2 uc))
        (TM2.init K'.main (trList [n]) : Cf2 (L2 uc)) := by
  have he : halt [m] ∈ StateTransition.eval (TM2.step tr) (init uc [n]) := by
    rw [PartrecToTM2.tr_eval]
    exact (Part.mem_map_iff _).2 ⟨[m], hm, rfl⟩
  have hr := reaches_lift uc (mem_eval.1 he).1
  have hinit : lift uc (init uc [n]) = (TM2.init K'.main (trList [n]) : Cf2 (L2 uc)) := by
    simp only [lift, init, TM2.init]
    congr 1
    funext k
    cases k <;> rfl
  rw [hinit] at hr
  refine mem_eval.2 ⟨hr.tail ?_, rfl⟩
  exact Option.mem_def.2 rfl

/-! ### The result bit -/

/-- The bit read from the local variable: is the top of the stack a digit? -/
def bitOf : Option Γ' → Bool
  | some Γ'.cons => false
  | _ => true

theorem trNat_ne_nil {m : ℕ} (hm : m ≠ 0) : trNat m ≠ [] := by
  intro h
  have hz : (m : Num) = 0 := by
    rw [trNat] at h
    cases hx : (m : Num) with
    | zero => rfl
    | pos p =>
      rw [hx] at h
      cases p <;> simp [trNum, trPosNum] at h
  exact hm (by have := Num.to_of_nat m; rw [hz] at this; simpa using this.symm)

theorem bitOf_top (m : ℕ) : bitOf (trList [m]).head? = decide (m ≠ 0) := by
  by_cases hm : m = 0
  · subst hm
    rfl
  · obtain ⟨x, l, hx⟩ := List.exists_cons_of_ne_nil (trNat_ne_nil hm)
    have hend := trNat_natEnd m x (by rw [hx]; exact List.mem_cons_self)
    simp only [trList, hx, List.cons_append, List.head?_cons, hm, ne_eq, not_false_eq_true,
      decide_true]
    cases x <;> first | rfl | simp [natEnd] at hend

instance : Fintype K' := ⟨{K'.main, K'.rev, K'.aux, K'.stack}, by rintro ⟨⟩ <;> simp⟩

/-- The alphabet of the TM1 machine. -/
abbrev Γ2 := TM2to1.Γ' K' (fun _ : K' => Γ')

/-- The cell of the initial tape holding `a`. -/
def cell (b : Bool) (a : Γ') : Γ2 := (b, update (fun _ => none) K'.main (some a))

theorem trInit_eq (n : ℕ) :
    TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main (trList [n]) =
      cell true Γ'.cons :: (trNat n).reverse.map (cell false) := by
  have hrev : (trList [n]).reverse = Γ'.cons :: (trNat n).reverse := by simp
  unfold TM2to1.trInit
  simp only [hrev]
  rfl

theorem trTape_mk₁ {n : ℕ} {enc : Γ2 → List.Vector Bool n}
    (enc0 : enc default = List.Vector.replicate n false) (l : List Γ2) :
    TM1to1.trTape enc0 (Tape.mk₁ l) =
      Tape.mk₁ (l.flatMap fun x => (enc x).toList) := by
  simp only [Tape.mk₁, Tape.mk₂, TM1to1.trTape_mk', TM1to1.trTape', ListBlank.flatMap_mk,
    List.flatMap_nil]

/-- **The compiler.** A partial recursive function, as a fixed machine that outputs whether the
value is zero. The input is a tape built from a finite table. -/
theorem exists_machine (g : ℕ →. ℕ) (hg : Partrec g) :
    ∃ (W : Cslib.Turing.SingleTapeTM Bool) (e₀ : List Bool) (e : Γ' → List Bool),
      ∀ n m, m ∈ g n → W.Outputs (e₀ ++ (trNat n).reverse.flatMap e) [decide (m ≠ 0)] := by
  classical
  obtain ⟨uc, huc⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.2 hg)
  obtain ⟨k, enc, dec, enc0, encdec⟩ := TM1to1.exists_enc_dec (Γ := Γ2)
  let M2 := tr2 uc
  let M1 := TM2to1.tr M2
  let Mb := TM1to1.tr enc dec M1
  let M0 := TM1to0.tr Mb
  have s1 := TM2to1.tr_supports M2 (supports2 uc)
  have sb := TM1to1.tr_supports (enc := enc) (dec := dec) M1 s1
  have s0 := TM1to0.tr_supports Mb sb
  let bit : TM1to0.Λ' Mb → Bool := fun q => bitOf q.2
  refine ⟨wrap M0 _ s0 bit, (enc (cell true Γ'.cons)).toList,
    fun a => (enc (cell false a)).toList, fun n m hm => ?_⟩
  have hv : [m] ∈ uc.eval [n] := by
    have h := huc ⟨[n], rfl⟩
    have h' : uc.eval [n] = pure <$> g n := h
    rw [h']
    exact (Part.mem_map_iff _).2 ⟨m, hm, rfl⟩
  have h2 := tr2_eval uc hv
  obtain ⟨b₁, hb₁, hb₁e⟩ := StateTransition.tr_eval (TM2to1.tr_respects M2)
    (TM2to1.trCfg_init K'.main (trList [n])) h2
  obtain ⟨b₂, hb₂, hb₂e⟩ := StateTransition.tr_eval (TM1to1.tr_respects dec M1 encdec (enc0 := enc0))
    (a₂ := (TM1.init ((TM2to1.trInit K'.main (trList [n])).flatMap fun x => (enc x).toList) :
      TM1.Cfg Bool (TM1to1.Λ' Γ2 _ _) _))
    (by simp only [TM1to1.trCfg, TM1.init, trTape_mk₁]; rfl) hb₁e
  obtain ⟨b₃, hb₃, hb₃e⟩ := StateTransition.tr_eval (TM1to0.tr_respects Mb)
    (a₂ := (TM0.init ((TM2to1.trInit K'.main (trList [n])).flatMap fun x => (enc x).toList) :
      TM0.Cfg Bool (TM1to0.Λ' Mb))) rfl hb₂e
  have hout := wrap_outputs M0 _ s0 bit hb₃e
  have hbit : bit b₃.q = decide (m ≠ 0) := by
    rw [← bitOf_top m]
    cases hb₁
    subst hb₂
    subst hb₃
    rfl
  rw [hbit, trInit_eq] at hout
  rw [List.flatMap_cons, List.flatMap_map] at hout
  exact hout

end DiagonaLean.Foundations.Computability
