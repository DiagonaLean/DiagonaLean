/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CFGame.Simulation
import DiagonaLean.CFGame.Regular

@[expose] public section

/-! # The target of the simulation game as a regular expression

The target of the simulation game (`Simulation.Target`) is a finite union of languages of the
form `A* · m · A*`, for a set of letters `A` and a word `m`. Over a finite alphabet each is
given by a regular expression (`CFGame.pattern`), so the target is one too
(`target`, `mem_target`).
-/

namespace DiagonaLean.CFGame.Simulation

open RegularExpression Letter

/-! ### The target -/

variable {Q Γ : Type}

/-- The letters of the game for the states `qs` and the tape symbols `cs`. -/
def letters (qs : List Q) (cs : List Γ) : List (Letter Q Γ) :=
  [dollar, endm, halt, objTape, objHead, objR, objL] ++ cs.map tape ++
    qs.flatMap fun q => cs.flatMap fun c => [head q c, rmark q c, lmark q c]

/-- `letters qs cs` lists all letters when `qs` and `cs` list all states and symbols. -/
theorem mem_letters {qs : List Q} {cs : List Γ} (hqs : ∀ q, q ∈ qs) (hcs : ∀ c, c ∈ cs)
    (x : Letter Q Γ) : x ∈ letters qs cs := by
  cases x <;> simp [letters, hqs, hcs]

/-- A letter is a head or a marker. -/
def isActiveB : Letter Q Γ → Bool
  | head _ _ | rmark _ _ | lmark _ _ => true
  | _ => false

/-- The letters that are not objections. -/
def nonObj (qs : List Q) (cs : List Γ) : List (Letter Q Γ) :=
  (letters qs cs).filter fun x => !isObjB x

/-- The letters that are neither objections, heads nor markers. -/
def quiet (qs : List Q) (cs : List Γ) : List (Letter Q Γ) :=
  (letters qs cs).filter fun x => !isObjB x && !isActiveB x

/-- The letters that are neither objections nor heads. -/
def headless (qs : List Q) (cs : List Γ) : List (Letter Q Γ) :=
  (letters qs cs).filter fun x => !isObjB x && !isHeadB x

/-- The target of the game for the states `qs` and the tape symbols `cs`. -/
def target [DecidableEq Q] (qs : List Q) (cs : List Γ) : RegularExpression (Letter Q Γ) :=
  sumRE (pattern (nonObj qs cs) [halt] ::
    ((qs.flatMap fun q => cs.flatMap fun b => qs.flatMap fun p => cs.flatMap fun c =>
        if p = q then [] else
          [pattern (nonObj qs cs) [rmark q b, head p c],
            pattern (nonObj qs cs) [head p c, lmark q b]]) ++
      [pattern (quiet qs cs) [objHead]] ++
      (qs.flatMap fun q => cs.flatMap fun b =>
        [pattern (headless qs cs) [rmark q b, objTape],
          pattern (headless qs cs) [objTape, lmark q b]]) ++
      (qs.flatMap fun p => cs.flatMap fun c =>
        [pattern (nonObj qs cs) [objR, head p c],
          pattern (nonObj qs cs) [head p c, objL]])))

section Equivalence

variable {qs : List Q} {cs : List Γ} (hqs : ∀ q, q ∈ qs) (hcs : ∀ c, c ∈ cs)
include hqs hcs

omit hqs hcs in
/-- A word has no objection iff none of its letters is one. -/
theorem objCount_eq_zero_iff {w : List (Letter Q Γ)} : objCount w = 0 ↔ ∀ x ∈ w, ¬ x.IsObj := by
  simp [objCount, List.countP_eq_zero]

/-- The letters of `nonObj` are the letters that are not objections. -/
theorem mem_nonObj {x : Letter Q Γ} : x ∈ nonObj qs cs ↔ ¬ x.IsObj := by
  simp [nonObj, mem_letters hqs hcs, isObjB]

/-- The letters of `quiet` are the letters that are neither objections, heads nor markers. -/
theorem mem_quiet {x : Letter Q Γ} : x ∈ quiet qs cs ↔ ¬ x.IsObj ∧ ¬ x.IsActive := by
  cases x <;> simp [quiet, mem_letters hqs hcs, isObjB, isActiveB, IsObj, IsActive]

/-- The letters of `headless` are the letters that are neither objections nor heads. -/
theorem mem_headless {x : Letter Q Γ} : x ∈ headless qs cs ↔ ¬ x.IsObj ∧ ¬ x.IsHead := by
  cases x <;> simp [headless, mem_letters hqs hcs, isObjB, isHeadB, IsObj, IsHead]

omit hqs hcs in
/-- `u ++ m ++ v` has the objections of `u`, `m` and `v`. -/
theorem objCount_append3 (u m v : List (Letter Q Γ)) :
    objCount (u ++ m ++ v) = objCount u + objCount m + objCount v := by
  simp [objCount, List.countP_append]
  omega

omit hqs hcs in
/-- The objections of `u ++ m ++ v`, when `u` and `v` have none, are those of `m`. -/
theorem objCount_pattern {u m v : List (Letter Q Γ)} (hu : ∀ x ∈ u, ¬ x.IsObj)
    (hv : ∀ x ∈ v, ¬ x.IsObj) : objCount (u ++ m ++ v) = objCount m := by
  rw [objCount_append3, objCount_eq_zero_iff.2 hu, objCount_eq_zero_iff.2 hv]
  simp

omit hqs hcs in
/-- The letters of `u` and `v` are not objections when `u ++ m ++ v` has as many objections as
`m`. -/
theorem parts_of_objCount {u m v : List (Letter Q Γ)}
    (h : objCount (u ++ m ++ v) = objCount m) :
    (∀ x ∈ u, ¬ x.IsObj) ∧ ∀ x ∈ v, ¬ x.IsObj := by
  rw [objCount_append3] at h
  exact ⟨objCount_eq_zero_iff.1 (by omega), objCount_eq_zero_iff.1 (by omega)⟩

/-- A word matches the target expression iff it is in the target. -/
theorem mem_target [DecidableEq Q] {w : List (Letter Q Γ)} :
    w ∈ (target qs cs).matches' ↔ Target w := by
  have hn := fun x => mem_nonObj (x := x) hqs hcs
  have hqt := fun x => mem_quiet (x := x) hqs hcs
  have hhl := fun x => mem_headless (x := x) hqs hcs
  simp only [target, mem_sumRE, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨e, he, hw⟩
    rcases he with rfl | (((⟨q, -, b, -, p, -, c, -, he⟩ | rfl) | ⟨q, -, b, -, he⟩) |
      ⟨p, -, c, -, he⟩)
    · obtain ⟨u, v, rfl, hu, hv⟩ := mem_pattern.1 hw
      refine Or.inl ⟨?_, Or.inl (by simp)⟩
      rw [objCount_pattern (fun x hx => (hn x).1 (hu x hx)) (fun x hx => (hn x).1 (hv x hx))]
      simp [objCount, IsObj]
    · split_ifs at he with hpq
      · simp at he
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> obtain ⟨u, v, rfl, hu, hv⟩ := mem_pattern.1 hw <;>
          refine Or.inl ⟨?_, ?_⟩
        · rw [objCount_pattern (fun x hx => (hn x).1 (hu x hx)) (fun x hx => (hn x).1 (hv x hx))]
          simp [objCount, IsObj]
        · exact Or.inr (Or.inl ⟨u, v, q, b, p, c, by simp, hpq⟩)
        · rw [objCount_pattern (fun x hx => (hn x).1 (hu x hx)) (fun x hx => (hn x).1 (hv x hx))]
          simp [objCount, IsObj]
        · exact Or.inr (Or.inr ⟨u, v, q, b, p, c, by simp, hpq⟩)
    · obtain ⟨u, v, rfl, hu, hv⟩ := mem_pattern.1 hw
      refine Or.inr ⟨?_, Or.inl ⟨by simp, ?_⟩⟩
      · rw [objCount_pattern (fun x hx => ((hqt x).1 (hu x hx)).1)
          (fun x hx => ((hqt x).1 (hv x hx)).1)]
        simp [objCount, IsObj]
      · simp only [List.mem_append, List.mem_singleton]
        rintro x ((hx | rfl) | hx)
        exacts [((hqt x).1 (hu x hx)).2, id, ((hqt x).1 (hv x hx)).2]
    · rcases he with rfl | rfl <;> obtain ⟨u, v, rfl, hu, hv⟩ := mem_pattern.1 hw <;>
        refine Or.inr ⟨?_, ?_⟩
      · rw [objCount_pattern (fun x hx => ((hhl x).1 (hu x hx)).1)
          (fun x hx => ((hhl x).1 (hv x hx)).1)]
        simp [objCount, IsObj]
      · refine Or.inr (Or.inl ⟨u, v, q, b, by simp, ?_⟩)
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        rintro x ((hx | rfl | rfl) | hx)
        exacts [((hhl x).1 (hu x hx)).2, id, id, ((hhl x).1 (hv x hx)).2]
      · rw [objCount_pattern (fun x hx => ((hhl x).1 (hu x hx)).1)
          (fun x hx => ((hhl x).1 (hv x hx)).1)]
        simp [objCount, IsObj]
      · refine Or.inr (Or.inr (Or.inl ⟨u, v, q, b, by simp, ?_⟩))
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        rintro x ((hx | rfl | rfl) | hx)
        exacts [((hhl x).1 (hu x hx)).2, id, id, ((hhl x).1 (hv x hx)).2]
    · rcases he with rfl | rfl <;> obtain ⟨u, v, rfl, hu, hv⟩ := mem_pattern.1 hw <;>
        refine Or.inr ⟨?_, ?_⟩
      · rw [objCount_pattern (fun x hx => (hn x).1 (hu x hx)) (fun x hx => (hn x).1 (hv x hx))]
        simp [objCount, IsObj]
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨u, v, p, c, by simp⟩)))
      · rw [objCount_pattern (fun x hx => (hn x).1 (hu x hx)) (fun x hx => (hn x).1 (hv x hx))]
        simp [objCount, IsObj]
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨u, v, p, c, by simp⟩)))
  · have nob : ∀ {u m v : List (Letter Q Γ)}, objCount (u ++ m ++ v) = objCount m →
        (∀ x ∈ u, x ∈ nonObj qs cs) ∧ ∀ x ∈ v, x ∈ nonObj qs cs := fun h =>
      ⟨fun x hx => (hn x).2 ((parts_of_objCount h).1 x hx),
        fun x hx => (hn x).2 ((parts_of_objCount h).2 x hx)⟩
    rintro (⟨h0, hh | ⟨u, v, q, b, p, c, rfl, hpq⟩ | ⟨u, v, q, b, p, c, rfl, hpq⟩⟩ |
      ⟨h1, ⟨hm, hact⟩ | ⟨u, v, q, b, rfl, hnh⟩ | ⟨u, v, q, b, rfl, hnh⟩ | ⟨u, v, p, c, rfl⟩ |
        ⟨u, v, p, c, rfl⟩⟩)
    · obtain ⟨u, v, rfl⟩ := List.append_of_mem hh
      obtain ⟨hu, hv⟩ := nob (u := u) (m := [halt]) (v := v) (by simpa [objCount, IsObj] using h0)
      exact ⟨_, Or.inl rfl, mem_pattern.2 ⟨u, v, by simp, hu, hv⟩⟩
    · obtain ⟨hu, hv⟩ := nob (u := u) (m := [rmark q b, head p c]) (v := v)
        (by simpa [objCount, IsObj] using h0)
      refine ⟨pattern (nonObj qs cs) [rmark q b, head p c],
        Or.inr (Or.inl (Or.inl (Or.inl ⟨q, hqs q, b, hcs b, p, hqs p, c, hcs c, ?_⟩))),
        mem_pattern.2 ⟨u, v, by simp, hu, hv⟩⟩
      simp [hpq]
    · obtain ⟨hu, hv⟩ := nob (u := u) (m := [head p c, lmark q b]) (v := v)
        (by simpa [objCount, IsObj] using h0)
      refine ⟨pattern (nonObj qs cs) [head p c, lmark q b],
        Or.inr (Or.inl (Or.inl (Or.inl ⟨q, hqs q, b, hcs b, p, hqs p, c, hcs c, ?_⟩))),
        mem_pattern.2 ⟨u, v, by simp, hu, hv⟩⟩
      simp [hpq]
    · obtain ⟨u, v, rfl⟩ := List.append_of_mem hm
      have h1' : objCount (u ++ [objHead] ++ v) = objCount [(objHead : Letter Q Γ)] := by
        simpa [objCount, IsObj] using h1
      have hu := (parts_of_objCount h1').1
      have hv := (parts_of_objCount h1').2
      refine ⟨_, Or.inr (Or.inl (Or.inl (Or.inr rfl))), mem_pattern.2 ⟨u, v, by simp, ?_, ?_⟩⟩
      · exact fun x hx => (hqt x).2 ⟨hu x hx, hact x (by simp [hx])⟩
      · exact fun x hx => (hqt x).2 ⟨hv x hx, hact x (by simp [hx])⟩
    · have h1' : objCount (u ++ [rmark q b, objTape] ++ v) =
          objCount [rmark q b, (objTape : Letter Q Γ)] := by simpa [objCount, IsObj] using h1
      have hu := (parts_of_objCount h1').1
      have hv := (parts_of_objCount h1').2
      refine ⟨_, Or.inr (Or.inl (Or.inr ⟨q, hqs q, b, hcs b, Or.inl rfl⟩)),
        mem_pattern.2 ⟨u, v, by simp, ?_, ?_⟩⟩
      · exact fun x hx => (hhl x).2 ⟨hu x hx, hnh x (by simp [hx])⟩
      · exact fun x hx => (hhl x).2 ⟨hv x hx, hnh x (by simp [hx])⟩
    · have h1' : objCount (u ++ [objTape, lmark q b] ++ v) =
          objCount [(objTape : Letter Q Γ), lmark q b] := by simpa [objCount, IsObj] using h1
      have hu := (parts_of_objCount h1').1
      have hv := (parts_of_objCount h1').2
      refine ⟨_, Or.inr (Or.inl (Or.inr ⟨q, hqs q, b, hcs b, Or.inr rfl⟩)),
        mem_pattern.2 ⟨u, v, by simp, ?_, ?_⟩⟩
      · exact fun x hx => (hhl x).2 ⟨hu x hx, hnh x (by simp [hx])⟩
      · exact fun x hx => (hhl x).2 ⟨hv x hx, hnh x (by simp [hx])⟩
    · obtain ⟨hu, hv⟩ := nob (u := u) (m := [objR, head p c]) (v := v)
        (by simpa [objCount, IsObj] using h1)
      exact ⟨_, Or.inr (Or.inr ⟨p, hqs p, c, hcs c, Or.inl rfl⟩),
        mem_pattern.2 ⟨u, v, by simp, hu, hv⟩⟩
    · obtain ⟨hu, hv⟩ := nob (u := u) (m := [head p c, objL]) (v := v)
        (by simpa [objCount, IsObj] using h1)
      exact ⟨_, Or.inr (Or.inr ⟨p, hqs p, c, hcs c, Or.inr rfl⟩),
        mem_pattern.2 ⟨u, v, by simp, hu, hv⟩⟩

end Equivalence

end DiagonaLean.CFGame.Simulation
