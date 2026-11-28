/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar, Claude Opus
-/

import DiagonaLean.CFGame.Basic
import DiagonaLean.Foundations.Computability.ListMachine

@[expose] public section

/-! # Simulating a list machine by a context-free game

A list machine has a finite set of states `Q`, tape symbols `Γ` with a blank `bl`, and a
transition function `δ : Q → Γ → Act Q Γ`. A configuration is a state, the cells left of the head
(nearest first), the head cell, and the cells right of the head (nearest first).

The rules `rules δ qs cs bl`, with the target `Target`, simulate it. The construction adapts the
head encoding of Lemma 4.1 and the objections of Lemma 8.1 of A. Muscholl, T. Schwentick and
L. Segoufin to a deterministic machine whose tape grows at `#`. A configuration is the word
`$ · left · [q,c] · right · #`. A move of the head takes three rounds: the head becomes a marker
`[q',b,→]`, the next cell becomes a head `[p,c']` for a state `p` that Romeo chooses, and the
marker becomes the written symbol `b`.
A wrong state is a win for Juliet. Every non-terminal can be replaced by an objection letter; the
target accepts a word with one objection at the position Juliet had to play, and no word with two
objections. So Romeo objects to a move at any other position, and objects again at every later
move.

## Main statements

* `wins_iff_halts`: Juliet wins the game from the word of a configuration iff the machine halts
  from that configuration.
* `not_reach_of_two_le`: a word with at least two objections is not winning for Juliet, and
  `target_of_reach_of_one`: a winning word with one objection is in the target.

## References

* [A. Muscholl, T. Schwentick, L. Segoufin,
  *Active Context-Free Games*][MuschollSchwentickSegoufin2006], Lemmas 4.1 and 8.1
-/

namespace DiagonaLean.CFGame.Simulation

open DiagonaLean.Foundations.Computability.ListMachine

variable {Q Γ : Type}

/-- The letters of the game. -/
inductive Letter (Q Γ : Type) where
  /-- The left end `$`. -/
  | dollar
  /-- The right end `#`. -/
  | endm
  /-- A tape cell holding `c`. -/
  | tape (c : Γ)
  /-- The head, in state `q`, on a cell holding `c`. -/
  | head (q : Q) (c : Γ)
  /-- A cell holding `b`, which the head leaves to the right, entering `q`. -/
  | rmark (q : Q) (b : Γ)
  /-- A cell holding `b`, which the head leaves to the left, entering `q`. -/
  | lmark (q : Q) (b : Γ)
  /-- The machine has halted. -/
  | halt
  /-- An objection to a move on a tape cell or on `#`. -/
  | objTape
  /-- An objection to a move on the head. -/
  | objHead
  /-- An objection to a move on a right marker. -/
  | objR
  /-- An objection to a move on a left marker. -/
  | objL
  deriving DecidableEq

namespace Letter

/-- The letter is an objection. -/
def IsObj : Letter Q Γ → Prop
  | objTape | objHead | objR | objL => True
  | _ => False

/-- Being an objection is decidable. -/
instance : DecidablePred (IsObj : Letter Q Γ → Prop) := fun x => by
  cases x <;> simp only [IsObj] <;> infer_instance

/-- The letter is a head. -/
def IsHead : Letter Q Γ → Prop
  | head _ _ => True
  | _ => False

/-- The letter is a head or a marker. -/
def IsActive : Letter Q Γ → Prop
  | head _ _ | rmark _ _ | lmark _ _ => True
  | _ => False

end Letter

open Letter

/-- The number of objections in a word. -/
def objCount (w : List (Letter Q Γ)) : ℕ := w.countP fun x => decide x.IsObj

/-- The letter of the head after a transition from a head letter. -/
def actLetter : Act Q Γ → Letter Q Γ
  | .halt => .halt
  | .stay q b => .head q b
  | .right q b => .rmark q b
  | .left q b => .lmark q b

/-- The rules of the game for the machine `δ`, the states `qs`, the tape symbols `cs` and the
blank `bl`: the transition of each head letter, the choice of a state for a new head on a cell or
on `#`, the written symbol for a marker, and an objection for each non-terminal. -/
def rules (δ : Q → Γ → Act Q Γ) (qs : List Q) (cs : List Γ) (bl : Γ) : Rules (Letter Q Γ) :=
  (qs.flatMap fun q => cs.flatMap fun c =>
      [(head q c, actLetter (δ q c), []), (head q c, objHead, []),
       (rmark q c, tape c, []), (rmark q c, objR, []),
       (lmark q c, tape c, []), (lmark q c, objL, [])]) ++
    (cs.flatMap fun c => (qs.map fun p => (tape c, head p c, [])) ++ [(tape c, objTape, [])]) ++
    ((qs.map fun p => (endm, head p bl, [endm])) ++ [(endm, objTape, [])])

variable {δ : Q → Γ → Act Q Γ} {qs : List Q} {cs : List Γ} {bl : Γ}

/-- A rule of the game is one of the following, when `qs` and `cs` list all states and symbols. -/
theorem mem_rules (hqs : ∀ q, q ∈ qs) (hcs : ∀ c, c ∈ cs) {a b : Letter Q Γ}
    {x : List (Letter Q Γ)} :
    (a, b, x) ∈ rules δ qs cs bl ↔
      (∃ q c, a = head q c ∧ x = [] ∧ (b = actLetter (δ q c) ∨ b = objHead)) ∨
      (∃ q c, a = rmark q c ∧ x = [] ∧ (b = tape c ∨ b = objR)) ∨
      (∃ q c, a = lmark q c ∧ x = [] ∧ (b = tape c ∨ b = objL)) ∨
      (∃ c, a = tape c ∧ x = [] ∧ ((∃ p, b = head p c) ∨ b = objTape)) ∨
      (a = endm ∧ ((∃ p, b = head p bl ∧ x = [endm]) ∨ (b = objTape ∧ x = []))) := by
  simp only [rules, List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_map,
    List.not_mem_nil, Prod.mk.injEq, or_false]
  constructor
  · rintro ((⟨q, -, c, -, h⟩ | ⟨c, -, h⟩) | h)
    · rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact Or.inl ⟨q, c, rfl, rfl, Or.inl rfl⟩
      · exact Or.inl ⟨q, c, rfl, rfl, Or.inr rfl⟩
      · exact Or.inr (Or.inl ⟨q, c, rfl, rfl, Or.inl rfl⟩)
      · exact Or.inr (Or.inl ⟨q, c, rfl, rfl, Or.inr rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨q, c, rfl, rfl, Or.inl rfl⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨q, c, rfl, rfl, Or.inr rfl⟩))
    · rcases h with ⟨p, -, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl, rfl, Or.inl ⟨p, rfl⟩⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl, rfl, Or.inr rfl⟩)))
    · rcases h with ⟨p, -, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨p, rfl, rfl⟩⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)))
  · rintro (⟨q, c, rfl, rfl, rfl | rfl⟩ | ⟨q, c, rfl, rfl, rfl | rfl⟩ |
      ⟨q, c, rfl, rfl, rfl | rfl⟩ |
      ⟨c, rfl, rfl, ⟨p, rfl⟩ | rfl⟩ | ⟨rfl, ⟨p, rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · exact Or.inl (Or.inl ⟨q, hqs q, c, hcs c, by simp⟩)
    · exact Or.inl (Or.inl ⟨q, hqs q, c, hcs c, by simp⟩)
    · exact Or.inl (Or.inl ⟨q, hqs q, c, hcs c, by simp⟩)
    · exact Or.inl (Or.inl ⟨q, hqs q, c, hcs c, by simp⟩)
    · exact Or.inl (Or.inl ⟨q, hqs q, c, hcs c, by simp⟩)
    · exact Or.inl (Or.inl ⟨q, hqs q, c, hcs c, by simp⟩)
    · exact Or.inl (Or.inr ⟨c, hcs c, Or.inl ⟨p, hqs p, rfl, rfl, rfl⟩⟩)
    · exact Or.inl (Or.inr ⟨c, hcs c, Or.inr ⟨rfl, rfl, rfl⟩⟩)
    · exact Or.inr (Or.inl ⟨p, hqs p, rfl, rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)

/-- The target of the game, as a predicate. With no objection: the machine has halted, or Romeo
chose a wrong state for a new head. With one objection: the objection is at the position Juliet
had to play, which is the head when there is no marker, the cell right of a right marker or left of
a left marker when there is no head, and the marker when it is next to the head. -/
def Target (w : List (Letter Q Γ)) : Prop :=
  (objCount w = 0 ∧ (halt ∈ w ∨ (∃ u v q b p c, w = u ++ rmark q b :: head p c :: v ∧ p ≠ q) ∨
      (∃ u v q b p c, w = u ++ head p c :: lmark q b :: v ∧ p ≠ q))) ∨
  (objCount w = 1 ∧ ((objHead ∈ w ∧ ∀ x ∈ w, ¬ x.IsActive) ∨
      (∃ u v q b, w = u ++ rmark q b :: objTape :: v ∧ ∀ x ∈ w, ¬ x.IsHead) ∨
      (∃ u v q b, w = u ++ objTape :: lmark q b :: v ∧ ∀ x ∈ w, ¬ x.IsHead) ∨
      (∃ u v p c, w = u ++ objR :: head p c :: v) ∨
      (∃ u v p c, w = u ++ head p c :: objL :: v)))

/-- A word in the target has at most one objection. -/
theorem objCount_le_one_of_target {w : List (Letter Q Γ)} (h : Target w) : objCount w ≤ 1 := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- `u ++ a :: v` has the objections of `u` and of `v`, when `a` is not one. -/
theorem objCount_split_of_not {a : Letter Q Γ} (h : ¬ a.IsObj) (u v : List (Letter Q Γ)) :
    objCount (u ++ a :: v) = objCount u + objCount v := by
  simp [objCount, List.countP_append, h]

/-- `u ++ a :: v` has one objection more than `u` and `v` together, when `a` is one. -/
theorem objCount_split_of_obj {a : Letter Q Γ} (h : a.IsObj) (u v : List (Letter Q Γ)) :
    objCount (u ++ a :: v) = objCount u + 1 + objCount v := by
  simp [objCount, List.countP_append, h]
  omega

/-- A non-terminal of the game is not an objection, and it has a rule to an objection. -/
theorem exists_obj_rule (hqs : ∀ q, q ∈ qs) (hcs : ∀ c, c ∈ cs) {a : Letter Q Γ}
    (ha : IsNonterminal (rules δ qs cs bl) a) :
    ¬ a.IsObj ∧ ∃ o : Letter Q Γ, o.IsObj ∧ (a, o, []) ∈ rules δ qs cs bl := by
  obtain ⟨⟨a', b, x⟩, hr, rfl⟩ := ha
  rw [mem_rules hqs hcs] at hr
  rcases hr with ⟨q, c, rfl, -⟩ | ⟨q, c, rfl, -⟩ | ⟨q, c, rfl, -⟩ | ⟨c, rfl, -⟩ | ⟨rfl, -⟩
  · exact ⟨id, objHead, trivial, (mem_rules hqs hcs).2 (Or.inl ⟨q, c, rfl, rfl, Or.inr rfl⟩)⟩
  · exact ⟨id, objR, trivial,
      (mem_rules hqs hcs).2 (Or.inr (Or.inl ⟨q, c, rfl, rfl, Or.inr rfl⟩))⟩
  · exact ⟨id, objL, trivial,
      (mem_rules hqs hcs).2 (Or.inr (Or.inr (Or.inl ⟨q, c, rfl, rfl, Or.inr rfl⟩)))⟩
  · exact ⟨id, objTape, trivial,
      (mem_rules hqs hcs).2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl, rfl, Or.inr rfl⟩))))⟩
  · exact ⟨id, objTape, trivial,
      (mem_rules hqs hcs).2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩))))⟩

variable {t : RegularExpression (Letter Q Γ)}

/-- **A word with at least two objections is not winning for Juliet**: Romeo answers every move
with an objection, and the target has no word with two objections. -/
theorem not_reach_of_two_le (hqs : ∀ q, q ∈ qs) (hcs : ∀ c, c ∈ cs)
    (ht : ∀ w, w ∈ t.matches' ↔ Target w) {w : List (Letter Q Γ)}
    (h : Reach (rules δ qs cs bl, t) w) : 2 ≤ objCount w → False := by
  induction h with
  | target hw =>
    intro h2
    have := objCount_le_one_of_target ((ht _).1 hw)
    omega
  | move u v a hw ha _ ih =>
    intro h2
    obtain ⟨hna, o, ho, hr⟩ := exists_obj_rule hqs hcs ha
    refine ih o [] hr ?_
    subst hw
    rw [objCount_split_of_not hna] at h2
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [objCount_split_of_obj ho]
    omega

/-- A winning word with one objection is in the target: otherwise Romeo objects to Juliet's
move. -/
theorem target_of_reach_of_one (hqs : ∀ q, q ∈ qs) (hcs : ∀ c, c ∈ cs)
    (ht : ∀ w, w ∈ t.matches' ↔ Target w) {w : List (Letter Q Γ)}
    (h : Reach (rules δ qs cs bl, t) w) (h1 : objCount w = 1) : Target w := by
  cases h with
  | target hw => exact (ht _).1 hw
  | move u v a hw ha hmove =>
    exfalso
    obtain ⟨hna, o, ho, hr⟩ := exists_obj_rule hqs hcs ha
    refine not_reach_of_two_le hqs hcs ht (hmove o [] hr) ?_
    subst hw
    rw [objCount_split_of_not hna] at h1
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [objCount_split_of_obj ho]
    omega

/-! ### The words of configurations -/

/-- The word `$ · left · m · right · #`, with the left cells reversed. -/
def frame (l : List Γ) (m : List (Letter Q Γ)) (r : List Γ) : List (Letter Q Γ) :=
  dollar :: (l.reverse.map tape ++ m ++ (r.map tape ++ [endm]))

/-- The word of a configuration. -/
def cfgWord (k : Cfg Q Γ) : List (Letter Q Γ) := frame k.l [head k.q k.c] k.r

/-- A tape word has no objection. -/
@[simp]
theorem objCount_map_tape (l : List Γ) : objCount (l.map (tape : Γ → Letter Q Γ)) = 0 := by
  simp [objCount, List.countP_eq_zero, IsObj]

/-- The objections of a framed word are those of its middle part. -/
@[simp]
theorem objCount_frame (l : List Γ) (m : List (Letter Q Γ)) (r : List Γ) :
    objCount (frame l m r) = objCount m := by
  have hl := objCount_map_tape (Q := Q) l.reverse
  have hr := objCount_map_tape (Q := Q) r
  simp only [objCount] at hl hr ⊢
  simp only [frame, List.countP_cons, List.countP_append, hl, hr]
  simp [IsObj]

/-- A cell left of the middle part of a framed word can join it. -/
theorem frame_cons_left (b : Γ) (l : List Γ) (m : List (Letter Q Γ)) (r : List Γ) :
    frame (b :: l) m r = frame l (tape b :: m) r := by
  simp [frame]

/-- A cell right of the middle part of a framed word can join it. -/
theorem frame_cons_right (l : List Γ) (m : List (Letter Q Γ)) (b : Γ) (r : List Γ) :
    frame l m (b :: r) = frame l (m ++ [tape b]) r := by
  simp [frame]

/-- A property of all tape letters, of `$`, of `#` and of the letters of `m` holds for all letters
of a framed word. -/
theorem forall_mem_frame {P : Letter Q Γ → Prop} (ht : ∀ c, P (tape c)) (hd : P dollar)
    (he : P endm) {l r : List Γ} {m : List (Letter Q Γ)} (hm : ∀ x ∈ m, P x) :
    ∀ x ∈ frame l m r, P x := by
  intro x hx
  simp only [frame, List.mem_cons, List.mem_append, List.mem_map, List.mem_reverse,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | (⟨c, -, rfl⟩ | hx) | ⟨c, -, rfl⟩ | rfl
  exacts [hd, ht c, hm x hx, ht c, he]

/-- A letter of a framed word is `$`, a tape letter, a letter of the middle part, or `#`. -/
theorem mem_frame {x : Letter Q Γ} {l r : List Γ} {m : List (Letter Q Γ)} :
    x ∈ frame l m r ↔
      x = dollar ∨ (∃ c ∈ l, x = tape c) ∨ x ∈ m ∨ (∃ c ∈ r, x = tape c) ∨ x = endm := by
  simp only [frame, List.mem_cons, List.mem_append, List.mem_map, List.mem_reverse,
    List.not_mem_nil, or_false]
  constructor
  · rintro (h | (⟨c, hc, rfl⟩ | h) | ⟨c, hc, rfl⟩ | h)
    exacts [Or.inl h, Or.inr (Or.inl ⟨c, hc, rfl⟩), Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))), Or.inr (Or.inr (Or.inr (Or.inr h)))]
  · rintro (h | ⟨c, hc, rfl⟩ | h | ⟨c, hc, rfl⟩ | h)
    exacts [Or.inl h, Or.inr (Or.inl (Or.inl ⟨c, hc, rfl⟩)), Or.inr (Or.inl (Or.inr h)),
      Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩)), Or.inr (Or.inr (Or.inr h))]

/-! ### Words in the target -/

section Targets

variable (l r : List Γ)

/-- The halt letter is in the target. -/
theorem target_halt : Target (frame l [(halt : Letter Q Γ)] r) :=
  Or.inl ⟨by rw [objCount_frame]; simp [objCount, IsObj], Or.inl (by simp [frame])⟩

/-- A wrong state right of a right marker is in the target. -/
theorem target_mismatchR {q p : Q} (b c : Γ) (h : p ≠ q) :
    Target (frame l [rmark q b, head p c] r) :=
  Or.inl ⟨by rw [objCount_frame]; simp [objCount, IsObj],
    Or.inr (Or.inl ⟨dollar :: l.reverse.map tape, r.map tape ++ [endm], q, b, p, c,
      by simp [frame], h⟩)⟩

/-- A wrong state left of a left marker is in the target. -/
theorem target_mismatchL {q p : Q} (b c : Γ) (h : p ≠ q) :
    Target (frame l [head p c, lmark q b] r) :=
  Or.inl ⟨by rw [objCount_frame]; simp [objCount, IsObj],
    Or.inr (Or.inr ⟨dollar :: l.reverse.map tape, r.map tape ++ [endm], q, b, p, c,
      by simp [frame], h⟩)⟩

/-- An objection on the head, with no marker, is in the target. -/
theorem target_objHead : Target (frame l [(objHead : Letter Q Γ)] r) :=
  Or.inr ⟨by rw [objCount_frame]; simp [objCount, IsObj], Or.inl ⟨by simp [frame],
    forall_mem_frame (by simp [IsActive]) (by simp [IsActive]) (by simp [IsActive])
      (by simp [IsActive])⟩⟩

/-- An objection on the cell right of a right marker, with no head, is in the target. -/
theorem target_objR_cell (q : Q) (b : Γ) :
    Target (frame l [rmark q b, (objTape : Letter Q Γ)] r) :=
  Or.inr ⟨by rw [objCount_frame]; simp [objCount, IsObj], Or.inr (Or.inl
    ⟨dollar :: l.reverse.map tape, r.map tape ++ [endm], q, b, by simp [frame],
      forall_mem_frame (by simp [IsHead]) (by simp [IsHead]) (by simp [IsHead])
        (by simp [IsHead])⟩)⟩

/-- An objection on `#` right of a right marker, with no head, is in the target. -/
theorem target_objR_end (q : Q) (b : Γ) :
    Target (dollar :: (l.reverse.map tape ++ [rmark q b]) ++ [(objTape : Letter Q Γ)]) :=
  Or.inr ⟨by simp [objCount, List.countP_append, IsObj], Or.inr (Or.inl
    ⟨dollar :: l.reverse.map tape, [], q, b, by simp, by
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_reverse,
        List.not_mem_nil, or_false]
      rintro x (rfl | (⟨c, -, rfl⟩ | rfl) | rfl) <;> simp [IsHead]⟩)⟩

/-- An objection on the cell left of a left marker, with no head, is in the target. -/
theorem target_objL_cell (q : Q) (b : Γ) :
    Target (frame l [(objTape : Letter Q Γ), lmark q b] r) :=
  Or.inr ⟨by rw [objCount_frame]; simp [objCount, IsObj], Or.inr (Or.inr (Or.inl
    ⟨dollar :: l.reverse.map tape, r.map tape ++ [endm], q, b, by simp [frame],
      forall_mem_frame (by simp [IsHead]) (by simp [IsHead]) (by simp [IsHead])
        (by simp [IsHead])⟩))⟩

/-- An objection on a right marker next to the head is in the target. -/
theorem target_objR_mark (p : Q) (c : Γ) :
    Target (frame l [(objR : Letter Q Γ), head p c] r) :=
  Or.inr ⟨by rw [objCount_frame]; simp [objCount, IsObj], Or.inr (Or.inr (Or.inr (Or.inl
    ⟨dollar :: l.reverse.map tape, r.map tape ++ [endm], p, c, by simp [frame]⟩)))⟩

/-- An objection on a left marker next to the head is in the target. -/
theorem target_objL_mark (p : Q) (c : Γ) :
    Target (frame l [head p c, (objL : Letter Q Γ)] r) :=
  Or.inr ⟨by rw [objCount_frame]; simp [objCount, IsObj], Or.inr (Or.inr (Or.inr (Or.inr
    ⟨dollar :: l.reverse.map tape, r.map tape ++ [endm], p, c, by simp [frame]⟩)))⟩

end Targets

/-! ### Rules, letter by letter -/

section Rules

variable (hqs : ∀ q, q ∈ qs) (hcs : ∀ c, c ∈ cs)
include hqs hcs

/-- A head letter is rewritten by its transition or by an objection. -/
theorem rules_head {q : Q} {c : Γ} {b : Letter Q Γ} {x : List (Letter Q Γ)} :
    (head q c, b, x) ∈ rules δ qs cs bl ↔ x = [] ∧ (b = actLetter (δ q c) ∨ b = objHead) := by
  rw [mem_rules hqs hcs]
  simp only [head.injEq, reduceCtorEq, false_and, exists_false, or_false]
  constructor
  · rintro ⟨q', c', ⟨rfl, rfl⟩, h⟩
    exact h
  · exact fun h => ⟨q, c, ⟨rfl, rfl⟩, h⟩

/-- A right marker is rewritten by the written symbol or by an objection. -/
theorem rules_rmark {q : Q} {c : Γ} {b : Letter Q Γ} {x : List (Letter Q Γ)} :
    (rmark q c, b, x) ∈ rules δ qs cs bl ↔ x = [] ∧ (b = tape c ∨ b = objR) := by
  rw [mem_rules hqs hcs]
  simp only [rmark.injEq, reduceCtorEq, false_and, exists_false, or_false, false_or]
  constructor
  · rintro ⟨q', c', ⟨rfl, rfl⟩, h⟩
    exact h
  · exact fun h => ⟨q, c, ⟨rfl, rfl⟩, h⟩

/-- A left marker is rewritten by the written symbol or by an objection. -/
theorem rules_lmark {q : Q} {c : Γ} {b : Letter Q Γ} {x : List (Letter Q Γ)} :
    (lmark q c, b, x) ∈ rules δ qs cs bl ↔ x = [] ∧ (b = tape c ∨ b = objL) := by
  rw [mem_rules hqs hcs]
  simp only [lmark.injEq, reduceCtorEq, false_and, exists_false, or_false, false_or]
  constructor
  · rintro ⟨q', c', ⟨rfl, rfl⟩, h⟩
    exact h
  · exact fun h => ⟨q, c, ⟨rfl, rfl⟩, h⟩

/-- A tape cell is rewritten by a head in any state or by an objection. -/
theorem rules_tape {c : Γ} {b : Letter Q Γ} {x : List (Letter Q Γ)} :
    (tape c, b, x) ∈ rules δ qs cs bl ↔ x = [] ∧ ((∃ p, b = head p c) ∨ b = objTape) := by
  rw [mem_rules hqs hcs]
  simp only [tape.injEq, reduceCtorEq, false_and, exists_false, or_false, false_or]
  constructor
  · rintro ⟨c', rfl, h⟩
    exact h
  · exact fun h => ⟨c, rfl, h⟩

/-- `#` is rewritten by a head on a blank cell in any state, followed by `#`, or by an objection. -/
theorem rules_endm {b : Letter Q Γ} {x : List (Letter Q Γ)} :
    (endm, b, x) ∈ rules δ qs cs bl ↔
      (∃ p, b = head p bl ∧ x = [endm]) ∨ (b = objTape ∧ x = []) := by
  rw [mem_rules hqs hcs]
  simp [reduceCtorEq]

/-- A head letter is a non-terminal. -/
theorem isNonterminal_head (q : Q) (c : Γ) : IsNonterminal (rules δ qs cs bl) (head q c) :=
  ⟨_, (rules_head hqs hcs).2 ⟨rfl, Or.inr rfl⟩, rfl⟩

/-- A right marker is a non-terminal. -/
theorem isNonterminal_rmark (q : Q) (c : Γ) : IsNonterminal (rules δ qs cs bl) (rmark q c) :=
  ⟨_, (rules_rmark hqs hcs).2 ⟨rfl, Or.inr rfl⟩, rfl⟩

/-- A left marker is a non-terminal. -/
theorem isNonterminal_lmark (q : Q) (c : Γ) : IsNonterminal (rules δ qs cs bl) (lmark q c) :=
  ⟨_, (rules_lmark hqs hcs).2 ⟨rfl, Or.inr rfl⟩, rfl⟩

/-- A tape cell is a non-terminal. -/
theorem isNonterminal_tape (c : Γ) : IsNonterminal (rules δ qs cs bl) (tape c) :=
  ⟨_, (rules_tape hqs hcs).2 ⟨rfl, Or.inr rfl⟩, rfl⟩

/-- `#` is a non-terminal. -/
theorem isNonterminal_endm : IsNonterminal (rules δ qs cs bl) (endm : Letter Q Γ) :=
  ⟨_, (rules_endm hqs hcs).2 (Or.inr ⟨rfl, rfl⟩), rfl⟩

end Rules

/-! ### Moves in a framed word -/

/-- Juliet can play on a letter in the middle part of a framed word. -/
theorem reach_frame_move {R : Rules (Letter Q Γ)} {l r : List Γ} {m₁ m₂ : List (Letter Q Γ)}
    {a : Letter Q Γ} (ha : IsNonterminal R a)
    (h : ∀ b x, (a, b, x) ∈ R → Reach (R, t) (frame l (m₁ ++ b :: x ++ m₂) r)) :
    Reach (R, t) (frame l (m₁ ++ a :: m₂) r) :=
  Reach.move (dollar :: (l.reverse.map tape ++ m₁)) (m₂ ++ (r.map tape ++ [endm])) a
    (by simp [frame]) ha (fun b x hr => by simpa [frame] using h b x hr)

/-- Juliet can play on `#` in a framed word. -/
theorem reach_frame_end {R : Rules (Letter Q Γ)} {l : List Γ} {m : List (Letter Q Γ)}
    (ha : IsNonterminal R endm)
    (h : ∀ b x, (endm, b, x) ∈ R → Reach (R, t) (dollar :: (l.reverse.map tape ++ m) ++ b :: x)) :
    Reach (R, t) (frame l m []) :=
  Reach.move (dollar :: (l.reverse.map tape ++ m)) [] endm (by simp [frame]) ha
    (fun b x hr => by simpa using h b x hr)

/-! ### If the machine halts, Juliet wins -/

section Forward

variable (hqs : ∀ q, q ∈ qs) (hcs : ∀ c, c ∈ cs) (ht : ∀ w, w ∈ t.matches' ↔ Target w)
include hqs hcs ht

/-- Juliet wins from a right marker followed by a head in the state of the marker, when she wins
after the marker becomes the written symbol. -/
theorem reach_rmark_head {l r : List Γ} {q : Q} {b c : Γ}
    (h : Reach (rules δ qs cs bl, t) (cfgWord ⟨q, b :: l, c, r⟩)) :
    Reach (rules δ qs cs bl, t) (frame l [rmark q b, head q c] r) := by
  refine reach_frame_move (m₁ := []) (isNonterminal_rmark hqs hcs q b) fun b' x hr => ?_
  obtain ⟨rfl, rfl | rfl⟩ := (rules_rmark hqs hcs).1 hr
  · simpa [cfgWord, frame_cons_left] using h
  · exact .target ((ht _).2 (target_objR_mark l r q c))

/-- Juliet wins from a right marker, when she wins from the configuration after the move. -/
theorem reach_rmark {l r : List Γ} {q : Q} {b : Γ}
    (h : Reach (rules δ qs cs bl, t) (cfgWord ⟨q, b :: l, r.headD bl, r.tail⟩)) :
    Reach (rules δ qs cs bl, t) (frame l [rmark q b] r) := by
  cases r with
  | nil =>
    refine reach_frame_end (isNonterminal_endm hqs hcs) fun b' x hr => ?_
    rcases (rules_endm hqs hcs).1 hr with ⟨p, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hw : dollar :: (l.reverse.map tape ++ [rmark q b]) ++ [head p bl, endm] =
          frame l [rmark q b, head p bl] [] := by simp [frame]
      rw [hw]
      by_cases hp : p = q
      · subst hp
        exact reach_rmark_head hqs hcs ht h
      · exact .target ((ht _).2 (target_mismatchR l [] b bl hp))
    · exact .target ((ht _).2 (target_objR_end l q b))
  | cons d r =>
    rw [frame_cons_right]
    refine reach_frame_move (m₁ := [rmark q b]) (m₂ := []) (isNonterminal_tape hqs hcs d)
      fun b' x hr => ?_
    obtain ⟨rfl, ⟨p, rfl⟩ | rfl⟩ := (rules_tape hqs hcs).1 hr
    · by_cases hp : p = q
      · subst hp
        simpa using reach_rmark_head hqs hcs ht h
      · exact .target ((ht _).2 (by simpa using target_mismatchR l r b d hp))
    · exact .target ((ht _).2 (by simpa using target_objR_cell l r q b))

/-- Juliet wins from a head next to a left marker in its state, when she wins after the marker
becomes the written symbol. -/
theorem reach_head_lmark {l r : List Γ} {q : Q} {b d : Γ}
    (h : Reach (rules δ qs cs bl, t) (cfgWord ⟨q, l, d, b :: r⟩)) :
    Reach (rules δ qs cs bl, t) (frame l [head q d, lmark q b] r) := by
  refine reach_frame_move (m₁ := [head q d]) (m₂ := []) (isNonterminal_lmark hqs hcs q b)
    fun b' x hr => ?_
  obtain ⟨rfl, rfl | rfl⟩ := (rules_lmark hqs hcs).1 hr
  · simpa [cfgWord, frame_cons_right] using h
  · exact .target ((ht _).2 (by simpa using target_objL_mark l r q d))

/-- Juliet wins from a left marker, when she wins from the configuration after the move. -/
theorem reach_lmark {l r : List Γ} {q : Q} {b d : Γ}
    (h : Reach (rules δ qs cs bl, t) (cfgWord ⟨q, l, d, b :: r⟩)) :
    Reach (rules δ qs cs bl, t) (frame (d :: l) [lmark q b] r) := by
  rw [frame_cons_left]
  refine reach_frame_move (m₁ := []) (m₂ := [lmark q b]) (isNonterminal_tape hqs hcs d)
    fun b' x hr => ?_
  obtain ⟨rfl, ⟨p, rfl⟩ | rfl⟩ := (rules_tape hqs hcs).1 hr
  · by_cases hp : p = q
    · subst hp
      simpa using reach_head_lmark hqs hcs ht h
    · exact .target ((ht _).2 (by simpa using target_mismatchL l r b d hp))
  · exact .target ((ht _).2 (by simpa using target_objL_cell l r q b))

/-- Juliet wins from a configuration whose transition halts. -/
theorem reach_of_halt {k : Cfg Q Γ} (hk : δ k.q k.c = .halt) :
    Reach (rules δ qs cs bl, t) (cfgWord k) := by
  refine reach_frame_move (m₁ := []) (m₂ := []) (isNonterminal_head hqs hcs k.q k.c)
    fun b x hr => ?_
  obtain ⟨rfl, rfl | rfl⟩ := (rules_head hqs hcs).1 hr
  · rw [hk]
    exact .target ((ht _).2 (target_halt k.l k.r))
  · exact .target ((ht _).2 (target_objHead k.l k.r))

/-- One step of the machine is three rounds of the game: Juliet wins from a configuration when she
wins from the next one. -/
theorem reach_of_next {k k' : Cfg Q Γ} (hk : next δ bl k = some k')
    (h : Reach (rules δ qs cs bl, t) (cfgWord k')) :
    Reach (rules δ qs cs bl, t) (cfgWord k) := by
  obtain ⟨q, l, c, r⟩ := k
  refine reach_frame_move (m₁ := []) (m₂ := []) (isNonterminal_head hqs hcs q c)
    fun b x hr => ?_
  obtain ⟨rfl, rfl | rfl⟩ := (rules_head hqs hcs).1 hr
  · simp only [next] at hk
    revert hk
    cases hδ : δ q c with
    | halt => simp
    | stay q' b' =>
      intro hk
      cases hk
      simpa [actLetter, cfgWord] using h
    | right q' b' =>
      intro hk
      cases hk
      simpa [actLetter] using reach_rmark hqs hcs ht h
    | left q' b' =>
      cases l with
      | nil => simp
      | cons d l =>
        intro hk
        cases hk
        simpa [actLetter] using reach_lmark hqs hcs ht h
  · exact .target ((ht _).2 (target_objHead l r))

/-- **If the machine halts, Juliet wins from the word of its configuration**, or that word is
already in the target. -/
theorem reach_of_halts {k : Cfg Q Γ} (h : Halts δ bl k) :
    Reach (rules δ qs cs bl, t) (cfgWord k) := by
  obtain ⟨k', hrun, hk'⟩ := h
  induction hrun using Relation.ReflTransGen.head_induction_on with
  | refl => exact reach_of_halt hqs hcs ht hk'
  | head hstep _ ih => exact reach_of_next hqs hcs ht hstep ih

end Forward

/-! ### Positions in a word -/

section Positions

variable {α : Type}

/-- If exactly one letter of a word satisfies `P`, two splits of the word at letters satisfying `P`
are equal. -/
theorem split_eq_of_countP_eq_one {P : α → Bool} {u v u' v' : List α} {x y : α}
    (hx : P x) (hy : P y) (h : u ++ x :: v = u' ++ y :: v')
    (hc : (u ++ x :: v).countP P = 1) : u = u' ∧ x = y ∧ v = v' := by
  induction u generalizing u' with
  | nil =>
    cases u' with
    | nil => simpa using h
    | cons z u' =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      simp [List.countP_append, hx, hy] at hc
  | cons z u ih =>
    cases u' with
    | nil =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      simp [List.countP_append, hx, hy] at hc
    | cons z' u' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      by_cases hz : P z
      · simp [List.countP_append, hx, hz] at hc
      · obtain ⟨rfl, rfl, rfl⟩ := ih h (by simpa [List.countP_cons, hz] using hc)
        exact ⟨rfl, rfl, rfl⟩

/-- A framed word has as many letters satisfying `P` as its middle part, when `P` fails on tape
letters, `$` and `#`. -/
theorem countP_frame {P : Letter Q Γ → Bool} (ht : ∀ c, P (tape c) = false)
    (hd : P dollar = false) (he : P endm = false) (l r : List Γ) (m : List (Letter Q Γ)) :
    (frame l m r).countP P = m.countP P := by
  have h0 : ∀ k : List Γ, List.countP (P ∘ tape) k = 0 := fun k =>
    List.countP_eq_zero.2 fun c _ => by simp [ht]
  simp [frame, List.countP_append, hd, he, h0]

end Positions

/-! ### Phases of a faithful play -/

/-- The words through which a faithful play passes while the machine makes its step from `k`: the
word of `k`, then the markers and the new head of a move, or the halt letter. -/
inductive Phase (δ : Q → Γ → Act Q Γ) (bl : Γ) (k : Cfg Q Γ) : List (Letter Q Γ) → Prop
  /-- The word of the configuration. -/
  | cfg : Phase δ bl k (cfgWord k)
  /-- The machine has halted. -/
  | halted (h : δ k.q k.c = .halt) : Phase δ bl k (frame k.l [halt] k.r)
  /-- The head has become a right marker. -/
  | right₁ {q : Q} {b : Γ} (h : δ k.q k.c = .right q b) : Phase δ bl k (frame k.l [rmark q b] k.r)
  /-- The cell right of the marker has become the new head. -/
  | right₂ {q : Q} {b : Γ} (h : δ k.q k.c = .right q b) :
      Phase δ bl k (frame k.l [rmark q b, head q (k.r.headD bl)] k.r.tail)
  /-- The head has become a left marker. -/
  | left₁ {q : Q} {b : Γ} (h : δ k.q k.c = .left q b) : Phase δ bl k (frame k.l [lmark q b] k.r)
  /-- The cell left of the marker has become the new head. -/
  | left₂ {q : Q} {b d : Γ} {l : List Γ} (h : δ k.q k.c = .left q b) (hl : k.l = d :: l) :
      Phase δ bl k (frame l [head q d, lmark q b] k.r)

/-- The objection that replaces a letter. -/
def objOf : Letter Q Γ → Letter Q Γ
  | head _ _ => objHead
  | rmark _ _ => objR
  | lmark _ _ => objL
  | _ => objTape

/-- A letter is a right marker. -/
def isRmark : Letter Q Γ → Bool
  | rmark _ _ => true
  | _ => false

/-- A letter is a left marker. -/
def isLmark : Letter Q Γ → Bool
  | lmark _ _ => true
  | _ => false

/-- A letter is a head. -/
def isHeadB : Letter Q Γ → Bool
  | head _ _ => true
  | _ => false

/-- A letter is an objection. -/
def isObjB (x : Letter Q Γ) : Bool := decide x.IsObj

/-- The objection of a non-terminal is a rule for it. -/
theorem objOf_mem_rules (hqs : ∀ q, q ∈ qs) (hcs : ∀ c, c ∈ cs) {a : Letter Q Γ}
    (ha : IsNonterminal (rules δ qs cs bl) a) : (a, objOf a, []) ∈ rules δ qs cs bl := by
  obtain ⟨⟨a', b, x⟩, hr, rfl⟩ := ha
  rw [mem_rules hqs hcs] at hr
  rcases hr with ⟨q, c, rfl, -⟩ | ⟨q, c, rfl, -⟩ | ⟨q, c, rfl, -⟩ | ⟨c, rfl, -⟩ | ⟨rfl, -⟩
  · exact (rules_head hqs hcs).2 ⟨rfl, Or.inr rfl⟩
  · exact (rules_rmark hqs hcs).2 ⟨rfl, Or.inr rfl⟩
  · exact (rules_lmark hqs hcs).2 ⟨rfl, Or.inr rfl⟩
  · exact (rules_tape hqs hcs).2 ⟨rfl, Or.inr rfl⟩
  · exact (rules_endm hqs hcs).2 (Or.inr ⟨rfl, rfl⟩)

/-- A non-terminal is a head, a marker, a tape cell or `#`. -/
theorem nonterminal_cases (hqs : ∀ q, q ∈ qs) (hcs : ∀ c, c ∈ cs) {a : Letter Q Γ}
    (ha : IsNonterminal (rules δ qs cs bl) a) :
    (∃ q c, a = head q c) ∨ (∃ q c, a = rmark q c) ∨ (∃ q c, a = lmark q c) ∨
      (∃ c, a = tape c) ∨ a = endm := by
  obtain ⟨⟨a', b, x⟩, hr, rfl⟩ := ha
  rw [mem_rules hqs hcs] at hr
  rcases hr with ⟨q, c, rfl, -⟩ | ⟨q, c, rfl, -⟩ | ⟨q, c, rfl, -⟩ | ⟨c, rfl, -⟩ | ⟨rfl, -⟩
  exacts [Or.inl ⟨q, c, rfl⟩, Or.inr (Or.inl ⟨q, c, rfl⟩), Or.inr (Or.inr (Or.inl ⟨q, c, rfl⟩)),
    Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))), Or.inr (Or.inr (Or.inr (Or.inr rfl)))]

/-- A phase word has no objection. -/
theorem objCount_phase {k : Cfg Q Γ} {w : List (Letter Q Γ)} (h : Phase δ bl k w) :
    objCount w = 0 := by
  cases h <;> simp only [cfgWord, objCount_frame] <;> simp [objCount, IsObj]

/-- A split of a framed word at a letter that satisfies `P` is the split at the middle part, when
exactly one letter of the middle
part does and `P` fails on tape letters, `$` and `#`. -/
theorem frame_split {P : Letter Q Γ → Bool} (ht : ∀ c, P (tape c) = false)
    (hd : P dollar = false) (he : P endm = false) {l r : List Γ} {m₁ m₂ u v : List (Letter Q Γ)}
    {x y : Letter Q Γ} (hx : P x) (hy : P y) (hm : (m₁ ++ y :: m₂).countP P = 1)
    (h : frame l (m₁ ++ y :: m₂) r = u ++ x :: v) :
    u = dollar :: (l.reverse.map tape ++ m₁) ∧ x = y ∧ v = m₂ ++ (r.map tape ++ [endm]) := by
  have hw : frame l (m₁ ++ y :: m₂) r =
      dollar :: (l.reverse.map tape ++ m₁) ++ y :: (m₂ ++ (r.map tape ++ [endm])) := by
    simp [frame]
  rw [hw] at h
  have hc : (dollar :: (l.reverse.map tape ++ m₁) ++ y :: (m₂ ++ (r.map tape ++ [endm]))).countP P
      = 1 := by rw [← hw, countP_frame ht hd he]; exact hm
  obtain ⟨h1, h2, h3⟩ := split_eq_of_countP_eq_one hy hx h hc
  exact ⟨h1.symm, h2.symm, h3.symm⟩

/-- No letter before the left marker of a framed word is a head. -/
theorem not_head_before_lmark {l r : List Γ} {q q' p : Q} {b b' c : Γ} {u v : List (Letter Q Γ)}
    (h : frame l [lmark q' b'] r = u ++ head p c :: lmark q b :: v) : False := by
  have h' : frame l ([] ++ lmark q' b' :: []) r = (u ++ [head p c]) ++ lmark q b :: v := by
    simpa using h
  obtain ⟨hu, -, -⟩ := frame_split (P := isLmark) (by simp [isLmark]) rfl rfl rfl rfl
    (by simp [List.countP_cons, isLmark]) h'
  have hmem : head p c ∈ dollar :: (l.reverse.map tape ++ []) := by
    rw [← hu]; simp
  simp at hmem

/-- The letter after the right marker of a framed word is not a head. -/
theorem not_head_after_rmark {l r : List Γ} {q q' p : Q} {b b' c : Γ} {u v : List (Letter Q Γ)}
    (h : frame l [rmark q' b'] r = u ++ rmark q b :: head p c :: v) : False := by
  have h' : frame l ([] ++ rmark q' b' :: []) r = u ++ rmark q b :: head p c :: v := by
    simpa using h
  obtain ⟨-, -, hv⟩ := frame_split (P := isRmark) (by simp [isRmark]) rfl rfl rfl rfl
    (by simp [List.countP_cons, isRmark]) h'
  cases r <;> simp at hv

/-- **A phase word is in the target only once the machine has halted.** -/
theorem halt_of_target_phase {k : Cfg Q Γ} {w : List (Letter Q Γ)} (hp : Phase δ bl k w)
    (ht : Target w) : δ k.q k.c = .halt := by
  have h0 := objCount_phase hp
  rcases ht with ⟨-, hh | ⟨u, v, q, b, p, c, hw, hpq⟩ | ⟨u, v, q, b, p, c, hw, hpq⟩⟩ | ⟨h1, -⟩
  · cases hp with
    | halted h => exact h
    | _ => simp [cfgWord, mem_frame] at hh
  · cases hp with
    | halted h => exact h
    | right₁ h => exact (not_head_after_rmark hw).elim
    | @right₂ q' b' h =>
      have h' : frame k.l ([] ++ rmark q' b' :: [head q' (k.r.headD bl)]) k.r.tail =
          u ++ rmark q b :: head p c :: v := by simpa using hw
      obtain ⟨-, hx, hv⟩ := frame_split (P := isRmark) (by simp [isRmark]) rfl rfl rfl rfl
        (by simp [List.countP_cons, isRmark]) h'
      simp only [rmark.injEq] at hx
      simp only [List.cons_append, List.nil_append, List.cons.injEq, head.injEq] at hv
      exact (hpq (hv.1.1.trans hx.1.symm)).elim
    | _ =>
      have hm : rmark q b ∈ u ++ rmark q b :: head p c :: v := by simp
      rw [← hw] at hm
      simp [cfgWord, mem_frame] at hm
  · cases hp with
    | halted h => exact h
    | left₁ h => exact (not_head_before_lmark hw).elim
    | @left₂ q' b' d l h hl =>
      have h' : frame l ([head q' d] ++ lmark q' b' :: []) k.r =
          (u ++ [head p c]) ++ lmark q b :: v := by simpa using hw
      obtain ⟨hu, hx, -⟩ := frame_split (P := isLmark) (by simp [isLmark]) rfl rfl rfl rfl
        (by simp [List.countP_cons, isLmark]) h'
      have hu' : u ++ [head p c] = (dollar :: l.reverse.map tape) ++ [head q' d] := by
        simpa using hu
      have := (List.append_singleton_inj.mp hu').2
      simp only [head.injEq, lmark.injEq] at this hx
      exact (hpq (this.1.trans hx.1.symm)).elim
    | _ =>
      have hm : lmark q b ∈ u ++ head p c :: lmark q b :: v := by simp
      rw [← hw] at hm
      simp [cfgWord, mem_frame] at hm
  · omega

/-! ### If Juliet wins, the machine halts -/

section Backward

/-- Two splits of a word with one objection, at objections, are equal. -/
theorem split_obj {u v u' v' : List (Letter Q Γ)} {o o' : Letter Q Γ} (ho : o.IsObj)
    (ho' : o'.IsObj) (h : u ++ o :: v = u' ++ o' :: v') (hu : objCount u = 0)
    (hv : objCount v = 0) : u = u' ∧ o = o' ∧ v = v' := by
  refine split_eq_of_countP_eq_one (P := isObjB) (by simpa [isObjB] using ho)
    (by simpa [isObjB] using ho') h ?_
  show objCount (u ++ o :: v) = 1
  rw [objCount_split_of_obj ho]
  omega

/-- The parts of a word with no objection have no objection. -/
theorem objCount_parts {u v : List (Letter Q Γ)} {a : Letter Q Γ}
    (h : objCount (u ++ a :: v) = 0) : ¬ a.IsObj ∧ objCount u = 0 ∧ objCount v = 0 := by
  by_cases ha : a.IsObj
  · rw [objCount_split_of_obj ha] at h
    omega
  · rw [objCount_split_of_not ha] at h
    exact ⟨ha, by omega, by omega⟩

/-- An objection of a letter is an objection. -/
theorem isObj_objOf (a : Letter Q Γ) : (objOf a).IsObj := by
  cases a <;> trivial

/-- A letter of `u ++ a :: v` other than `a` is a letter of `u` or of `v`. -/
theorem mem_parts {u v : List (Letter Q Γ)} {a x : Letter Q Γ} (hx : x ∈ u ++ a :: v)
    (hne : x ≠ a) : x ∈ u ∨ x ∈ v := by
  simp only [List.mem_append, List.mem_cons] at hx
  tauto

/-- The faithful answer to Juliet's move, as found by the objection lemmas: a rule for the letter
she played that keeps the play in a phase of this step or of the next one. -/
def FaithfulAnswer (δ : Q → Γ → Act Q Γ) (qs : List Q) (cs : List Γ) (bl : Γ) (k : Cfg Q Γ)
    (u v : List (Letter Q Γ)) (a : Letter Q Γ) : Prop :=
  ∃ b x, (a, b, x) ∈ rules δ qs cs bl ∧
    (Phase δ bl k (u ++ b :: x ++ v) ∨
      ∃ k', next δ bl k = some k' ∧ Phase δ bl k' (u ++ b :: x ++ v))

/-- After the head transition, the word is a phase of the step. -/
theorem phase_actLetter {k : Cfg Q Γ} :
    Phase δ bl k (frame k.l [actLetter (δ k.q k.c)] k.r) ∨
      ∃ k', next δ bl k = some k' ∧ Phase δ bl k' (frame k.l [actLetter (δ k.q k.c)] k.r) := by
  cases hδ : δ k.q k.c with
  | halt => exact Or.inl (by simpa [actLetter, hδ] using Phase.halted (bl := bl) hδ)
  | stay q b =>
    refine Or.inr ⟨⟨q, k.l, b, k.r⟩, by simp [next, hδ], ?_⟩
    simpa [actLetter, cfgWord] using Phase.cfg (δ := δ) (bl := bl) (k := ⟨q, k.l, b, k.r⟩)
  | right q b => exact Or.inl (by simpa [actLetter] using Phase.right₁ (bl := bl) hδ)
  | left q b => exact Or.inl (by simpa [actLetter] using Phase.left₁ (bl := bl) hδ)

variable (hqs : ∀ q, q ∈ qs) (hcs : ∀ c, c ∈ cs)
include hqs hcs

omit hqs hcs in
/-- A word with an objection in it has a positive number of objections. -/
theorem objCount_pos_of_mem {u : List (Letter Q Γ)} {x : Letter Q Γ} (hx : x.IsObj)
    (hm : x ∈ u) : 0 < objCount u :=
  List.countP_pos_iff.2 ⟨x, hm, by simpa using hx⟩

/-- **If an objection on the head is in the target, Juliet played the head of a configuration
word**,
and Romeo answers with the transition. -/
theorem faithful_of_objHead {k : Cfg Q Γ} {w u v : List (Letter Q Γ)} {a : Letter Q Γ}
    (hp : Phase δ bl k w) (hw : w = u ++ a :: v) (ha : IsNonterminal (rules δ qs cs bl) a)
    (hm : objHead ∈ u ++ objOf a :: v) (hact : ∀ x ∈ u ++ objOf a :: v, ¬ x.IsActive) :
    FaithfulAnswer δ qs cs bl k u v a := by
  obtain ⟨-, hu, hv⟩ := objCount_parts (hw ▸ objCount_phase hp)
  have hoa : objOf a = objHead := by
    simp only [List.mem_append, List.mem_cons] at hm
    rcases hm with hm | hm | hm
    · exact absurd (objCount_pos_of_mem (x := (objHead : Letter Q Γ)) trivial hm) (by omega)
    · exact hm.symm
    · exact absurd (objCount_pos_of_mem (x := (objHead : Letter Q Γ)) trivial hm) (by omega)
  have hnact : ∀ x, x ∈ u ∨ x ∈ v → ¬ x.IsActive := fun x hx => hact x (by
    rcases hx with hx | hx <;> simp [hx])
  obtain ⟨q, c, rfl⟩ : ∃ q c, a = head q c := by
    rcases nonterminal_cases hqs hcs ha with h | ⟨q, c, rfl⟩ | ⟨q, c, rfl⟩ | ⟨c, rfl⟩ | rfl
    · exact h
    all_goals simp [objOf] at hoa
  have hhead : head q c ∈ w := by rw [hw]; simp
  cases hp with
  | cfg =>
    have h' : frame k.l ([] ++ head k.q k.c :: []) k.r = u ++ head q c :: v := by
      simpa [cfgWord] using hw
    obtain ⟨rfl, hx, rfl⟩ := frame_split (P := isHeadB) (by simp [isHeadB]) rfl rfl rfl rfl
      (by simp [List.countP_cons, isHeadB]) h'
    simp only [head.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨actLetter (δ k.q k.c), [], (rules_head hqs hcs).2 ⟨rfl, Or.inl rfl⟩, ?_⟩
    simpa [frame] using phase_actLetter (bl := bl) (k := k)
  | halted => simp [mem_frame] at hhead
  | right₁ => simp [mem_frame] at hhead
  | @right₂ q' b' h =>
    have hm1 : rmark q' b' ∈ u ++ head q c :: v := by rw [← hw]; simp [mem_frame]
    exact absurd trivial (hnact _ (mem_parts hm1 (by simp)))
  | left₁ => simp [mem_frame] at hhead
  | @left₂ q' b' d l h hl =>
    have hm1 : lmark q' b' ∈ u ++ head q c :: v := by rw [← hw]; simp [mem_frame]
    exact absurd trivial (hnact _ (mem_parts hm1 (by simp)))

/-- A letter whose objection is the cell objection is a tape cell or `#`. -/
theorem tape_or_endm_of_objOf {a : Letter Q Γ} (ha : IsNonterminal (rules δ qs cs bl) a)
    (hoa : objOf a = objTape) : (∃ c, a = tape c) ∨ a = endm := by
  rcases nonterminal_cases hqs hcs ha with ⟨q, c, rfl⟩ | ⟨q, c, rfl⟩ | ⟨q, c, rfl⟩ | h | h
  · simp [objOf] at hoa
  · simp [objOf] at hoa
  · simp [objOf] at hoa
  · exact Or.inl h
  · exact Or.inr h

/-- **If an objection right of a right marker is in the target, Juliet played the cell right of the
marker, and Romeo answers with a head in the state of the marker. -/
theorem faithful_of_objR_cell {k : Cfg Q Γ} {w u v : List (Letter Q Γ)} {a : Letter Q Γ}
    (hp : Phase δ bl k w) (hw : w = u ++ a :: v) (ha : IsNonterminal (rules δ qs cs bl) a)
    {u' v' : List (Letter Q Γ)} {q : Q} {b : Γ}
    (h' : u ++ objOf a :: v = u' ++ rmark q b :: objTape :: v')
    (hnh : ∀ x ∈ u ++ objOf a :: v, ¬ x.IsHead) : FaithfulAnswer δ qs cs bl k u v a := by
  obtain ⟨-, hu, hv⟩ := objCount_parts (hw ▸ objCount_phase hp)
  have h'' : u ++ objOf a :: v = (u' ++ [rmark q b]) ++ objTape :: v' := by simpa using h'
  obtain ⟨rfl, hoa, rfl⟩ := split_obj (o' := (objTape : Letter Q Γ)) (isObj_objOf a) trivial h''
    hu hv
  have hnh' : ∀ x, x ∈ u' ++ [rmark q b] ∨ x ∈ v → ¬ x.IsHead := fun x hx => hnh x (by
    simp only [List.mem_append, List.mem_singleton] at hx
    simp only [List.mem_append, List.mem_cons]
    tauto)
  have hta := tape_or_endm_of_objOf hqs hcs ha hoa
  have hw' : w = u' ++ rmark q b :: a :: v := by simpa using hw
  have hmr : rmark q b ∈ w := by rw [hw']; simp
  obtain ⟨kq, kl, kc, kr⟩ := k
  cases hp with
  | cfg => simp [cfgWord, mem_frame] at hmr
  | halted => simp [mem_frame] at hmr
  | @right₁ q₁ b₁ h =>
    have h₁ : frame kl ([] ++ rmark q₁ b₁ :: []) kr = u' ++ rmark q b :: (a :: v) := by
      simpa using hw'
    obtain ⟨hu', hx, hv'⟩ := frame_split (P := isRmark) (by simp [isRmark]) rfl rfl rfl rfl
      (by simp [List.countP_cons, isRmark]) h₁
    simp only [rmark.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    cases kr with
    | nil =>
      simp only [List.nil_append, List.map_nil, List.cons.injEq] at hv'
      obtain ⟨rfl, rfl⟩ := hv'
      refine ⟨head q bl, [endm], (rules_endm hqs hcs).2 (Or.inl ⟨q, rfl, rfl⟩), Or.inl ?_⟩
      have := Phase.right₂ (bl := bl) (k := ⟨kq, kl, kc, []⟩) h
      simp only [List.headD_nil, List.tail_nil] at this
      convert this using 1
      simp [hu', frame]
    | cons d r =>
      simp only [List.nil_append, List.map_cons, List.cons_append, List.cons.injEq] at hv'
      obtain ⟨rfl, rfl⟩ := hv'
      refine ⟨head q d, [], (rules_tape hqs hcs).2 ⟨rfl, Or.inl ⟨q, rfl⟩⟩, Or.inl ?_⟩
      have := Phase.right₂ (bl := bl) (k := ⟨kq, kl, kc, d :: r⟩) h
      simp only [List.headD_cons, List.tail_cons] at this
      convert this using 1
      simp [hu', frame]
  | @right₂ q₁ b₁ h =>
    have hm1 : head q₁ (kr.headD bl) ∈ u' ++ rmark q b :: a :: v := by
      rw [← hw']; simp [mem_frame]
    have hne : head q₁ (kr.headD bl) ≠ a := by rcases hta with ⟨c, rfl⟩ | rfl <;> simp
    have hm2 := mem_parts (by simpa using hm1 : head q₁ (kr.headD bl) ∈
      (u' ++ [rmark q b]) ++ a :: v) hne
    exact absurd trivial (hnh' _ hm2)
  | left₁ => simp [mem_frame] at hmr
  | left₂ => simp [mem_frame] at hmr

/-- **If an objection left of a left marker is in the target, Juliet played the cell left of the
marker, and Romeo answers with a head in the state of the marker. -/
theorem faithful_of_objL_cell {k : Cfg Q Γ} {w u v : List (Letter Q Γ)} {a : Letter Q Γ}
    (hp : Phase δ bl k w) (hw : w = u ++ a :: v) (ha : IsNonterminal (rules δ qs cs bl) a)
    {u' v' : List (Letter Q Γ)} {q : Q} {b : Γ}
    (h' : u ++ objOf a :: v = u' ++ objTape :: lmark q b :: v')
    (hnh : ∀ x ∈ u ++ objOf a :: v, ¬ x.IsHead) : FaithfulAnswer δ qs cs bl k u v a := by
  obtain ⟨-, hu, hv⟩ := objCount_parts (hw ▸ objCount_phase hp)
  obtain ⟨rfl, hoa, rfl⟩ := split_obj (o' := (objTape : Letter Q Γ)) (isObj_objOf a) trivial h'
    hu hv
  have hta := tape_or_endm_of_objOf hqs hcs ha hoa
  have hml : lmark q b ∈ w := by rw [hw]; simp
  obtain ⟨kq, kl, kc, kr⟩ := k
  cases hp with
  | cfg => simp [cfgWord, mem_frame] at hml
  | halted => simp [mem_frame] at hml
  | right₁ => simp [mem_frame] at hml
  | right₂ => simp [mem_frame] at hml
  | @left₁ q₁ b₁ h =>
    have h₁ : frame kl ([] ++ lmark q₁ b₁ :: []) kr = (u ++ [a]) ++ lmark q b :: v' := by
      simpa using hw
    obtain ⟨hu', hx, hv'⟩ := frame_split (P := isLmark) (by simp [isLmark]) rfl rfl rfl rfl
      (by simp [List.countP_cons, isLmark]) h₁
    simp only [lmark.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    cases kl with
    | nil =>
      have : u ++ [a] = [] ++ [dollar] := by simpa using hu'
      obtain ⟨-, rfl⟩ := List.append_singleton_inj.mp this
      rcases hta with ⟨c, h⟩ | h <;> cases h
    | cons d l =>
      have : u ++ [a] = (dollar :: l.reverse.map tape) ++ [tape d] := by simpa using hu'
      obtain ⟨rfl, rfl⟩ := List.append_singleton_inj.mp this
      refine ⟨head q d, [], (rules_tape hqs hcs).2 ⟨rfl, Or.inl ⟨q, rfl⟩⟩, Or.inl ?_⟩
      have := Phase.left₂ (bl := bl) (k := ⟨kq, d :: l, kc, kr⟩) h rfl
      convert this using 1
      simp [frame, hv']
  | @left₂ q₁ b₁ d l h hl =>
    have hm1 : head q₁ d ∈ u ++ a :: lmark q b :: v' := by rw [← hw]; simp [mem_frame]
    have hne : head q₁ d ≠ a := by rcases hta with ⟨c, rfl⟩ | rfl <;> simp
    exact ((hnh (head q₁ d) (by
      rcases mem_parts hm1 hne with hm | hm <;> simp [hm])) trivial).elim

/-- **If an objection on a right marker next to the head is in the target, Juliet played the
marker**,
and Romeo answers with the written symbol, which completes the move to the right. -/
theorem faithful_of_objR_mark {k : Cfg Q Γ} {w u v : List (Letter Q Γ)} {a : Letter Q Γ}
    (hp : Phase δ bl k w) (hw : w = u ++ a :: v) (ha : IsNonterminal (rules δ qs cs bl) a)
    {u' v' : List (Letter Q Γ)} {p : Q} {c : Γ}
    (h' : u ++ objOf a :: v = u' ++ objR :: head p c :: v') :
    FaithfulAnswer δ qs cs bl k u v a := by
  obtain ⟨-, hu, hv⟩ := objCount_parts (hw ▸ objCount_phase hp)
  obtain ⟨rfl, hoa, rfl⟩ := split_obj (o' := (objR : Letter Q Γ)) (isObj_objOf a) trivial h'
    hu hv
  obtain ⟨q, b, rfl⟩ : ∃ q b, a = rmark q b := by
    rcases nonterminal_cases hqs hcs ha with ⟨q, b, rfl⟩ | h | ⟨q, b, rfl⟩ | ⟨b, rfl⟩ | rfl
    · simp [objOf] at hoa
    · exact h
    all_goals simp [objOf] at hoa
  have hmr : rmark q b ∈ w := by rw [hw]; simp
  obtain ⟨kq, kl, kc, kr⟩ := k
  cases hp with
  | cfg => simp [cfgWord, mem_frame] at hmr
  | halted => simp [mem_frame] at hmr
  | right₁ => exact (not_head_after_rmark hw).elim
  | @right₂ q₁ b₁ h =>
    have h₁ : frame kl ([] ++ rmark q₁ b₁ :: [head q₁ (kr.headD bl)]) kr.tail =
        u ++ rmark q b :: head p c :: v' := by simpa using hw
    obtain ⟨rfl, hx, hv'⟩ := frame_split (P := isRmark) (by simp [isRmark]) rfl rfl rfl rfl
      (by simp [List.countP_cons, isRmark]) h₁
    simp only [rmark.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨tape b, [], (rules_rmark hqs hcs).2 ⟨rfl, Or.inl rfl⟩,
      Or.inr ⟨⟨q, b :: kl, kr.headD bl, kr.tail⟩, by simp [next, h], ?_⟩⟩
    have := Phase.cfg (δ := δ) (bl := bl) (k := ⟨q, b :: kl, kr.headD bl, kr.tail⟩)
    convert this using 1
    rw [List.append_assoc, List.singleton_append, hv']
    simp [cfgWord, frame]
  | left₁ => simp [mem_frame] at hmr
  | left₂ => simp [mem_frame] at hmr

/-- **If an objection on a left marker next to the head is in the target, Juliet played the
marker**,
and Romeo answers with the written symbol, which completes the move to the left. -/
theorem faithful_of_objL_mark {k : Cfg Q Γ} {w u v : List (Letter Q Γ)} {a : Letter Q Γ}
    (hp : Phase δ bl k w) (hw : w = u ++ a :: v) (ha : IsNonterminal (rules δ qs cs bl) a)
    {u' v' : List (Letter Q Γ)} {p : Q} {c : Γ}
    (h' : u ++ objOf a :: v = u' ++ head p c :: objL :: v') :
    FaithfulAnswer δ qs cs bl k u v a := by
  obtain ⟨-, hu, hv⟩ := objCount_parts (hw ▸ objCount_phase hp)
  have h'' : u ++ objOf a :: v = (u' ++ [head p c]) ++ objL :: v' := by simpa using h'
  obtain ⟨rfl, hoa, rfl⟩ := split_obj (o' := (objL : Letter Q Γ)) (isObj_objOf a) trivial h''
    hu hv
  obtain ⟨q, b, rfl⟩ : ∃ q b, a = lmark q b := by
    rcases nonterminal_cases hqs hcs ha with ⟨q, b, rfl⟩ | ⟨q, b, rfl⟩ | h | ⟨b, rfl⟩ | rfl
    · simp [objOf] at hoa
    · simp [objOf] at hoa
    · exact h
    all_goals simp [objOf] at hoa
  have hw' : w = u' ++ head p c :: lmark q b :: v := by simpa using hw
  have hml : lmark q b ∈ w := by rw [hw]; simp
  obtain ⟨kq, kl, kc, kr⟩ := k
  cases hp with
  | cfg => simp [cfgWord, mem_frame] at hml
  | halted => simp [mem_frame] at hml
  | right₁ => simp [mem_frame] at hml
  | right₂ => simp [mem_frame] at hml
  | left₁ => exact (not_head_before_lmark hw').elim
  | @left₂ q₁ b₁ d l h hl =>
    have h₁ : frame l ([head q₁ d] ++ lmark q₁ b₁ :: []) kr =
        (u' ++ [head p c]) ++ lmark q b :: v := by simpa using hw'
    obtain ⟨hu', hx, rfl⟩ := frame_split (P := isLmark) (by simp [isLmark]) rfl rfl rfl rfl
      (by simp [List.countP_cons, isLmark]) h₁
    simp only [lmark.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    simp only at hl
    subst hl
    refine ⟨tape b, [], (rules_lmark hqs hcs).2 ⟨rfl, Or.inl rfl⟩,
      Or.inr ⟨⟨q, l, d, b :: kr⟩, by simp [next, h], ?_⟩⟩
    have := Phase.cfg (δ := δ) (bl := bl) (k := ⟨q, l, d, b :: kr⟩)
    convert this using 1
    rw [hu']
    simp [cfgWord, frame]

variable {t : RegularExpression (Letter Q Γ)} (ht : ∀ w, w ∈ t.matches' ↔ Target w)
include ht

/-- **If Juliet wins from a phase word, the machine halts.** Romeo objects to every move off the
designated position, and answers a designated move faithfully. -/
theorem halts_of_reach {w : List (Letter Q Γ)} (h : Reach (rules δ qs cs bl, t) w) :
    ∀ {k : Cfg Q Γ}, Phase δ bl k w → Halts δ bl k := by
  induction h with
  | target hw =>
    intro k hp
    exact ⟨k, .refl, halt_of_target_phase hp ((ht _).1 hw)⟩
  | @move w u v a hw ha hmove ih =>
    intro k hp
    by_cases hhalt : δ k.q k.c = .halt
    · exact ⟨k, .refl, hhalt⟩
    obtain ⟨hna, hu, hv⟩ := objCount_parts (hw ▸ objCount_phase hp)
    have hr := hmove _ _ (objOf_mem_rules hqs hcs ha)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at hr
    have h1 : objCount (u ++ objOf a :: v) = 1 := by
      rw [objCount_split_of_obj (isObj_objOf a)]
      omega
    have htw := target_of_reach_of_one hqs hcs ht hr h1
    have hfa : FaithfulAnswer δ qs cs bl k u v a := by
      rcases htw with ⟨h0, -⟩ | ⟨-, ⟨hm, hact⟩ | ⟨u', v', q, b, h', hnh⟩ | ⟨u', v', q, b, h', hnh⟩ |
          ⟨u', v', p, c, h'⟩ | ⟨u', v', p, c, h'⟩⟩
      · omega
      · exact faithful_of_objHead hqs hcs hp hw ha hm hact
      · exact faithful_of_objR_cell hqs hcs hp hw ha h' hnh
      · exact faithful_of_objL_cell hqs hcs hp hw ha h' hnh
      · exact faithful_of_objR_mark hqs hcs hp hw ha h'
      · exact faithful_of_objL_mark hqs hcs hp hw ha h'
    obtain ⟨b, x, hbx, hph | ⟨k', hk', hph⟩⟩ := hfa
    · exact ih b x hbx hph
    · obtain ⟨k'', hrun, hk''⟩ := ih b x hbx hph
      exact ⟨k'', .head hk' hrun, hk''⟩

omit hqs hcs ht in
/-- The word of a configuration is not in the target. -/
theorem not_target_cfgWord (k : Cfg Q Γ) : ¬ Target (cfgWord k) := by
  have h0 : objCount (cfgWord k) = 0 := by
    simp only [cfgWord, objCount_frame]
    simp [objCount, IsObj]
  rintro (⟨-, hh | ⟨u, v, q, b, p, c, hw, -⟩ | ⟨u, v, q, b, p, c, hw, -⟩⟩ | ⟨h1, -⟩)
  · simp [cfgWord, mem_frame] at hh
  · have hm : rmark q b ∈ u ++ rmark q b :: head p c :: v := by simp
    rw [← hw] at hm
    simp [cfgWord, mem_frame] at hm
  · have hm : lmark q b ∈ u ++ head p c :: lmark q b :: v := by simp
    rw [← hw] at hm
    simp [cfgWord, mem_frame] at hm
  · omega

/-- **Juliet wins the game from the word of a configuration iff the machine halts from it.** -/
theorem wins_iff_halts (k : Cfg Q Γ) :
    Wins (rules δ qs cs bl, t) (cfgWord k) ↔ Halts δ bl k := by
  constructor
  · rintro ⟨u, v, a, hw, ha, h⟩
    exact halts_of_reach hqs hcs ht (.move u v a hw ha h) Phase.cfg
  · intro h
    cases reach_of_halts hqs hcs ht h with
    | target hw => exact absurd ((ht _).1 hw) (not_target_cfgWord k)
    | move u v a hw ha hmove => exact ⟨u, v, a, hw, ha, hmove⟩

end Backward

end DiagonaLean.CFGame.Simulation
