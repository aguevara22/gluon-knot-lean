namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- Collapse remains strictly below s before A. -/
theorem collapse_lt_distinguished (s : Fin n) (p : Fin (n + 1)) (hp : p < A s) :
    collapse s p < s := by
  have h := (collapse_lt_iff_of_lt s p (A s) hp).mpr
    (fun he => (ne_of_lt hp) he.1)
  simpa only [collapse_A] using h

/-- Collapse remains strictly above s after B. -/
theorem distinguished_lt_collapse (s : Fin n) (p : Fin (n + 1)) (hp : B s < p) :
    s < collapse s p := by
  have h := (collapse_lt_iff_of_lt s (B s) p hp).mpr
    (fun he => (ne_of_lt (A_lt_B s)) he.1.symm)
  simpa only [collapse_B] using h

/-- Literal occurrence membership of both duplicated positions in a triple. -/
def tripleContainsBoth (s : Fin n) (T : IncreasingBoundaryTriple (n + 1)) : Prop :=
  (T.lower = A s ∨ T.middle = A s ∨ T.upper = A s) ∧
  (T.lower = B s ∨ T.middle = B s ∨ T.upper = B s)

theorem triple_exception_disjoint (s : Fin n) (T : IncreasingBoundaryTriple (n + 1)) :
    ¬ ((T.middle = A s ∧ T.upper = B s) ∧ (T.lower = A s ∧ T.middle = B s)) := by
  rintro ⟨hu, hl⟩
  exact (ne_of_lt (A_lt_B s)) (hu.1.symm.trans hl.2)

/-- Consecutiveness rules out A and B as lower/upper with a middle between
them. The two adjacent exceptional placements are therefore exhaustive. -/
theorem triple_contains_both_iff (s : Fin n) (T : IncreasingBoundaryTriple (n + 1)) :
    tripleContainsBoth s T ↔
      (T.middle = A s ∧ T.upper = B s) ∨ (T.lower = A s ∧ T.middle = B s) := by
  constructor
  · rintro ⟨hA, hB⟩
    have hlow : T.lower.val < T.middle.val := T.lower_middle
    have hupp : T.middle.val < T.upper.val := T.middle_upper
    rcases hA with hA | hA | hA <;> rcases hB with hB | hB | hB <;>
      first
      | exact Or.inl ⟨hA, hB⟩
      | exact Or.inr ⟨hA, hB⟩
      | have ha := congrArg Fin.val hA
        have hb := congrArg Fin.val hB
        simp only [A_val, B_val] at ha hb
        omega
  · rintro (⟨hm, hu⟩ | ⟨hl, hm⟩)
    · exact ⟨Or.inr (Or.inl hm), Or.inr (Or.inr hu)⟩
    · exact ⟨Or.inl hl, Or.inr (Or.inl hm)⟩

/-- The plain case has strictly increasing collapsed positions, proved from
the exact sole equality exception of the collapse map. -/
def collapseTriple (s : Fin n) (T : IncreasingBoundaryTriple (n + 1))
    (hplain : ¬ tripleContainsBoth s T) : IncreasingBoundaryTriple n where
  lower := collapse s T.lower
  middle := collapse s T.middle
  upper := collapse s T.upper
  lower_middle := (collapse_lt_iff_of_lt s T.lower T.middle T.lower_middle).mpr
    (fun hl => hplain ((triple_contains_both_iff s T).mpr (Or.inr hl)))
  middle_upper := (collapse_lt_iff_of_lt s T.middle T.upper T.middle_upper).mpr
    (fun hu => hplain ((triple_contains_both_iff s T).mpr (Or.inl hu)))

theorem collapseTriple_positions (s : Fin n) (T : IncreasingBoundaryTriple (n + 1))
    (hplain : ¬ tripleContainsBoth s T) :
    (collapseTriple s T hplain).lower = collapse s T.lower ∧
    (collapseTriple s T hplain).middle = collapse s T.middle ∧
    (collapseTriple s T hplain).upper = collapse s T.upper := ⟨rfl, rfl, rfl⟩

def oldTriple (s : Fin n) (T : IncreasingBoundaryTriple n) : IncreasingBoundaryTriple (n + 1) where
  lower := old s T.lower
  middle := old s T.middle
  upper := old s T.upper
  lower_middle := old_strictMono s T.lower_middle
  middle_upper := old_strictMono s T.middle_upper

theorem oldTriple_plain (s : Fin n) (T : IncreasingBoundaryTriple n) :
    ¬ tripleContainsBoth s (oldTriple s T) := by
  intro h
  rcases (triple_contains_both_iff s (oldTriple s T)).mp h with hu | hl
  · exact old_ne_B s T.upper hu.2
  · exact old_ne_B s T.middle hl.2

theorem triple_ext {T U : IncreasingBoundaryTriple n}
    (hl : T.lower = U.lower) (hm : T.middle = U.middle) (hu : T.upper = U.upper) : T = U := by
  cases T with
  | mk l m u h1 h2 =>
    cases U with
    | mk l' m' u' h1' h2' =>
      change l = l' at hl
      change m = m' at hm
      change u = u' at hu
      cases hl
      cases hm
      cases hu
      rfl

theorem collapseTriple_oldTriple (s : Fin n) (T : IncreasingBoundaryTriple n)
    (hplain : ¬ tripleContainsBoth s (oldTriple s T)) :
    collapseTriple s (oldTriple s T) hplain = T := by
  apply triple_ext
  · exact collapse_old s T.lower
  · exact collapse_old s T.middle
  · exact collapse_old s T.upper

/-- The complete source pullback/exceptional array prescription. The two
exceptional pairs are disjoint; every other triple has a proved core triple. -/
def tripleLift {R : Type*} (s : Fin n) (H0 : TripleArray n R) (t : Fin n → R) :
    TripleArray (n + 1) R := fun T =>
  if hu : T.middle = A s ∧ T.upper = B s then t (collapse s T.lower)
  else if hl : T.lower = A s ∧ T.middle = B s then t (collapse s T.upper)
  else H0 (collapseTriple s T (fun h =>
    ((triple_contains_both_iff s T).mp h).elim hu hl))

theorem tripleLift_upper {R : Type*} (s : Fin n) (H0 : TripleArray n R) (t : Fin n → R)
    (T : IncreasingBoundaryTriple (n + 1)) (hu : T.middle = A s ∧ T.upper = B s) :
    tripleLift s H0 t T = t (collapse s T.lower) := by
  simp only [tripleLift, dif_pos hu]

theorem tripleLift_lower {R : Type*} (s : Fin n) (H0 : TripleArray n R) (t : Fin n → R)
    (T : IncreasingBoundaryTriple (n + 1)) (hl : T.lower = A s ∧ T.middle = B s) :
    tripleLift s H0 t T = t (collapse s T.upper) := by
  have hu : ¬ (T.middle = A s ∧ T.upper = B s) :=
    fun h => triple_exception_disjoint s T ⟨h, hl⟩
  simp only [tripleLift, dif_neg hu, dif_pos hl]

theorem tripleLift_plain {R : Type*} (s : Fin n) (H0 : TripleArray n R) (t : Fin n → R)
    (T : IncreasingBoundaryTriple (n + 1)) (hplain : ¬ tripleContainsBoth s T) :
    tripleLift s H0 t T = H0 (collapseTriple s T hplain) := by
  have hu : ¬ (T.middle = A s ∧ T.upper = B s) :=
    fun h => hplain ((triple_contains_both_iff s T).mpr (Or.inl h))
  have hl : ¬ (T.lower = A s ∧ T.middle = B s) :=
    fun h => hplain ((triple_contains_both_iff s T).mpr (Or.inr h))
  simp only [tripleLift, dif_neg hu, dif_neg hl]

theorem tripleLift_oldTriple {R : Type*} (s : Fin n) (H0 : TripleArray n R) (t : Fin n → R)
    (T : IncreasingBoundaryTriple n) : tripleLift s H0 t (oldTriple s T) = H0 T := by
  rw [tripleLift_plain s H0 t (oldTriple s T) (oldTriple_plain s T), collapseTriple_oldTriple]

theorem upper_exception_argument_lt (s : Fin n) (T : IncreasingBoundaryTriple (n + 1))
    (hu : T.middle = A s ∧ T.upper = B s) : collapse s T.lower < s :=
  collapse_lt_distinguished s T.lower (lt_of_lt_of_eq T.lower_middle hu.1)

theorem lower_exception_argument_gt (s : Fin n) (T : IncreasingBoundaryTriple (n + 1))
    (hl : T.lower = A s ∧ T.middle = B s) : s < collapse s T.upper := by
  apply distinguished_lt_collapse s T.upper
  simpa only [hl.2] using T.middle_upper

/-- The source auxiliary core near array; it is not asserted geometric. -/
def coreNear (s : Fin n) (t : Fin n → ℚ) : TripleArray n ℚ := fun T =>
  if T.middle = s then t T.lower else 0

theorem coreNear_at_middle (s : Fin n) (t : Fin n → ℚ) (T : IncreasingBoundaryTriple n)
    (hm : T.middle = s) : coreNear s t T = t T.lower := by
  simp only [coreNear, if_pos hm]

theorem coreNear_off_middle (s : Fin n) (t : Fin n → ℚ) (T : IncreasingBoundaryTriple n)
    (hm : T.middle ≠ s) : coreNear s t T = 0 := by
  simp only [coreNear, if_neg hm]

theorem coreNear_argument_lt (s : Fin n) (T : IncreasingBoundaryTriple n)
    (hm : T.middle = s) : T.lower < s := lt_of_lt_of_eq T.lower_middle hm

/-- The auxiliary parent near array uses the same exact exceptional t-data
and otherwise pulls back coreNear. -/
def parentNear (s : Fin n) (t : Fin n → ℚ) : TripleArray (n + 1) ℚ :=
  tripleLift s (coreNear s t) t

theorem parentNear_oldTriple (s : Fin n) (t : Fin n → ℚ) (T : IncreasingBoundaryTriple n) :
    parentNear s t (oldTriple s T) = coreNear s t T := tripleLift_oldTriple s _ t T

/-- Both occurrences lie in the closed interval. Since A<B, the other two
endpoint inequalities follow automatically. -/
def intervalContainsBoth (s : Fin n) (I : BoundaryInterval (n + 1)) : Prop :=
  I.left ≤ A s ∧ B s ≤ I.right

theorem intervalContainsBoth_iff (s : Fin n) (I : BoundaryInterval (n + 1)) :
    intervalContainsBoth s I ↔
      (I.left ≤ A s ∧ A s ≤ I.right) ∧ (I.left ≤ B s ∧ B s ≤ I.right) := by
  constructor
  · intro h
    exact ⟨⟨h.1, le_trans (A_lt_B s).le h.2⟩,
      ⟨le_trans h.1 (A_lt_B s).le, h.2⟩⟩
  · intro h
    exact ⟨h.1.1, h.2.2⟩

theorem interval_eq_duplicate (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left = A s) (hr : I.right = B s) : I = duplicateInterval s := by
  apply (collapse_endpoints_eq_iff s I).mp
  rw [hl, hr, collapse_A, collapse_B]

/-- Exactly the five source rows, with strict exterior endpoints in the
three nonsingleton cases containing both occurrences. -/
theorem interval_five_cases (s : Fin n) (I : BoundaryInterval (n + 1)) :
    (¬ intervalContainsBoth s I) ∨ I = duplicateInterval s ∨
    (I.left = A s ∧ B s < I.right) ∨ (I.left < A s ∧ I.right = B s) ∨
    (I.left < A s ∧ B s < I.right) := by
  by_cases h : intervalContainsBoth s I
  · rcases lt_or_eq_of_le h.1 with hl | hl
    · rcases lt_or_eq_of_le h.2 with hr | hr
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hl, hr⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hl, hr.symm⟩)))
    · rcases lt_or_eq_of_le h.2 with hr | hr
      · exact Or.inr (Or.inr (Or.inl ⟨hl, hr⟩))
      · exact Or.inr (Or.inl (interval_eq_duplicate s I hl hr.symm))
  · exact Or.inl h

theorem not_duplicate_of_not_contains (s : Fin n) (I : BoundaryInterval (n + 1))
    (h : ¬ intervalContainsBoth s I) : I ≠ duplicateInterval s := by
  rintro rfl
  exact h ⟨le_rfl, le_rfl⟩

theorem not_duplicate_of_right_gt (s : Fin n) (I : BoundaryInterval (n + 1))
    (h : B s < I.right) : I ≠ duplicateInterval s := by
  intro he
  have hb : B s < B s := by simpa only [he, duplicateInterval] using h
  exact (lt_irrefl _) hb

theorem not_duplicate_of_left_lt (s : Fin n) (I : BoundaryInterval (n + 1))
    (h : I.left < A s) : I ≠ duplicateInterval s := by
  intro he
  have ha : A s < A s := by simpa only [he, duplicateInterval] using h
  exact (lt_irrefl _) ha

theorem start_collapsed_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left = A s) (hr : B s < I.right) :
    collapse s I.left = s ∧ s < collapse s I.right :=
  ⟨by rw [hl, collapse_A], distinguished_lt_collapse s I.right hr⟩

theorem end_collapsed_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : I.right = B s) :
    collapse s I.left < s ∧ collapse s I.right = s :=
  ⟨collapse_lt_distinguished s I.left hl, by rw [hr, collapse_B]⟩

theorem span_collapsed_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : B s < I.right) :
    collapse s I.left < s ∧ s < collapse s I.right :=
  ⟨collapse_lt_distinguished s I.left hl, distinguished_lt_collapse s I.right hr⟩

/-- The proposed five-row ordinary array, defined on every child interval.
The duplicate interval is handled before forming any collapsed interval.
No recurrence or inverse-solution assertion is built into this definition. -/
def ordinaryLift (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) : IntervalArray (n + 1) ℚ := fun I =>
  if hdup : I = duplicateInterval s then 1
  else
    let J := collapseInterval s I hdup
    if intervalContainsBoth s I then
      if I.left = A s then ((etaPlus - t (collapse s I.right)) / 2) * b0 J
      else if I.right = B s then ((etaMinus - t (collapse s I.left)) / 2) * b0 J
      else ((etaMinus + etaPlus) / 2) * b0 J
    else b0 J

theorem ordinaryLift_duplicate (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) : ordinaryLift s etaMinus etaPlus t b0 (duplicateInterval s) = 1 := by
  simp only [ordinaryLift, dif_pos rfl]

theorem ordinaryLift_plain (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (h : ¬ intervalContainsBoth s I) :
    ordinaryLift s etaMinus etaPlus t b0 I =
      b0 (collapseInterval s I (not_duplicate_of_not_contains s I h)) := by
  simp only [ordinaryLift, dif_neg (not_duplicate_of_not_contains s I h), if_neg h]

theorem ordinaryLift_start (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (hl : I.left = A s) (hr : B s < I.right) :
    ordinaryLift s etaMinus etaPlus t b0 I =
      ((etaPlus - t (collapse s I.right)) / 2) *
        b0 (collapseInterval s I (not_duplicate_of_right_gt s I hr)) := by
  have hboth : intervalContainsBoth s I := ⟨le_of_eq hl, hr.le⟩
  simp only [ordinaryLift, dif_neg (not_duplicate_of_right_gt s I hr), if_pos hboth, if_pos hl]

theorem ordinaryLift_end (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : I.right = B s) :
    ordinaryLift s etaMinus etaPlus t b0 I =
      ((etaMinus - t (collapse s I.left)) / 2) *
        b0 (collapseInterval s I (not_duplicate_of_left_lt s I hl)) := by
  have hboth : intervalContainsBoth s I := ⟨hl.le, le_of_eq hr.symm⟩
  simp only [ordinaryLift, dif_neg (not_duplicate_of_left_lt s I hl), if_pos hboth,
    if_neg (ne_of_lt hl), if_pos hr]

theorem ordinaryLift_span (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : B s < I.right) :
    ordinaryLift s etaMinus etaPlus t b0 I =
      ((etaMinus + etaPlus) / 2) *
        b0 (collapseInterval s I (not_duplicate_of_left_lt s I hl)) := by
  have hboth : intervalContainsBoth s I := ⟨hl.le, hr.le⟩
  simp only [ordinaryLift, dif_neg (not_duplicate_of_left_lt s I hl), if_pos hboth,
    if_neg (ne_of_lt hl), if_neg (ne_of_gt hr)]

end
end SM.SoftDuplication
