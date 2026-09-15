namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- A zero rational geometric far entry is exactly collinearity. The
change from reversed far orientation to the endpoint-line determinant
only negates that determinant and does not change its zero set. -/
theorem rational_geometric_far_zero_iff (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) :
    geometricBoundaryArray (R := ℚ) P g t = 0 ↔
      det (boundaryWord P g t.middle - boundaryWord P g t.lower)
        (boundaryWord P g t.upper - boundaryWord P g t.lower) = 0 := by
  have hs (s : SignType) : ((s : ℤ) : ℚ) = 0 ↔ s = 0 := by
    cases s <;> norm_num
  unfold geometricBoundaryArray
  rw [hs, chi, sign_eq_zero_iff]
  change det (boundaryWord P g t.middle - boundaryWord P g t.upper)
      (boundaryWord P g t.lower - boundaryWord P g t.upper) = 0 ↔ _
  have hd : det (boundaryWord P g t.middle - boundaryWord P g t.upper)
      (boundaryWord P g t.lower - boundaryWord P g t.upper) =
      -det (boundaryWord P g t.middle - boundaryWord P g t.lower)
        (boundaryWord P g t.upper - boundaryWord P g t.lower) := by
    dsimp [det]
    ring
  rw [hd, neg_eq_zero]

/-- If every selected top cut is silent, every point in the actual
composition cut list lies on its endpoint line. Endpoints are included
explicitly, and no independence of determinant differentials is used. -/
theorem silent_composition_cuts_collinear (P : LabelledTuple n) (g : ZMod n)
    {I : BoundaryInterval n} (π : IntervalComposition I)
    (hzero : ∀ j : Fin (π.parts - 1), geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0) :
    ∀ l, det (boundaryWord P g (π.cut l) - boundaryWord P g (π.cut 0))
      (boundaryWord P g (π.cut (Fin.last π.parts)) - boundaryWord P g (π.cut 0)) = 0 := by
  intro l
  by_cases hfirst : l = 0
  · subst l
    simp [det]
  by_cases hlast : l = Fin.last π.parts
  · subst l
    simp [det, mul_comm]
  have hlo : 0 < l.val := by
    by_contra h
    apply hfirst
    apply Fin.ext
    change l.val = 0
    omega
  have hhi : l.val < π.parts := by
    have hv := l.isLt
    by_contra h
    apply hlast
    apply Fin.ext
    change l.val = π.parts
    omega
  let j : Fin (π.parts - 1) := ⟨l.val - 1, by omega⟩
  have hm : π.interiorPosition j = π.cut l := by
    unfold IntervalComposition.interiorPosition
    congr 1
    apply Fin.ext
    change (l.val - 1) + 1 = l.val
    omega
  have hd := (rational_geometric_far_zero_iff P g (π.farTriple j)).mp (hzero j)
  change det (boundaryWord P g (π.interiorPosition j) - boundaryWord P g I.left)
    (boundaryWord P g I.right - boundaryWord P g I.left) = 0 at hd
  rw [hm] at hd
  rw [π.first, π.last]
  exact hd

/-- Every nonempty silent selection has a positive gap of at least two
leaves in the actual composition, ready for its zero inverse-coordinate
factor. The rational zero array supplies the collinearity premise. -/
theorem silent_composition_positive_gap (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) {I : BoundaryInterval n}
    (π : IntervalComposition I) (hparts : 2 ≤ π.parts)
    (hzero : ∀ j : Fin (π.parts - 1), geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0) :
    ∃ j : Fin π.parts, lineGapEpsilon (selectedLineCoordinate P g π.cut) j = 1 ∧
      2 ≤ (π.part j).leaves := by
  have h := silent_line_gap_of_collinear hn hP g π.parts hparts π.cut π.strict
    (silent_composition_cuts_collinear P g π hzero)
  exact h.2.2.2.1

/-- The negative gap assertion is used only on the full physical root
interval; the source's endpoint condition is discharged by π.first/last. -/
theorem silent_composition_full_negative_gap (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : WeakGeneric P) (g : ZMod n) (π : IntervalComposition (fullBoundaryInterval hn))
    (hparts : 2 ≤ π.parts)
    (hzero : ∀ j : Fin (π.parts - 1), geometricBoundaryArray (R := ℚ) P g (π.farTriple j) = 0) :
    ∃ j : Fin π.parts, lineGapEpsilon (selectedLineCoordinate P g π.cut) j = -1 ∧
      2 ≤ (π.part j).leaves := by
  have h := silent_line_gap_of_collinear hn hP g π.parts hparts π.cut π.strict
    (silent_composition_cuts_collinear P g π hzero)
  apply h.2.2.2.2
  · rw [π.first]
    rfl
  · rw [π.last]
    rfl

end
end SM
