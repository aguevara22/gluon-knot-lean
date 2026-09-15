import SM.CriticalSourceResponse
import SM.FiniteChiStability
import SM.RestrictedWordRoot

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

namespace IncreasingBoundaryTriple

def positionSet (t : IncreasingBoundaryTriple n) : Finset (Fin n) :=
  {t.lower, t.middle, t.upper}

theorem positionSet_bounds (t : IncreasingBoundaryTriple n) (x : Fin n)
    (hx : x ∈ t.positionSet) : t.lower ≤ x ∧ x ≤ t.upper := by
  simp only [positionSet, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨le_rfl, le_of_lt (lt_trans t.lower_middle t.middle_upper)⟩
  · exact ⟨le_of_lt t.lower_middle, le_of_lt t.middle_upper⟩
  · exact ⟨le_of_lt (lt_trans t.lower_middle t.middle_upper), le_rfl⟩

/-- The unordered position set determines the increasing triple. Min/max
fix both endpoints, and the distinct remaining position fixes the middle. -/
theorem positionSet_injective : Function.Injective (positionSet (n := n)) := by
  intro t u he
  have hl : t.lower = u.lower := by
    apply le_antisymm
    · exact (t.positionSet_bounds u.lower (by rw [he]; simp [positionSet])).1
    · exact (u.positionSet_bounds t.lower (by rw [← he]; simp [positionSet])).1
  have hr : t.upper = u.upper := by
    apply le_antisymm
    · exact (u.positionSet_bounds t.upper (by rw [← he]; simp [positionSet])).2
    · exact (t.positionSet_bounds u.upper (by rw [he]; simp [positionSet])).2
  have hm : t.middle = u.middle := by
    have hx : t.middle ∈ u.positionSet := by rw [← he]; simp [positionSet]
    simp only [positionSet, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h
    · exact ((ne_of_gt t.lower_middle) (h.trans hl.symm)).elim
    · exact h
    · exact ((ne_of_lt t.middle_upper) (h.trans hr.symm)).elim
  exact eq_of_entries hl hm hr

/-- The actual unordered source vertex support in the chosen root reading. -/
def vertexSet (g : ZMod n) (t : IncreasingBoundaryTriple n) : Finset (ZMod n) :=
  t.positionSet.image (boundaryIndex g)

theorem vertexSet_injective (g : ZMod n) : Function.Injective (vertexSet g) := by
  intro t u he
  apply positionSet_injective
  exact Finset.image_injective (boundaryIndex_injective g) he

theorem vertexSet_reversed (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    t.vertexSet g = {boundaryIndex g t.upper, boundaryIndex g t.middle, boundaryIndex g t.lower} := by
  ext x
  simp [vertexSet, positionSet, or_comm, or_left_comm, or_assoc]

end IncreasingBoundaryTriple

/-- Unique zero support implies every other increasing boundary triple has
a nonzero determinant sign. This uses label injectivity of the root reading,
without inferring geometric vertex distinctness from singleton Zpt at n=3. -/
theorem boundary_chi_nonzero_off_critical (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hP : pointZeroTriples P = {t.vertexSet g})
    (u : IncreasingBoundaryTriple n) (hu : u ≠ t) :
    chi P (boundaryIndex g u.upper) (boundaryIndex g u.middle) (boundaryIndex g u.lower) ≠ 0 := by
  apply chi_nonzero_outside_singleton hP
  · exact fun h => (ne_of_gt u.middle_upper) (boundaryIndex_injective g h)
  · exact fun h => (ne_of_gt u.lower_middle) (boundaryIndex_injective g h)
  · exact fun h => (ne_of_gt (lt_trans u.lower_middle u.middle_upper)) (boundaryIndex_injective g h)
  · intro he
    have hs : u.vertexSet g = t.vertexSet g := (u.vertexSet_reversed g).trans he
    exact hu (IncreasingBoundaryTriple.vertexSet_injective g hs)

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The label map for the already defined closed contiguous word, with
residue zero still labeling its actual last vertex. -/
def restrictedVertexIndex (g : ZMod n) (J : BoundaryInterval n)
    (j : ZMod (J.leaves + 1)) : ZMod n :=
  boundaryIndex g (J.globalPosition ⟨(j - 1).val, ZMod.val_lt _⟩)

theorem restrictedVertexIndex_injective (g : ZMod n) (J : BoundaryInterval n) :
    Function.Injective (restrictedVertexIndex g J) := by
  intro i j he
  have hp := J.globalPosition_strict.injective (boundaryIndex_injective g he)
  have hv := congrArg Fin.val hp
  have hz : i - 1 = j - 1 := ZMod.val_injective (J.leaves + 1) hv
  simpa only [sub_add_cancel] using congrArg (fun v : ZMod (J.leaves + 1) => v + 1) hz

/-- A closed contiguous word excluding the complete critical span has no
zero distinct-label triple. This proves its actual G1 condition directly from
the singleton zero-support hypothesis, without assuming global G1 at the wall. -/
theorem restrictedWord_G1_off_critical (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) :
    G1 (restrictedWordTuple P g J) := by
  intro i j k hij hjk hik
  change chi P (restrictedVertexIndex g J i) (restrictedVertexIndex g J j)
    (restrictedVertexIndex g J k) ≠ 0
  apply chi_nonzero_outside_singleton hZ
  · exact fun he => hij (restrictedVertexIndex_injective g J he)
  · exact fun he => hjk (restrictedVertexIndex_injective g J he)
  · exact fun he => hik (restrictedVertexIndex_injective g J he)
  · intro he
    have hb (a : Fin n) (v : ZMod (J.leaves + 1))
        (h : boundaryIndex g a = restrictedVertexIndex g J v) :
        J.left ≤ a ∧ a ≤ J.right := by
      have hp : a = J.globalPosition ⟨(v - 1).val, ZMod.val_lt _⟩ :=
        boundaryIndex_injective g h
      rw [hp]
      exact J.globalPosition_bounds _
    have hs (a : Fin n)
        (ha : boundaryIndex g a ∈ ({restrictedVertexIndex g J i,
          restrictedVertexIndex g J j, restrictedVertexIndex g J k} : Finset (ZMod n))) :
        J.left ≤ a ∧ a ≤ J.right := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with hi | hj | hk
      · exact hb a i hi
      · exact hb a j hj
      · exact hb a k hk
    have hl := hs t.lower (by
      rw [he]
      simp [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet])
    have hu := hs t.upper (by
      rw [he]
      simp [IncreasingBoundaryTriple.vertexSet, IncreasingBoundaryTriple.positionSet])
    exact hJ ⟨hl.1, hu.2⟩

/-- Both nonleaf closed gap polygons satisfy G1. The explicit leaf-count
premises retain the source distinction between polygon amplitudes and the
formal one-leaf convention. -/
theorem critical_closed_gaps_G1 (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g}) :
    (2 ≤ t.leftInterval.leaves → G1 (restrictedWordTuple P g t.leftInterval)) ∧
      (2 ≤ t.rightInterval.leaves → G1 (restrictedWordTuple P g t.rightInterval)) := by
  constructor
  · intro _
    apply restrictedWord_G1_off_critical P g t hZ
    rintro ⟨_, hr⟩
    exact (not_le_of_gt t.middle_upper) hr
  · intro _
    apply restrictedWord_G1_off_critical P g t hZ
    rintro ⟨hl, _⟩
    exact (not_le_of_gt t.lower_middle) hl

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The source U switches between the exact unit array E and full B output.
Its consumers require the actual wall epsilon to be either1 or-1. -/
def wallGapU (H : TripleArray n R) (I : BoundaryInterval n) (ε : SignType) : R :=
  if ε = 1 then boundaryUnitArray I else farOnlyOutput H I

/-- The source V interchanges the same two complete interval values. -/
def wallGapV (H : TripleArray n R) (I : BoundaryInterval n) (ε : SignType) : R :=
  if ε = 1 then farOnlyOutput H I else boundaryUnitArray I

/-- Every raw composition is retained. The actual signed far gates identify
the complete weighted sum with source U through the proved inverse equation. -/
theorem cutWeightedSum_signed_inverse (f : Fin n → R) (H : TripleArray n R)
    (I : BoundaryInterval n) (ε : SignType) (hε : ε = 1 ∨ ε = -1)
    (h : ∀ π : IntervalComposition I, ∀ k : Fin (π.parts - 1),
      f (π.interiorPosition k) = -((((ε : ℤ) : R)) * H (π.farTriple k)) * ⅟ (2 : R)) :
    cutWeightedSum f (farOnlyCoordinates H) I = wallGapU H I ε := by
  rcases hε with rfl | rfl
  · rw [wallGapU, if_pos rfl]
    calc
      cutWeightedSum f (farOnlyCoordinates H) I = farTransform H (farOnlyCoordinates H) I := by
        apply cutWeightedSum_eq_farTransform
        intro π k
        simpa using h π k
      _ = boundaryUnitArray I := congrFun (farOnlyCoordinates_equation H) I
  · rw [wallGapU, if_neg (by decide)]
    change cutWeightedSum f (farOnlyCoordinates H) I = farTransform (-H) (farOnlyCoordinates H) I
    apply cutWeightedSum_eq_farTransform
    intro π k
    simpa using h π k

/-- Reversing every far gate interchanges E and B, including the unary gap
whose empty gate product remains1. -/
theorem cutWeightedSum_neg_signed_inverse (f : Fin n → R) (H : TripleArray n R)
    (I : BoundaryInterval n) (ε : SignType) (hε : ε = 1 ∨ ε = -1)
    (h : ∀ π : IntervalComposition I, ∀ k : Fin (π.parts - 1),
      f (π.interiorPosition k) = -((((ε : ℤ) : R)) * H (π.farTriple k)) * ⅟ (2 : R)) :
    cutWeightedSum (-f) (farOnlyCoordinates H) I = wallGapV H I ε := by
  rcases hε with rfl | rfl
  · rw [wallGapV, if_pos rfl]
    change cutWeightedSum (-f) (farOnlyCoordinates H) I = farTransform (-H) (farOnlyCoordinates H) I
    apply cutWeightedSum_eq_farTransform
    intro π k
    simpa using congrArg Neg.neg (h π k)
  · rw [wallGapV, if_neg (by decide)]
    calc
      cutWeightedSum (-f) (farOnlyCoordinates H) I = farTransform H (farOnlyCoordinates H) I := by
        apply cutWeightedSum_eq_farTransform
        intro π k
        simpa using congrArg Neg.neg (h π k)
      _ = boundaryUnitArray I := congrFun (farOnlyCoordinates_equation H) I

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem IncreasingBoundaryTriple.leftInterval_excludes_span (t : IncreasingBoundaryTriple n) :
    ¬ (t.leftInterval.left ≤ t.lower ∧ t.upper ≤ t.leftInterval.right) := by
  rintro ⟨_, hr⟩
  exact (not_le_of_gt t.middle_upper) hr

theorem IncreasingBoundaryTriple.rightInterval_excludes_span (t : IncreasingBoundaryTriple n) :
    ¬ (t.rightInterval.left ≤ t.lower ∧ t.upper ≤ t.rightInterval.right) := by
  rintro ⟨hl, _⟩
  exact (not_le_of_gt t.lower_middle) hl

/-- The integer B value on a noncritical interval is one on a formal leaf and
otherwise the actual closed endpoint polygon's tree coefficient. The latter
has proved G1 and at least three vertices. No inverse over the integers is used. -/
def criticalIntervalIntegerOutput (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) : ℤ :=
  if hl : J.leaves = 1 then 1 else
    treeCoefficient (restrictedWordTuple P g J) (restrictedWord_G1_off_critical P g t hZ J hJ) 0
      (by have := J.leaves_pos; omega)

/-- Source U as an integer: the exact unit array or the proved integral B value. -/
def criticalGapUInteger (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (ε : SignType) : ℤ :=
  if ε = 1 then boundaryUnitArray (R := ℤ) J else criticalIntervalIntegerOutput P g t hZ J hJ

/-- Source V interchanges the same two integer values. -/
def criticalGapVInteger (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (ε : SignType) : ℤ :=
  if ε = 1 then criticalIntervalIntegerOutput P g t hZ J hJ else boundaryUnitArray (R := ℤ) J

theorem critical_integer_leaf_values (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right))
    (hl : J.leaves = 1) (ε : SignType) :
    criticalIntervalIntegerOutput P g t hZ J hJ = 1 ∧
      criticalGapUInteger P g t hZ J hJ ε = 1 ∧ criticalGapVInteger P g t hZ J hJ ε = 1 := by
  have hb : criticalIntervalIntegerOutput P g t hZ J hJ = 1 := by
    simp only [criticalIntervalIntegerOutput, dif_pos hl]
  have hr : J.right.val = J.left.val + 1 := by
    have hpos := J.increasing
    change J.left.val < J.right.val at hpos
    change J.right.val - J.left.val = 1 at hl
    omega
  have he : boundaryUnitArray (R := ℤ) J = 1 := by simp [boundaryUnitArray, hr]
  simp only [criticalGapUInteger, criticalGapVInteger, hb, he, ite_self, and_self]

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

theorem boundaryUnitArray_intCast (J : BoundaryInterval n) :
    ((boundaryUnitArray (R := ℤ) J : ℤ) : R) = boundaryUnitArray (R := R) J := by
  by_cases h : J.right.val = J.left.val + 1 <;> simp [boundaryUnitArray, h]

/-- Only the complete B output is identified with an integer cast. The
constructed inverse coordinates themselves may have denominators. -/
theorem criticalIntervalIntegerOutput_cast (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) :
    (criticalIntervalIntegerOutput P g t hZ J hJ : R) =
      farOnlyOutput (geometricBoundaryArray P g) J := by
  by_cases hl : J.leaves = 1
  · rw [criticalIntervalIntegerOutput, dif_pos hl, Int.cast_one]
    exact (farOnly_leaf_values (geometricBoundaryArray P g) J hl).2.symm
  · rw [criticalIntervalIntegerOutput, dif_neg hl]
    have htwo : 2 ≤ J.leaves := by have := J.leaves_pos; omega
    exact (farOnlyOutput_restricted_tree P g J htwo
      (restrictedWord_G1_off_critical P g t hZ J hJ)).symm

theorem criticalGapUInteger_cast (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (ε : SignType) :
    (criticalGapUInteger P g t hZ J hJ ε : R) = wallGapU (geometricBoundaryArray P g) J ε := by
  by_cases hε : ε = 1
  · simp only [criticalGapUInteger, wallGapU, if_pos hε]
    exact boundaryUnitArray_intCast J
  · simp only [criticalGapUInteger, wallGapU, if_neg hε]
    exact criticalIntervalIntegerOutput_cast P g t hZ J hJ

theorem criticalGapVInteger_cast (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right)) (ε : SignType) :
    (criticalGapVInteger P g t hZ J hJ ε : R) = wallGapV (geometricBoundaryArray P g) J ε := by
  by_cases hε : ε = 1
  · simp only [criticalGapVInteger, wallGapV, if_pos hε]
    exact criticalIntervalIntegerOutput_cast P g t hZ J hJ
  · simp only [criticalGapVInteger, wallGapV, if_neg hε]
    exact boundaryUnitArray_intCast J

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

theorem boundaryUnitArray_nonleaf_zero {R : Type*} [CommRing R]
    (J : BoundaryInterval n) (hJ : 2 ≤ J.leaves) : boundaryUnitArray (R := R) J = 0 := by
  have he : J.right.val ≠ J.left.val + 1 := by
    change 2 ≤ J.right.val - J.left.val at hJ
    omega
  simp only [boundaryUnitArray, if_neg he]

/-- Two singleton gaps give the proper-span unit multiplier for all signs. -/
theorem integer_wall_factor_two_leaves (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : t.leftInterval.leaves = 1) (hR : t.rightInterval.leaves = 1) (εL εR : SignType) :
    criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span εL *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span εR = 1 := by
  have hl := critical_integer_leaf_values P g t hZ t.leftInterval t.leftInterval_excludes_span hL εL
  have hr := critical_integer_leaf_values P g t hZ t.rightInterval t.rightInterval_excludes_span hR εR
  rw [hl.2.1, hr.2.1, one_mul]

/-- At the incoming root, epsilon (-,+) annihilates the unbarred product;
the barred product is precisely the nonleaf right-gap B output. -/
theorem integer_wall_factor_left_leaf (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : t.leftInterval.leaves = 1) (hR : 2 ≤ t.rightInterval.leaves) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span (-1) *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span (-1) *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 =
      criticalIntervalIntegerOutput P g t hZ t.rightInterval t.rightInterval_excludes_span) := by
  have hl := critical_integer_leaf_values P g t hZ t.leftInterval t.leftInterval_excludes_span hL (-1)
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  constructor
  · rw [hl.2.1]
    simp only [criticalGapUInteger, ite_true, he, mul_zero]
  · rw [hl.2.2]
    simp only [criticalGapVInteger, ite_true, one_mul]

/-- At the outgoing root epsilon (+,-) reverses the roles of the two gaps. -/
theorem integer_wall_factor_right_leaf (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : t.rightInterval.leaves = 1) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span (-1) = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span (-1) =
      criticalIntervalIntegerOutput P g t hZ t.leftInterval t.leftInterval_excludes_span) := by
  have hr := critical_integer_leaf_values P g t hZ t.rightInterval t.rightInterval_excludes_span hR (-1)
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  constructor
  · rw [hr.2.1]
    simp only [criticalGapUInteger, ite_true, he, zero_mul]
  · rw [hr.2.2]
    simp only [criticalGapVInteger, ite_true, mul_one]

end
end SM




namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The exact integer gap factors for the source cusp table, with the
left gap singleton and the right gap nonleaf. -/
theorem integer_wall_factor_left_leaf_pos_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : t.leftInterval.leaves = 1) (hR : 2 ≤ t.rightInterval.leaves) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = criticalIntervalIntegerOutput P g t hZ t.rightInterval t.rightInterval_excludes_span) := by
  have hl := critical_integer_leaf_values P g t hZ t.leftInterval t.leftInterval_excludes_span hL 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  constructor
  · rw [hl.2.1]
    norm_num only [criticalGapUInteger, he, one_mul, mul_one]
  · rw [hl.2.2]
    norm_num only [criticalGapVInteger, he, one_mul, mul_one]

/-- The exact integer gap factors for the source cusp table, with the
left gap singleton and the right gap nonleaf. -/
theorem integer_wall_factor_left_leaf_pos_neg (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : t.leftInterval.leaves = 1) (hR : 2 ≤ t.rightInterval.leaves) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span (-1) = criticalIntervalIntegerOutput P g t hZ t.rightInterval t.rightInterval_excludes_span) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span (-1) = 0) := by
  have hl := critical_integer_leaf_values P g t hZ t.leftInterval t.leftInterval_excludes_span hL 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.rightInterval hR
  constructor
  · rw [hl.2.1]
    norm_num only [criticalGapUInteger, he, one_mul, mul_one]
  · rw [hl.2.2]
    norm_num only [criticalGapVInteger, he, one_mul, mul_one]

/-- The exact integer gap factors for the source cusp table, with the
right gap singleton and the left gap nonleaf. -/
theorem integer_wall_factor_right_leaf_neg_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : t.rightInterval.leaves = 1) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span (-1) *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = criticalIntervalIntegerOutput P g t hZ t.leftInterval t.leftInterval_excludes_span) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span (-1) *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) := by
  have hl := critical_integer_leaf_values P g t hZ t.rightInterval t.rightInterval_excludes_span hR 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  constructor
  · rw [hl.2.1]
    norm_num only [criticalGapUInteger, he, one_mul, mul_one]
  · rw [hl.2.2]
    norm_num only [criticalGapVInteger, he, one_mul, mul_one]

/-- The exact integer gap factors for the source cusp table, with the
right gap singleton and the left gap nonleaf. -/
theorem integer_wall_factor_right_leaf_pos_pos (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hL : 2 ≤ t.leftInterval.leaves) (hR : t.rightInterval.leaves = 1) :
    (criticalGapUInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapUInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = 0) ∧
    (criticalGapVInteger P g t hZ t.leftInterval t.leftInterval_excludes_span 1 *
      criticalGapVInteger P g t hZ t.rightInterval t.rightInterval_excludes_span 1 = criticalIntervalIntegerOutput P g t hZ t.leftInterval t.leftInterval_excludes_span) := by
  have hl := critical_integer_leaf_values P g t hZ t.rightInterval t.rightInterval_excludes_span hR 1
  have he := boundaryUnitArray_nonleaf_zero (R := ℤ) t.leftInterval hL
  constructor
  · rw [hl.2.1]
    norm_num only [criticalGapUInteger, he, one_mul, mul_one]
  · rw [hl.2.2]
    norm_num only [criticalGapVInteger, he, one_mul, mul_one]

end
end SM

#check SM.integer_wall_factor_left_leaf_pos_pos
#print axioms SM.integer_wall_factor_left_leaf_pos_pos

#check SM.integer_wall_factor_left_leaf_pos_neg
#print axioms SM.integer_wall_factor_left_leaf_pos_neg

#check SM.integer_wall_factor_right_leaf_neg_pos
#print axioms SM.integer_wall_factor_right_leaf_neg_pos

#check SM.integer_wall_factor_right_leaf_pos_pos
#print axioms SM.integer_wall_factor_right_leaf_pos_pos
