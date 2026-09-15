import SM.CriticalSourceResponse
import SM.FiniteChiStability

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
  exact sub_right_cancel hz

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

#print axioms SM.restrictedVertexIndex
#print axioms SM.restrictedVertexIndex_injective
#print axioms SM.restrictedWord_G1_off_critical
#print axioms SM.critical_closed_gaps_G1
