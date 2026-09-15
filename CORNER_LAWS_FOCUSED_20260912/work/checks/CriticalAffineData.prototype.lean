import SM.EuclideanPlane
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

/-- Actual distinct collinear points admit the affine coordinates used in the
wall theorem. The direction is the endpoint difference; no choice of a
collinearity oracle or additional dimension assumption is required. -/
theorem distinct_collinear_affine_data (a b c : Plane)
    (hba : b ≠ a) (hcb : c ≠ b) (hca : c ≠ a)
    (hd : det (b - a) (c - a) = 0) :
    ∃ p ω : Plane, ∃ x y z : ℝ,
      ω ≠ 0 ∧ a = p + x • ω ∧ b = p + y • ω ∧ c = p + z • ω ∧
      y ≠ x ∧ z ≠ y ∧ z ≠ x := by
  have hω : c - a ≠ 0 := sub_ne_zero.mpr hca
  let q := planeDot (c - a) (b - a) / planeDot (c - a) (c - a)
  have hd' : det (c - a) (b - a) = 0 := by rw [det_swap, hd, neg_zero]
  have hs : b - a = q • (c - a) := scalar_of_det_zero hω hd'
  have hb : b = a + q • (c - a) := by
    calc
      b = a + (b - a) := by abel
      _ = a + q • (c - a) := by rw [hs]
  have hc : c = a + (1 : ℝ) • (c - a) := by simp
  have hq0 : q ≠ 0 := by
    intro hq
    exact hba (by simpa only [hq, zero_smul, add_zero] using hb)
  have h1q : (1 : ℝ) ≠ q := by
    intro hq
    exact hcb (hc.trans ((congrArg (fun r : ℝ => a + r • (c - a)) hq).trans hb.symm))
  exact ⟨a, c - a, 0, q, 1, hω, by simp, hb, hc, hq0, h1q, by norm_num⟩

variable {n : ℕ} [NeZero n]

/-- Apply the constructed affine coordinates to the actual critical boundary
points. Physical pairwise distinctness is explicit and is not inferred from
a singleton zero support, which would fail at arity three. -/
theorem critical_boundary_affine_data (P : LabelledTuple n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples P = {t.vertexSet g})
    (hba : boundaryWord P g t.middle ≠ boundaryWord P g t.lower)
    (hcb : boundaryWord P g t.upper ≠ boundaryWord P g t.middle)
    (hca : boundaryWord P g t.upper ≠ boundaryWord P g t.lower) :
    ∃ p ω : Plane, ∃ x y z : ℝ,
      ω ≠ 0 ∧ boundaryWord P g t.lower = p + x • ω ∧
      boundaryWord P g t.middle = p + y • ω ∧
      boundaryWord P g t.upper = p + z • ω ∧ y ≠ x ∧ z ≠ y ∧ z ≠ x := by
  have hdata := singlePointTriple_data hZ
  have hχ : chi P (boundaryIndex g t.lower) (boundaryIndex g t.middle)
      (boundaryIndex g t.upper) = 0 := by
    apply hdata.2
    all_goals rw [t.vertexSet_reversed g]; simp
  have hd : det (boundaryWord P g t.middle - boundaryWord P g t.lower)
      (boundaryWord P g t.upper - boundaryWord P g t.lower) = 0 := sign_eq_zero_iff.mp hχ
  exact distinct_collinear_affine_data _ _ _ hba hcb hca hd

end
end SM

#check SM.distinct_collinear_affine_data
#print axioms SM.distinct_collinear_affine_data
#check SM.critical_boundary_affine_data
#print axioms SM.critical_boundary_affine_data
