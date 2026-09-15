namespace SM.WallGerm

open Filter Topology

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- One positive radius preserves all noncritical geometric far entries and
all inverse/output coordinates outside the critical span, on both sides of the
actual continuous germ. The center is included in this local assertion. -/
theorem boundary_values_stable_near_center (w : WallGerm n) (g : ZMod n)
    (t : IncreasingBoundaryTriple n) (hZ : pointZeroTriples w.center = {t.vertexSet g}) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧ ∀ s : w.Parameter, |s.val| < δ →
      (∀ u : IncreasingBoundaryTriple n, u ≠ t →
        geometricBoundaryArray (R := R) (w.curve s) g u =
          geometricBoundaryArray w.center g u) ∧
      (∀ J : BoundaryInterval n, ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right) →
        farOnlyCoordinates (geometricBoundaryArray (R := R) (w.curve s) g) J =
          farOnlyCoordinates (geometricBoundaryArray w.center g) J) ∧
      (∀ J : BoundaryInterval n, ¬ (J.left ≤ t.lower ∧ t.upper ≤ J.right) →
        farOnlyOutput (geometricBoundaryArray (R := R) (w.curve s) g) J =
          farOnlyOutput (geometricBoundaryArray w.center g) J) := by
  apply (w.eventually_center_iff_radius _).mp
  have h := w.continuous_curve.continuousAt
  filter_upwards [h.eventually (geometric_array_persists_off_critical (R := R) w.center g t hZ),
    h.eventually (geometric_inverse_persists_off_span (R := R) w.center g t hZ),
    h.eventually (geometric_output_persists_off_span (R := R) w.center g t hZ)] with s hA hC hB
  exact ⟨hA, hC, hB⟩

end
end SM.WallGerm
