import SM.GeometricParameters

/-! Preservation of the complete actual visit order from preservation of
the complete crossing supports and all same-edge parameter comparisons. -/

namespace SM

variable {n : ℕ} [NeZero n] {P Q : LabelledTuple n}

def CrossingParameterOrderAgrees (P Q : LabelledTuple n) : Prop :=
  ∀ i j k : ZMod n, IsCrossing P {i, j} → IsCrossing P {i, k} →
    (edgeParameter Q i j < edgeParameter Q i k ↔ edgeParameter P i j < edgeParameter P i k)

theorem geometric_visitParameterOrder (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (ho : CrossingParameterOrderAgrees P Q)
    (v w : Visit P) (he : v.2.val = w.2.val) :
    visitParameter v < visitParameter w ↔
      visitParameter (visitTransport hs v) < visitParameter (visitTransport hs w) := by
  obtain ⟨j, _, hv⟩ := crossing_support_partner v.1 v.2.val v.2.property
  obtain ⟨k, _, hw⟩ := crossing_support_partner w.1 w.2.val w.2.property
  have hij : IsCrossing P {v.2.val, j} := by simpa only [hv] using v.1.property
  have hik : IsCrossing P {v.2.val, k} := by simpa only [hw, he] using w.1.property
  rw [visitParameter_eq_of_support_pair_of_geometry hP v j hv,
    visitParameter_eq_of_support_pair_of_geometry hP w k hw,
    visitParameter_eq_of_support_pair_of_geometry hQ (visitTransport hs v) j hv,
    visitParameter_eq_of_support_pair_of_geometry hQ (visitTransport hs w) k hw,
    visitTransport_edge, visitTransport_edge, ← he]
  exact (ho v.2.val j k hij hik).symm

theorem geometric_visitKey_lt_transport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (ho : CrossingParameterOrderAgrees P Q)
    (v w : Visit P) : geometricVisitKey hP v < geometricVisitKey hP w ↔
      geometricVisitKey hQ (visitTransport hs v) < geometricVisitKey hQ (visitTransport hs w) := by
  unfold geometricVisitKey
  rw [traversalKey_lt_iff, traversalKey_lt_iff]
  change (v.2.val.val < w.2.val.val ∨ v.2.val = w.2.val ∧
    visitParameter v < visitParameter w) ↔
    (v.2.val.val < w.2.val.val ∨ v.2.val = w.2.val ∧
      visitParameter (visitTransport hs v) < visitParameter (visitTransport hs w))
  exact or_congr Iff.rfl (and_congr_right (geometric_visitParameterOrder hP hQ hs ho v w))

theorem geometric_visitKey_le_transport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (ho : CrossingParameterOrderAgrees P Q)
    (v w : Visit P) : geometricVisitKey hP v ≤ geometricVisitKey hP w ↔
      geometricVisitKey hQ (visitTransport hs v) ≤ geometricVisitKey hQ (visitTransport hs w) := by
  simpa only [not_lt] using not_congr (geometric_visitKey_lt_transport hP hQ hs ho w v)

end SM
