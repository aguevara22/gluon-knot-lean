import SM.CrossingGeometry

/-! Actual interior points avoid every vertex when nonincident contacts are
excluded. Incident endpoint cases are proved using nonzero edge vectors. -/

namespace SM

variable {n : ℕ} {P : LabelledTuple n}

theorem interior_point_ne_vertex
    (hedge : ∀ i, edge P i ≠ 0)
    (hv : ∀ k i, ¬ incident k i → P k ∉ edgeSegment P i)
    {i : ZMod n} {x : Plane} (hx : x ∈ edgeInterior P i) (k : ZMod n) : x ≠ P k := by
  intro he
  obtain ⟨t, ht0, ht1, ht⟩ := hx
  by_cases hk0 : k = i
  · rw [hk0] at he
    have heq : t = 0 := edgePoint_injective (hedge i)
      (ht.symm.trans (he.trans (edgePoint_zero P i).symm))
    exact ht0.ne' heq
  · by_cases hk1 : k = i + 1
    · rw [hk1] at he
      have heq : t = 1 := edgePoint_injective (hedge i)
        (ht.symm.trans (he.trans (edgePoint_one P i).symm))
      exact ht1.ne heq
    · exact hv k i ((nonincident_iff k i).mpr ⟨hk0, hk1⟩)
        ⟨t, ht0.le, ht1.le, he.symm.trans ht⟩

theorem crossingPoint_ne_vertex_of_geometry (hP : CrossingGeometry P)
    (hv : ∀ k i, ¬ incident k i → P k ∉ edgeSegment P i)
    (c : Crossing P) (k : ZMod n) : crossingPoint c ≠ P k := by
  obtain ⟨a, b, hs, _, _⟩ := c.property
  exact interior_point_ne_vertex hP.1 hv
    (crossingPoint_interior_of_geometry hP c a (by rw [hs]; simp)) k

end SM
