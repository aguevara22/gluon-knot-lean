import SourcePolygonDomain
set_option autoImplicit false
namespace DirectGLSSW.SourcePolygonData
open DirectGLSSW.HOMFLY.PolygonDrawingBridge

/-- A nonempty closed cyclic list with nonzero edges and no antipodal adjacent
pair automatically has at least three labels. No genericity is used. -/
theorem immersed_polygon_size_ge_three {n : ℕ} (hn : 0 < n)
    (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i /
      polygonEdgeVector q ((cyclicSuccessorPerm n).symm i) ∈ Complex.slitPlane) :
    3 ≤ n := by
  by_contra h
  have hle : n ≤ 2 := by omega
  interval_cases n
  · have hs : cyclicSuccessor (0 : Fin 1) = 0 := Subsingleton.elim _ _
    have hz : polygonEdgeVector q 0 = 0 := by
      apply Complex.ext <;> simp [polygonEdgeVector,cyclicTangent,hs]
    exact hedge 0 hz
  · have hs0 : cyclicSuccessor (0 : Fin 2) = 1 := rfl
    have hs1 : cyclicSuccessor (1 : Fin 2) = 0 := rfl
    have hp : (cyclicSuccessorPerm 2).symm (0 : Fin 2) = 1 := by
      apply (cyclicSuccessorPerm 2).injective
      simp only [Equiv.apply_symm_apply,cyclicSuccessorPerm_apply,hs1]
    have hv : polygonEdgeVector q 1 = -polygonEdgeVector q 0 := by
      apply Complex.ext <;> simp [polygonEdgeVector,cyclicTangent,hs0,hs1]
    have hh := hshort 0
    rw [hp,hv,div_neg,div_self (hedge 0)] at hh
    rw [Complex.mem_slitPlane_iff] at hh
    norm_num at hh

end DirectGLSSW.SourcePolygonData

