import DirectGLSSW.ShortEdgeGenericityRadius
import DirectGLSSW.ShortEdgeCyclicG1
import DirectGLSSW.ShortEdgeZeroGeometry

namespace DirectGLSSW.ShortEdgeGenericity

open DirectGLSSW.ShortEdgeCyclicAdapter DirectGLSSW.ShortEdgeSignStability

theorem exists_insertCyclicAfter_G2_radius {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a : Fin n) (v : PlanarPoint ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      cyclicNoncollinear (insertCyclicAfter q a ε v) →
      cyclicNoTripleIntersections (insertCyclicAfter q a ε v) := by
  exact exists_cyclicG2_radius (by have := hq.size_ge_three; omega)
    (fun ε => insertCyclicAfter q a ε v)
    (continuous_insertCyclicAfter q a v)
    (insert_zero_no_three_separated q hq a v)

theorem exists_insertCyclicAfter_generic_and_sign_stability {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a : Fin n) (v : PlanarPoint ℝ)
    (ha : 0 < a.val) (haN : a.val < n - 1)
    (hdir : DirectionGeneric
      (rootedPolygonWord q (lastCoreRoot (by have := hq.size_ge_three; omega)))
      (n - 1) a.val v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      CyclicGeneric (insertCyclicAfter q a ε v) ∧
      ShortEdgeStability
        (rootedPolygonWord q (lastCoreRoot (by have := hq.size_ge_three; omega)))
        (n - 1) a.val v ε (by omega)
        (coreHGeneric_of_cyclicNoncollinear hq.size_ge_three q hq.g1) hdir := by
  let hc := coreHGeneric_of_cyclicNoncollinear hq.size_ge_three q hq.g1
  obtain ⟨δs, hδs, hs⟩ := exists_shortEdge_sign_stability
    (rootedPolygonWord q (lastCoreRoot (by have := hq.size_ge_three; omega)))
    (n - 1) a.val v ha haN (by omega) hc hdir
  obtain ⟨δg, hδg, hg⟩ := exists_insertCyclicAfter_G2_radius q hq a v
  refine ⟨min δs δg, lt_min hδs hδg, ?_⟩
  intro ε hε hεδ
  have hst := hs ε hε (lt_of_lt_of_le hεδ (min_le_left _ _))
  have hG1 := ShortEdgeCyclicG1.inserted_cyclicNoncollinear_of_openStability
    hq.size_ge_three q a ε v hc hdir hst
  refine ⟨⟨by have := hq.size_ge_three; omega, hG1, ?_⟩, hst⟩
  exact hg ε hε (lt_of_lt_of_le hεδ (min_le_right _ _)) hG1

end DirectGLSSW.ShortEdgeGenericity
