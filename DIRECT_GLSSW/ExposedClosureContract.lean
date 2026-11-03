import ActiveArcExposedInitialContract

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ExposedOpenPrimitive

/-- Complete exposed-closure contract: every closing far sign is negative,
the literal D=-1 marked root gate is negative, and the actual open current is A. -/
theorem exposed_closure_signs_gates_current
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (he : LeftExposed q e) (hRI : GLSSWRootIndependence) :
    (∀ k∈Finset.Ioo 0 (n-1), polygonSignArray (rootedPolygonWord q e) 0 k (n-1)=-1) ∧
    (∀ k∈Finset.Ioo 0 (n-1),
      ((-1 : ℚ)-(-polygonSignArray (rootedPolygonWord q e) 0 k (n-1)))/2=-1) ∧
    openedEdgeCurrent q e=polygonAmplitude q hq := by
  refine ⟨leftExposed_root_far_sign q hq e he,?_,openedEdgeCurrent_eq_amplitude q hq e he hRI⟩
  intro k hk
  rw [leftExposed_root_far_sign q hq e he k hk]
  norm_num


end DirectGLSSW.ExposedOpenPrimitive
