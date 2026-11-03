import ScalarRefinementSum

set_option autoImplicit false
namespace DirectGLSSW.FullScalarInversion
open scoped BigOperators
open DirectGLSSW.PermutationOrbits DirectGLSSW.DaughterFirstReturn
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 4000000 in
theorem scalar_empty_componentProduct_eq_polygon {R : Type*} [CommRing R]
    (X : CyclicScalar R) {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) :
    componentProduct X q hq.g2 ∅ = X.toFun (List.ofFn q) := by
  classical
  let root0 : PolygonEvent q := Sum.inl ⟨0, by have := hq.size_ge_three; omega⟩
  let p := smoothingDartPermutation q hq.g2 ∅
  let C0 := componentOf p root0
  have hAll (C : Component p) : C = C0 := by
    refine Quotient.inductionOn C ?_
    intro x
    apply (componentOf_eq_iff p x root0).2
    simpa [p, smoothingDartPermutation_empty] using
      (polygonEventSuccessor_isCycleOn q hq.g2).2 (Set.mem_univ x) (Set.mem_univ root0)
  have hProd : componentProduct X q hq.g2 ∅ =
      X.toFun (componentWord q hq.g2 ∅ C0) := by
    unfold componentProduct
    rw [Finset.prod_eq_single C0]
    · intro C hC hne
      exact (hne (hAll C)).elim
    · intro h
      exact (h (Finset.mem_univ C0)).elim
  rw [hProd]
  have hword := scalar_component_eq_at_root X q hq.g2 ∅ C0 root0 rfl
  rw [hword]
  exact congrArg X.toFun
    (DirectGLSSW.ScalarInversionFinal.empty_daughterPointList_zero_local
      (by have := hq.size_ge_three; omega) q hq.g2)

end DirectGLSSW.FullScalarInversion

