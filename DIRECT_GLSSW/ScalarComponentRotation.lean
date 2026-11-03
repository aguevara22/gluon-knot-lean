import ScalarPrimitiveG2

set_option autoImplicit false
namespace DirectGLSSW.FullScalarInversion
open DirectGLSSW.PermutationOrbits

/-- The arbitrary scalar value on an actual smoothing component is independent
of which event in that component is used to enumerate its cyclic vertex word. -/
theorem scalar_component_eq_at_root {R : Type*} (X : CyclicScalar R)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (C : Component (smoothingDartPermutation q hG2 S))
    (root : PolygonEvent q)
    (hroot : componentOf (smoothingDartPermutation q hG2 S) root = C) :
    X.toFun (componentWord q hG2 S C) =
      X.toFun (DaughterFirstReturn.daughterPointList q hG2 S root) := by
  have hout : componentOf (smoothingDartPermutation q hG2 S) (Quotient.out C) = C :=
    Quotient.out_eq C
  have hcycle := (componentOf_eq_iff (smoothingDartPermutation q hG2 S)
    (Quotient.out C) root).mp (hout.trans hroot.symm)
  exact scalar_daughter_root_invariant X q hG2 S (Quotient.out C) root hcycle

end DirectGLSSW.FullScalarInversion

