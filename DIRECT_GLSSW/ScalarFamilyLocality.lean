import ScalarComponentRotation
import RefinementFamilyLocality

set_option autoImplicit false
namespace DirectGLSSW.FullScalarInversion
open DirectGLSSW.PermutationOrbits DirectGLSSW.ActualLocalSupports
attribute [local instance] Classical.propDecidable

/-- Genuine geometric locality for an arbitrary cyclic scalar: when two
second-stage families agree on an old component, the selected final
component value agrees. This is derived from equality of the actual daughter
vertex words and cyclic-root invariance, with no amplitude premise. -/
theorem scalar_component_eq_of_family_eq {R : Type*} (X : CyclicScalar R)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))
    (f g : LocalSupports q (smoothingIncomingPermutation q hq.g2 S) S)
    (A : Component (smoothingIncomingPermutation q hq.g2 S)) (hfg : f A = g A)
    (root : PolygonEvent q)
    (hroot : DirectGLSSW.RefinementFamilyLocality.outgoingOldLabel q hq S root = A) :
    let fullF := S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S f
    let fullG := S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S g
    X.toFun (componentWord q hq.g2 fullF
      (componentOf (smoothingDartPermutation q hq.g2 fullF) root)) =
    X.toFun (componentWord q hq.g2 fullG
      (componentOf (smoothingDartPermutation q hq.g2 fullG) root)) := by
  classical
  dsimp only
  calc
    X.toFun (componentWord q hq.g2 _ (componentOf _ root)) =
        X.toFun (DaughterFirstReturn.daughterPointList q hq.g2
          (S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S f) root) :=
      scalar_component_eq_at_root X q hq.g2 _ _ root rfl
    _ = X.toFun (DaughterFirstReturn.daughterPointList q hq.g2
          (S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S g) root) := by
      rw [DirectGLSSW.RefinementFamilyLocality.daughterPointList_eq_of_family_eq
        q hq S f g A hfg root hroot]
    _ = X.toFun (componentWord q hq.g2 _ (componentOf _ root)) :=
      (scalar_component_eq_at_root X q hq.g2 _ _ root rfl).symm

end DirectGLSSW.FullScalarInversion

