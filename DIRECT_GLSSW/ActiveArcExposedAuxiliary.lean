import ActiveArcGammaM
import DirectGLSSW.DaughterRootAmplitude
import ExposedOpenInitialization

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW ExposedOpenPrimitive GeometricSmoothingWeights DaughterFirstReturn PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2))
variable (hq : CyclicGeneric q) (he : LeftExposed q e) (hAux : auxiliaryGenericity q hq)

include he hAux in
/-- Existing parent daughter genericity transfers through the exact retained point word. -/
theorem retained_generic (S : Primitive.Support (cutArc q e) (cutArc_regular q e hq))
    (x : ActiveArc.Event (cutArc q e)) :
    CyclicGeneric (RetainedWords.vertex (cutArc q e) (cutArc_regular q e hq) S.val x) := by
  have hs := (nonalternating_iff_parent q e hq he S.val).mp S.property
  have hv := daughterPointList_eq_retainedWord q e hq he S.val x
  have hrot : List.ofFn (daughterVertex q hq.g2 (mappedSupport q e hq he S.val)
      (dartEventEquiv q e hq he S.val x)) ~r
    List.ofFn (RetainedWords.vertex (cutArc q e) (cutArc_regular q e hq) S.val x) :=
    ⟨0,by simpa only [List.rotate_zero] using hv⟩
  exact DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated hrot
    (hAux _ hs (dartEventEquiv q e hq he S.val x))

/-- The source closed-daughter condition is discharged on this chart, not assumed anew. -/
def closedAuxiliary_of_parent : Primitive.ClosedAuxiliary (cutArc q e) (cutArc_regular q e hq) :=
  fun S C hc => retained_generic q e hq he hAux S
    (closedRoot (cutArc q e) (cutArc_regular q e hq).noTriple S.val C hc)

include hAux in
/-- Actual retained amplitude equals the amplitude of its transported parent component. -/
theorem retainedAmplitude_eq_component (hRI : GLSSWRootIndependence)
    (S : Primitive.Support (cutArc q e) (cutArc_regular q e hq))
    (x : ActiveArc.Event (cutArc q e)) :
    polygonAmplitude (RetainedWords.vertex (cutArc q e) (cutArc_regular q e hq) S.val x)
      (retained_generic q e hq he hAux S x)=
      componentAmplitude q hq (mappedSupport q e hq he S.val) hAux
        ((nonalternating_iff_parent q e hq he S.val).mp S.property)
        (componentOf (smoothingDartPermutation q hq.g2 (mappedSupport q e hq he S.val))
          (dartEventEquiv q e hq he S.val x)) := by
  let T := mappedSupport q e hq he S.val
  have hs := (nonalternating_iff_parent q e hq he S.val).mp S.property
  let y := dartEventEquiv q e hq he S.val x
  let C := componentOf (smoothingDartPermutation q hq.g2 T) y
  let r := componentRoot q hq T C
  have hv := daughterPointList_eq_retainedWord q e hq he S.val x
  have hrot : List.ofFn (daughterVertex q hq.g2 T y) ~r
      List.ofFn (RetainedWords.vertex (cutArc q e) (cutArc_regular q e hq) S.val x) :=
    ⟨0,by simpa only [List.rotate_zero] using hv⟩
  have hA := DaughterRootAmplitude.polygonAmplitude_ofFn_isRotated hRI (hAux T hs y) hrot
  have hc : (smoothingDartPermutation q hq.g2 T).SameCycle y r := by
    apply (componentOf_eq_iff _ _ _).mp
    exact (componentRoot_sameComponent q hq T C).symm
  have hB := DaughterRootAmplitude.daughterPolygonAmplitude_eq_of_sameCycle
    hRI q hq.g2 T y r hc (hAux T hs y)
  exact hA.symm.trans hB

end DirectGLSSW.ActiveArc.ExposedChart
