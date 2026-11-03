import ActiveArcExposedAuxiliary
import ActualCursorConstancy
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ExposedChart
open RetainedWords Primitive ExposedOpenPrimitive GeometricSmoothingWeights

/-- Original all-component auxiliary genericity supplies the missing initial
open Core domain through the literal exposed-opening retained word. ClosedAuxiliary
alone is not used to assert genericity of the open component. -/
theorem initial_exposed_all_support_core {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (e : Fin (n+2)) (hq : CyclicGeneric q) (he : LeftExposed q e)
    (hAux : auxiliaryGenericity q hq)
    (U : Support (cutArc q e) (cutArc_regular q e hq)) :
    ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex (cutArc q e) (cutArc_regular q e hq) U)
        (openLast (cutArc q e) (cutArc_regular q e hq) U.val))
      (openCount (cutArc q e) (cutArc_regular q e hq) U.val-1) := by
  have hQ := retained_generic q e hq he hAux U (start (cutArc q e))
  have hh := rootedPolygonWord_noncollinear _ hQ.g1
    (openLast (cutArc q e) (cutArc_regular q e hq) U.val)
  intro i j k hij hjk hk
  exact hh i j k (Nat.zero_le _) hij hjk hk
end DirectGLSSW.ActiveArc.ExposedChart
