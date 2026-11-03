import PrimitiveContinuation
import SourcePrimitiveConsequences

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.PrimitiveContinuation
open DirectGLSSW.PolygonUniformity

/-- The characterized full primitive has the nonuniform source value. -/
theorem fullPrimitive_nonuniform_zero (hRI : GLSSWRootIndependence)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hnu : ¬ PolygonUniform q) :
    fullPrimitive hRI n q hq = 0 := by
  obtain ⟨hlocal, hagree, _⟩ := fullPrimitive_characterization hRI n
  exact DirectGLSSW.SourcePrimitiveConsequences.any_extension_nonuniform_zero
    hRI (fullPrimitive hRI n) hlocal hagree q hq hnu

/-- The characterized full primitive has the prescribed uniform source value. -/
theorem fullPrimitive_uniform_corner (hRI : GLSSWRootIndependence)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hu : PolygonUniform q) :
    fullPrimitive hRI n q hq =
      (-1 : ℚ) ^ SmoothingTurnCount.leftTurnCount q *
        (GeminiReversalContract.prescribedCorner q hq : ℚ) := by
  obtain ⟨hlocal, hagree, _⟩ := fullPrimitive_characterization hRI n
  exact DirectGLSSW.SourcePrimitiveConsequences.any_extension_uniform_corner
    hRI (fullPrimitive hRI n) hlocal hagree q hq hu

end DirectGLSSW.PrimitiveContinuation
