import DirectGLSSW.PolygonGeometry
import Mathlib.Data.Real.Basic

/-!
# Concrete real generic polygons and the GLSSW root-independence input

Source: Section 1, lines 61–100 and the main theorem's full generic domain.
The global premise ranges over exactly all finite real polygons of size at
least three satisfying G1 and G2. It concerns the independently defined
GLSSW recursion; no root averaging or extra genericity condition is used.

The canonical amplitude reads that recursion at edge zero. Root independence
is a proposition passed to the root-removal theorem, never a global axiom.
No HOMFLY equality or assertion about smoothing components is made here.
-/

namespace DirectGLSSW

/-- The permitted GLSSW input on all concrete real G1–G2 polygons. -/
def GLSSWRootIndependence : Prop :=
  ∀ (n : ℕ) (q : Fin n → PlanarPoint ℝ), CyclicGeneric q → RootIndependentOn q

/-- The polygon amplitude is the independent recursion rooted at edge zero. -/
noncomputable def polygonAmplitude {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) : ℚ :=
  rootedSpinorAmplitude q ⟨0, by have := hq.size_ge_three; omega⟩

/-- The explicit global GLSSW input removes the choice of the root edge. -/
theorem polygonAmplitude_eq_rootedSpinorAmplitude (hRI : GLSSWRootIndependence)
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (root : Fin n) :
    polygonAmplitude q hq = rootedSpinorAmplitude q root := by
  exact hRI n q hq ⟨0, by have := hq.size_ge_three; omega⟩ root

/-- At the defining root, the amplitude is the concrete note-convention
marked-tree sum, with no root-independence premise needed. -/
theorem polygonAmplitude_eq_markedTreeSum {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    polygonAmplitude q hq =
      markedTreeSum
        (polygonSignArray (rootedPolygonWord q ⟨0, by have := hq.size_ge_three; omega⟩))
        (polygonSignArray (rootedPolygonWord q ⟨0, by have := hq.size_ge_three; omega⟩))
        0 (n - 1) := by
  exact rootedSpinorAmplitude_eq_markedTreeSum hq.size_ge_three q hq.g1 _

/-- The full real G1–G2 locus is inhabited by the actual standard triangle. -/
theorem realStandardTriangle_generic : CyclicGeneric (standardTriangle (K := ℝ)) :=
  standardTriangle_generic

/-- The concrete real triangle has the exact prescribed amplitude normalization. -/
theorem polygonAmplitude_standardTriangle :
    polygonAmplitude (standardTriangle (K := ℝ)) realStandardTriangle_generic = -1 := by
  exact rootedSpinorAmplitude_standardTriangle _

end DirectGLSSW
