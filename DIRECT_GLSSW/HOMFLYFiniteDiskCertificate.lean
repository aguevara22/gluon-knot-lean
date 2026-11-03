import HOMFLYDrawingCircuit
import Mathlib.Analysis.Convex.Topology

/-!
Finite geometric input for the named innermost-fewgon/empty-triangle consumer.
This module does not assert existence of a filling for any circuit. The
certificate is built from actual nondegenerate triangles by boundary-edge
attachments whose intersections are checked as sets in the real plane.
-/

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

structure TrianglePatch where
  a : PlanarPoint ℝ
  b : PlanarPoint ℝ
  c : PlanarPoint ℝ
  nondegenerate : planarDet (b-a) (c-a) ≠ 0

namespace TrianglePatch

def fill (T : TrianglePatch) : Set (PlanarPoint ℝ) :=
  convexHull ℝ {T.a,T.b,T.c}

def boundary (T : TrianglePatch) : Set (PlanarPoint ℝ) :=
  segment ℝ T.a T.b ∪ segment ℝ T.b T.c ∪ segment ℝ T.c T.a

theorem fill_isCompact (T : TrianglePatch) : IsCompact T.fill := by
  exact (((Set.finite_singleton T.c).insert T.b).insert T.a).isCompact_convexHull

end TrianglePatch

/-- A finite disk is described by actual triangle gluing. The indices are
computed region and boundary sets, not externally supplied topology claims. -/
inductive FiniteDiskCertificate : Set (PlanarPoint ℝ) → Set (PlanarPoint ℝ) → Type
  | triangle (T : TrianglePatch) : FiniteDiskCertificate T.fill T.boundary
  | attach {K B : Set (PlanarPoint ℝ)} (previous : FiniteDiskCertificate K B)
      (T : TrianglePatch)
      (boundary_edge : segment ℝ T.a T.b ⊆ B)
      (exact_intersection : K ∩ T.fill = segment ℝ T.a T.b) :
      FiniteDiskCertificate (K ∪ T.fill)
        ((B \ openSegment ℝ T.a T.b) ∪ segment ℝ T.b T.c ∪ segment ℝ T.c T.a)

namespace FiniteDiskCertificate

def tileCount {K B : Set (PlanarPoint ℝ)} (W : FiniteDiskCertificate K B) : ℕ :=
  match W with
  | .triangle _ => 1
  | .attach previous _ _ _ => previous.tileCount + 1

theorem tileCount_pos {K B : Set (PlanarPoint ℝ)} (W : FiniteDiskCertificate K B) :
    0 < W.tileCount := by
  cases W <;> simp only [tileCount] <;> omega

theorem region_isCompact {K B : Set (PlanarPoint ℝ)} (W : FiniteDiskCertificate K B) :
    IsCompact K := by
  induction W with
  | triangle T => exact T.fill_isCompact
  | attach previous T boundary_edge exact_intersection ih =>
      exact ih.union T.fill_isCompact

end FiniteDiskCertificate

/-- Geometric certificate with boundary exactly the selected drawing circuit. -/
def CircuitDiskWitness {D : PLLinkDiagram} (P : DrawingCircuit D) :=
  Σ K : Set (PlanarPoint ℝ), FiniteDiskCertificate K P.boundary

namespace CircuitDiskWitness

def interiorCrossingCount {D : PLLinkDiagram} {P : DrawingCircuit D}
    (W : CircuitDiskWitness P) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun c : Fin D.nCrossing => D.vertexPoint (D.crossingVertex c) ∈ W.1 \ P.boundary)).card

end CircuitDiskWitness
end
end DirectGLSSW.HOMFLY





