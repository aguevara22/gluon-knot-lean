import CornerStateSumLocality
import ConfigurationDaughterTransport
import LocalSupportConjugacy
import Gemini.Solution
import SharpDaughterCharacterization
import SharpDaughterRotationInteger
import UniformDaughterSupportCharacterization
import NormalizedEvaluatorUniqueness
import DirectGLSSW.HOMFLY.HOMFLYSignedDiagramIso

set_option autoImplicit false
open scoped BigOperators Classical

/-! Proposed, unfrozen chamber contract. This file defines only geometric objects and an alias to the accepted source sum;
it contains no new theorem or replacement for the frozen theorem. The geometric witness uses genuine
homeomorphisms of the real plane with joint forward and inverse continuity. -/
namespace DirectGLSSW.GeminiChamber
open DirectGLSSW.HOMFLY DirectGLSSW.HOMFLY.Coefficients
open DirectGLSSW.HOMFLY.SharpDaughter
open DirectGLSSW.UniformDaughterSupportLocality
open DirectGLSSW.PermutationOrbits

abbrev Time := Set.Icc (0 : ℝ) 1
abbrev Plane := PlanarPoint ℝ

def start : Time := ⟨0, by simp⟩
def finish : Time := ⟨1, by simp⟩

/-- A literal ambient isotopy, with continuous motion of every plane point
and continuous reverse motion. -/
structure AmbientPlaneIsotopy where
  motion : Time → Plane ≃ₜ Plane
  at_start : motion start = Homeomorph.refl Plane
  forward_continuous : Continuous (fun p : Time × Plane => motion p.1 p.2)
  inverse_continuous : Continuous (fun p : Time × Plane => (motion p.1).symm p.2)

/-- Actual straight closed segment, including endpoints. -/
def trace (a b : Plane) : Set Plane :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = a + t • (b - a)}

/-- Original labelled polygon edge, in its given cyclic orientation. -/
def originalEdge {n : ℕ} (q : Fin n → Plane) (e : Fin n) : Set Plane :=
  trace (q e) (q (cyclicSuccessor e))

/-- Actual PL diagram arc, with ordered source and target. -/
def diagramArc (D : PLLinkDiagram) (a : Fin D.nArc) : Set Plane :=
  trace (D.vertexPoint (D.arcSource a)) (D.vertexPoint (D.arcTarget a))

/-- Exact source left-turn count. -/
noncomputable def leftCount {n : ℕ} (q : Fin n → Plane) : ℕ :=
  (Finset.univ.filter (fun i : Fin n =>
    0 < planarDet (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i))
      (cyclicTangent q i))).card

/-- A transport of actual PL diagrams, including every geometric arc; the
signed combinatorial isomorphism records ordered continuation and crossing
branches, while `arc_image` asserts the real planar isotopy. -/
structure DiagramTransport (F : Plane ≃ₜ Plane) (D E : PLLinkDiagram) where
  signed : SignedDiagramIso D E
  vertex : Fin D.nVertex ≃ Fin E.nVertex
  vertex_image : ∀ v, F (D.vertexPoint v) = E.vertexPoint (vertex v)
  source_image : ∀ a, vertex (D.arcSource a) = E.arcSource (signed.arcEquiv a)
  target_image : ∀ a, vertex (D.arcTarget a) = E.arcTarget (signed.arcEquiv a)
  arc_image : ∀ a, F '' diagramArc D a = diagramArc E (signed.arcEquiv a)

/-- The exact G1/G2 generic locus, with no auxiliary genericity. -/
def genericLocus (n : ℕ) : Set (Fin n → Plane) :=
  {q | CyclicGeneric q}

/-- Alias to the already accepted literal source sum. Its exact expansion is
`CornerStateSumLocality.cornerStateSum_eq_literal`. -/
noncomputable abbrev stateSum := DirectGLSSW.CornerStateSumLocality.cornerStateSum

end DirectGLSSW.GeminiChamber
