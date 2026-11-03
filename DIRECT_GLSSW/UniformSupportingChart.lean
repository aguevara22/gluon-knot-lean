import UniformPolynomialSetup
import PolygonRebaseAuxiliary
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open PermutationOrbits LowestRowContract FramedPolynomial Coefficients PrincipalTurning
open GeometricSmoothingWeights PolygonRebase TruncationDirection
attribute [local instance] Classical.propDecidable

/-- Every actual uniform polygon supplies its exposed edge-zero chart, with
unchanged crossing count and framed row, on the inherited auxiliary domain. -/
theorem exists_uniform_exposed_chart
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (hAux : auxiliaryGenericity q hq) :
    ∃ m : ℕ, ∃ Q : Fin (m+2) → PlanarPoint ℝ, ∃ hQ : CyclicGeneric Q,
      (∀ i, 0 < planarDet (cyclicTangent Q i) (cyclicTangent Q (cyclicSuccessor i))) ∧
      auxiliaryGenericity Q hQ ∧ ExposedOpenPrimitive.LeftExposed Q 0 ∧
      (positivePolygonEventDiagram Q hQ).nCrossing = (positivePolygonEventDiagram q hq).nCrossing ∧
      framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
        (positivePolygonEventDiagram_nArc_pos _ _)
        (componentOf (positivePolygonEventDiagram q hq).continuation ⟨0,positivePolygonEventDiagram_nArc_pos _ _⟩) =
      framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram Q hQ)
        (positivePolygonEventDiagram_nArc_pos _ _)
        (componentOf (positivePolygonEventDiagram Q hQ).continuation ⟨0,positivePolygonEventDiagram_nArc_pos _ _⟩) := by
  obtain ⟨m,hn⟩ : ∃ m : ℕ, n=m+2 := ⟨n-2,by have := hq.size_ge_three;omega⟩
  subst n
  obtain ⟨a,p,hp,scale,hs,δ,hδ,hfamily⟩ :=
    exists_supporting_truncation_preserves_nu_and_corner hRI q hq hleft hAux
  obtain ⟨hε1,hs1,hT,hAuxT,hleftT,heT,hamp,hsum,hnu,hcount,hturn,hdegree,heval,hcoeff⟩ :=
    hfamily (δ/2) (by linarith) (by linarith)
  let T := truncateCyclicCorner q a p scale (δ/2)
  let ρ := atEdge a.castSucc
  let Q := T ∘ ρ
  let hQ : CyclicGeneric Q := cyclicGeneric_relabel T ρ (atEdge_commutes_successor _) hT
  have hleftQ := strictLeft_relabel T ρ (atEdge_commutes_successor _) hleftT
  have hAuxQ := auxiliaryGenericity_relabel T hT ρ (atEdge_commutes_successor _) hAuxT
  have heQ : ExposedOpenPrimitive.LeftExposed Q 0 := by
    apply leftExposed_relabel T ρ (atEdge_commutes_successor _)
    have hz : ρ (0 : Fin (m+3)) = a.castSucc := atEdge_zero a.castSucc (by omega)
    rw [hz]
    exact heT
  have hrowT := positivePolygon_framedRow_eq_of_data q hq T hT hcount hdegree.symm heval
  have hrowQ := framedKnotRow_relabel T hT ρ (atEdge_commutes_successor _)
    (componentOf (positivePolygonEventDiagram Q hQ).continuation ⟨0,positivePolygonEventDiagram_nArc_pos _ _⟩)
    (componentOf (positivePolygonEventDiagram T hT).continuation ⟨0,positivePolygonEventDiagram_nArc_pos _ _⟩)
  exact ⟨m+1,Q,hQ,hleftQ,hAuxQ,heQ,
    (positiveDiagram_crossingCount T ρ (atEdge_commutes_successor _) hT).trans hcount.symm,
    hrowT.trans hrowQ.symm⟩
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
