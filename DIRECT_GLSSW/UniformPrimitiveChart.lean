import UniformSupportingChart
import PolygonRebasePrimitive
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open GeometricSmoothingWeights PolygonRebase TruncationDirection Coefficients PrincipalTurning
attribute [local instance] Classical.propDecidable

/-- One actual supporting truncation and cyclic restart preserves both sides
of the uniform identity. No exposed point, replacement amplitude, or coefficient
equality is supplied by the caller. -/
theorem exists_uniform_exposed_primitive_corner_chart
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i)
      (cyclicTangent q (cyclicSuccessor i)))
    (hAux : auxiliaryGenericity q hq) :
    ∃ m : ℕ, ∃ Q : Fin (m+2) → PlanarPoint ℝ, ∃ hQ : CyclicGeneric Q,
    ∃ hAuxQ : auxiliaryGenericity Q hQ,
      (∀ i, 0 < planarDet (cyclicTangent Q i)
        (cyclicTangent Q (cyclicSuccessor i))) ∧
      ExposedOpenPrimitive.LeftExposed Q 0 ∧
      (positivePolygonEventDiagram Q hQ).nCrossing =
        (positivePolygonEventDiagram q hq).nCrossing ∧
      (-1 : ℚ)^(m+2) * separatingSmoothingSum Q hQ hAuxQ =
        (-1 : ℚ)^n * separatingSmoothingSum q hq hAux ∧
      coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram Q hQ)
        (positivePolygonEventDiagram_nArc_pos Q hQ))
        (1-((positivePolygonEventDiagram Q hQ).nCrossing : ℤ)-
          |turnInteger (positivePolygonEventDiagram Q hQ)|) 0 =
      coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
        (positivePolygonEventDiagram_nArc_pos q hq))
        (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
          |turnInteger (positivePolygonEventDiagram q hq)|) 0 := by
  obtain ⟨m,hn⟩ : ∃ m : ℕ, n=m+2 := ⟨n-2,by have := hq.size_ge_three; omega⟩
  subst n
  obtain ⟨a,p,hp,scale,hs,δ,hδ,hfamily⟩ :=
    exists_supporting_truncation_preserves_nu_and_corner hRI q hq hleft hAux
  obtain ⟨hε1,hs1,hT,hAuxT,hleftT,heT,hamp,hsum,hnu,hcount,hturn,hdegree,heval,hcoeff⟩ :=
    hfamily (δ/2) (by linarith) (by linarith)
  let T := truncateCyclicCorner q a p scale (δ/2)
  let ρ := atEdge a.castSucc
  let Q := T ∘ ρ
  let hQ : CyclicGeneric Q := cyclicGeneric_relabel T ρ (atEdge_commutes_successor _) hT
  let hAuxQ : auxiliaryGenericity Q hQ :=
    auxiliaryGenericity_relabel T hT ρ (atEdge_commutes_successor _) hAuxT
  have heQ : ExposedOpenPrimitive.LeftExposed Q 0 := by
    apply leftExposed_relabel T ρ (atEdge_commutes_successor _)
    have hz : ρ (0 : Fin (m+3)) = a.castSucc := atEdge_zero a.castSucc (by omega)
    rw [hz]
    exact heT
  have hcountQ := positiveDiagram_crossingCount T ρ (atEdge_commutes_successor _) hT
  have hturnQ := turnInteger_relabel T hT ρ (atEdge_commutes_successor _)
  have hH := candidateEvaluator_relabel T hT ρ (atEdge_commutes_successor _)
  have hnuQ := vertexParity_normalizedPrimitive_relabel T ρ
    (atEdge_commutes_successor _) hT hRI hAuxT
  refine ⟨m+1,Q,hQ,hAuxQ,
    strictLeft_relabel T ρ (atEdge_commutes_successor _) hleftT,
    heQ,hcountQ.trans hcount.symm,hnuQ.trans hnu,?_⟩
  change coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram (T ∘ ρ) hQ)
    (positivePolygonEventDiagram_nArc_pos _ _))
    (1-((positivePolygonEventDiagram (T ∘ ρ) hQ).nCrossing : ℤ)-
      |turnInteger (positivePolygonEventDiagram (T ∘ ρ) hQ)|) 0 = _
  rw [hH,hcountQ,hturnQ]
  exact hcoeff.symm

end DirectGLSSW.HOMFLY.PolygonDrawingBridge

