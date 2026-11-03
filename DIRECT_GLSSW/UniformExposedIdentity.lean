import PhysicalMarkedComparison
import SourcePreservingSuppliedPolygon
import InitialExposedCore
import ActiveArcExposedInitialization
import UniformPrimitiveChart
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open GeometricSmoothingWeights ExposedOpenPrimitive ActiveArc ActiveArc.ExposedChart
  ActiveArc.FiniteCalculation ActiveArc.Primitive PolygonDrawingBridge PrincipalTurning Coefficients
  SmoothingCornerGeometry Filter Topology
attribute [local instance] Classical.propDecidable

/-- All cyclic left turns give the literal vertex count in the signed primitive. -/
theorem uniform_left_count {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i))) :
    (Finset.univ.filter (fun i : Fin n => 0 < planarDet
      (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i)) (cyclicTangent q i))).card=n := by
  have hp : ∀ i : Fin n, 0 < planarDet
      (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i)) (cyclicTangent q i) := by
    intro i
    have hs : cyclicSuccessor ((cyclicSuccessorPerm n)⁻¹ i)=i :=
      (cyclicSuccessorPerm n).apply_symm_apply i
    simpa only [hs] using hleft ((cyclicSuccessorPerm n)⁻¹ i)
  simp [hp]

/-- Exposed original polygons satisfy the primitive/corner identity under the
actual smaller-crossing induction hypothesis. All auxiliary cursor fields are
produced at one source-preserving nearby polygon. -/
theorem exposed_identity_of_strongIH
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (he : LeftExposed q 0) (hAux : auxiliaryGenericity q hq)
    (hstrongIH : SmallerPolygonCornerIH q) :
    (-1 : ℚ)^(n+2)*separatingSmoothingSum q hq hAux =
      coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
        (positivePolygonEventDiagram_nArc_pos q hq))
        (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
          |turnInteger (positivePolygonEventDiagram q hq)|) 0 := by
  obtain ⟨p,hpV,hp,hAp,hEp,hleftp,hν,hcount,hEval,hTurn,hcoeff,L,hL,hT,hinc,hterm⟩ :=
    PhysicalSourceInitialization.exists_nearby_source_full_preservation hRI q hq he hAux hleft
      Set.univ (Filter.univ_mem)
  have hG : cyclicNoncollinear (cutArc p 0) := by
    intro i j k hij hjk hik
    exact hp.g1 (cyclicVertexEquiv (0 : Fin (n+2)) i) (cyclicVertexEquiv 0 j) (cyclicVertexEquiv 0 k)
      (fun hh => hij ((cyclicVertexEquiv 0).injective hh))
      (fun hh => hjk ((cyclicVertexEquiv 0).injective hh))
      (fun hh => hik ((cyclicVertexEquiv 0).injective hh))
  have hLeft : TraversalClosure.RemainingLeft (cutArc p 0) := by
    intro i
    change 0 < planarDet
      (cutArc p 0 i.castSucc.succ-cutArc p 0 i.castSucc.castSucc)
      (cutArc p 0 i.succ.succ-cutArc p 0 i.succ.castSucc)
    rw [cut_tangent,cut_tangent]
    have hn : edgeLabel (0 : Fin (n+2)) i.succ=cyclicSuccessor (edgeLabel 0 i.castSucc) :=
      edgeLabel_successor 0 i.castSucc
    rw [hn]
    exact hleftp _
  let D : Domain (cutArc p 0) := ⟨cutArc_regular p 0 hp,hG,closedAuxiliary_of_parent p 0 hp hEp hAp,
    hLeft,initial_exposed_all_support_core p 0 hp hEp hAp,L,hL,hT,hinc,hterm⟩
  have hcount' : Fintype.card (PolygonCrossing p)=Fintype.card (PolygonCrossing q) := hcount
  have hpIH : SmallerPolygonCornerIH p := by
    intro k P hP hlP hAP hcard
    exact hstrongIH P hP hlP hAP (hcount' ▸ hcard)
  have hf := physical_value_eq_marked_of_strongIH hRI p hp hleftp hEp hAp hpIH
    (cutArc p 0) D (positivePolygonMarkedState p hp (initialAnchorTraversal p hp))
    (MarkedParentTrace.nil _) (initial_cursor p hp hEp)
  have hg := MarkedG.uniform_initial_value_eq_corner hRI p hp hleftp hEp hAp
  have hinit := GammaM_eq_separatingSmoothingSum p 0 hp hEp hAp hRI
  change (-1 : ℚ)^(List.ofFn (cutArc p 0)).length*
    GammaM (cutArc p 0) (cutArc_regular p 0 hp) (closedAuxiliary_of_parent p 0 hp hEp hAp) = _ at hf
  rw [hinit,hg] at hf
  simpa only [List.length_ofFn,hν,hcoeff] using hf

end DirectGLSSW.HOMFLY.PhysicalCursorComparison


