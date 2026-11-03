import UniformLeftIdentity
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open GeometricSmoothingWeights PolygonDrawingBridge PrincipalTurning Coefficients
  SmoothingCornerGeometry PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable

/-- The original marked value has the prescribed corner, without exposure. -/
theorem uniform_left_marked_value_eq_corner
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (hAux : auxiliaryGenericity q hq) :
    MarkedG.value (positivePolygonMarkedState q hq (initialAnchorTraversal q hq))
      (positivePolygonEventDiagram_nArc_pos q hq) =
      coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
        (positivePolygonEventDiagram_nArc_pos q hq))
        (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
          |turnInteger (positivePolygonEventDiagram q hq)|) 0 := by
  obtain ⟨F,hF,hs,hvan,hcorner,hnegative⟩ := uniform_polygon_corner_evaluation hRI q hq hleft hAux
  exact hnegative.trans hcorner.symm

/-- The zero-crossing initial coefficient is one. This uses the actual marked
terminal theorem after the existing supporting chart, without an amplitude anchor. -/
theorem uniform_left_zero_crossing_corner_one
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (hAux : auxiliaryGenericity q hq) (hzero : Fintype.card (PolygonCrossing q)=0) :
    coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
      (positivePolygonEventDiagram_nArc_pos q hq))
      (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
        |turnInteger (positivePolygonEventDiagram q hq)|) 0 = 1 := by
  obtain ⟨m,Q,hQ,hAQ,hleftQ,heQ,hcount,hsum,hcoeff⟩ :=
    exists_uniform_exposed_primitive_corner_chart hRI q hq hleft hAux
  have hcount0 : (positivePolygonEventDiagram Q hQ).nCrossing=0 := hcount.trans hzero
  let s := positivePolygonMarkedState Q hQ (initialAnchorTraversal Q hQ)
  have hterminal : ∀ c : Fin s.1.nCrossing, ¬badAt s.2.1 c := by
    intro c
    have hlt := c.isLt
    change c.val < (positivePolygonEventDiagram Q hQ).nCrossing at hlt
    rw [hcount0] at hlt
    omega
  have hg := MarkedG.terminal_value Q hQ heQ s (.nil s) hterminal
  have hc := uniform_left_marked_value_eq_corner hRI Q hQ hleftQ hAQ
  exact hcoeff.symm.trans (hc.symm.trans hg)

/-- The middle marked value in nu_A(Q)=g_Q=c(Q), for the original polygon. -/
theorem uniform_left_primitive_eq_marked
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (hAux : auxiliaryGenericity q hq) :
    let ell := (Finset.univ.filter (fun i : Fin n => 0 < planarDet
      (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i)) (cyclicTangent q i))).card
    (-1 : ℚ)^ell*separatingSmoothingSum q hq hAux =
      (MarkedG.value (positivePolygonMarkedState q hq (initialAnchorTraversal q hq))
        (positivePolygonEventDiagram_nArc_pos q hq) : ℚ) := by
  exact (uniform_left_primitive_corner_identity hRI q hq hleft hAux).trans
    (congrArg (fun z : ℤ => (z : ℚ)) (uniform_left_marked_value_eq_corner hRI q hq hleft hAux).symm)

/-- Both original initial calculations equal one when there are no crossings. -/
theorem uniform_left_zero_crossing_values
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (hAux : auxiliaryGenericity q hq) (hzero : Fintype.card (PolygonCrossing q)=0) :
    ((-1 : ℚ)^n*separatingSmoothingSum q hq hAux=1) ∧
      MarkedG.value (positivePolygonMarkedState q hq (initialAnchorTraversal q hq))
        (positivePolygonEventDiagram_nArc_pos q hq)=1 := by
  have hc := uniform_left_zero_crossing_corner_one hRI q hq hleft hAux hzero
  have hp := uniform_left_primitive_corner_identity hRI q hq hleft hAux
  dsimp only at hp
  rw [uniform_left_count q hleft,hc] at hp
  exact ⟨by simpa only [Int.cast_one] using hp,
    (uniform_left_marked_value_eq_corner hRI q hq hleft hAux).trans hc⟩

end DirectGLSSW.HOMFLY.PhysicalCursorComparison
