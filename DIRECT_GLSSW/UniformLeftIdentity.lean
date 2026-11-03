import UniformExposedIdentity
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open GeometricSmoothingWeights PolygonDrawingBridge PrincipalTurning Coefficients
attribute [local instance] Classical.propDecidable

/-- A supporting truncation and actual cyclic restart remove exposure from the
inductive step, preserving crossing count, signed primitive and exact corner. -/
theorem uniform_identity_of_strongIH
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (hAux : auxiliaryGenericity q hq) (hstrongIH : SmallerPolygonCornerIH q) :
    (-1 : ℚ)^n*separatingSmoothingSum q hq hAux =
      coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
        (positivePolygonEventDiagram_nArc_pos q hq))
        (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
          |turnInteger (positivePolygonEventDiagram q hq)|) 0 := by
  obtain ⟨m,Q,hQ,hAQ,hleftQ,heQ,hcount,hsum,hcoeff⟩ :=
    exists_uniform_exposed_primitive_corner_chart hRI q hq hleft hAux
  have hcount' : Fintype.card (PolygonCrossing Q)=Fintype.card (PolygonCrossing q) := hcount
  have hQIH : SmallerPolygonCornerIH Q := by
    intro k P hP hlP hAP hcard
    exact hstrongIH P hP hlP hAP (hcount' ▸ hcard)
  have hf := exposed_identity_of_strongIH hRI Q hQ hleftQ heQ hAQ hQIH
  exact hsum.symm.trans (hf.trans (congrArg (fun z : ℤ => (z : ℚ)) hcoeff))

/-- The full primitive/corner identity for every uniformly left-turning polygon
on the source auxiliary domain. The outer induction is discharged here. -/
theorem uniform_left_primitive_corner_identity
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (hAux : auxiliaryGenericity q hq) :
    let ell := (Finset.univ.filter (fun i : Fin n => 0 < planarDet
      (cyclicTangent q ((cyclicSuccessorPerm n)⁻¹ i)) (cyclicTangent q i))).card
    (-1 : ℚ)^ell*separatingSmoothingSum q hq hAux =
      coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
        (positivePolygonEventDiagram_nArc_pos q hq))
        (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
          |turnInteger (positivePolygonEventDiagram q hq)|) 0 := by
  have H : ∀ N : ℕ, ∀ {k : ℕ} (P : Fin k → PlanarPoint ℝ) (hP : CyclicGeneric P)
      (hlP : ∀ i, 0 < planarDet (cyclicTangent P i) (cyclicTangent P (cyclicSuccessor i)))
      (hAP : auxiliaryGenericity P hP),
      Fintype.card (PolygonCrossing P)=N →
      (-1 : ℚ)^k*separatingSmoothingSum P hP hAP =
        coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram P hP)
          (positivePolygonEventDiagram_nArc_pos P hP))
          (1-((positivePolygonEventDiagram P hP).nCrossing : ℤ)-
            |turnInteger (positivePolygonEventDiagram P hP)|) 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro k P hP hlP hAP hcard
      apply uniform_identity_of_strongIH hRI P hP hlP hAP
      intro j Q hQ hlQ hAQ hlt
      have hsmall := ih (Fintype.card (PolygonCrossing Q)) (hcard ▸ hlt) Q hQ hlQ hAQ rfl
      dsimp only
      rw [uniform_left_count Q hlQ]
      exact hsmall
  dsimp only
  rw [uniform_left_count q hleft]
  exact H (Fintype.card (PolygonCrossing q)) q hq hleft hAux rfl

end DirectGLSSW.HOMFLY.PhysicalCursorComparison


