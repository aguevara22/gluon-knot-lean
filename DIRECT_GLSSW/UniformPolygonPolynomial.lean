import UniformSupportingChart
import ExposedUniformPolynomialStep
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open PermutationOrbits LowestRowContract FramedPolynomial Coefficients PrincipalTurning
open GeometricSmoothingWeights
attribute [local instance] Classical.propDecidable

/-- The actual framed row of every uniformly-left polygon on the source AUX
domain is framedVariable times an ordinary integer polynomial. Exposure and
all smaller-child certificates are produced internally. -/
theorem uniform_polygon_framed_polynomial
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (hAux : auxiliaryGenericity q hq) :
    ∃ F : Polynomial ℤ,
      framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
        (positivePolygonEventDiagram_nArc_pos _ _)
        (componentOf (positivePolygonEventDiagram q hq).continuation ⟨0,positivePolygonEventDiagram_nArc_pos _ _⟩) =
      framedVariable * polynomialValue F := by
  suffices hall : ∀ k : ℕ, ∀ {m : ℕ} (Q : Fin m → PlanarPoint ℝ) (hQ : CyclicGeneric Q),
      (∀ i, 0 < planarDet (cyclicTangent Q i) (cyclicTangent Q (cyclicSuccessor i))) →
      auxiliaryGenericity Q hQ → (positivePolygonEventDiagram Q hQ).nCrossing = k →
      ∃ F : Polynomial ℤ,
        framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram Q hQ)
          (positivePolygonEventDiagram_nArc_pos _ _)
          (componentOf (positivePolygonEventDiagram Q hQ).continuation ⟨0,positivePolygonEventDiagram_nArc_pos _ _⟩) =
        framedVariable * polynomialValue F from
    hall _ q hq hleft hAux rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro m Q hQ hl hA hk
    obtain ⟨r,P,hP,hlP,hAP,heP,hcount,hrow⟩ := exists_uniform_exposed_chart hRI Q hQ hl hA
    have hsmall : ∀ {l : ℕ} (Z : Fin l → PlanarPoint ℝ) (hZ : CyclicGeneric Z),
        (∀ i, 0 < planarDet (cyclicTangent Z i) (cyclicTangent Z (cyclicSuccessor i))) →
        auxiliaryGenericity Z hZ →
        (positivePolygonEventDiagram Z hZ).nCrossing < (positivePolygonEventDiagram P hP).nCrossing →
        ∃ F : Polynomial ℤ,
          framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram Z hZ)
            (positivePolygonEventDiagram_nArc_pos _ _)
            (componentOf (positivePolygonEventDiagram Z hZ).continuation ⟨0,positivePolygonEventDiagram_nArc_pos _ _⟩) =
          framedVariable * polynomialValue F := by
      intro l Z hZ hlZ hAZ hlt
      apply ih (positivePolygonEventDiagram Z hZ).nCrossing _ Z hZ hlZ hAZ rfl
      exact hlt.trans_eq (hcount.trans hk)
    obtain ⟨F,hF⟩ := exposed_uniform_polynomial_of_smaller P hP hlP heP hAP hsmall
    exact ⟨F,hrow.trans hF⟩
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
