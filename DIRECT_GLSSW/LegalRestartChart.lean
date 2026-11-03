import UniformPrimitiveChart
import ActiveArcCutGeometry
import PolygonRebaseGeometry

set_option autoImplicit false
noncomputable section

namespace DirectGLSSW.SourceLegalHistoryGenericity

open DirectGLSSW DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW.PolygonRebase
open DirectGLSSW.GeometricSmoothingWeights
open DirectGLSSW.ExposedOpenPrimitive
open DirectGLSSW.HOMFLY.Gemini
open DirectGLSSW.HOMFLY.Coefficients
open DirectGLSSW.HOMFLY.PrincipalTurning
open DirectGLSSW.TruncationDirection

private theorem cyclicVertexEquiv_succRoot {N : ℕ} (root i : Fin N) :
    cyclicVertexEquiv (cyclicSuccessor root) i =
      cyclicSuccessor (cyclicVertexEquiv root i) := by
  have hrel := cyclicVertexIndex_relabel (cyclicSuccessorPerm N)
    (by intro e; simp only [cyclicSuccessorPerm_apply]) root i.val
  change cyclicSuccessor (cyclicVertexIndex root i.val) =
    cyclicVertexIndex (cyclicSuccessor root) i.val at hrel
  exact hrel.symm

private theorem cyclicVertexEquiv_zero {N : ℕ} (hN : 0 < N) (i : Fin N) :
    cyclicVertexEquiv (⟨0,hN⟩ : Fin N) i = cyclicSuccessor i := by
  apply Fin.ext
  simp [cyclicVertexEquiv, cyclicVertexIndex, cyclicSuccessor, Nat.add_comm]

/-- Cutting the cyclically rebased polygon at vertex zero is literally the
same open point word as cutting the unrebased polygon at the selected edge. -/
theorem cutArc_atEdge_eq {m : ℕ} (T : Fin (m+2) → PlanarPoint ℝ)
    (e : Fin (m+2)) :
    cutArc (T ∘ atEdge e) (0 : Fin (m+2)) = cutArc T e := by
  funext i
  change T (atEdge e (cyclicVertexEquiv 0 i)) = T (cyclicVertexEquiv e i)
  congr 1
  let pred := (cyclicSuccessorPerm (m+2)).symm e
  have hpred : cyclicSuccessor pred = e :=
    (cyclicSuccessorPerm (m+2)).apply_symm_apply e
  change cyclicVertexEquiv pred
    (cyclicVertexEquiv (⟨0, by omega⟩ : Fin (m+2)) i) = cyclicVertexEquiv e i
  rw [cyclicVertexEquiv_zero (by omega) i,
    cyclicVertexEquiv_commutes_successor pred i]
  rw [← hpred, cyclicVertexEquiv_succRoot pred i]

/-- Keep the actual truncation parameters and the rebased polygon in the
uniform exposed chart witness. This is the chart-level source provenance needed
to identify `cutArc Q 0` with the literal truncated child arc. -/
theorem exists_uniform_exposed_primitive_corner_chart_with_truncation
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0 < planarDet (cyclicTangent q i)
      (cyclicTangent q (cyclicSuccessor i)))
    (hAux : auxiliaryGenericity q hq) :
    ∃ a p : Fin n, cyclicSuccessor p = a ∧
    ∃ scale : ℝ, 0 < scale ∧ ∃ δ : ℝ, 0 < δ ∧
    let ε := δ / 2
    let T := truncateCyclicCorner q a p scale ε
    ε > 0 ∧ ε < δ ∧ ε < 1 ∧ ε * scale < 1 ∧
    ∃ hT : CyclicGeneric T,
    ∃ hAuxT : auxiliaryGenericity T hT,
      (∀ i, 0 < planarDet (cyclicTangent T i)
        (cyclicTangent T (cyclicSuccessor i))) ∧
      LeftExposed T a.castSucc ∧
      polygonAmplitude T hT = -polygonAmplitude q hq ∧
      separatingSmoothingSum T hT hAuxT = -separatingSmoothingSum q hq hAux ∧
      (-1 : ℚ)^(n+1) * separatingSmoothingSum T hT hAuxT =
        (-1 : ℚ)^n * separatingSmoothingSum q hq hAux ∧
      ∃ Q : Fin (n+1) → PlanarPoint ℝ, Q = T ∘ atEdge a.castSucc ∧
      ∃ hQ : CyclicGeneric Q,
      ∃ hAuxQ : auxiliaryGenericity Q hQ,
        (∀ i, 0 < planarDet (cyclicTangent Q i)
          (cyclicTangent Q (cyclicSuccessor i))) ∧
        LeftExposed Q 0 ∧
        (positivePolygonEventDiagram Q hQ).nCrossing =
          (positivePolygonEventDiagram q hq).nCrossing ∧
        (-1 : ℚ)^(n+1) * separatingSmoothingSum Q hQ hAuxQ =
          (-1 : ℚ)^n * separatingSmoothingSum q hq hAux ∧
        coeff (DirectGLSSW.HOMFLY.Gemini.candidateEvaluator (positivePolygonEventDiagram Q hQ)
          (positivePolygonEventDiagram_nArc_pos Q hQ))
          (1-((positivePolygonEventDiagram Q hQ).nCrossing : ℤ)-
            |turnInteger (positivePolygonEventDiagram Q hQ)|) 0 =
        coeff (DirectGLSSW.HOMFLY.Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
          (positivePolygonEventDiagram_nArc_pos q hq))
          (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
            |turnInteger (positivePolygonEventDiagram q hq)|) 0 := by
  obtain ⟨a,p,hp,scale,hs,δ,hδ,hfamily⟩ :=
    exists_supporting_truncation_preserves_nu_and_corner hRI q hq hleft hAux
  let ε : ℝ := δ / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεδ : ε < δ := by dsimp [ε]; linarith
  obtain ⟨hε1,hs1,hT,hAuxT,hleftT,heT,hamp,hsum,hnu,hcount,hturn,hdegree,heval,hcoeff⟩ :=
    hfamily ε hε hεδ
  let T := truncateCyclicCorner q a p scale ε
  let ρ := atEdge a.castSucc
  let Q := T ∘ ρ
  let hQ : CyclicGeneric Q := cyclicGeneric_relabel T ρ (atEdge_commutes_successor _) hT
  let hAuxQ : auxiliaryGenericity Q hQ :=
    auxiliaryGenericity_relabel T hT ρ (atEdge_commutes_successor _) hAuxT
  have hleftQ := strictLeft_relabel T ρ (atEdge_commutes_successor _) hleftT
  have heQ : LeftExposed Q 0 := by
    apply leftExposed_relabel T ρ (atEdge_commutes_successor _)
    have hz : ρ (0 : Fin (n+1)) = a.castSucc := atEdge_zero a.castSucc (by omega)
    rw [hz]
    exact heT
  have hcountQ := positiveDiagram_crossingCount T ρ (atEdge_commutes_successor _) hT
  have hturnQ := turnInteger_relabel T hT ρ (atEdge_commutes_successor _)
  have hH := candidateEvaluator_relabel T hT ρ (atEdge_commutes_successor _)
  have hnuQ := vertexParity_normalizedPrimitive_relabel T ρ
    (atEdge_commutes_successor _) hT hRI hAuxT
  refine ⟨a,p,hp,scale,hs,δ,hδ,?_⟩
  dsimp [ε,T]
  refine ⟨hε,hεδ,hε1,hs1,hT,hAuxT,hleftT,heT,hamp,hsum,hnu,?_⟩
  have hnuChart :
      (-1 : ℚ)^(n+1) * separatingSmoothingSum Q hQ hAuxQ =
        (-1 : ℚ)^n * separatingSmoothingSum q hq hAux := by
    calc
      (-1 : ℚ)^(n+1) * separatingSmoothingSum Q hQ hAuxQ =
          (-1 : ℚ)^(n+1) * separatingSmoothingSum T hT hAuxT := by
        simpa [Q] using hnuQ
      _ = (-1 : ℚ)^n * separatingSmoothingSum q hq hAux := hnu
  have hcountChart :
      (positivePolygonEventDiagram Q hQ).nCrossing =
        (positivePolygonEventDiagram q hq).nCrossing := by
    calc
      (positivePolygonEventDiagram Q hQ).nCrossing =
          (positivePolygonEventDiagram T hT).nCrossing := by
        simpa [Q] using hcountQ
      _ = (positivePolygonEventDiagram q hq).nCrossing := by
        simpa [T] using hcount.symm
  have hturnChart :
      turnInteger (positivePolygonEventDiagram Q hQ) =
        turnInteger (positivePolygonEventDiagram q hq) := by
    calc
      turnInteger (positivePolygonEventDiagram Q hQ) =
          turnInteger (positivePolygonEventDiagram T hT) := by
        simpa [Q] using hturnQ
      _ = turnInteger (positivePolygonEventDiagram q hq) := by
        simpa [T] using hdegree
  refine ⟨Q,rfl,hQ,hAuxQ,hleftQ,heQ,hcountChart,hnuChart,?_⟩
  change coeff (candidateEvaluator (positivePolygonEventDiagram (T ∘ ρ) hQ)
      (positivePolygonEventDiagram_nArc_pos (T ∘ ρ) hQ))
      (1-((positivePolygonEventDiagram (T ∘ ρ) hQ).nCrossing : ℤ)-
        |turnInteger (positivePolygonEventDiagram (T ∘ ρ) hQ)|) 0 =
    coeff (candidateEvaluator (positivePolygonEventDiagram q hq)
      (positivePolygonEventDiagram_nArc_pos q hq))
      (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
        |turnInteger (positivePolygonEventDiagram q hq)|) 0
  rw [hH,hcountQ,hturnQ]
  simpa [T] using hcoeff.symm

end DirectGLSSW.SourceLegalHistoryGenericity



