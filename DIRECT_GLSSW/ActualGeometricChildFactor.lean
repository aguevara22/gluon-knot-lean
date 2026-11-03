import GeometricCursorOrientation
import PhysicalSelectedChildCorner
import ActualFiniteCalculation
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry ProcessedExposedChild
open ActiveArc ActiveArc.Cursor ActiveArc.Split ActiveArc.ExposedChart ExposedOpenPrimitive
open ActiveArc.SingletonWords ActiveArc.CompatibleWords
open Coefficients PrincipalTurning GeometricSmoothingWeights
attribute [local instance] Classical.propDecidable

private theorem left_of_word {r s : ℕ} (P : Fin r → PlanarPoint ℝ) (Q : Fin s → PlanarPoint ℝ)
    (hw : List.ofFn P=List.ofFn Q)
    (hl : ∀ i, 0<planarDet (cyclicTangent P i) (cyclicTangent P (cyclicSuccessor i))) :
    ∀ i, 0<planarDet (cyclicTangent Q i) (cyclicTangent Q (cyclicSuccessor i)) := by
  obtain ⟨hn,hpts⟩ := pointWord_eq_of_ofFn_eq P Q hw
  subst s
  have heq : P=Q := by funext i; exact hpts i
  subst Q
  exact hl

private theorem card_of_word {r s : ℕ} (P : Fin r → PlanarPoint ℝ) (Q : Fin s → PlanarPoint ℝ)
    (hw : List.ofFn P=List.ofFn Q) :
    Fintype.card (PolygonCrossing P)=Fintype.card (PolygonCrossing Q) := by
  obtain ⟨hn,hpts⟩ := pointWord_eq_of_ofFn_eq P Q hw
  subst s
  have heq : P=Q := by funext i; exact hpts i
  subst Q
  rfl

/-- The exact detached factor in the actual physical under step, at the supplied
geometric cursor, equals the actual marked parent's canonical detached value.
The only induction premise is the stated smaller-original-crossing hypothesis. -/
theorem GeometricCursor.detached_factor_of_strongIH {n a b : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q) (he : LeftExposed q 0)
    (hRI : GLSSWRootIndependence)
    (hleft : ∀ i, 0<planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (hAux : auxiliaryGenericity q hq)
    (p : Fin (a+b+2) → PlanarPoint ℝ) (t : MarkedParentState)
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (G : GeometricCursor q hq p t h) (D : FiniteCalculation.Domain p)
    (c : Crossing p) (hc : FirstCrossing p c) (hcut : c.val.2.val=a)
    (hu : crossingUnder p (polygonCrossingOfArc p c)=(polygonCrossingOfArc p c).val.1)
    (hstrongIH : ∀ {k : ℕ} (P : Fin k → PlanarPoint ℝ) (hP : CyclicGeneric P)
      (hleftP : ∀ i, 0<planarDet (cyclicTangent P i) (cyclicTangent P (cyclicSuccessor i)))
      (hAuxP : auxiliaryGenericity P hP)
      (hcard : Fintype.card (PolygonCrossing P)<Fintype.card (PolygonCrossing q)),
      let ell := (Finset.univ.filter (fun i : Fin k =>
        0<planarDet (cyclicTangent P ((cyclicSuccessorPerm k)⁻¹ i)) (cyclicTangent P i))).card
      (-1:ℚ)^ell * separatingSmoothingSum P hP hAuxP =
        coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram P hP)
          (positivePolygonEventDiagram_nArc_pos P hP))
          (1-((positivePolygonEventDiagram P hP).nCrossing:ℤ)-
            |turnInteger (positivePolygonEventDiagram P hP)|) 0) :
    let Q := child p D.hR c hc.1 hcut
    let ell := (Finset.univ.filter (fun i : Fin (a+1) =>
      0<planarDet (cyclicTangent Q ((cyclicSuccessorPerm (a+1))⁻¹ i)) (cyclicTangent Q i))).card
    (-1:ℚ)^ell * separatingSmoothingSum Q
      (child_cyclicGeneric_of_closedAuxiliary p D.hR c hc.1 hcut D.hAux)
      (child_auxiliaryGenericity p D.hR c hc hcut D.hAux) =
        (MarkedG.detachedValue t ((G.crossingEquiv he) c).val:ℚ) := by
  have hb := G.under_bad he c hu
  rcases G with ⟨k,B,A,hs,θ,h0,h1,hcarrier,hlo,hhi,rfl⟩
  let phys := moveStart (suffixWord (cutArc q 0) A (a+b) hs) θ
  let F := boundaryPhysicalCrossingEquiv q hq he h k B A (a+b) hs θ hcarrier hlo hhi
  let d := (F c).val
  change badAt t.2.1 d at hb
  have horigin := (boundaryPhysicalCrossingEquiv_origin q hq he h k B A (a+b) hs θ
    hcarrier hlo hhi c).symm
  obtain ⟨hPcorner,hcorner⟩ := detachedValue_eq_physical_child_corner_of_selected_origin
    q hq he h d hb hRI hleft hAux hs θ h0 h1 D.hR c hc.1 hcut horigin
  let Q := child phys D.hR c hc.1 hcut
  let hP := child_cyclicGeneric_of_closedAuxiliary phys D.hR c hc.1 hcut D.hAux
  let hAuxP := child_auxiliaryGenericity phys D.hR c hc hcut D.hAux
  let hAuxCut := closedAuxiliary_of_parent q 0 hq he hAux
  let R := canonicalDetachedRestriction t d
  let H := historicalSharpPolygon q hq h d hb R
  obtain ⟨hH,hleftH,hcount,_,_⟩ := canonical_actual_recursive_child q hq h d hb hleft he hAuxCut
  have hw := historicalSharpPolygon_eq_physical_child_of_selected_origin
    q hq he h d hb R hAuxCut hs θ h0 h1 D.hR c hc.1 hcut horigin
  have hleftQ := left_of_word H Q hw hleftH
  have hcardTraceFin : Fintype.card (Fin t.1.nCrossing) ≤
      Fintype.card (Fin (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)).1.nCrossing) :=
    Fintype.card_le_of_injective h.crossingOrigin h.crossingOrigin.injective
  have hcardTrace : t.1.nCrossing ≤ Fintype.card (PolygonCrossing q) := by
    simpa [Fintype.card_fin,positivePolygonMarkedState,positivePolygonEventDiagram,
      PolygonDrawingBridge.Cr] using hcardTraceFin
  have hcardQ : Fintype.card (PolygonCrossing Q)<Fintype.card (PolygonCrossing q) := by
    rw [← card_of_word H Q hw]
    exact lt_of_lt_of_le hcount hcardTrace
  have hfactor := hstrongIH Q hP hleftQ hAuxP hcardQ
  exact hfactor.trans (congrArg (fun z:ℤ => (z:ℚ)) hcorner.symm)


end DirectGLSSW.HOMFLY.PhysicalCursorComparison
