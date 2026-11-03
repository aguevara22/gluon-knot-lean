import PhysicalParentFutureFilter
import PhysicalParentOriginalSuffix
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalParentHistory
open PermutationOrbits LowestRowContract ProcessedParentMarks MarkedG
open SmoothingCornerGeometry
open PolygonDrawingBridge PolygonDrawing ActiveArc ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable

/-- Actual physical parent crossings, matched to original strict-future crossings. -/
def exposedParentFutureEquiv {a b : Nat} (q : Fin (a+b+2) → PlanarPoint Real)
    (hq : CyclicGeneric q) (he : LeftExposed q 0)
    (z : Crossing (cutArc q 0)) (hcut : z.val.2.val=a) :
    Crossing (Split.parent (cutArc q 0) z hcut) ≃
      StrictFutureCrossing (positivePolygonMarkedState q hq (initialAnchorTraversal q hq))
        ((positivePolygonEventDiagram q hq).incoming (crossingFin q (exposedCrossingEquiv q 0 hq he z)) 1) :=
  Equiv.ofBijective
    (fun d => ⟨crossingFin q (exposedCrossingEquiv q 0 hq he
      (Split.parentCrossingToOriginal (cutArc q 0) z hcut d)),
      (exposed_parent_filter q hq he z _ hcut).mp
        (Split.parentCrossingToOriginal_inParent _ (cutArc_regular q 0 hq) z hcut d)⟩) (by
      constructor
      · intro d e hh
        exact Split.parentCrossingToOriginal_injective _ z hcut
          ((exposedCrossingEquiv q 0 hq he).injective ((crossingFin q).injective (congrArg Subtype.val hh)))
      · intro d
        let w := (exposedCrossingEquiv q 0 hq he).symm ((crossingFin q).symm d.val)
        have hw : Split.InParent (a:=a) (b:=b) (cutArc q 0) z w := by
          apply (exposed_parent_filter q hq he z w hcut).mpr
          simpa only [w,Equiv.apply_symm_apply] using d.property
        obtain ⟨e,heq⟩ := (Split.parentCrossing_range _ (cutArc_regular q 0 hq) z hcut w).mpr hw
        refine ⟨e,Subtype.ext ?_⟩
        change crossingFin q (exposedCrossingEquiv q 0 hq he
          (Split.parentCrossingToOriginal _ z hcut e)) = d.val
        rw [heq]
        simp only [w,Equiv.apply_symm_apply])

/-- The selected original open crossing is constructed from actual history ancestry. -/
def selectedOriginalOpenCrossing {n : Nat} (q : Fin (n+2) → PlanarPoint Real)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) : Crossing (cutArc q 0) :=
  (exposedCrossingEquiv q 0 hq he).symm ((crossingFin q).symm (h.crossingOrigin c))

@[simp] theorem selectedOriginalOpenCrossing_origin {n : Nat} (q : Fin (n+2) → PlanarPoint Real)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) :
    crossingFin q (exposedCrossingEquiv q 0 hq he (selectedOriginalOpenCrossing q hq he h c)) =
      h.crossingOrigin c := by simp only [selectedOriginalOpenCrossing,Equiv.apply_symm_apply]

/-- Actual continuing parent future crossings equal the literal physical parent
carrier. The parent's old root, switches and processed prefix remain untouched. -/
def physicalContinuingParentCrossingEquiv {a b : Nat} (q : Fin (a+b+2) → PlanarPoint Real)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) (hgood : GoodBefore t c)
    (hcut : (selectedOriginalOpenCrossing q hq he h c).val.2.val=a) :
    Crossing (Split.parent (cutArc q 0) (selectedOriginalOpenCrossing q hq he h c) hcut) ≃
      StrictFutureCrossing (continuingState t c hc hgood) (connector t c) := by
  let E := exposedParentFutureEquiv q hq he (selectedOriginalOpenCrossing q hq he h c) hcut
  have hb := history_selected_branch_zero q hq h c hc
  let F : Crossing (Split.parent (cutArc q 0) (selectedOriginalOpenCrossing q hq he h c) hcut) →
      StrictFutureCrossing (positivePolygonMarkedState q hq (initialAnchorTraversal q hq))
        ((positivePolygonEventDiagram q hq).incoming (h.crossingOrigin c)
          (otherBranch (firstVisitedBranch t.2.1 c))) := fun d => ⟨(E d).val,by
            have hm := (E d).property
            simpa only [selectedOriginalOpenCrossing_origin,hb,otherBranch,Fin.isValue,ite_true] using hm⟩
  have hF : Function.Bijective F := by
    constructor
    · intro d e hh
      apply E.injective
      apply Subtype.ext
      have hv := congrArg (fun x => x.val) hh
      change (E d).val=(E e).val at hv
      exact hv
    · intro d
      have hd : ∀ i : Fin 2,
          visitPosition (initialAnchorTraversal q hq)
            ((positivePolygonEventDiagram q hq).incoming
              (crossingFin q (exposedCrossingEquiv q 0 hq he (selectedOriginalOpenCrossing q hq he h c))) 1) <
          visitPosition (initialAnchorTraversal q hq)
            ((positivePolygonEventDiagram q hq).incoming d.val i) := by
        rw [selectedOriginalOpenCrossing_origin]
        simpa only [hb,otherBranch,Fin.isValue,ite_true] using d.property
      obtain ⟨e,heq⟩ := E.surjective ⟨d.val,hd⟩
      refine ⟨e,Subtype.ext ?_⟩
      have hv := congrArg (fun x => x.val) heq
      change (F e).val=d.val
      exact hv
  exact (Equiv.ofBijective F hF).trans (continuingFutureCrossingEquiv h c hc hgood).symm
end DirectGLSSW.HOMFLY.PhysicalParentHistory
