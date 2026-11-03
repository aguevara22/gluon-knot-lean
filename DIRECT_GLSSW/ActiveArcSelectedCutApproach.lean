import ActiveArcParentFarProjector
import ActiveArcPreFirstSelectedCut

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.TinyParentFarProjector
open Cursor Split SingletonWords Primitive CompatibleWords OpenFirstEdgeGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Conditional actual pre-event selected-cut value. All motion and smoothing
identifications are proved; physical far-nonzero remains an explicit domain premise. -/
theorem exists_pre_first_selectedCut_constant
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hAux : Primitive.ClosedAuxiliary q hR) (hRI : GLSSWRootIndependence)
    (hfar : ∀ T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut),
      ∀ k j, 1<k → k<j → j≤RetainedWords.openCount (parent q c hcut)
        (regular_parent q hR c hcut) T.val →
        polygonHDet (fun k => if k=0 then q 0 else
          rootedPolygonWord (Primitive.OpenVertex (parent q c hcut)
            (regular_parent q hR c hcut) T)
            (RetainedWords.openLast (parent q c hcut) (regular_parent q hR c hcut) T.val)
            (k-1)) 1 k j ≠ 0) :
    ∃ (r : ℝ) (_hr : 0<r) (hr1 : r≤1), ∀ (ε : ℝ) (he : 0<ε) (her : ε<r),
    let t := leftParameter q c*(1-ε)
    let bounds := approach_parameter_bounds q c ε he (lt_of_lt_of_le her hr1)
    let qm := moveStart q t
    let hm := before_first_regular q hR c hc t bounds.1 bounds.2
    let C := crossingFromOriginal q t (lt_trans bounds.2 (leftParameter_spec q c).2.1)
      c (survives_before_first q c hc t bounds.2 c)
    let hAm := BeforeFirst.closedAuxiliary q hR c hc t bounds.1 bounds.2 hAux
    (∑ U : {U : Primitive.Support qm hm // C ∈ U.val},
      (-1 : ℚ)^U.val.val.card *
        (Primitive.openCurrent qm hm U.val *
          ∏ D ∈ Finset.univ.erase (openComponent qm hm.noTriple U.val.val),
            Primitive.closedWeight qm hm hAm U.val D)) =
      ((1+scalarSignValue (planarDet (q 1-q 0)
        (q c.val.2.succ-q c.val.2.castSucc)))/2) *
        (GeometricSmoothingWeights.separatingSmoothingSum
          (child q hR c hc.1 hcut)
          (child_cyclicGeneric_of_closedAuxiliary q hR c hc.1 hcut hAux)
          (child_auxiliaryGenericity q hR c hc hcut hAux) *
          Primitive.GammaM (parent q c hcut) (regular_parent q hR c hcut)
            (parent_closedAuxiliary q hR c hc hcut hAux)) := by
  obtain ⟨r,hr,hr1,hgood⟩ := exists_weighted_parent_projector q hR c hc hcut hAux hfar
  refine ⟨r,hr,hr1,?_⟩
  intro ε he her
  let t := leftParameter q c*(1-ε)
  have bounds := approach_parameter_bounds q c ε he (lt_of_lt_of_le her hr1)
  have hf := gammaM_selectedCut_before_first q hR c hc hcut hAux hRI t bounds.1 bounds.2
  have hp := hgood ε he her
  simp only [parent_prefix_approach_endpoint q hR c hc hcut] at hp
  dsimp only
  rw [hf,hp]
  ring

end DirectGLSSW.ActiveArc.TinyParentFarProjector
