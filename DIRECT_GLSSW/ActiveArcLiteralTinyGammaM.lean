import ActiveArcLiteralTinyOpenCurrent
import ActiveArcTinyParentClosedTransport

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive RetainedWords CompatibleWords OpenFirstEdgeGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Actual tiny-parent GammaM, reindexed over genuine parent supports, with
the complete physical closed product and actual retained open current. -/
theorem tinyParent_GammaM_eq_weighted_approach
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (η : ℝ) (hη : 0<η) (hη1 : η<1)
    (hRI : GLSSWRootIndependence) (hAux : ClosedAuxiliary q hR) :
    GammaM (tinyParent q c hcut η) (regular_tinyParent q hR c hc hcut η hη hη1)
      (tinyParent_closedAuxiliary_from_original q hR c hc hcut η hη hη1 hAux) =
    ∑ T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut),
      (-1:ℚ)^T.val.card *
      (OpenMarkedCurrent.entry (polygonSignArray
        (approach (fun k => if k=0 then q 0 else
          rootedPolygonWord (OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T)
            (openLast (parent q c hcut) (regular_parent q hR c hcut) T.val) (k-1)) η))
          0 (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val) *
        ∏ C∈Finset.univ.erase (openComponent (parent q c hcut)
          (regular_parent q hR c hcut).noTriple T.val),
          closedWeight (parent q c hcut) (regular_parent q hR c hcut)
            (parent_closedAuxiliary q hR c hc hcut hAux) T C) := by
  unfold GammaM
  symm
  apply Fintype.sum_equiv (tinyParentSupportEquiv q hR c hc hcut η hη hη1).symm
  intro T
  rw [←tinySupportOfParent_eq_supportEquiv_symm q hR c hc hcut η hη hη1 T]
  rw [tinyParent_openCurrent_eq_approach q hR c hc hcut η hη hη1 T]
  rw [tinyParent_closedWeight_product_eq_from_original q hR c hc hcut η hη hη1 hRI hAux T]
  rw [show (tinySupportOfParent q hR c hc hcut η hη hη1 T).val.card=T.val.card from
    parentTinySelection_card q c hcut η T.val]
  rfl

end DirectGLSSW.ActiveArc.LiteralTinyParent
