import PhysicalSuffixChildWord
import HistoricalChildOffsetWord
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedExposedChild
open DirectGLSSW PermutationOrbits LowestRowContract PolygonDrawingBridge SmoothingCornerGeometry
open ActiveArc ActiveArc.Cursor ActiveArc.Split ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable
variable {n A B a b : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (he : LeftExposed q 0) {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

theorem resized_physical_child_word (hs : A+(a+b)=n) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1)
    (hM : Regular (moveStart (suffixWord (cutArc q 0) A (a+b) hs) θ))
    (d : Crossing (moveStart (suffixWord (cutArc q 0) A (a+b) hs) θ))
    (hd0 : d.val.1=0) (hdcut : d.val.2.val=a) :
    List.ofFn (child (moveStart (suffixWord (cutArc q 0) A (a+b) hs) θ) hM d hd0 hdcut) =
      ActiveArc.crossingPoint (cutArc q 0)
        (suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq)
          A (a+b) hs θ h0 h1 d).val ::
      List.ofFn (fun i : Fin a => cutArc q 0 ⟨A+i.val+1,by omega⟩) := by
  subst n
  exact ActiveArc.PhysicalKnotSplit.physical_child_suffix_word _ _ θ h0 h1 hM d hd0 hdcut

/-- The original event identity selects the same crossing in both carriers.
The point-list equality is derived, rather than supplied as an input. -/
theorem historicalSharpPolygon_eq_physical_child_of_selected_origin
    (hAux : Primitive.ClosedAuxiliary (cutArc q 0) (cutArc_regular q 0 hq))
    (hs : A+(a+b)=n) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1)
    (hM : Regular (moveStart (suffixWord (cutArc q 0) A (a+b) hs) θ))
    (d : Crossing (moveStart (suffixWord (cutArc q 0) A (a+b) hs) θ))
    (hd0 : d.val.1=0) (hdcut : d.val.2.val=a)
    (horigin : crossingFin q (exposedCrossingEquiv q 0 hq he
      (suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq)
        A (a+b) hs θ h0 h1 d).val) = h.crossingOrigin c) :
    List.ofFn (historicalSharpPolygon q hq h c hc R) =
      List.ofFn (child (moveStart (suffixWord (cutArc q 0) A (a+b) hs) θ)
        hM d hd0 hdcut) := by
  have hmap : (suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq)
        A (a+b) hs θ h0 h1 d).val = openingCrossing q hq he h c := by
    apply (exposedCrossingEquiv q 0 hq he).injective
    apply (crossingFin q).injective
    simpa only [openingCrossing,Equiv.apply_symm_apply] using horigin
  have hl : (openingCrossing q hq he h c).val.1.val=A := by
    rw [← hmap,suffixWordCrossingEquiv_left_label,hd0]
    simp
  have hr : (openingCrossing q hq he h c).val.2.val=A+a := by
    rw [← hmap,suffixWordCrossingEquiv_right_label,hdcut]
  have hlen : (openingCrossing q hq he h c).val.2.val-
      (openingCrossing q hq he h c).val.1.val=a := by omega
  rw [historicalSharpPolygon_offset_word_eq q hq he h c hc R hAux]
  rw [resized_physical_child_word q hq hs θ h0 h1 hM d hd0 hdcut,hmap]
  congr 1
  rw [List.ofFn_congr hlen]
  apply congrArg List.ofFn
  funext i
  congr 1
  apply Fin.ext
  simp [hl]
end DirectGLSSW.HOMFLY.ProcessedExposedChild
