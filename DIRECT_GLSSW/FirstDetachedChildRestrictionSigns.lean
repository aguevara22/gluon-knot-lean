import FirstDetachedChildCrossingEquiv
import ComponentRestrictionSigns
import ActiveArcChildCanonicalSigns
import DirectGLSSW.HOMFLY.HOMFLYSmoothingRetainedSign

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open HOMFLY HOMFLY.PolygonDrawingBridge HOMFLY.LowestRowContract

variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (hQ : CyclicGeneric q) (hR : Regular q) (c : Crossing q)
    (hfirst : c.val.1 = 0) (hcut : c.val.2.val = a)
    (R : ComponentRestriction
      (smoothCrossing (positivePolygonEventDiagram q hQ)
        (crossingFin q (polygonCrossingOfArc q c)))
      (positiveSmoothedChildComponent q hQ (polygonCrossingOfArc q c)))

/-- The sign of every crossing in the actual first component restriction is
positive, by retained smoothing signs and the actual restriction geometry. -/
theorem firstDetachedChildRestriction_crossingSign (j : Fin R.diagram.nCrossing) :
    crossingSign R.diagram j = Sign.pos := by
  rw [R.crossingSign_eq]
  let old := (smoothCrossingEquiv (positivePolygonEventDiagram q hQ)
    (crossingFin q (polygonCrossingOfArc q c))).symm (R.crossingEquiv j).val
  have he := (smoothCrossingEquiv (positivePolygonEventDiagram q hQ)
    (crossingFin q (polygonCrossingOfArc q c))).apply_symm_apply (R.crossingEquiv j).val
  rw [← he, crossingSign_smoothRetained]
  exact positivePolygonEventDiagram_crossingSign q hQ old.val

/-- Over-branch correspondence for the explicit crossing equivalence. -/
theorem firstDetachedChildRestriction_overBranch
    (hChild : CyclicGeneric (child q hR c hfirst hcut))
    (e : PolygonCrossing (child q hR c hfirst hcut)) :
    R.diagram.overBranch (R.crossingEquiv.symm
      (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut e)) =
    (positivePolygonEventDiagram (child q hR c hfirst hcut) hChild).overBranch
      (crossingFin (child q hR c hfirst hcut) e) := by
  rw [R.overBranch_eq, Equiv.apply_symm_apply, firstDetachedChildCrossingEquiv_val]
  simp only [positiveSmoothedCrossing, smoothCrossing, Equiv.symm_apply_apply]
  exact (childCrossing_positiveDiagram_overBranch q hR c hfirst hcut hQ hChild e).symm

/-- The explicit crossing equivalence also preserves through-branch pairing. -/
theorem firstDetachedChildRestriction_through
    (hChild : CyclicGeneric (child q hR c hfirst hcut))
    (e : PolygonCrossing (child q hR c hfirst hcut)) :
    R.diagram.through (R.crossingEquiv.symm
      (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut e)) =
    (positivePolygonEventDiagram (child q hR c hfirst hcut) hChild).through
      (crossingFin (child q hR c hfirst hcut) e) := by
  rw [R.through_eq]
  rfl

/-- The actual crossing signs agree on the explicit child correspondence. -/
theorem firstDetachedChildRestriction_sign_correspondence
    (hChild : CyclicGeneric (child q hR c hfirst hcut))
    (e : PolygonCrossing (child q hR c hfirst hcut)) :
    crossingSign R.diagram (R.crossingEquiv.symm
      (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut e)) =
    crossingSign (positivePolygonEventDiagram (child q hR c hfirst hcut) hChild)
      (crossingFin (child q hR c hfirst hcut) e) := by
  rw [firstDetachedChildRestriction_crossingSign q hQ c R,
    positivePolygonEventDiagram_crossingSign]

end DirectGLSSW.ActiveArc.Split
