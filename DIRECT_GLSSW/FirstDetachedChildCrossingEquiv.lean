import FirstDetachedChildClassification
import LowestRowContract.Contract

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open HOMFLY HOMFLY.PolygonDrawingBridge HOMFLY.LowestRowContract PermutationOrbits
attribute [local instance] Classical.propDecidable

variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (hQ : CyclicGeneric q) (hR : Regular q) (c : Crossing q)
    (hfirst : c.val.1 = 0) (hcut : c.val.2.val = a)

theorem childCrossingToOriginal_ne_cut
    (e : PolygonCrossing (child q hR c hfirst hcut)) :
    polygonCrossingOfArc q (childCrossingToOriginal q hR c hfirst hcut e) ≠
      polygonCrossingOfArc q c := by
  intro h
  have he := childCrossingToOriginal_inChild q hR c hfirst hcut e
  rw [ActiveArc.polygonCrossingOfArc_injective q h] at he
  exact crossing_not_inChild q c hfirst he

/-- Literal child crossings enumerate exactly the self crossings of the actual
first detached component, with the canonical surviving crossing labels. -/
def firstDetachedChildCrossingMap
    (e : PolygonCrossing (child q hR c hfirst hcut)) :
    ComponentCrossing
      (smoothCrossing (positivePolygonEventDiagram q hQ)
        (crossingFin q (polygonCrossingOfArc q c)))
      (positiveSmoothedChildComponent q hQ (polygonCrossingOfArc q c)) :=
  ⟨positiveSmoothedCrossing q hQ (polygonCrossingOfArc q c)
      (polygonCrossingOfArc q (childCrossingToOriginal q hR c hfirst hcut e))
      (childCrossingToOriginal_ne_cut q hR c hfirst hcut e), by
    apply (firstDetachedChild_all_crossings_iff q hQ hR c hfirst hcut _ _).mpr
    refine ⟨e,rfl,?_⟩
    intro z hz
    exact childCrossingToOriginal_injective q hR c hfirst hcut
      (ActiveArc.polygonCrossingOfArc_injective q hz)⟩

theorem firstDetachedChildCrossingMap_injective :
    Function.Injective (firstDetachedChildCrossingMap q hQ hR c hfirst hcut) := by
  intro e f h
  have hv := congrArg Subtype.val h
  have hs := (smoothCrossingEquiv (positivePolygonEventDiagram q hQ)
    (crossingFin q (polygonCrossingOfArc q c))).injective hv
  have hp := (crossingFin q).injective (congrArg Subtype.val hs)
  exact childCrossingToOriginal_injective q hR c hfirst hcut
    (ActiveArc.polygonCrossingOfArc_injective q hp)

theorem firstDetachedChildCrossingMap_surjective :
    Function.Surjective (firstDetachedChildCrossingMap q hQ hR c hfirst hcut) := by
  intro x
  let old := (smoothCrossingEquiv (positivePolygonEventDiagram q hQ)
    (crossingFin q (polygonCrossingOfArc q c))).symm x.val
  let d := (crossingFin q).symm old.val
  have hd : d ≠ polygonCrossingOfArc q c := by
    intro h
    apply old.property
    have he := congrArg (crossingFin q) h
    simpa only [d, Equiv.apply_symm_apply] using he
  have he : positiveSmoothedCrossing q hQ (polygonCrossingOfArc q c) d hd = x.val := by
    unfold positiveSmoothedCrossing
    calc
      _ = (smoothCrossingEquiv (positivePolygonEventDiagram q hQ)
          (crossingFin q (polygonCrossingOfArc q c))) old := by
        apply congrArg _
        apply Subtype.ext
        exact (crossingFin q).apply_symm_apply old.val
      _ = x.val := (smoothCrossingEquiv (positivePolygonEventDiagram q hQ)
        (crossingFin q (polygonCrossingOfArc q c))).apply_symm_apply x.val
  have hx := x.property
  rw [← he] at hx
  obtain ⟨e,heold,_⟩ := (firstDetachedChild_all_crossings_iff q hQ hR c hfirst hcut d hd).mp hx
  refine ⟨e,Subtype.ext ?_⟩
  change positiveSmoothedCrossing q hQ (polygonCrossingOfArc q c)
    (polygonCrossingOfArc q (childCrossingToOriginal q hR c hfirst hcut e))
    (childCrossingToOriginal_ne_cut q hR c hfirst hcut e) = x.val
  calc
    _ = positiveSmoothedCrossing q hQ (polygonCrossingOfArc q c) d hd := by
      unfold positiveSmoothedCrossing
      apply congrArg _
      exact Subtype.ext (congrArg (crossingFin q) heold)
    _ = x.val := he

/-- Explicit crossing equivalence, before any component extraction or
polynomial comparison. -/
def firstDetachedChildCrossingEquiv :
    PolygonCrossing (child q hR c hfirst hcut) ≃
    ComponentCrossing
      (smoothCrossing (positivePolygonEventDiagram q hQ)
        (crossingFin q (polygonCrossingOfArc q c)))
      (positiveSmoothedChildComponent q hQ (polygonCrossingOfArc q c)) :=
  Equiv.ofBijective (firstDetachedChildCrossingMap q hQ hR c hfirst hcut)
    ⟨firstDetachedChildCrossingMap_injective q hQ hR c hfirst hcut,
      firstDetachedChildCrossingMap_surjective q hQ hR c hfirst hcut⟩

@[simp] theorem firstDetachedChildCrossingEquiv_val
    (e : PolygonCrossing (child q hR c hfirst hcut)) :
    (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut e).val =
      positiveSmoothedCrossing q hQ (polygonCrossingOfArc q c)
        (polygonCrossingOfArc q (childCrossingToOriginal q hR c hfirst hcut e))
        (childCrossingToOriginal_ne_cut q hR c hfirst hcut e) := rfl

/-- Every exact component restriction has these same crossing labels. -/
def firstDetachedChildRestrictionCrossingEquiv
    (R : ComponentRestriction
      (smoothCrossing (positivePolygonEventDiagram q hQ)
        (crossingFin q (polygonCrossingOfArc q c)))
      (positiveSmoothedChildComponent q hQ (polygonCrossingOfArc q c))) :
    Fin R.diagram.nCrossing ≃ PolygonCrossing (child q hR c hfirst hcut) :=
  R.crossingEquiv.trans (firstDetachedChildCrossingEquiv q hQ hR c hfirst hcut).symm

end DirectGLSSW.ActiveArc.Split
