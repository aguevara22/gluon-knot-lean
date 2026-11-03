import PositivePolygonChildCrossings
import ArcPolygonVisitParameters

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open HOMFLY.PolygonDrawing HOMFLY.PolygonDrawingBridge PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hQ : CyclicGeneric q) (hR : Regular q)

include hR in
/-- Actual polygon visit order cuts out exactly the physical open-arc child interval. -/
theorem polygon_visits_between_iff_inChild (c d : Crossing q)
    (hfirst : c.val.1=0) (hcut : c.val.2.val=a) :
    letI := polygonEventOrder q hQ.g2
    (visit q (polygonCrossingOfArc q c) 0 < visit q (polygonCrossingOfArc q d) 0 ∧
      visit q (polygonCrossingOfArc q d) 1 < visit q (polygonCrossingOfArc q c) 1) ↔ InChild q c d := by
  letI := polygonEventOrder q hQ.g2
  rw [polygonEvent_lt_iff,polygonEvent_lt_iff]
  change
    (((polygonCrossingOfArc q c).val.1 < (polygonCrossingOfArc q d).val.1 ∨
      (polygonCrossingOfArc q c).val.1 = (polygonCrossingOfArc q d).val.1 ∧
      crossingVisitParameter q (polygonCrossingOfArc q c,false) <
        crossingVisitParameter q (polygonCrossingOfArc q d,false)) ∧
    ((polygonCrossingOfArc q d).val.2 < (polygonCrossingOfArc q c).val.2 ∨
      (polygonCrossingOfArc q d).val.2 = (polygonCrossingOfArc q c).val.2 ∧
      crossingVisitParameter q (polygonCrossingOfArc q d,true) <
        crossingVisitParameter q (polygonCrossingOfArc q c,true))) ↔ _
  rw [polygonCrossingOfArc_visitParameter q hQ hR c false,
    polygonCrossingOfArc_visitParameter q hQ hR d false,
    polygonCrossingOfArc_visitParameter q hQ hR d true,
    polygonCrossingOfArc_visitParameter q hQ hR c true]
  simp only [polygonCrossingOfArc,Fin.castSucc_inj,visitParameter]
  rw [hfirst]
  change ((0 < d.val.1.val ∨ (0 : Fin (a+b+1)) = d.val.1 ∧ leftParameter q c < leftParameter q d) ∧
    (d.val.2.val < c.val.2.val ∨ d.val.2 = c.val.2 ∧ rightParameter q d < rightParameter q c)) ↔ _
  rw [hcut]
  unfold InChild
  have hde : d.val.2=c.val.2 ↔ d.val.2.val=a := by
    constructor
    · intro h;exact (congrArg Fin.val h).trans hcut
    · intro h;apply Fin.ext;exact h.trans hcut.symm
  rw [hde]
  by_cases hl : d.val.1=0
  · simp only [hl,Fin.val_zero,lt_self_iff_false,eq_self_iff_true,true_and,false_or]
    constructor
    · rintro ⟨h,hr⟩
      refine ⟨?_,fun _=>h,?_⟩
      · rcases hr with h|h <;> omega
      · intro he;rcases hr with h|h
        · omega
        · exact h.2
    · rintro ⟨hr,hl,he⟩
      refine ⟨hl trivial,?_⟩
      rcases lt_or_eq_of_le hr with h|h
      · exact Or.inl h
      · exact Or.inr ⟨h,he h⟩
  · have hlv : 0<d.val.1.val := by have := d.val.1.isLt;have hn : d.val.1.val≠0 := fun h=>hl (Fin.ext h);omega
    simp only [hlv,true_or,hl,false_implies,true_and]
    constructor
    · intro h
      refine ⟨?_,?_⟩
      · rcases h with h|h <;> omega
      · intro he;rcases h with h|h
        · omega
        · exact h.2
    · rintro ⟨h,he⟩
      rcases lt_or_eq_of_le h with h|h
      · exact Or.inl h
      · exact Or.inr ⟨h,he h⟩

private theorem polygonCrossingOfArc_injective : Function.Injective (polygonCrossingOfArc q) := by
  intro d e h
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun z : PolygonCrossing q => z.val.1.val) h
  · apply Fin.ext
    exact congrArg (fun z : PolygonCrossing q => z.val.2.val) h

/-- Actual self-crossing membership in the first detached component is exactly
membership in the existing literal child polygon's crossing carrier. -/
theorem firstDetachedChild_crossing_iff (c d : Crossing q)
    (hfirst : c.val.1=0) (hcut : c.val.2.val=a) (hd : d≠c) :
    (∀ i : Fin 2,
      componentOf (HOMFLY.smoothCrossing (positivePolygonEventDiagram q hQ)
        (crossingFin q (polygonCrossingOfArc q c))).continuation
        ((HOMFLY.smoothCrossing (positivePolygonEventDiagram q hQ)
          (crossingFin q (polygonCrossingOfArc q c))).incoming
          (positiveSmoothedCrossing q hQ (polygonCrossingOfArc q c) (polygonCrossingOfArc q d)
            (fun h => hd (polygonCrossingOfArc_injective q h))) i) =
        positiveSmoothedChildComponent q hQ (polygonCrossingOfArc q c)) ↔
    ∃! e : PolygonCrossing (child q hR c hfirst hcut),
      childCrossingToOriginal q hR c hfirst hcut e=d := by
  rw [positiveSmoothedChild_selfCrossing_iff,
    polygon_visits_between_iff_inChild q hQ hR c d hfirst hcut]
  constructor
  · intro h
    obtain ⟨e,he⟩ := (childCrossing_range q hR c hfirst hcut d).mpr h
    refine ⟨e,he,?_⟩
    intro e' he'
    exact childCrossingToOriginal_injective q hR c hfirst hcut (he'.trans he.symm)
  · rintro ⟨e,he,_⟩
    exact (childCrossing_range q hR c hfirst hcut d).mp ⟨e,he⟩

end DirectGLSSW.ActiveArc.Split
