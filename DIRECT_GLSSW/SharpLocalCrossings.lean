import ProcessedSharpPolygonEquiv
import DirectGLSSW.TwoStageRefinement
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SharpDaughter
open PermutationOrbits PolygonDrawingBridge ActualLocalSupports
attribute [local instance] Classical.propDecidable

/-- Literal geometric sharp crossings are exactly unselected actual crossings
whose two visits belong to the same dart component. -/
def crossingLocalDartEquiv {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S)) :
    Crossing q hq S C ≃ LocalCrossing q (P q hq S) S C :=
  Equiv.subtypeEquiv (crossingFin q).symm (by
    intro d
    constructor
    · rintro ⟨hd,hm⟩
      refine ⟨hd,?_,?_⟩
      · simpa only [outgoing_event,PolygonDrawing.visit,ite_true] using hm 0
      · simpa only [outgoing_event,PolygonDrawing.visit,ite_false] using hm 1
    · rintro ⟨hd,h0,h1⟩
      refine ⟨hd,?_⟩
      intro i
      fin_cases i
      · simpa only [outgoing_event,PolygonDrawing.visit,ite_true] using h0
      · simpa only [outgoing_event,PolygonDrawing.visit,ite_false] using h1)

/-- Pairing converts the old dart component into the exact incoming component;
unselected crossing visits themselves are fixed by that pairing. -/
def localDartIncomingEquiv {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (C : Component (P q hq S)) :
    LocalCrossing q (P q hq S) S C ≃
      LocalCrossing q (smoothingIncomingPermutation q hq.g2 S) S
        ((smoothingComponentEquiv q hq.g2 S).symm C) :=
  Equiv.subtypeEquiv (Equiv.refl _) (by
    intro d
    change (d ∉ S ∧ _ ∧ _) ↔ (d ∉ S ∧ _ ∧ _)
    by_cases hd : d ∈ S
    · simp [hd]
    have hcoord (b : Bool) :
        componentOf (smoothingIncomingPermutation q hq.g2 S) (Sum.inr (d,b)) =
          (smoothingComponentEquiv q hq.g2 S).symm C ↔
        componentOf (P q hq S) (Sum.inr (d,b)) = C := by
      rw [←(smoothingComponentEquiv q hq.g2 S).injective.eq_iff]
      rw [Equiv.apply_symm_apply,smoothingComponentEquiv_componentOf,
        (smoothingPairing_visit_fixed_iff q S (d,b)).mpr hd]
    exact and_congr Iff.rfl (and_congr (hcoord false).symm (hcoord true).symm))
end DirectGLSSW.HOMFLY.SharpDaughter
