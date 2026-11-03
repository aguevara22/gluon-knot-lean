import ActualCutCalculationInitialization
import ActiveArcChildAuxiliary
import ActiveArcUniformChild
import ActiveArcClosedChildCrossings

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open ActiveArc ActiveArc.Cursor ActiveArc.Split ActiveArc.FiniteCalculation
open ActiveArc.ChildRestartRecursion

/-- The actual removed crossing is outside the injective image of all child crossings. -/
theorem actual_calculation_child_crossing_decrease
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (D : Domain q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a) :
    Fintype.card (PolygonCrossing (child q D.hR c hc.1 hcut)) <
      Fintype.card (Crossing q) := by
  classical
  let f := childCrossingToOriginal q D.hR c hc.1 hcut
  have hf : Function.Injective f := childCrossingToOriginal_injective q D.hR c hc.1 hcut
  exact Fintype.card_lt_of_injective_of_not_mem f hf (b:=c) (by
    rintro ⟨d,hd⟩
    have hmem := childCrossingToOriginal_inChild q D.hR c hc.1 hcut d
    change InChild q c (f d) at hmem
    rw [hd] at hmem
    exact crossing_not_inChild q c hc.1 hmem)

/-- Literal open blocks end in the actual generic all-left closed child;
its auxiliary condition and original history are derived, not supplied. -/
theorem actual_calculation_under_child_history
    {original : LiteralCarrierState} {s : ActiveWordState} {a b : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (D : Domain q)
    (hinit : LiteralCarrierPath original (.inr s))
    (hpath : Relation.ReflTransGen
      (fun u v : ActiveWordState => LiteralCarrierStep (.inr u) (.inr v)) s ⟨a+b,q⟩)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hu : crossingUnder q (polygonCrossingOfArc q c)=(polygonCrossingOfArc q c).val.1) :
    ∃ hd : CyclicGeneric (child q D.hR c hc.1 hcut),
      GeometricSmoothingWeights.auxiliaryGenericity (child q D.hR c hc.1 hcut) hd ∧
      (∀ e, 0 < planarDet (cyclicTangent (child q D.hR c hc.1 hcut) e)
        (cyclicTangent (child q D.hR c hc.1 hcut) (cyclicSuccessor e))) ∧
      LiteralCarrierPath original (.inl ⟨a+1,child q D.hR c hc.1 hcut⟩) ∧
      Fintype.card (PolygonCrossing (child q D.hR c hc.1 hcut)) <
        Fintype.card (Crossing q) := by
  have hfull := literalCarrierPath_trans hinit (literal_open_path_to_literalCarrierPath hpath)
  refine ⟨SingletonWords.child_cyclicGeneric_of_closedAuxiliary q D.hR c hc.1 hcut D.hAux,
    CompatibleWords.child_auxiliaryGenericity q D.hR c hc hcut D.hAux, ?_,
    literalCarrierPath_snoc hfull (.detach q D.hR c hc hcut),
    actual_calculation_child_crossing_decrease q D c hc hcut⟩
  exact child_all_turns_pos q D.hR c hc hcut D.hG hu (fun i _ => D.hleft i)

end DirectGLSSW.CyclicCarrierClearing


