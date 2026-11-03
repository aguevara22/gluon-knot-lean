import ActualCalculationChildHistory
import ActiveArcCutCrossings

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open ActiveArc ActiveArc.Cursor ActiveArc.Split ActiveArc.FiniteCalculation
open ActiveArc.ExposedChart ActiveArc.ChildRestartRecursion ExposedOpenPrimitive

/-- The explicit exposed truncation, with its actual crossing equivalence,
restarts with strictly fewer physical crossings. No opaque restart is used. -/
theorem actual_explicit_restart_crossing_decrease
    {a b m : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (D : Domain q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (T : Fin (m+2) → PlanarPoint ℝ) (hT : CyclicGeneric T)
    (e : Fin (m+2)) (he : LeftExposed T e)
    (E : PolygonCrossing (child q D.hR c hc.1 hcut) ≃ PolygonCrossing T) :
    Fintype.card (Crossing (cutArc T e)) < Fintype.card (Crossing q) := by
  have hcount : Fintype.card (Crossing (cutArc T e)) =
      Fintype.card (PolygonCrossing (child q D.hR c hc.1 hcut)) :=
    (Fintype.card_congr (exposedCrossingEquiv T e hT he)).trans
      (Fintype.card_congr E).symm
  rw [hcount]
  exact actual_calculation_child_crossing_decrease q D c hc hcut

/-- The same previously used lexicographic measure decreases for the explicit
good-line restart, regardless of how many vertices its chart adds. -/
theorem actual_explicit_restart_measure_decrease
    {a b m : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (D : Domain q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (T : Fin (m+2) → PlanarPoint ℝ) (hT : CyclicGeneric T)
    (e : Fin (m+2)) (he : LeftExposed T e)
    (E : PolygonCrossing (child q D.hR c hc.1 hcut) ≃ PolygonCrossing T) :
    LexLess (activeWordMeasure ⟨m,cutArc T e⟩) (activeWordMeasure ⟨a+b,q⟩) := by
  exact (Prod.lex_iff).2
    (Or.inl (actual_explicit_restart_crossing_decrease q D c hc hcut T hT e he E))

end DirectGLSSW.CyclicCarrierClearing
