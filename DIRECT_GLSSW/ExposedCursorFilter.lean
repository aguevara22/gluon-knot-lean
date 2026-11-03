import ActiveArcCutVisits
import PolygonCursorFilter
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ExposedChart
attribute [local instance] Classical.propDecidable
open ExposedOpenPrimitive
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q) (he : LeftExposed q 0)

theorem zero_edgeLabel_val (e : Fin (n+1)) : (edgeLabel (0 : Fin (n+2)) e).val = e.val+1 := by
  change (0+1+e.val)%(n+2)=e.val+1
  rw [Nat.mod_eq_of_lt (by have := e.isLt;omega)]
  omega

theorem physical_crossing_filter_iff (a : ℕ) (θ : ℝ) (d : Crossing (cutArc q 0)) :
    (a ≤ d.val.1.val ∧ (d.val.1.val = a → θ < leftParameter (cutArc q 0) d)) ↔
      ∀ b : Bool, a < (visitEdge (cutArc q 0) (d,b)).val ∨
        (a = (visitEdge (cutArc q 0) (d,b)).val ∧ θ < visitParameter (cutArc q 0) (d,b)) := by
  constructor
  · rintro ⟨ha,hθ⟩ b
    cases b
    · change a<d.val.1.val ∨ (a=d.val.1.val ∧ θ<leftParameter (cutArc q 0) d)
      by_cases hh : d.val.1.val=a
      · exact Or.inr ⟨hh.symm,hθ hh⟩
      · exact Or.inl (lt_of_le_of_ne ha (Ne.symm hh))
    · left
      change a<d.val.2.val
      exact lt_of_le_of_lt ha d.property.1
  · intro hh
    have hf := hh false
    change a<d.val.1.val ∨ (a=d.val.1.val ∧ θ<leftParameter (cutArc q 0) d) at hf
    rcases hf with hf|⟨ha,hθ⟩
    · exact ⟨le_of_lt hf,fun heq => (by omega)⟩
    · exact ⟨le_of_eq ha,fun _=>hθ⟩

/-- Exact original opening: no local branch convention is presumed; the
canonical incident-edge permutation is quantified over both physical visits. -/
theorem exposed_crossing_cursor_filter (a : ℕ) (θ : ℝ) (d : Crossing (cutArc q 0)) :
    (a ≤ d.val.1.val ∧ (d.val.1.val = a → θ < leftParameter (cutArc q 0) d)) ↔
      ∀ b : Bool, a+1 < (crossingVisitEdge q (exposedCrossingEquiv q 0 hq he d,b)).val ∨
        (a+1 = (crossingVisitEdge q (exposedCrossingEquiv q 0 hq he d,b)).val ∧
          θ < crossingVisitParameter q (exposedCrossingEquiv q 0 hq he d,b)) := by
  rw [physical_crossing_filter_iff]
  have H (b : Bool) :
      (a < (visitEdge (cutArc q 0) (d,b)).val ∨
        (a = (visitEdge (cutArc q 0) (d,b)).val ∧ θ < visitParameter (cutArc q 0) (d,b))) ↔
      (a+1 < (crossingVisitEdge q (exposedCrossingEquiv q 0 hq he d,visitBoolEquiv q 0 hq he d b)).val ∨
        (a+1 = (crossingVisitEdge q (exposedCrossingEquiv q 0 hq he d,visitBoolEquiv q 0 hq he d b)).val ∧
          θ < crossingVisitParameter q (exposedCrossingEquiv q 0 hq he d,visitBoolEquiv q 0 hq he d b))) := by
    change _ ↔ a+1 < (crossingVisitEdge q (visitEquiv q 0 hq he (d,b))).val ∨
      (a+1 = (crossingVisitEdge q (visitEquiv q 0 hq he (d,b))).val ∧
        θ < crossingVisitParameter q (visitEquiv q 0 hq he (d,b)))
    simp only [visitEquiv_edge,visitEquiv_parameter,zero_edgeLabel_val]
    simp only [Nat.add_lt_add_iff_right, Nat.add_left_inj]
  constructor
  · intro hh b
    obtain ⟨b',hb⟩ := (visitBoolEquiv q 0 hq he d).surjective b
    exact hb ▸ (H b').mp (hh b')
  · intro hh b
    exact (H b).mpr (hh _)
end DirectGLSSW.ActiveArc.ExposedChart
