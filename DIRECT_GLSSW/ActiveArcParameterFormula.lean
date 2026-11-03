import ActiveArcEvents
import LocalCrossingAlgebra
import Mathlib.Tactic.FunProp
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationLocality
open DirectGLSSW ActiveArc Filter Topology
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)

/-- Explicit carrier parameter for a fixed pair of genuine physical edge labels. -/
def parameterFormula (p : Fin (n+1) × Fin (n+1)) (b : Bool) : ℝ :=
  if b then LocalCrossingTransport.rightParameter
    (q p.1.castSucc) (q p.1.succ) (q p.2.castSucc) (q p.2.succ)
  else LocalCrossingTransport.leftParameter
    (q p.1.castSucc) (q p.1.succ) (q p.2.castSucc) (q p.2.succ)

/-- On the actual regular crossing domain, the explicit quotient equals the unique physical parameter. -/
theorem parameterFormula_eq_actual (hR : Regular q) (v : Visit q) :
    parameterFormula q v.1.val v.2=visitParameter q v := by
  have hD := hR.transverse v.1.val.1 v.1.val.2 (ne_of_lt v.1.property.1)
    (crossingPoint q v.1) (crossingPoint_mem q v.1).1 (crossingPoint_mem q v.1).2
  have hx := (leftParameter_spec q v.1).2.2.symm.trans (rightParameter_spec q v.1).2.2
  rcases v with ⟨c,b⟩
  cases b
  · exact LocalCrossingTransport.leftParameter_eq _ _ _ _ _ _ hD hx
  · exact LocalCrossingTransport.rightParameter_eq _ _ _ _ _ _ hD hx

/-- The actual original visit's carrier quotient is continuous under arbitrary nearby anchor motion. -/
theorem parameterFormula_continuousAt (hR : Regular q) (v : Visit q) :
    ContinuousAt (fun r : Fin (n+2) → PlanarPoint ℝ => parameterFormula r v.1.val v.2) q := by
  have hD := hR.transverse v.1.val.1 v.1.val.2 (ne_of_lt v.1.property.1)
    (crossingPoint q v.1) (crossingPoint_mem q v.1).1 (crossingPoint_mem q v.1).2
  have hdet (a b c d : Fin (n+2)) : Continuous (fun r : Fin (n+2) → PlanarPoint ℝ =>
      planarDet (r b-r a) (r d-r c)) := by
    unfold planarDet
    fun_prop
  rcases v with ⟨c,b⟩
  cases b <;> unfold parameterFormula <;> simp only [Bool.false_eq_true,if_false,if_true]
  · unfold LocalCrossingTransport.leftParameter
    exact (hdet _ _ _ _).continuousAt.div (hdet _ _ _ _).continuousAt hD
  · unfold LocalCrossingTransport.rightParameter
    exact (hdet _ _ _ _).continuousAt.div (hdet _ _ _ _).continuousAt hD

/-- Two distinct actual visits on one physical edge have distinct parameters. -/
theorem visitParameter_ne (hR : Regular q) (v w : Visit q) (hvw : v≠w)
    (he : visitEdge q v=visitEdge q w) : visitParameter q v≠visitParameter q w := by
  intro hp
  apply hvw
  apply Sum.inr.inj
  apply key_injective q hR.noTriple
  exact Prod.ext (congrArg Fin.val he) hp

/-- The strict order of the actual visit parameters persists in a configuration neighborhood. -/
theorem eventually_parameterFormula_order (hR : Regular q) (v w : Visit q)
    (he : visitEdge q v=visitEdge q w) :
    ∀ᶠ r in 𝓝 q, (visitParameter q v<visitParameter q w ↔
      parameterFormula r v.1.val v.2<parameterFormula r w.1.val w.2) := by
  by_cases hvw : v=w
  · subst w
    exact Eventually.of_forall (fun _ => by simp)
  · have hne := visitParameter_ne q hR v w hvw he
    let D : (Fin (n+2) → PlanarPoint ℝ) → ℝ := fun r =>
      parameterFormula r w.1.val w.2-parameterFormula r v.1.val v.2
    have hc : ContinuousAt D q :=
      (parameterFormula_continuousAt q hR w).sub (parameterFormula_continuousAt q hR v)
    have hD0 : D q=visitParameter q w-visitParameter q v := by
      dsimp [D]
      rw [parameterFormula_eq_actual q hR w,parameterFormula_eq_actual q hR v]
    by_cases hlt : visitParameter q v<visitParameter q w
    · have hpos : 0 < D q := by rw [hD0]; exact sub_pos.mpr hlt
      have hg := hc.eventually (isOpen_Ioi.mem_nhds hpos)
      filter_upwards [hg] with r hr
      exact ⟨fun _ => sub_pos.mp hr,fun _ => hlt⟩
    · have hgt : visitParameter q w<visitParameter q v := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
      have hneg : D q < 0 := by rw [hD0]; exact sub_neg.mpr hgt
      have hg := hc.eventually (isOpen_Iio.mem_nhds hneg)
      filter_upwards [hg] with r hr
      exact ⟨fun h => False.elim (hlt h),fun h => False.elim (not_lt_of_ge (le_of_lt (sub_neg.mp hr)) h)⟩

end DirectGLSSW.ActiveArc.ConfigurationLocality
