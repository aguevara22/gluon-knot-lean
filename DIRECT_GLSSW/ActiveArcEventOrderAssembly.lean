import ActiveArcEventMap
import ActiveArcOpenRegularNeighborhood
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationLocality
open DirectGLSSW ActiveArc Filter Topology
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)

/-- Internal neighborhood assembly. The only pending input is the physical-pair
crossing producer; actual parameter order and the entire event equivalence are derived. -/
theorem eventually_event_order_of_pair_neighborhood (hR : Regular q) (hG1 : cyclicNoncollinear q)
    (hpairs : ∀ᶠ r in 𝓝 q, ∀ e f : Fin (n+1), e≠f →
      ((∃ x, ActiveArc.edgeInterior q e x ∧ ActiveArc.edgeInterior q f x) ↔
       (∃ x, ActiveArc.edgeInterior r e x ∧ ActiveArc.edgeInterior r f x))) :
    ∀ᶠ r in 𝓝 q, ∃ hr : Regular r, ∃ E : Crossing q ≃ Crossing r,
      (∀ c, (E c).val=c.val) ∧ ∀ x y : Event q,
        ((eventOrder q hR.noTriple).lt x y ↔
         (eventOrder r hr.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y)) := by
  classical
  have horder : ∀ᶠ r in 𝓝 q, ∀ v w : Visit q, visitEdge q v=visitEdge q w →
      (visitParameter q v<visitParameter q w ↔
       parameterFormula r v.1.val v.2<parameterFormula r w.1.val w.2) := by
    apply Filter.eventually_all.mpr
    intro v
    apply Filter.eventually_all.mpr
    intro w
    by_cases he : visitEdge q v=visitEdge q w
    · exact (eventually_parameterFormula_order q hR v w he).mono (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ h => False.elim (he h))
  filter_upwards [eventually_regular_G1 q hR hG1,hpairs,horder] with r hr hp ho
  let forward : Crossing q → Crossing r := fun c =>
    ⟨c.val,c.property.1,(hp c.val.1 c.val.2 (ne_of_lt c.property.1)).mp c.property.2⟩
  let backward : Crossing r → Crossing q := fun c =>
    ⟨c.val,c.property.1,(hp c.val.1 c.val.2 (ne_of_lt c.property.1)).mpr c.property.2⟩
  let E : Crossing q ≃ Crossing r :=
    ⟨forward,backward,fun c => Subtype.ext rfl,fun c => Subtype.ext rfl⟩
  have hlabels : ∀ c, (E c).val=c.val := fun _ => rfl
  refine ⟨hr.1,E,hlabels,?_⟩
  have hv : ∀ v w : Visit q, visitEdge q v=visitEdge q w →
      (visitParameter q v<visitParameter q w ↔
       visitParameter r (visitMapEquiv q r E v)<visitParameter r (visitMapEquiv q r E w)) := by
    intro v w he
    have hh := ho v w he
    rw [parameterFormula_eq_mapped q r hr.1 E hlabels v,
      parameterFormula_eq_mapped q r hr.1 E hlabels w] at hh
    exact hh
  exact eventMapEquiv_order_iff q r hR hr.1 E hlabels hv

end DirectGLSSW.ActiveArc.ConfigurationLocality
