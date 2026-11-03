import ActiveArcExposedOpenWeight

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW ExposedOpenPrimitive GeometricSmoothingWeights PermutationOrbits
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2))
variable (hq : CyclicGeneric q) (he : LeftExposed q e) (hAux : auxiliaryGenericity q hq)
variable (hRI : GLSSWRootIndependence)

/-- Literal physical support bijection to the original separating support domain. -/
def separatingSupportEquiv : Primitive.Support (cutArc q e) (cutArc_regular q e hq) ≃ SeparatingSupport q hq :=
  (supportEquiv q e hq he).trans (ExposedOpenPrimitive.exposedSupportEquiv q hq e he)

theorem separatingSupportEquiv_val (S : Primitive.Support (cutArc q e) (cutArc_regular q e hq)) :
    (separatingSupportEquiv q e hq he S).val=mappedSupport q e hq he S.val := rfl

include hRI in
theorem closedWeight_eq_component (S : Primitive.Support (cutArc q e) (cutArc_regular q e hq))
    (C : Primitive.Components (cutArc q e) (cutArc_regular q e hq) S)
    (hc : C≠ActiveArc.openComponent (cutArc q e) (cutArc_regular q e hq).noTriple S.val) :
    Primitive.closedWeight (cutArc q e) (cutArc_regular q e hq)
      (closedAuxiliary_of_parent q e hq he hAux) S C=
      componentAmplitude q hq (mappedSupport q e hq he S.val) hAux
        ((nonalternating_iff_parent q e hq he S.val).mp S.property)
        (dartComponentEquiv q e hq he S.val C) := by
  rw [Primitive.closedWeight,dif_pos hc]
  let r := closedRoot (cutArc q e) (cutArc_regular q e hq).noTriple S.val C hc
  have hh := retainedAmplitude_eq_component q e hq he hAux hRI S r
  have hr := (closedRoot_spec (cutArc q e) (cutArc_regular q e hq).noTriple S.val C hc).1
  rw [← dartComponentEquiv_componentOf,hr] at hh
  exact hh

include hRI in
theorem open_closed_product_eq_parent (S : Primitive.Support (cutArc q e) (cutArc_regular q e hq)) :
    Primitive.openCurrent (cutArc q e) (cutArc_regular q e hq) S *
      (∏ C ∈ Finset.univ.erase (ActiveArc.openComponent (cutArc q e) (cutArc_regular q e hq).noTriple S.val),
        Primitive.closedWeight (cutArc q e) (cutArc_regular q e hq)
          (closedAuxiliary_of_parent q e hq he hAux) S C)=
      componentAmplitudeProduct q hq (mappedSupport q e hq he S.val) hAux
        ((nonalternating_iff_parent q e hq he S.val).mp S.property) := by
  let P := fun C => componentAmplitude q hq (mappedSupport q e hq he S.val) hAux
    ((nonalternating_iff_parent q e hq he S.val).mp S.property) (dartComponentEquiv q e hq he S.val C)
  have ho := openCurrent_eq_component q e hq he hAux S hRI
  have hp : (∏ C ∈ Finset.univ.erase (ActiveArc.openComponent (cutArc q e) (cutArc_regular q e hq).noTriple S.val),
        Primitive.closedWeight (cutArc q e) (cutArc_regular q e hq)
          (closedAuxiliary_of_parent q e hq he hAux) S C)=
      ∏ C ∈ Finset.univ.erase (ActiveArc.openComponent (cutArc q e) (cutArc_regular q e hq).noTriple S.val), P C := by
    apply Finset.prod_congr rfl
    intro C hC
    exact closedWeight_eq_component q e hq he hAux hRI S C (Finset.mem_erase.mp hC).1
  rw [hp,ho]
  change P (ActiveArc.openComponent (cutArc q e) (cutArc_regular q e hq).noTriple S.val)*_= _
  rw [Finset.mul_prod_erase _ _ (Finset.mem_univ _)]
  exact Fintype.prod_equiv (dartComponentEquiv q e hq he S.val) _ _ (by intro C;rfl)

include hRI in
/-- Source un:initial for the genuine physical ΓM carrier and actual closed amplitudes. -/
theorem GammaM_eq_separatingSmoothingSum :
    Primitive.GammaM (cutArc q e) (cutArc_regular q e hq) (closedAuxiliary_of_parent q e hq he hAux)=
      separatingSmoothingSum q hq hAux := by
  unfold Primitive.GammaM separatingSmoothingSum
  apply Fintype.sum_equiv (separatingSupportEquiv q e hq he)
  intro S
  have hcard : (separatingSupportEquiv q e hq he S).val.card=S.val.card := by
    rw [separatingSupportEquiv_val]
    exact Finset.card_map _
  rw [hcard]
  congr 1
  exact open_closed_product_eq_parent q e hq he hAux hRI S

include hRI in
/-- The physical initialization agrees with the previously proved exposed edge chart. -/
theorem GammaM_eq_openAtEdgeSum :
    Primitive.GammaM (cutArc q e) (cutArc_regular q e hq) (closedAuxiliary_of_parent q e hq he hAux)=
      ExposedOpenPrimitive.openAtEdgeSum q hq hAux e :=
  (GammaM_eq_separatingSmoothingSum q e hq he hAux hRI).trans
    (exposed_openAtEdgeSum_eq_separatingSmoothingSum q hq hAux e he hRI).symm

end DirectGLSSW.ActiveArc.ExposedChart
