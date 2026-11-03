import ActiveArcBeforeFirstComponents

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.BeforeFirst
open DirectGLSSW ActiveArc PermutationOrbits
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (t : ℝ) (ht0 : 0 ≤ t) (htc : t < leftParameter q c)
variable (hRI : GLSSWRootIndependence) (hAux : Primitive.ClosedAuxiliary q hR)
include hRI

/-- Every actual closed weight is fixed in the pre-first chamber; open weights are neutral on both sides. -/
theorem closedWeight_eq
    (S : Primitive.Support (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc))
    (C : Primitive.Components (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc) S) :
    Primitive.closedWeight q hR hAux (supportEquiv q hR c hc t ht0 htc S)
      (componentEquiv q hR c hc t ht0 htc S.val C) =
    Primitive.closedWeight (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc)
      (closedAuxiliary q hR c hc t ht0 htc hAux) S C := by
  by_cases hC : C = openComponent (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S.val
  · subst C
    rw [componentEquiv_open]
    simp [Primitive.closedWeight,supportEquiv_val]
  · have hD : componentEquiv q hR c hc t ht0 htc S.val C ≠
        openComponent q hR.noTriple (supportEquiv q hR c hc t ht0 htc S).val :=
      (closedComponentEquiv q hR c hc t ht0 htc S.val ⟨C,hC⟩).property
    rw [Primitive.closedWeight,dif_pos hD,Primitive.closedWeight,dif_pos hC]
    exact DaughterRootAmplitude.polygonAmplitude_ofFn_isRotated hRI
      (hAux (supportEquiv q hR c hc t ht0 htc S) _ hD)
      (closed_word_isRotated q hR c hc t ht0 htc S.val ⟨C,hC⟩)

/-- The full actual erased-open closed-factor product is fixed under the proved support correspondence. -/
theorem closedWeight_product_eq
    (S : Primitive.Support (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc)) :
    (∏ D ∈ Finset.univ.erase (openComponent q hR.noTriple
        (supportEquiv q hR c hc t ht0 htc S).val),
      Primitive.closedWeight q hR hAux (supportEquiv q hR c hc t ht0 htc S) D) =
    (∏ C ∈ Finset.univ.erase (openComponent (moveStart q t)
        (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S.val),
      Primitive.closedWeight (moveStart q t)
        (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc)
        (closedAuxiliary q hR c hc t ht0 htc hAux) S C) := by
  symm
  apply Finset.prod_equiv (componentEquiv q hR c hc t ht0 htc S.val)
  · intro C
    simp only [Finset.mem_erase,Finset.mem_univ,and_true,supportEquiv_val]
    rw [← componentEquiv_open q hR c hc t ht0 htc S.val]
    exact not_congr (componentEquiv q hR c hc t ht0 htc S.val).injective.eq_iff.symm
  · intro C _
    exact (closedWeight_eq q hR c hc t ht0 htc hRI hAux S C).symm

end DirectGLSSW.ActiveArc.Cursor.BeforeFirst
