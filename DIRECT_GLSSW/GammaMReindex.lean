import ActiveArcGammaM
import ActiveArcBeforeFirstWeights
import ActiveArcAfterFirstWeights

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.BeforeFirst
open DirectGLSSW ActiveArc
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n + 2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (t : ℝ) (ht0 : 0 ≤ t) (htc : t < leftParameter q c)
variable (hRI : GLSSWRootIndependence) (hAux : Primitive.ClosedAuxiliary q hR)
include hRI

/-- Before the first crossing, reindex the complete physical ΓM finite sum by
the actual support equivalence, preserving the original closed factors. -/
theorem GammaM_eq_reindexed_original_support :
    Primitive.GammaM (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc)
      (closedAuxiliary q hR c hc t ht0 htc hAux) =
    ∑ U : Primitive.Support q hR,
      (-1 : ℚ) ^ U.val.card *
        (Primitive.openCurrent (moveStart q t)
            (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc)
            ((supportEquiv q hR c hc t ht0 htc).symm U) *
          ∏ D ∈ Finset.univ.erase (openComponent q hR.noTriple U.val),
            Primitive.closedWeight q hR hAux U D) := by
  classical
  let e := supportEquiv q hR c hc t ht0 htc
  unfold Primitive.GammaM
  apply Fintype.sum_equiv e
  intro S
  have hcard := supportEquiv_card q hR c hc t ht0 htc S
  have hprod := closedWeight_product_eq q hR c hc t ht0 htc hRI hAux S
  simp only [e, Equiv.symm_apply_apply]
  rw [hcard, ← hprod]

end DirectGLSSW.ActiveArc.Cursor.BeforeFirst

namespace DirectGLSSW.ActiveArc.Cursor.Surviving
open DirectGLSSW ActiveArc
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n + 2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (t : ℝ) (hct : leftParameter q c < t) (htb : t < afterBound q c)
variable (hRI : GLSSWRootIndependence) (hAux : Primitive.ClosedAuxiliary q hR)
include hRI

/-- After the first crossing, reindex ΓM by precisely the original supports
that omit the crossed event, retaining their actual moving open currents. -/
theorem GammaM_eq_reindexed_unselected_support :
    let ht0 : 0 ≤ t := (lt_trans (leftParameter_spec q c).1 hct).le
    let hM : Regular (moveStart q t) :=
      (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
    Primitive.GammaM (moveStart q t) hM
      (after_first_closedAuxiliary q hR c hc t hct htb hAux) =
    ∑ U : {U : Primitive.Support q hR // c ∉ U.val},
      (-1 : ℚ) ^ U.val.val.card *
        (Primitive.openCurrent (moveStart q t) hM
            ((afterFirstSupportEquiv q hR c hc t hct htb).symm U) *
          ∏ D ∈ Finset.univ.erase (openComponent q hR.noTriple U.val.val),
            Primitive.closedWeight q hR hAux U.val D) := by
  classical
  dsimp only
  let e := afterFirstSupportEquiv q hR c hc t hct htb
  unfold Primitive.GammaM
  apply Fintype.sum_equiv e
  intro V
  have hcard := afterFirstSupportEquiv_card q hR c hc t hct htb V
  have hprod := after_first_closedWeight_product_eq q hR c hc t hct htb hRI hAux
    (e V).val (e V).property
  dsimp only at hprod
  have hsub : (⟨(e V).val, (e V).property⟩ :
      {U : Primitive.Support q hR // c ∉ U.val}) = e V := by rfl
  have hV : (afterFirstSupportEquiv q hR c hc t hct htb).symm
      ⟨(e V).val, (e V).property⟩ = V := by
    rw [hsub, Equiv.symm_apply_apply]
  rw [hV] at hprod
  simp only [e, Equiv.symm_apply_apply]
  rw [hcard, ← hprod]

end DirectGLSSW.ActiveArc.Cursor.Surviving



