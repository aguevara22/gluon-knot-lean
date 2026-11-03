import ActiveArcSurvivingSelections

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.Surviving
open DirectGLSSW ActiveArc
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (t : ℝ) (hct : leftParameter q c < t) (htb : t < afterBound q c)

/-- Actual supports after removal correspond to exactly the original supports
not selecting the removed crossing. Nonalternation is proved, not supplied. -/
def afterFirstSupportEquiv :
    let ht0 : 0 ≤ t := (lt_trans (leftParameter_spec q c).1 hct).le
    let hM : Regular (moveStart q t) :=
      (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
    Primitive.Support (moveStart q t) hM ≃ {U : Primitive.Support q hR // c ∉ U.val} := by
  let ht0 : 0 ≤ t := (lt_trans (leftParameter_spec q c).1 hct).le
  let ht1 : t < 1 := lt_of_lt_of_le htb (afterBound_le_one q c)
  let hM : Regular (moveStart q t) :=
    (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
  have hS (U : {U : Primitive.Support q hR // c ∉ U.val}) : ∀ d∈U.val.val, Survives q t d := by
    intro d hd
    exact (survives_after_first_iff q hR c hc t hct htb d).mpr (fun he => U.property (he ▸ hd))
  let forward (V : Primitive.Support (moveStart q t) hM) :
      {U : Primitive.Support q hR // c ∉ U.val} :=
    ⟨⟨originalSelection q t ht0 ht1 V.val,
      (originalSelection_nonalternating q hR t ht0 ht1 hM V.val).mpr V.property⟩,by
      intro hh
      exact (survives_after_first_iff q hR c hc t hct htb c).mp
        (originalSelection_survives q hR t ht0 ht1 V.val c hh) rfl⟩
  let backward (U : {U : Primitive.Support q hR // c ∉ U.val}) :
      Primitive.Support (moveStart q t) hM :=
    ⟨movingSelection q t ht0 ht1 U.val.val,by
      apply (originalSelection_nonalternating q hR t ht0 ht1 hM _).mp
      rw [originalSelection_movingSelection q t ht0 ht1 U.val.val (hS U)]
      exact U.val.property⟩
  exact {
    toFun := forward
    invFun := backward
    left_inv := fun V => Subtype.ext (movingSelection_originalSelection q t ht0 ht1 V.val)
    right_inv := fun U => Subtype.ext (Subtype.ext (originalSelection_movingSelection q t ht0 ht1 U.val.val (hS U))) }

@[simp] theorem afterFirstSupportEquiv_val :
    let ht0 : 0 ≤ t := (lt_trans (leftParameter_spec q c).1 hct).le
    let ht1 : t < 1 := lt_of_lt_of_le htb (afterBound_le_one q c)
    let hM : Regular (moveStart q t) :=
      (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
    ∀ V : Primitive.Support (moveStart q t) hM,
      (afterFirstSupportEquiv q hR c hc t hct htb V).val.val = originalSelection q t ht0 ht1 V.val := by
  intro ht0 ht1 hM V
  rfl

@[simp] theorem afterFirstSupportEquiv_symm_val
    (U : {U : Primitive.Support q hR // c ∉ U.val}) :
    let ht0 : 0 ≤ t := (lt_trans (leftParameter_spec q c).1 hct).le
    let ht1 : t < 1 := lt_of_lt_of_le htb (afterBound_le_one q c)
    ((afterFirstSupportEquiv q hR c hc t hct htb).symm U).val = movingSelection q t ht0 ht1 U.val.val := by
  rfl

@[simp] theorem afterFirstSupportEquiv_card :
    let ht0 : 0 ≤ t := (lt_trans (leftParameter_spec q c).1 hct).le
    let hM : Regular (moveStart q t) :=
      (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
    ∀ V : Primitive.Support (moveStart q t) hM,
      (afterFirstSupportEquiv q hR c hc t hct htb V).val.val.card = V.val.card := by
  intro ht0 hM V
  exact originalSelection_card q t ht0 (lt_of_lt_of_le htb (afterBound_le_one q c)) V.val

end DirectGLSSW.ActiveArc.Cursor.Surviving
