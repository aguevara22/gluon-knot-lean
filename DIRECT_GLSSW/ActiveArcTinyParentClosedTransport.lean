import ActiveArcTinyParentClosedWeights

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive Nonalternation
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (η : ℝ) (hη : 0<η) (hη1 : η<1)

/-- Explicit orientation of the concrete support used in the closed-word/product lemmas. -/
theorem tinySupportOfParent_eq_supportEquiv_symm
    (T : Nonalternation.Support (ParentArc q c hcut) (ParentRegular q hR c hcut)) :
    tinySupportOfParent q hR c hc hcut η hη hη1 T =
      (tinyParentSupportEquiv q hR c hc hcut η hη hη1).symm T := by
  apply Subtype.ext
  rfl

theorem tinyParentSupportEquiv_tinySupportOfParent
    (T : Nonalternation.Support (ParentArc q c hcut) (ParentRegular q hR c hcut)) :
    tinyParentSupportEquiv q hR c hc hcut η hη hη1
      (tinySupportOfParent q hR c hc hcut η hη hη1 T) = T := by
  rw [tinySupportOfParent_eq_supportEquiv_symm q hR c hc hcut η hη hη1 T]
  exact (tinyParentSupportEquiv q hR c hc hcut η hη hη1).apply_symm_apply T

end DirectGLSSW.ActiveArc.LiteralTinyParent
