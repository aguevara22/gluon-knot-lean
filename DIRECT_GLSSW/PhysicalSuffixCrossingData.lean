import ResizedPhysicalSuffix
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (a b : ℕ) (hs : a+b=n) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1)

theorem suffixWordCrossingEquiv_left_label
    (d : Crossing (Cursor.moveStart (suffixWord q a b hs) θ)) :
    (suffixWordCrossingEquiv q hR a b hs θ h0 h1 d).val.val.1.val = a+d.val.1.val := by
  subst n
  rfl

theorem suffixWordCrossingEquiv_right_label
    (d : Crossing (Cursor.moveStart (suffixWord q a b hs) θ)) :
    (suffixWordCrossingEquiv q hR a b hs θ h0 h1 d).val.val.2.val = a+d.val.2.val := by
  subst n
  rfl

theorem suffixWordCrossingEquiv_point
    (d : Crossing (Cursor.moveStart (suffixWord q a b hs) θ)) :
    crossingPoint q (suffixWordCrossingEquiv q hR a b hs θ h0 h1 d).val =
      crossingPoint (Cursor.moveStart (suffixWord q a b hs) θ) d := by
  subst n
  change crossingPoint q (suffixCrossingToOriginal q
    (Cursor.crossingEquiv (suffix q) (regular_suffix q hR) θ h0 h1 d).val) = _
  rw [suffixCrossingToOriginal_point q hR, Cursor.crossingEquiv_point]
  rfl
end DirectGLSSW.ActiveArc.Split
