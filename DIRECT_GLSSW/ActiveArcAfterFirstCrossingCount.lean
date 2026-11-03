import ActiveArcFirstCrossing
import Mathlib.Data.Fintype.Card
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)

include hR hc in
/-- In the genuine after-first-crossing window the actual remaining crossing
carrier is equivalent to all original crossings except c, so its count drops. -/
theorem after_first_crossing_count_lt (t : ℝ)
    (htc : leftParameter q c<t) (htb : t<afterBound q c) :
    Fintype.card (Crossing (moveStart q t)) < Fintype.card (Crossing q) := by
  classical
  rw [Fintype.card_congr (crossingEquiv_after_first q hR c hc t htc htb)]
  exact Fintype.card_subtype_lt (x:=c) (by simp)

include hR hc in
/-- A positive actual event displacement inside the derived finite window
produces both physical Regularity and strict crossing-count descent. -/
theorem regular_after_first_and_crossing_count_lt (ε : ℝ) (hε : 0<ε)
    (hwindow : leftParameter q c+ε<afterBound q c) :
    Regular (moveStart q (leftParameter q c+ε)) ∧
      Fintype.card (Crossing (moveStart q (leftParameter q c+ε))) <
        Fintype.card (Crossing q) := by
  have hp := (leftParameter_spec q c).1
  have ht : leftParameter q c<leftParameter q c+ε := by linarith
  constructor
  · exact (regular_first_window_iff q hR c hc _ (by linarith) hwindow).mpr (ne_of_gt ht)
  · exact after_first_crossing_count_lt q hR c hc _ ht hwindow
end DirectGLSSW.ActiveArc.Cursor
