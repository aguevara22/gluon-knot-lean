import ActiveArcClosedChildGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor
open Split
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (t : ℝ) (ht0 : 0 ≤ t) (htc : t < leftParameter q c)

include hR c hc ht0 htc in
/-- The pre-event physical arc is regular throughout the actual first chamber. -/
theorem before_first_regular : Regular (moveStart q t) :=
  (regular_first_window_iff q hR c hc t ht0
    (lt_trans htc (parameter_lt_afterBound q c))).mpr (ne_of_lt htc)

include hR ht0 in
/-- The surviving cut is the same physical intersection point. -/
theorem before_first_crossingPoint :
    crossingPoint (moveStart q t)
      (crossingFromOriginal q t (lt_trans htc (leftParameter_spec q c).2.1)
        c (survives_before_first q c hc t htc c)) = crossingPoint q c := by
  exact (crossingToOriginal_point q hR t ht0
    (lt_trans htc (leftParameter_spec q c).2.1) _).symm

include hR ht0 in
/-- Moving the mark before the first cut preserves which actual cut is first. -/
theorem before_first_isFirst :
    FirstCrossing (moveStart q t)
      (crossingFromOriginal q t (lt_trans htc (leftParameter_spec q c).2.1)
        c (survives_before_first q c hc t htc c)) := by
  let C := crossingFromOriginal q t (lt_trans htc (leftParameter_spec q c).2.1)
    c (survives_before_first q c hc t htc c)
  refine ⟨hc.1, ?_⟩
  intro d hd
  have ht1 := lt_trans htc (leftParameter_spec q c).2.1
  have hleft := crossingEquiv_firstParameter q hR t ht0 ht1 C hc.1
  have hright := crossingEquiv_firstParameter q hR t ht0 ht1 d hd
  have hmin := hc.2 (crossingEquiv q hR t ht0 ht1 d).val hd
  change leftParameter q c = t + (1-t)*leftParameter (moveStart q t) C at hleft
  rw [hleft,hright] at hmin
  have hpos : 0 < 1-t := by linarith
  nlinarith

include hR ht0 in
/-- The actual shortened parent is fixed before the physical cut is reached. -/
theorem before_first_parent (hcut : c.val.2.val=a) :
    parent (moveStart q t)
      (crossingFromOriginal q t (lt_trans htc (leftParameter_spec q c).2.1)
        c (survives_before_first q c hc t htc c)) hcut = parent q c hcut := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [parent_zero,parent_zero]
    exact before_first_crossingPoint q hR c hc t ht0 htc
  · rw [parent_succ,parent_succ,vertex_succ,moveStart_succ]

/-- The actual closed child, including its physical closing edge, is fixed
before the first cut. Its genericity is not assumed by this identity. -/
theorem before_first_child (hcut : c.val.2.val=a) :
    child (moveStart q t) (before_first_regular q hR c hc t ht0 htc)
      (crossingFromOriginal q t (lt_trans htc (leftParameter_spec q c).2.1)
        c (survives_before_first q c hc t htc c)) hc.1 hcut =
      child q hR c hc.1 hcut := by
  funext i
  by_cases hi : i=0
  · subst i
    rw [child_zero,child_zero]
    exact before_first_crossingPoint q hR c hc t ht0 htc
  · rw [child_nonzero _ _ _ _ _ i hi,child_nonzero _ _ _ _ _ i hi]
    exact moveStart_eq q t (childVertex i) (by
      intro h
      apply hi
      apply Fin.ext
      exact congrArg (fun z : Fin (a+b+2) => z.val) h)

/-- The positive shrinking-edge parameter lies strictly before the crossing. -/
theorem approach_parameter_bounds (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    0 ≤ leftParameter q c * (1-epsilon) ∧
      leftParameter q c * (1-epsilon) < leftParameter q c := by
  have hp := (leftParameter_spec q c).1
  constructor <;> nlinarith

include hc in
/-- The same physical endpoint path used by the short-first projector. -/
theorem moveStart_approach_endpoint (epsilon : ℝ) :
    moveStart q (leftParameter q c * (1-epsilon)) 0 =
      affinePoint (crossingPoint q c) (q 0) epsilon := by
  rw [moveStart_zero,(leftParameter_spec q c).2.2]
  simp only [hc.1]
  change affinePoint (q 0) (q 1) (leftParameter q c * (1-epsilon)) =
    affinePoint (affinePoint (q 0) (q 1) (leftParameter q c)) (q 0) epsilon
  ext <;> simp only [affinePoint] <;> ring

end DirectGLSSW.ActiveArc.Cursor
