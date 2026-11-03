import SupportingTruncationExposure
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.TruncationDirection
attribute [local instance] Classical.propDecidable

/-- Every genuine crossing lies strictly above a uniquely supporting original
vertex; hence all daughter event lines are avoided by this same direction. -/
theorem strict_support_event_avoidance {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a : Fin n) (v : PlanarPoint ℝ)
    (hsupport : ∀ x : Fin n, x ≠ a → 0 < planarDet v (q x-q a)) :
    ∀ e : PolygonEvent q, polygonEventPoint q e ≠ q a →
      planarDet v (polygonEventPoint q e-q a) ≠ 0 := by
  have hnonneg (x : Fin n) : 0 ≤ planarDet v (q x-q a) := by
    by_cases hx : x=a
    · subst x; simp [planarDet]
    · exact le_of_lt (hsupport x hx)
  intro e he
  rcases e with x|⟨c,b⟩
  · exact ne_of_gt (hsupport x (fun hx => he (congrArg q hx)))
  · change planarDet v (crossingPoint q c-q a) ≠ 0
    obtain ⟨t,ht,ht1,hpt⟩ := crossingPoint_mem_left q c
    have hdet : planarDet v (crossingPoint q c-q a) =
        (1-t)*planarDet v (q c.val.1-q a)+
          t*planarDet v (q (cyclicSuccessor c.val.1)-q a) := by
      rw [hpt]
      simp [planarDet,affinePoint]; ring
    rw [hdet]
    apply ne_of_gt
    by_cases hx : c.val.1=a
    · have hs : cyclicSuccessor c.val.1 ≠ a := by
        rw [hx]
        exact cyclicSuccessor_ne_self (by have := hq.size_ge_three;omega) a
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (le_of_lt (sub_pos.mpr ht1)) (hnonneg _))
        (mul_pos ht (hsupport _ hs))
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr ht1) (hsupport _ hx))
        (mul_nonneg (le_of_lt ht) (hnonneg _))
end DirectGLSSW.TruncationDirection
