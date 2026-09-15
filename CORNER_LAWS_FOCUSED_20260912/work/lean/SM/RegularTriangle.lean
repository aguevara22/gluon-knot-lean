import SM.RotationBounds

/-! Regular triangles have nonzero common turn determinant. This uses
regularity on closing edges, rather than silently adding genericity. -/

namespace SM

theorem three_regular_edges_det_ne_zero {u v w : Plane}
    (huv : RegularPair u v) (hvw : RegularPair v w) (hc : u + v + w = 0) : det u v ≠ 0 := by
  intro hd
  have hz := (principalAngle_zero_iff_det_zero huv).mpr hd
  obtain ⟨r, hr, hv⟩ := (principalAngle_eq_zero_iff huv.1 huv.2.1).mp hz
  apply hvw.2.2
  refine ⟨-(1 + r) / r, div_neg_of_neg_of_pos (by linarith) hr, ?_⟩
  have hw : w = -(u + v) := eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using hc)
  rw [hv, smul_smul, div_mul_cancel₀ _ hr.ne', hw, hv]
  simp only [neg_smul, add_smul, one_smul]

theorem triangle_sum_edges (P : LabelledTuple 3) :
    edge P 0 + edge P 1 + edge P 2 = 0 := by
  have hf : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  have h0 : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)) := by decide
  have h1 : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)) := by decide
  simpa only [hf, Finset.sum_insert h0, Finset.sum_insert h1, Finset.sum_singleton,
    add_assoc] using sum_edges P

theorem regular_triangle_det_ne_zero {P : LabelledTuple 3} (h : Regular P) :
    det (edge P 0) (edge P 1) ≠ 0 := by
  have h01 : RegularPair (edge P 0) (edge P 1) := by simpa using h 1
  have h12 : RegularPair (edge P 1) (edge P 2) := by
    simpa only [show (2 : ZMod 3) - 1 = 1 by decide] using h 2
  exact three_regular_edges_det_ne_zero h01 h12 (triangle_sum_edges P)

theorem triangle_turn_det (P : LabelledTuple 3) (i : ZMod 3) :
    det (edge P (i - 1)) (edge P i) = det (edge P 0) (edge P 1) := by
  have hi : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  have h01 : (0 : ZMod 3) - 1 = 2 := by decide
  have h12 : (2 : ZMod 3) - 1 = 1 := by decide
  have h21 : (2 : ZMod 3) + 1 = 0 := by decide
  have h11 : (1 : ZMod 3) + 1 = 2 := by decide
  rcases hi i with rfl | rfl | rfl <;> simp [edge, det, h01, h12, h21, h11] <;> ring

theorem regular_triangle_principalTurn_sign {P : LabelledTuple 3} (h : Regular P) (i : ZMod 3) :
    SignType.sign (principalTurn P i) = SignType.sign (det (edge P 0) (edge P 1)) := by
  have hs := principalAngle_sign (h i)
  simpa only [principalTurn, triangle_turn_det] using hs

end SM
