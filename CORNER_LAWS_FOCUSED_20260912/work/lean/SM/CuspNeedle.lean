import SM.CuspCrossing

/-! The nonsingular needle corner has the negative sign of Delta. Together
with the actual crossing test this proves both source needle-turn patterns. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n]

def cuspOtherCorner (b : Bool) (j : ZMod n) : ZMod n := if b then j + 1 else j - 1

theorem cusp_other_needle_multiple {P : LabelledTuple n} {b : Bool} {j : ZMod n}
    (hc : CuspCase P j b) :
    ∃ r : ℝ, r < 0 ∧ det (edge P (cuspOtherCorner b j - 1))
      (edge P (cuspOtherCorner b j)) = r * cuspDelta P b j := by
  cases b
  · obtain ⟨_, t, ht0, _, ht⟩ := hc
    have he : edge P (j - 1) = (-t) • edge P j := by
      simp only [edge, sub_add_cancel]
      rw [ht]
      ext <;> dsimp <;> ring
    refine ⟨-t, neg_neg_of_pos ht0, ?_⟩
    have hi := cusp_indices_B j
    simp only [cuspOtherCorner, Bool.false_eq_true, ↓reduceIte, cuspDelta, hi.1, hi.2.1]
    have hj : j - 1 - 1 = j - 2 := by ring
    rw [hj, he, det_smul_right]
  · obtain ⟨r, hr, he⟩ := cusp_negative_pair hc
    refine ⟨r, hr, ?_⟩
    have hi := cusp_indices_A j
    simp only [cuspOtherCorner, ↓reduceIte, cuspDelta, hi.1, hi.2.1, add_sub_cancel_right]
    rw [he]
    dsimp [det]; ring

theorem cusp_other_needle_sign {P : LabelledTuple n} {b : Bool} {j : ZMod n}
    (hc : CuspCase P j b) :
    turn P (cuspOtherCorner b j) = -SignType.sign (cuspDelta P b j) := by
  obtain ⟨r, hr, he⟩ := cusp_other_needle_multiple hc
  rw [turn_det, he, sign_mul, sign_eq_neg_one_iff.mpr hr, neg_one_mul]

theorem cusp_other_needle_persists {P : LabelledTuple n} {b : Bool} {j : ZMod n}
    (hc : CuspCase P j b) (hd : cuspDelta P b j ≠ 0) :
    ∀ᶠ Q in 𝓝 P, turn Q (cuspOtherCorner b j) = -SignType.sign (cuspDelta P b j) := by
  obtain ⟨r, hr, he⟩ := cusp_other_needle_multiple hc
  have hn : det (edge P (cuspOtherCorner b j - 1)) (edge P (cuspOtherCorner b j)) ≠ 0 := by
    rw [he]
    exact mul_ne_zero hr.ne hd
  have hc' : ContinuousAt (fun Q : LabelledTuple n => turn Q (cuspOtherCorner b j)) P := by
    simp only [turn_det]
    exact (continuousAt_sign_of_ne_zero hn).comp
      (f := fun Q : LabelledTuple n => det (edge Q (cuspOtherCorner b j - 1))
        (edge Q (cuspOtherCorner b j)))
      (continuousAt_det (continuous_edge _).continuousAt (continuous_edge _).continuousAt)
  have hs := hc'.eventually
    (isOpen_discrete _ |>.mem_nhds (Set.mem_singleton (turn P (cuspOtherCorner b j))))
  filter_upwards [hs] with Q hQ
  exact hQ.trans (cusp_other_needle_sign hc)

theorem sign_eq_or_eq_neg {x d : ℝ} (hx : x ≠ 0) (hd : d ≠ 0) :
    SignType.sign x = SignType.sign d ∨ SignType.sign x = -SignType.sign d := by
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hd with hd | hd
  · exact Or.inl ((sign_eq_neg_one_iff.mpr hx).trans (sign_eq_neg_one_iff.mpr hd).symm)
  · right; rw [sign_eq_neg_one_iff.mpr hx, sign_eq_one_iff.mpr hd]
  · right; rw [sign_eq_one_iff.mpr hx, sign_eq_neg_one_iff.mpr hd]; rfl
  · exact Or.inl ((sign_eq_one_iff.mpr hx).trans (sign_eq_one_iff.mpr hd).symm)

theorem cusp_needle_patterns (hn : 4 ≤ n) {P : LabelledTuple n} {j : ZMod n}
    (hz : pointZeroTriples P = {turnSupport j}) {b : Bool} (hc : CuspCase P j b) :
    ∀ᶠ Q in 𝓝 P, G1 Q →
      (IsCrossing Q {cuspFirst b j, cuspLast b j} →
        turn Q (cuspCorner₁ b j) = turn Q j ∧ turn Q (cuspCorner₂ b j) = turn Q j) ∧
      (¬ IsCrossing Q {cuspFirst b j, cuspLast b j} →
        turn Q (cuspCorner₁ b j) = -turn Q (cuspCorner₂ b j)) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hd := cusp_delta_ne_zero hn hz hc
  filter_upwards [cusp_newborn_persists hn hz hc, cusp_other_needle_persists hc hd] with Q hcross hother
  intro hG
  have hsame : IsCrossing Q {cuspFirst b j, cuspLast b j} →
      turn Q (cuspOtherCorner b j) = turn Q j := fun h => hother.trans ((hcross.2.2 hG).mp h).symm
  have hopposite : ¬ IsCrossing Q {cuspFirst b j, cuspLast b j} →
      turn Q (cuspOtherCorner b j) = -turn Q j := by
    intro hno
    have hne : turn Q j ≠ -SignType.sign (cuspDelta P b j) :=
      fun he => hno ((hcross.2.2 hG).mpr he)
    have ht : turn Q j = SignType.sign (cuspDelta P b j) := by
      have hh := sign_eq_or_eq_neg (g1_turn_nonzero (by omega) hG j) hd
      rw [← turn_det] at hh
      exact hh.resolve_right hne
    rw [hother, ht]
  constructor
  · intro hx
    have hs := hsame hx
    cases b
    · have hi := cusp_indices_B j
      rw [hi.2.2.1, hi.2.2.2]
      exact ⟨hs, rfl⟩
    · have hi := cusp_indices_A j
      rw [hi.2.2.1, hi.2.2.2]
      exact ⟨rfl, hs⟩
  · intro hx
    have hs := hopposite hx
    cases b
    · have hi := cusp_indices_B j
      simpa only [hi.2.2.1, hi.2.2.2, cuspOtherCorner, Bool.false_eq_true, ↓reduceIte] using hs
    · have hi := cusp_indices_A j
      rw [hi.2.2.1, hi.2.2.2]
      have hs' : turn Q (j + 1) = -turn Q j := hs
      rw [hs', neg_neg]

end SM
