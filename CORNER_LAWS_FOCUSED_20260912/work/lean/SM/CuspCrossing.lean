import SM.CuspParameters

/-! The cusp crossing test uses both actual segment parameters. It holds in
one neighbourhood of the singular centre for every nearby G1 tuple. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n]

theorem crossing_iff_edgeParameters_interior (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : G1 P) {i k : ZMod n} (hr : remote i k)
    (hd : det (edge P i) (edge P k) ≠ 0) :
    IsCrossing P {i, k} ↔
      (0 < edgeParameter P i k ∧ edgeParameter P i k < 1) ∧
      (0 < edgeParameter P k i ∧ edgeParameter P k i < 1) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  rw [isCrossing_pair P i k hr]
  constructor
  · rintro ⟨x, ⟨s, hs0, hs1, hs⟩, ⟨t, ht0, ht1, ht⟩⟩
    have he := hs.symm.trans ht
    have hinter := g1_remote_parameters_interior hP hr hs0 hs1 ht0 ht1 he
    have hp := edgeParameters_of_intersection hd he
    exact ⟨by simpa only [hp.1] using And.intro hinter.1 hinter.2.1,
      by simpa only [hp.2] using And.intro hinter.2.2.1 hinter.2.2.2⟩
  · rintro ⟨hs, ht⟩
    exact ⟨edgePoint P i (edgeParameter P i k),
      ⟨_, hs.1.le, hs.2.le, rfl⟩,
      ⟨_, ht.1.le, ht.2.le, edgeParameters_intersection P i k hd⟩⟩

theorem cusp_crossing_iff_distance_pos (hn : 4 ≤ n) {P : LabelledTuple n}
    (hP : G1 P) {b : Bool} {j : ZMod n} (hd : cuspDelta P b j ≠ 0)
    (hs : |cuspEndpointDistance P b j| < 1)
    (hi : 0 < cuspInteriorParameter P b j ∧ cuspInteriorParameter P b j < 1) :
    IsCrossing P {cuspFirst b j, cuspLast b j} ↔ 0 < cuspEndpointDistance P b j := by
  rw [crossing_iff_edgeParameters_interior (by omega) hP (cusp_newborn_remote hn b j) hd]
  have hs1 := (abs_lt.mp hs).2
  cases b
  · change 0 < edgeParameter P (cuspLast false j) (cuspFirst false j) ∧
      edgeParameter P (cuspLast false j) (cuspFirst false j) < 1 at hi
    change 1 - edgeParameter P (cuspFirst false j) (cuspLast false j) < 1 at hs1
    change _ ↔ 0 < 1 - edgeParameter P (cuspFirst false j) (cuspLast false j)
    constructor
    · intro h; linarith [h.1.2]
    · intro h; exact ⟨⟨by linarith, by linarith⟩, hi⟩
  · change 0 < edgeParameter P (cuspFirst true j) (cuspLast true j) ∧
      edgeParameter P (cuspFirst true j) (cuspLast true j) < 1 at hi
    change edgeParameter P (cuspLast true j) (cuspFirst true j) < 1 at hs1
    change _ ↔ 0 < edgeParameter P (cuspLast true j) (cuspFirst true j)
    exact ⟨fun h => h.2.1, fun h => ⟨hi, h, hs1⟩⟩

theorem neg_div_pos_iff_opposite_sign {x d : ℝ} (hx : x ≠ 0) (hd : d ≠ 0) :
    0 < -x / d ↔ SignType.sign x = -SignType.sign d := by
  rcases lt_or_gt_of_ne hx with hx | hx <;>
    rcases lt_or_gt_of_ne hd with hd | hd
  · rw [sign_eq_neg_one_iff.mpr hx, sign_eq_neg_one_iff.mpr hd]
    have h := div_neg_of_pos_of_neg (neg_pos.mpr hx) hd
    norm_num
    exact h.le
  · rw [sign_eq_neg_one_iff.mpr hx, sign_eq_one_iff.mpr hd]
    norm_num
    exact div_pos (neg_pos.mpr hx) hd
  · rw [sign_eq_one_iff.mpr hx, sign_eq_neg_one_iff.mpr hd]
    norm_num
    exact div_pos_of_neg_of_neg (neg_neg_of_pos hx) hd
  · rw [sign_eq_one_iff.mpr hx, sign_eq_one_iff.mpr hd]
    have h := div_neg_of_neg_of_pos (neg_neg_of_pos hx) hd
    norm_num
    exact h.le

theorem cusp_crossing_iff_turn (hn : 4 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    {b : Bool} {j : ZMod n} (hd : cuspDelta P b j ≠ 0)
    (hs : |cuspEndpointDistance P b j| < 1)
    (hi : 0 < cuspInteriorParameter P b j ∧ cuspInteriorParameter P b j < 1) :
    IsCrossing P {cuspFirst b j, cuspLast b j} ↔ turn P j = -SignType.sign (cuspDelta P b j) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  rw [cusp_crossing_iff_distance_pos hn hP hd hs hi, cusp_distance_formula P b j hd,
    neg_div_pos_iff_opposite_sign (g1_turn_nonzero (by omega) hP j) hd, turn_det]

theorem cusp_newborn_persists (hn : 4 ≤ n) {P : LabelledTuple n}
    (hz : pointZeroTriples P = {turnSupport j}) {b : Bool} (hc : CuspCase P j b) :
    ∀ᶠ Q in 𝓝 P, cuspDelta Q b j ≠ 0 ∧
      SignType.sign (cuspDelta Q b j) = SignType.sign (cuspDelta P b j) ∧
      (G1 Q → (IsCrossing Q {cuspFirst b j, cuspLast b j} ↔
        turn Q j = -SignType.sign (cuspDelta P b j))) := by
  filter_upwards [cusp_parameters_persist hc (cusp_delta_ne_zero hn hz hc)] with Q hQ
  refine ⟨hQ.1, hQ.2.1, fun hG => ?_⟩
  rw [cusp_crossing_iff_turn hn hG hQ.1 hQ.2.2.1 hQ.2.2.2, hQ.2.1]

end SM
