import SM.CuspCenter
import SM.Chambers

/-! Actual parameters on both finite cusp segments. The parameter measured
from the contact endpoint is derived by Cramer's rule in each source case. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n]

theorem edgeParameter_reverse_eq_second (P : LabelledTuple n) (i k : ZMod n) :
    edgeParameter P k i = cramerSecond (P i) (P k) (edge P i) (edge P k) := by
  have he : det (P i - P k) (edge P i) = -det (P k - P i) (edge P i) := by
    dsimp [det]; ring
  simp only [edgeParameter, cramerFirst, cramerSecond, he]
  rw [det_swap (edge P i) (edge P k), neg_div_neg_eq]

theorem edgeParameters_intersection (P : LabelledTuple n) (i k : ZMod n)
    (hd : det (edge P i) (edge P k) ≠ 0) :
    edgePoint P i (edgeParameter P i k) = edgePoint P k (edgeParameter P k i) := by
  rw [edgeParameter_reverse_eq_second P i k]
  exact cramer_intersection (P i) (P k) (edge P i) (edge P k) hd

theorem edgeParameters_of_intersection {P : LabelledTuple n} {i k : ZMod n}
    (hd : det (edge P i) (edge P k) ≠ 0) {s t : ℝ}
    (he : edgePoint P i s = edgePoint P k t) :
    edgeParameter P i k = s ∧ edgeParameter P k i = t := by
  exact intersection_parameters_unique hd (edgeParameters_intersection P i k hd) he

noncomputable def cuspEndpointDistance (P : LabelledTuple n) (b : Bool) (j : ZMod n) : ℝ :=
  if b then edgeParameter P (cuspLast b j) (cuspFirst b j)
  else 1 - edgeParameter P (cuspFirst b j) (cuspLast b j)

noncomputable def cuspInteriorParameter (P : LabelledTuple n) (b : Bool) (j : ZMod n) : ℝ :=
  if b then edgeParameter P (cuspFirst b j) (cuspLast b j)
  else edgeParameter P (cuspLast b j) (cuspFirst b j)

theorem cusp_distance_formula (P : LabelledTuple n) (b : Bool) (j : ZMod n)
    (hd : cuspDelta P b j ≠ 0) :
    cuspEndpointDistance P b j = -det (edge P (j - 1)) (edge P j) / cuspDelta P b j := by
  cases b
  · have hi := cusp_indices_B j
    have hn : cuspDelta P false j -
        det (P j - P (j - 2)) (edge P j) = -det (edge P (j - 1)) (edge P j) := by
      simp only [cuspDelta, hi.1, hi.2.1, edge, sub_add_cancel]
      have he : j - 2 + 1 = j - 1 := by ring
      rw [he]
      dsimp [det]; ring
    change 1 - edgeParameter P (cuspFirst false j) (cuspLast false j) = _
    simp only [edgeParameter, cramerFirst]
    change 1 - det (P (cuspLast false j) - P (cuspFirst false j))
      (edge P (cuspLast false j)) / cuspDelta P false j = _
    rw [hi.1, hi.2.1, one_sub_div hd, hn]
  · have hi := cusp_indices_A j
    have hn : det (P (j + 1) - P (j - 1)) (edge P (j - 1)) =
        -det (edge P (j - 1)) (edge P j) := by
      simp only [edge, sub_add_cancel]
      dsimp [det]; ring
    change edgeParameter P (cuspLast true j) (cuspFirst true j) = _
    rw [edgeParameter_reverse_eq_second]
    simp only [cramerSecond, hi.1, hi.2.1, hn]
    simp only [cuspDelta, hi.1, hi.2.1]

theorem cusp_center_parameters {P : LabelledTuple n} {b : Bool} {j : ZMod n}
    (hc : CuspCase P j b) (hd : cuspDelta P b j ≠ 0) :
    cuspEndpointDistance P b j = 0 ∧
      0 < cuspInteriorParameter P b j ∧ cuspInteriorParameter P b j < 1 := by
  cases b
  · have hi := cusp_indices_B j
    obtain ⟨_, t, ht0, ht1, ht⟩ := hc
    have he : edgePoint P (cuspFirst false j) 1 = edgePoint P (cuspLast false j) t := by
      rw [hi.1, hi.2.1, edgePoint_one]
      have he : j - 2 + 1 = j - 1 := by ring
      rw [he]
      exact ht
    have hp := edgeParameters_of_intersection hd he
    simp only [cuspEndpointDistance, cuspInteriorParameter, Bool.false_eq_true,
      ↓reduceIte, hp.1, hp.2, sub_self]
    exact ⟨True.intro, ht0, ht1⟩
  · have hi := cusp_indices_A j
    obtain ⟨_, t, ht0, ht1, ht⟩ := hc
    have he : edgePoint P (cuspFirst true j) t = edgePoint P (cuspLast true j) 0 := by
      rw [hi.1, hi.2.1, edgePoint_zero]
      simpa only [edgePoint, edge, sub_add_cancel] using ht.symm
    have hp := edgeParameters_of_intersection hd he
    simp only [cuspEndpointDistance, cuspInteriorParameter, ↓reduceIte, hp.1, hp.2]
    exact ⟨True.intro, ht0, ht1⟩

theorem continuousAt_edgeParameter_of_det {P : LabelledTuple n} {i k : ZMod n}
    (hd : det (edge P i) (edge P k) ≠ 0) :
    ContinuousAt (fun Q : LabelledTuple n => edgeParameter Q i k) P :=
  continuousAt_cramerFirst (continuous_vertex i).continuousAt (continuous_vertex k).continuousAt
    (continuous_edge i).continuousAt (continuous_edge k).continuousAt hd

theorem continuous_cuspDelta (b : Bool) (j : ZMod n) :
    Continuous (fun P : LabelledTuple n => cuspDelta P b j) := by
  exact continuous_iff_continuousAt.mpr fun _ =>
    continuousAt_det (continuous_edge _).continuousAt (continuous_edge _).continuousAt

theorem continuousAt_cusp_parameters {P : LabelledTuple n} {b : Bool} {j : ZMod n}
    (hd : cuspDelta P b j ≠ 0) :
    ContinuousAt (fun Q : LabelledTuple n => cuspEndpointDistance Q b j) P ∧
    ContinuousAt (fun Q : LabelledTuple n => cuspInteriorParameter Q b j) P := by
  have hf := continuousAt_edgeParameter_of_det hd
  have hg := continuousAt_edgeParameter_of_det (by
    rw [det_swap]; exact neg_ne_zero.mpr hd)
  cases b
  · exact ⟨continuousAt_const.sub hf, hg⟩
  · exact ⟨hg, hf⟩

theorem cusp_parameters_persist {P : LabelledTuple n} {b : Bool} {j : ZMod n}
    (hc : CuspCase P j b) (hd : cuspDelta P b j ≠ 0) :
    ∀ᶠ Q in 𝓝 P, cuspDelta Q b j ≠ 0 ∧
      SignType.sign (cuspDelta Q b j) = SignType.sign (cuspDelta P b j) ∧
      |cuspEndpointDistance Q b j| < 1 ∧
      0 < cuspInteriorParameter Q b j ∧ cuspInteriorParameter Q b j < 1 := by
  have hp := cusp_center_parameters hc hd
  have hcont := continuousAt_cusp_parameters hd
  have hdcont := (continuous_cuspDelta (n := n) b j).continuousAt (x := P)
  have hnonzero := hdcont.eventually (isOpen_compl_singleton.mem_nhds hd)
  have hsign := ((continuousAt_sign_of_ne_zero hd).comp
    (f := fun Q : LabelledTuple n => cuspDelta Q b j) hdcont).eventually
    (isOpen_discrete _ |>.mem_nhds (Set.mem_singleton (SignType.sign (cuspDelta P b j))))
  have hinter := continuousAt_preserves_unit_interval hcont.2 hp.2.1 hp.2.2
  have hsmall := hcont.1.abs.eventually
    (isOpen_Iio.mem_nhds (show |cuspEndpointDistance P b j| < 1 by rw [hp.1, abs_zero]; norm_num))
  filter_upwards [hnonzero, hsign, hsmall, hinter] with Q hdQ hsQ hsmallQ hiQ
  exact ⟨hdQ, hsQ, hsmallQ, hiQ⟩

end SM
