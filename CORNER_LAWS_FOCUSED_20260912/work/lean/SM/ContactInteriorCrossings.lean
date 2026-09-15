import SM.ContactApproach

/-! Exact central interpretation: the transverse interior crossings are
precisely the raw closed-segment crossings outside the two contact supports. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {M a : ZMod n}

def IsInteriorCrossing (P : LabelledTuple n) (s : Finset (ZMod n)) : Prop :=
  ∃ i j : ZMod n, s = {i, j} ∧ remote i j ∧ det (edge P i) (edge P j) ≠ 0 ∧
    ∃ q : Plane, q ∈ edgeInterior P i ∧ q ∈ edgeInterior P j

theorem contact_leg_no_common_interiors (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (forward : Bool) : ¬ ∃ q : Plane, q ∈ edgeInterior P a ∧
      q ∈ edgeInterior P (contactLeg forward M) := by
  rintro ⟨q, ⟨s, hs0, hs1, hs⟩, ⟨t, ht0, ht1, ht⟩⟩
  have hmc := hm
  obtain ⟨r, hr0, hr1, hr⟩ := hmc
  have hdet := contact_pair_det_ne_zero hn hsep hz hm forward
  have hdetrev : det (edge P (contactLeg forward M)) (edge P a) ≠ 0 := by
    rw [det_swap]; exact neg_ne_zero.mpr hdet
  have hparam : edgeParameter P (contactLeg forward M) a = t :=
    (div_eq_iff hdetrev).mpr (intersection_parameter_identity (ht.symm.trans hs))
  have hc := (contact_parameters_center hn hsep hz hm r hr forward).2
  rw [hparam] at hc
  cases forward
  · exact ht1.ne hc
  · exact ht0.ne' hc

theorem contact_interior_crossing_iff (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) (hm : P M ∈ edgeInterior P a)
    (s : Finset (ZMod n)) :
    IsInteriorCrossing P s ↔ IsCrossing P s ∧ ¬ ContactAffected M a s := by
  constructor
  · rintro ⟨i, j, hs, hr, hd, q, hi, hj⟩
    refine ⟨⟨i, j, hs, hr, q, edgeInterior_subset_edgeSegment P i hi,
      edgeInterior_subset_edgeSegment P j hj⟩, ?_⟩
    intro ha
    have hmem : ∀ k ∈ s, q ∈ edgeInterior P k := by
      intro k hk
      rw [hs] at hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hi
      · exact Finset.mem_singleton.mp hk ▸ hj
    rcases ha with ha | ha
    · apply contact_leg_no_common_interiors hn hsep hz hm false
      exact ⟨q, hmem a (by rw [ha]; simp), hmem (M - 1) (by rw [ha]; simp)⟩
    · apply contact_leg_no_common_interiors hn hsep hz hm true
      exact ⟨q, hmem a (by rw [ha]; simp), hmem M (by rw [ha]; simp)⟩
  · rintro ⟨⟨i, j, hs, hr, q, hi, hj⟩, ha⟩
    have hnot : ¬ ContactAffected M a {i, j} := by simpa only [hs] using ha
    have hg := contact_unaffected_pair_geometry hn hsep hz hr hnot hi hj
    exact ⟨i, j, hs, hr, hg.2.2, q, hg.1, hg.2.1⟩

end SM
