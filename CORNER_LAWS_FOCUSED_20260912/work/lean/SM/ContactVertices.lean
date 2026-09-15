import SM.ContactParameters

/-! Persistent crossings at a vertex wall avoid every actual vertex,
particularly the contact point needed for later finite localization. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {M a : ZMod n}

theorem interior_vertex_nonincident (hedge : ∀ i, edge P i ≠ 0)
    {i k : ZMod n} (hp : P k ∈ edgeInterior P i) : ¬ incident k i := by
  apply (nonincident_iff k i).mpr
  obtain ⟨s, hs0, hs1, hs⟩ := hp
  constructor
  · intro he
    subst k
    have heq : s = 0 := edgePoint_injective (hedge i)
      (hs.symm.trans (edgePoint_zero P i).symm)
    exact hs0.ne' heq
  · intro he
    subst k
    have heq : s = 1 := edgePoint_injective (hedge i)
      (hs.symm.trans (edgePoint_one P i).symm)
    exact hs1.ne heq

theorem contact_persistent_point_ne_vertex (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) {i j : ZMod n}
    (hcross : IsCrossing P {i, j}) (hnot : ¬ ContactAffected M a {i, j}) (k : ZMod n) :
    crossingPoint (⟨{i, j}, hcross⟩ : Crossing P) ≠ P k := by
  intro he
  have hd := contact_pair_data hn hsep hz hcross hnot
  have hn5 := contactSeparated_size hn hsep
  have hedge := singlePointTriple_edge_ne_zero (by omega) hz
  have hi : P k ∈ edgeInterior P i := he ▸ hd.point_in_i
  have hj : P k ∈ edgeInterior P j := he ▸ hd.point_in_j
  have hni := interior_vertex_nonincident hedge hi
  have hnj := interior_vertex_nonincident hedge hj
  have hia := (contact_vertex_incidence hn hsep hz hni
    (edgeInterior_subset_edgeSegment P i hi)).1
  have hja := (contact_vertex_incidence hn hsep hz hnj
    (edgeInterior_subset_edgeSegment P j hj)).1
  exact (remote_endpoints i j (crossing_pair_remote hcross)).1 (hja.trans hia.symm)

theorem contact_parameter_ne_contact (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) {j : ZMod n}
    (hcross : IsCrossing P {a, j}) (hnot : ¬ ContactAffected M a {a, j})
    (r : ℝ) (hr : P M = edgePoint P a r) : edgeParameter P a j ≠ r := by
  intro he
  have hd := contact_pair_data hn hsep hz hcross hnot
  apply contact_persistent_point_ne_vertex hn hsep hz hcross hnot M
  rw [hd.point_eq, he]
  exact hr.symm

end SM
