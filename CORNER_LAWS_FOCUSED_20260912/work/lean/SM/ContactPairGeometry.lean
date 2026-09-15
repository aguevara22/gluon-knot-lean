import SM.ContactCenter

/-! Every remote pair outside the two named contact pairs is disjoint or
transverse interior at a V/E centre. All endpoint incidences are classified. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {M a : ZMod n}

def ContactAffected (M a : ZMod n) (s : Finset (ZMod n)) : Prop :=
  s = {a, M - 1} ∨ s = {a, M}

theorem contact_endpoint_incidence_affected (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) {i j k : ZMod n}
    (hr : remote i j) (hk : k = i ∨ k = i + 1) (hp : P k ∈ edgeSegment P j) :
    ContactAffected M a {i, j} := by
  obtain ⟨hji, hji1, hj1i, hj1i1⟩ := remote_endpoints i j hr
  rcases hk with hk | hk
  · subst k
    have hki := (nonincident_iff i j).mpr ⟨hji.symm, hj1i.symm⟩
    obtain ⟨hj, hi⟩ := contact_vertex_incidence hn hsep hz hki hp
    right
    rw [hi, hj, Finset.pair_comm]
  · subst k
    have hki := (nonincident_iff (i + 1) j).mpr ⟨hji1.symm, hj1i1.symm⟩
    obtain ⟨hj, hi⟩ := contact_vertex_incidence hn hsep hz hki hp
    have hi' : i = M - 1 := by linear_combination hi
    left
    rw [hi', hj, Finset.pair_comm]

theorem edgeInterior_of_closed_ne_endpoints {i : ZMod n} {x : Plane}
    (hi : x ∈ edgeSegment P i) (h0 : x ≠ P i) (h1 : x ≠ P (i + 1)) :
    x ∈ edgeInterior P i := by
  obtain ⟨s, hs0, hs1, hs⟩ := hi
  have hsne0 : s ≠ 0 := by
    intro he
    apply h0
    simpa only [he, edgePoint_zero] using hs
  have hsne1 : s ≠ 1 := by
    intro he
    apply h1
    simpa only [he, edgePoint_one] using hs
  exact ⟨s, lt_of_le_of_ne hs0 hsne0.symm, lt_of_le_of_ne hs1 hsne1, hs⟩

theorem contact_unaffected_pair_geometry (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) {i j : ZMod n}
    (hr : remote i j) (hnot : ¬ ContactAffected M a {i, j}) {x : Plane}
    (hi : x ∈ edgeSegment P i) (hj : x ∈ edgeSegment P j) :
    x ∈ edgeInterior P i ∧ x ∈ edgeInterior P j ∧ det (edge P i) (edge P j) ≠ 0 := by
  have hn5 := contactSeparated_size hn hsep
  have hrev : ¬ ContactAffected M a {j, i} := by
    simpa only [Finset.pair_comm j i] using hnot
  have hi0 : P i ∉ edgeSegment P j := fun hp =>
    hnot (contact_endpoint_incidence_affected hn hsep hz hr (Or.inl rfl) hp)
  have hi1 : P (i + 1) ∉ edgeSegment P j := fun hp =>
    hnot (contact_endpoint_incidence_affected hn hsep hz hr (Or.inr rfl) hp)
  have hj0 : P j ∉ edgeSegment P i := fun hp =>
    hrev (contact_endpoint_incidence_affected hn hsep hz (remote_symm hr) (Or.inl rfl) hp)
  have hj1 : P (j + 1) ∉ edgeSegment P i := fun hp =>
    hrev (contact_endpoint_incidence_affected hn hsep hz (remote_symm hr) (Or.inr rfl) hp)
  exact ⟨edgeInterior_of_closed_ne_endpoints hi (fun he => hi0 (he ▸ hj)) (fun he => hi1 (he ▸ hj)),
    edgeInterior_of_closed_ne_endpoints hj (fun he => hj0 (he ▸ hi)) (fun he => hj1 (he ▸ hi)),
    singlePointTriple_remote_transverse (by omega) hz hr hi hj⟩

end SM
