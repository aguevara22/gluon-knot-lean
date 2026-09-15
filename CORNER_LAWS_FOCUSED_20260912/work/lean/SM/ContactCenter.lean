import SM.ContactIndices
import SM.NonFlatCenter

/-! Actual central vertex contacts and regularity for V/E wall supports.
In particular the unique contact location is derived from the zero set. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {M a : ZMod n}

theorem contact_vertex_incidence (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) {k i : ZMod n}
    (hki : ¬ incident k i) (hp : P k ∈ edgeSegment P i) : i = a ∧ k = M := by
  letI : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨hk0, hk1⟩ := (nonincident_iff k i).mp hki
  obtain ⟨t, _, _, ht⟩ := hp
  have hchi : chi P i (i + 1) k = 0 := by
    rw [chi_edge, ht, det_edge_line]
    simp
  have hm := (mem_pointZeroTriples P {i, i + 1, k}).mpr
    ((pointZeroTriple_iff (next_ne_self i).symm hk1.symm hk0.symm).mpr hchi)
  rw [hz, Finset.mem_singleton] at hm
  exact contactSupport_vertex_edge hn hsep hk0 hk1 hm

theorem contact_turns_nonzero (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) : ∀ i, turn P i ≠ 0 :=
  singlePointTriple_all_turns_nonzero hn hz (contactSupport_ne_turnSupport hn hsep)

theorem contact_regular (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) : Regular P :=
  nonzero_turns_regular (contact_turns_nonzero hn hsep hz)

theorem contact_g2 (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a})
    (hc : concurrenceTriples P = ∅) : G2 P :=
  nonzero_turns_g2 (contact_turns_nonzero hn hsep hz) hc

theorem extension_vertex_exclusion (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a})
    (hout : P M ∉ edgeSegment P a) :
    ∀ k i, ¬ incident k i → P k ∉ edgeSegment P i := by
  intro k i hki hp
  obtain ⟨rfl, rfl⟩ := contact_vertex_incidence hn hsep hz hki hp
  exact hout hp

theorem extension_crossingGeometry (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a})
    (hout : P M ∉ edgeSegment P a) (hc : concurrenceTriples P = ∅) :
    CrossingGeometry P := by
  have hn5 := contactSeparated_size hn hsep
  exact singlePointTriple_nonflat_crossingGeometry (by omega) hz
    (contactSupport_ne_turnSupport hn hsep)
    (extension_vertex_exclusion hn hsep hz hout) hc

end SM
