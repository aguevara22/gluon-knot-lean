import SM.ContactPairGeometry
import SM.GeometricParameters

/-! Actual Cramer parameters and their distinctness for persistent crossings
at a vertex-contact centre. No global central CrossingGeometry is assumed. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {M a : ZMod n}

structure ContactPairData (P : LabelledTuple n) (i j : ZMod n)
    (hcross : IsCrossing P {i, j}) : Prop where
  det_ne_zero : det (edge P i) (edge P j) ≠ 0
  parameter_interior : 0 < edgeParameter P i j ∧ edgeParameter P i j < 1
  point_eq : crossingPoint (⟨{i, j}, hcross⟩ : Crossing P) = edgePoint P i (edgeParameter P i j)
  point_in_i : crossingPoint (⟨{i, j}, hcross⟩ : Crossing P) ∈ edgeInterior P i
  point_in_j : crossingPoint (⟨{i, j}, hcross⟩ : Crossing P) ∈ edgeInterior P j

theorem contact_pair_data (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) {i j : ZMod n}
    (hcross : IsCrossing P {i, j}) (hnot : ¬ ContactAffected M a {i, j}) :
    ContactPairData P i j hcross := by
  let c : Crossing P := ⟨{i, j}, hcross⟩
  have hg := contact_unaffected_pair_geometry hn hsep hz (crossing_pair_remote hcross) hnot
    (crossingPoint_mem c i (by simp [c])) (crossingPoint_mem c j (by simp [c]))
  obtain ⟨s, hs0, hs1, hs⟩ := hg.1
  obtain ⟨t, _, _, ht⟩ := hg.2.1
  have he : edgeParameter P i j = s :=
    (div_eq_iff hg.2.2).mpr (intersection_parameter_identity (hs.symm.trans ht))
  exact ⟨hg.2.2, by rw [he]; exact ⟨hs0, hs1⟩,
    by rw [he]; exact hs, hg.1, hg.2.1⟩

theorem contact_crossingParameter_eq_edgeParameter (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) {i j : ZMod n}
    (hcross : IsCrossing P {i, j}) (hnot : ¬ ContactAffected M a {i, j}) :
    crossingParameter (⟨{i, j}, hcross⟩ : Crossing P) i (by simp) = edgeParameter P i j := by
  have hd := contact_pair_data hn hsep hz hcross hnot
  have hn5 := contactSeparated_size hn hsep
  have hs := (crossingParameter_spec (⟨{i, j}, hcross⟩ : Crossing P) i (by simp)).2.2
  exact edgePoint_injective (singlePointTriple_edge_ne_zero (by omega) hz i)
    (hs.symm.trans hd.point_eq)

theorem contact_unaffected_parameters_ne (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) (hc : concurrenceTriples P = ∅)
    {i j k : ZMod n} (hjk : j ≠ k)
    (hij : IsCrossing P {i, j}) (hnij : ¬ ContactAffected M a {i, j})
    (hik : IsCrossing P {i, k}) (hnik : ¬ ContactAffected M a {i, k}) :
    edgeParameter P i j ≠ edgeParameter P i k := by
  intro he
  have hdj := contact_pair_data hn hsep hz hij hnij
  have hdk := contact_pair_data hn hsep hz hik hnik
  have hp : crossingPoint (⟨{i, j}, hij⟩ : Crossing P) =
      crossingPoint (⟨{i, k}, hik⟩ : Crossing P) := by
    rw [hdj.point_eq, hdk.point_eq, he]
  have hji := (remote_endpoints i j (crossing_pair_remote hij)).1
  have hki := (remote_endpoints i k (crossing_pair_remote hik)).1
  apply contact_g2 hn hsep hz hc
  exact ⟨i, j, k, crossingPoint (⟨{i, j}, hij⟩ : Crossing P), hji.symm, hjk, hki.symm,
    hdj.point_in_i, hdj.point_in_j, hp ▸ hdk.point_in_j⟩

theorem continuousAt_contact_edgeParameter (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) {i j : ZMod n}
    (hij : IsCrossing P {i, j}) (hnot : ¬ ContactAffected M a {i, j}) :
    ContinuousAt (fun Q : LabelledTuple n => edgeParameter Q i j) P :=
  continuousAt_cramerFirst (continuous_vertex i).continuousAt (continuous_vertex j).continuousAt
    (continuous_edge i).continuousAt (continuous_edge j).continuousAt
    (contact_pair_data hn hsep hz hij hnot).det_ne_zero

end SM
