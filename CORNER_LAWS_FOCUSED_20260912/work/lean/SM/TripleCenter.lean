import SM.G1CrossingStability
import SM.ZeroTriples

/-! Actual geometry of a G1 centre with exactly one interior-concurrence
triple. Every other crossing on a selected edge has a different parameter. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem isCrossing_of_common_interiors {P : LabelledTuple n} {i j : ZMod n}
    (hr : remote i j) {q : Plane} (hi : q ∈ edgeInterior P i) (hj : q ∈ edgeInterior P j) :
    IsCrossing P {i, j} :=
  ⟨i, j, rfl, hr, q, edgeInterior_subset_edgeSegment P i hi,
    edgeInterior_subset_edgeSegment P j hj⟩

theorem crossingPoint_eq_edgeParameter (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    {i j : ZMod n} (hc : IsCrossing P {i, j}) :
    crossingPoint ⟨{i, j}, hc⟩ = edgePoint P i (edgeParameter P i j) := by
  have h := (crossingParameter_spec ⟨{i, j}, hc⟩ i (by simp)).2.2
  rw [crossingParameter_eq_edgeParameter hn hP hc] at h
  exact h

theorem edgeParameter_common_point (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    {i j : ZMod n} (hr : remote i j) {q : Plane}
    (hi : q ∈ edgeInterior P i) (hj : q ∈ edgeInterior P j) :
    edgePoint P i (edgeParameter P i j) = q := by
  letI : Fact (1 < n) := ⟨by omega⟩
  have hc := isCrossing_of_common_interiors hr hi hj
  rw [← crossingPoint_eq_edgeParameter hn hP hc]
  apply (crossingPoint_unique hP ⟨{i, j}, hc⟩ q ?_).symm
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact edgeInterior_subset_edgeSegment P _ hi
  · exact edgeInterior_subset_edgeSegment P _ hj

theorem uniqueTriple_data {P : LabelledTuple n} {i j k : ZMod n}
    (hc : concurrenceTriples P = {{i, j, k}}) :
    remote i j ∧ remote j k ∧ remote i k ∧
      ∃ q : Plane, q ∈ edgeInterior P i ∧ q ∈ edgeInterior P j ∧ q ∈ edgeInterior P k := by
  have hm : ({i, j, k} : Finset (ZMod n)) ∈ concurrenceTriples P := by rw [hc]; simp
  have hp := (mem_concurrenceTriples P _).mp hm
  have hd := Finset.card_triple_eq_three_iff.mp hp.1
  refine ⟨hp.2.1 (by simp) (by simp) hd.1,
    hp.2.1 (by simp) (by simp) hd.2.2, hp.2.1 (by simp) (by simp) hd.2.1, ?_⟩
  obtain ⟨q, hq⟩ := hp.2.2
  exact ⟨q, hq i (by simp), hq j (by simp), hq k (by simp)⟩

theorem uniqueTriple_parameters_eq (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    {i j k : ZMod n} (hc : concurrenceTriples P = {{i, j, k}}) :
    edgeParameter P i j = edgeParameter P i k := by
  letI : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨hij, _, hik, q, hi, hj, hk⟩ := uniqueTriple_data hc
  apply edgePoint_injective (g1_edge_ne_zero hn hP i)
  exact (edgeParameter_common_point hn hP hij hi hj).trans
    (edgeParameter_common_point hn hP hik hi hk).symm

theorem uniqueTriple_outside_parameter_ne (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : G1 P) {i j k h : ZMod n} (hc : concurrenceTriples P = {{i, j, k}})
    (hhi : h ≠ i) (hhj : h ≠ j) (hhk : h ≠ k) (hcross : IsCrossing P {i, h}) :
    edgeParameter P i h ≠ edgeParameter P i j := by
  letI : Fact (1 < n) := ⟨by omega⟩
  intro he
  obtain ⟨hij, _, _, q, hi, hj, _⟩ := uniqueTriple_data hc
  have hpq : crossingPoint ⟨{i, h}, hcross⟩ = q := by
    rw [crossingPoint_eq_edgeParameter hn hP hcross, he,
      edgeParameter_common_point hn hP hij hi hj]
  have hqh : q ∈ edgeInterior P h := by
    rw [← hpq]
    exact crossingPoint_interior hP ⟨{i, h}, hcross⟩ h (by simp)
  have hjh := g1_common_interiors_remote hn hP hhj.symm hj hqh
  have hih := crossing_pair_remote hcross
  have hnew : ({i, j, h} : Finset (ZMod n)) ∈ concurrenceTriples P :=
    (mem_concurrenceTriples P _).mpr ((concurrenceTriple_iff hij hjh hih).mpr ⟨q, hi, hj, hqh⟩)
  rw [hc, Finset.mem_singleton] at hnew
  have hmem : h ∈ ({i, j, k} : Finset (ZMod n)) := by rw [← hnew]; simp
  simpa [hhi, hhj, hhk] using hmem

end SM
