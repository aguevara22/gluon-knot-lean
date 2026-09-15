namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

/-- Cramer's first parameter on the actual incoming edge of the enlarged
polygon. The quotient is defined for all parameters; its geometric use below
is restricted by a proved nonzero determinant. -/
def softNewbornIncomingParameter (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (ε : ℝ) : ℝ :=
  cramerFirst (softInsertion P j q ε (softOldIndex j (j - 1)))
    (softInsertion P j q ε (softNewIndex j))
    (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
    (edge (softInsertion P j q ε) (softNewIndex j))

/-- Cramer's second parameter is measured in the actual return direction,
from the inserted vertex toward the old next vertex. -/
def softNewbornReturnParameter (P : LabelledTuple n) (j : ZMod n) (q : Plane)
    (ε : ℝ) : ℝ :=
  cramerSecond (softInsertion P j q ε (softOldIndex j (j - 1)))
    (softInsertion P j q ε (softNewIndex j))
    (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
    (edge (softInsertion P j q ε) (softNewIndex j))

/-- The supporting-line intersection evaluated on the actual incoming edge. -/
def softNewbornPoint (P : LabelledTuple n) (j : ZMod n) (q : Plane) (ε : ℝ) : Plane :=
  edgePoint (softInsertion P j q ε) (softOldIndex j (j - 1))
    (softNewbornIncomingParameter P j q ε)

/-- At zero, the two directions are exactly the two parent directions at j. -/
theorem softNewborn_det_zero_ne (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    det (edge (softInsertion P j q 0) (softOldIndex j (j - 1)))
      (edge (softInsertion P j q 0) (softNewIndex j)) ≠ 0 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  rw [edge_softInsertion_old P j (j - 1) q 0 (prev_ne_self j),
    edge_softInsertion_return, zero_smul, sub_zero]
  exact g1_turn_nonzero hn hP j

/-- The zero-parameter line intersection is the incoming endpoint and the
return starting point, with their actual enlarged labels. -/
theorem softNewborn_zero_meeting (hn : 3 ≤ n) (P : LabelledTuple n)
    (j : ZMod n) (q : Plane) :
    edgePoint (softInsertion P j q 0) (softOldIndex j (j - 1)) 1 =
      edgePoint (softInsertion P j q 0) (softNewIndex j) 0 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  rw [edgePoint_one, edgePoint_zero,
    softOldIndex_next j (j - 1) (prev_ne_self j), sub_add_cancel,
    softInsertion_old, softInsertion_new, zero_smul, add_zero]

/-- The actual Cramer values and supporting-line point at zero. No child
G1 or admissibility assumption is needed at the duplicate-vertex limit. -/
theorem softNewborn_values_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    softNewbornIncomingParameter P j q 0 = 1 ∧
    softNewbornReturnParameter P j q 0 = 0 ∧ softNewbornPoint P j q 0 = P j := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hd := softNewborn_det_zero_ne hn hP j q
  have hm := softNewborn_zero_meeting hn P j q
  have hs : softNewbornIncomingParameter P j q 0 = 1 :=
    (div_eq_iff hd).mpr (intersection_parameter_identity hm)
  have ht : softNewbornReturnParameter P j q 0 = 0 :=
    (div_eq_iff hd).mpr (intersection_second_parameter_identity hm)
  refine ⟨hs, ht, ?_⟩
  rw [softNewbornPoint, hs, edgePoint_one,
    softOldIndex_next j (j - 1) (prev_ne_self j), sub_add_cancel, softInsertion_old]

/-- Both Cramer parameters and their point are continuous at zero because
the actual direction determinant there is nonzero. -/
theorem softNewborn_continuousAt_zero (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ContinuousAt (softNewbornIncomingParameter P j q) (0 : ℝ) ∧
    ContinuousAt (softNewbornReturnParameter P j q) (0 : ℝ) ∧
    ContinuousAt (softNewbornPoint P j q) (0 : ℝ) := by
  have hc := continuous_softInsertion P j q
  have ha := ((continuous_vertex (softOldIndex j (j - 1))).comp hc).continuousAt (x := (0 : ℝ))
  have hb := ((continuous_vertex (softNewIndex j)).comp hc).continuousAt (x := (0 : ℝ))
  have hu := ((continuous_edge (softOldIndex j (j - 1))).comp hc).continuousAt (x := (0 : ℝ))
  have hv := ((continuous_edge (softNewIndex j)).comp hc).continuousAt (x := (0 : ℝ))
  have hd := softNewborn_det_zero_ne hn hP j q
  have hs : ContinuousAt (softNewbornIncomingParameter P j q) (0 : ℝ) :=
    continuousAt_cramerFirst ha hb hu hv hd
  have ht : ContinuousAt (softNewbornReturnParameter P j q) (0 : ℝ) :=
    continuousAt_cramerSecond ha hb hu hv hd
  refine ⟨hs, ht, ?_⟩
  exact ha.add (hs.smul hu)

/-- These are two-sided supporting-line limits. In the loop sector they
are the limits of the actual newborn crossing data by the theorem below. -/
theorem softNewborn_limits (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    Tendsto (softNewbornIncomingParameter P j q) (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) ∧
    Tendsto (softNewbornReturnParameter P j q) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
    Tendsto (softNewbornPoint P j q) (𝓝 (0 : ℝ)) (𝓝 (P j)) := by
  have hc := softNewborn_continuousAt_zero hn hP j q
  have hz := softNewborn_values_zero hn hP j q
  have hs : Tendsto (softNewbornIncomingParameter P j q) (𝓝 (0 : ℝ))
      (𝓝 (softNewbornIncomingParameter P j q 0)) := hc.1
  have ht : Tendsto (softNewbornReturnParameter P j q) (𝓝 (0 : ℝ))
      (𝓝 (softNewbornReturnParameter P j q 0)) := hc.2.1
  have hp : Tendsto (softNewbornPoint P j q) (𝓝 (0 : ℝ))
      (𝓝 (softNewbornPoint P j q 0)) := hc.2.2
  exact ⟨by simpa only [hz.1] using hs, by simpa only [hz.2.1] using ht,
    by simpa only [hz.2.2] using hp⟩

/-- A genuine two-sided interval of transverse supporting lines. -/
theorem softNewborn_small_det_ne (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) :
    ∃ δ > 0, ∀ ε : ℝ, |ε| < δ →
      det (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
        (edge (softInsertion P j q ε) (softNewIndex j)) ≠ 0 := by
  have hc := continuous_softInsertion P j q
  have he := continuousAt_preserves_transversality
    (((continuous_edge (softOldIndex j (j - 1))).comp hc).continuousAt)
    (((continuous_edge (softNewIndex j)).comp hc).continuousAt)
    (softNewborn_det_zero_ne hn hP j q)
  obtain ⟨δ, hδ, hmem⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨δ, hδ, fun ε hε => hmem (by simpa only [Real.dist_eq, sub_zero] using hε)⟩

/-- Cramer's rule solves the actual incoming/return supporting-line equations. -/
theorem softNewborn_parameters_intersection (P : LabelledTuple n) (j : ZMod n)
    (q : Plane) (ε : ℝ)
    (hd : det (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
      (edge (softInsertion P j q ε) (softNewIndex j)) ≠ 0) :
    edgePoint (softInsertion P j q ε) (softOldIndex j (j - 1))
        (softNewbornIncomingParameter P j q ε) =
      edgePoint (softInsertion P j q ε) (softNewIndex j)
        (softNewbornReturnParameter P j q ε) :=
  cramer_intersection _ _ _ _ hd

/-- Any actual crossing of this transverse pair has exactly the constructed
parameters and point. This identification itself needs no G1 or G2 hypothesis. -/
theorem softNewborn_crossing_data (P : LabelledTuple n) (j : ZMod n) (q : Plane) (ε : ℝ)
    (hd : det (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
      (edge (softInsertion P j q ε) (softNewIndex j)) ≠ 0)
    (hc : IsCrossing (softInsertion P j q ε) {softOldIndex j (j - 1), softNewIndex j}) :
    crossingParameter (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ :
      Crossing (softInsertion P j q ε)) (softOldIndex j (j - 1)) (by simp) =
        softNewbornIncomingParameter P j q ε ∧
    crossingParameter (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ :
      Crossing (softInsertion P j q ε)) (softNewIndex j) (by simp) =
        softNewbornReturnParameter P j q ε ∧
    crossingPoint (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ :
      Crossing (softInsertion P j q ε)) = softNewbornPoint P j q ε := by
  let c : Crossing (softInsertion P j q ε) :=
    ⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩
  have hs := crossingParameter_spec c (softOldIndex j (j - 1)) (by simp [c])
  have ht := crossingParameter_spec c (softNewIndex j) (by simp [c])
  have hu := intersection_parameters_unique hd
    (softNewborn_parameters_intersection P j q ε hd) (hs.2.2.symm.trans ht.2.2)
  refine ⟨hu.1.symm, hu.2.symm, ?_⟩
  change crossingPoint c = edgePoint (softInsertion P j q ε) (softOldIndex j (j - 1))
    (softNewbornIncomingParameter P j q ε)
  exact hs.2.2.trans (congrArg (edgePoint (softInsertion P j q ε)
    (softOldIndex j (j - 1))) hu.1.symm)

/-- On one common positive loop-sector interval, the constructed parameters
are strictly interior and give the actual unordered pair crossing point.
Child G1 and the existence of this crossing are derived here. This theorem
does not assert that the pair is the only newborn among all polygon edges. -/
theorem softNewborn_small_loop_data (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      det (edge (softInsertion P j q ε) (softOldIndex j (j - 1)))
        (edge (softInsertion P j q ε) (softNewIndex j)) ≠ 0 ∧
      (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j →
        ∃ hc : IsCrossing (softInsertion P j q ε) {softOldIndex j (j - 1), softNewIndex j},
          (0 < softNewbornIncomingParameter P j q ε ∧ softNewbornIncomingParameter P j q ε < 1) ∧
          (0 < softNewbornReturnParameter P j q ε ∧ softNewbornReturnParameter P j q ε < 1) ∧
          crossingParameter (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ :
            Crossing (softInsertion P j q ε)) (softOldIndex j (j - 1)) (by simp) =
              softNewbornIncomingParameter P j q ε ∧
          crossingParameter (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ :
            Crossing (softInsertion P j q ε)) (softNewIndex j) (by simp) =
              softNewbornReturnParameter P j q ε ∧
          crossingPoint (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ :
            Crossing (softInsertion P j q ε)) = softNewbornPoint P j q ε) := by
  obtain ⟨δd, hδd, hdet⟩ := softNewborn_small_det_ne hn hP j q
  obtain ⟨δc, hδc, hcross⟩ := softFamily_local_crossing hn P hP j q hq
  obtain ⟨δg, hδg, hgeneric⟩ := softInsertion_small_G1 hP j q hq
  refine ⟨min δd (min δc δg), lt_min hδd (lt_min hδc hδg), ?_⟩
  intro ε hε hεδ
  have hεd : |ε| < δd := by
    simpa only [abs_of_pos hε] using lt_of_lt_of_le hεδ (min_le_left δd (min δc δg))
  have hεc : ε < δc := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δd (min δc δg)) (min_le_left δc δg))
  have hεg : ε < δg := lt_of_lt_of_le hεδ
    (le_trans (min_le_right δd (min δc δg)) (min_le_right δc δg))
  have hd := hdet ε hεd
  refine ⟨hd, ?_⟩
  intro hloop
  have hc := (hcross ε hε hεc).2.mpr hloop
  have hg := hgeneric ε hε hεg
  have hdata := softNewborn_crossing_data P j q ε hd hc
  have hs := crossingParameter_interior (by omega : 3 ≤ n + 1) hg
    (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ : Crossing (softInsertion P j q ε))
    (softOldIndex j (j - 1)) (by simp)
  have ht := crossingParameter_interior (by omega : 3 ≤ n + 1) hg
    (⟨{softOldIndex j (j - 1), softNewIndex j}, hc⟩ : Crossing (softInsertion P j q ε))
    (softNewIndex j) (by simp)
  refine ⟨hc, ?_, ?_, hdata.1, hdata.2.1, hdata.2.2⟩
  · simpa only [hdata.1] using hs
  · simpa only [hdata.2.1] using ht

end
end SM
