namespace SM

noncomputable section
open Filter Topology
variable {n : ℕ} [NeZero n]

theorem continuous_softParent_vertex (P : LabelledTuple n) (j k : ZMod n) (q : Plane) :
    Continuous (fun ε : ℝ => softInsertion P j q ε (softParentEdge j k)) :=
  (continuous_vertex (softParentEdge j k)).comp (continuous_softInsertion P j q)

theorem continuous_softParent_edge (P : LabelledTuple n) (j k : ZMod n) (q : Plane) :
    Continuous (fun ε : ℝ => edge (softInsertion P j q ε) (softParentEdge j k)) :=
  (continuous_edge (softParentEdge j k)).comp (continuous_softInsertion P j q)

theorem softParentParameter_zero (P : LabelledTuple n) (j k l : ZMod n) (q : Plane) :
    edgeParameter (softInsertion P j q 0) (softParentEdge j k) (softParentEdge j l) =
      edgeParameter P k l := by
  simp only [edgeParameter, softInsertion_parent_zero, edge_softInsertion_parent_zero]

/-- Continuity uses the two parent directions, without Generic at the
duplicate-vertex tuple at epsilon zero. -/
theorem continuousAt_softParentParameter (P : LabelledTuple n) (j k l : ZMod n) (q : Plane)
    (hd : det (edge P k) (edge P l) ≠ 0) :
    ContinuousAt (fun ε : ℝ =>
      edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l)) 0 := by
  have hd0 : det (edge (softInsertion P j q 0) (softParentEdge j k))
      (edge (softInsertion P j q 0) (softParentEdge j l)) ≠ 0 := by
    simpa only [edge_softInsertion_parent_zero] using hd
  exact (continuousAt_edgeParameter_of_det hd0).comp (continuous_softInsertion P j q).continuousAt

theorem softParentParameter_tendsto (P : LabelledTuple n) (j k l : ZMod n) (q : Plane)
    (hd : det (edge P k) (edge P l) ≠ 0) :
    Tendsto (fun ε : ℝ =>
      edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l))
      (𝓝 (0 : ℝ)) (𝓝 (edgeParameter P k l)) := by
  have h := (continuousAt_softParentParameter P j k l q hd).tendsto
  simpa only [softParentParameter_zero] using h

/-- The supporting-line intersection on the edge corresponding to k. -/
def softInheritedPoint (P : LabelledTuple n) (j k l : ZMod n) (q : Plane) (ε : ℝ) : Plane :=
  edgePoint (softInsertion P j q ε) (softParentEdge j k)
    (edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l))

theorem softInheritedPoint_zero (P : LabelledTuple n) (j k l : ZMod n) (q : Plane) :
    softInheritedPoint P j k l q 0 = edgePoint P k (edgeParameter P k l) := by
  rw [softInheritedPoint, softParentParameter_zero, edgePoint_softInsertion_parent_zero]

theorem continuousAt_softInheritedPoint (P : LabelledTuple n) (j k l : ZMod n) (q : Plane)
    (hd : det (edge P k) (edge P l) ≠ 0) :
    ContinuousAt (softInheritedPoint P j k l q) (0 : ℝ) :=
  (continuous_softParent_vertex P j k q).continuousAt.add
    ((continuousAt_softParentParameter P j k l q hd).smul
      (continuous_softParent_edge P j k q).continuousAt)

theorem softInheritedPoint_zero_crossing (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j k l : ZMod n) (q : Plane) (hc : IsCrossing P {k, l}) :
    softInheritedPoint P j k l q 0 = crossingPoint (⟨{k, l}, hc⟩ : Crossing P) := by
  rw [softInheritedPoint_zero, ← crossingParameter_eq_edgeParameter hn hP hc]
  exact (crossingParameter_spec (⟨{k, l}, hc⟩ : Crossing P) k (by simp)).2.2.symm

theorem softInheritedPoint_tendsto (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j k l : ZMod n) (q : Plane) (hc : IsCrossing P {k, l}) :
    Tendsto (softInheritedPoint P j k l q) (𝓝 (0 : ℝ))
      (𝓝 (crossingPoint (⟨{k, l}, hc⟩ : Crossing P))) := by
  have h := (continuousAt_softInheritedPoint P j k l q
    (crossing_edgeParameter_det_ne_zero hn hP hc)).tendsto
  simpa only [softInheritedPoint_zero_crossing hn hP j k l q hc] using h

theorem softParent_direction_sign_persists (P : LabelledTuple n) (j k l : ZMod n) (q : Plane)
    (hd : det (edge P k) (edge P l) ≠ 0) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l)) ≠ 0 ∧
      SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l))) =
          SignType.sign (det (edge P k) (edge P l)) := by
  have hd0 : det (edge (softInsertion P j q 0) (softParentEdge j k))
      (edge (softInsertion P j q 0) (softParentEdge j l)) ≠ 0 := by
    simpa only [edge_softInsertion_parent_zero] using hd
  have hu := (continuous_softParent_edge P j k q).continuousAt (x := (0 : ℝ))
  have hv := (continuous_softParent_edge P j l q).continuousAt (x := (0 : ℝ))
  have hc := continuousAt_det hu hv
  have hnz := continuousAt_preserves_transversality hu hv hd0
  have hs := ((continuousAt_sign_of_ne_zero hd0).comp hc).eventually
    (isOpen_discrete _ |>.mem_nhds (Set.mem_singleton
      (SignType.sign (det (edge (softInsertion P j q 0) (softParentEdge j k))
        (edge (softInsertion P j q 0) (softParentEdge j l))))))
  filter_upwards [hnz, hs] with ε hε hsε
  refine ⟨hε, ?_⟩
  change SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
    (edge (softInsertion P j q ε) (softParentEdge j l))) =
      SignType.sign (det (edge (softInsertion P j q 0) (softParentEdge j k))
        (edge (softInsertion P j q 0) (softParentEdge j l))) at hsε
  simpa only [edge_softInsertion_parent_zero] using hsε

/-- Each actual parent crossing persists with both actual edge parameters
strictly interior and its ordered direction sign unchanged. -/
theorem softParent_crossing_parameters_persist (hn : 3 ≤ n) {P : LabelledTuple n} (hP : G1 P)
    (j k l : ZMod n) (q : Plane) (hc : IsCrossing P {k, l}) :
    ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      (0 < edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) ∧
        edgeParameter (softInsertion P j q ε) (softParentEdge j k) (softParentEdge j l) < 1) ∧
      (0 < edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k) ∧
        edgeParameter (softInsertion P j q ε) (softParentEdge j l) (softParentEdge j k) < 1) ∧
      det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l)) ≠ 0 ∧
      SignType.sign (det (edge (softInsertion P j q ε) (softParentEdge j k))
        (edge (softInsertion P j q ε) (softParentEdge j l))) =
          SignType.sign (det (edge P k) (edge P l)) ∧
      IsCrossing (softInsertion P j q ε) {softParentEdge j k, softParentEdge j l} := by
  have hd := crossing_edgeParameter_det_ne_zero hn hP hc
  have hrev : IsCrossing P {l, k} := by simpa only [Finset.pair_comm] using hc
  have hdr := crossing_edgeParameter_det_ne_zero hn hP hrev
  have hs := crossingParameter_interior hn hP (⟨{k, l}, hc⟩ : Crossing P) k (by simp)
  rw [crossingParameter_eq_edgeParameter hn hP hc] at hs
  have ht := crossingParameter_interior hn hP (⟨{l, k}, hrev⟩ : Crossing P) l (by simp)
  rw [crossingParameter_eq_edgeParameter hn hP hrev] at ht
  have hse := continuousAt_preserves_unit_interval (continuousAt_softParentParameter P j k l q hd)
    (by simpa only [softParentParameter_zero] using hs.1)
    (by simpa only [softParentParameter_zero] using hs.2)
  have hte := continuousAt_preserves_unit_interval (continuousAt_softParentParameter P j l k q hdr)
    (by simpa only [softParentParameter_zero] using ht.1)
    (by simpa only [softParentParameter_zero] using ht.2)
  filter_upwards [hse, hte, softParent_direction_sign_persists P j k l q hd] with ε hsε htε hdε
  refine ⟨hsε, htε, hdε.1, hdε.2, ?_⟩
  refine ⟨softParentEdge j k, softParentEdge j l, rfl,
    softParentEdge_remote j k l (crossing_pair_remote hc), ?_⟩
  refine ⟨softInheritedPoint P j k l q ε, ⟨_, hsε.1.le, hsε.2.le, rfl⟩,
    ⟨_, htε.1.le, htε.2.le, ?_⟩⟩
  exact edgeParameters_intersection (softInsertion P j q ε) _ _ hdε.1

/-- Identification with the canonical crossing point, independently of
which proof witnesses this inherited crossing. Child G1 is explicit here. -/
theorem softInheritedPoint_eq_crossingPoint (hn : 3 ≤ n) (P : LabelledTuple n)
    (j k l : ZMod n) (q : Plane) (ε : ℝ) (hQ : G1 (softInsertion P j q ε))
    (hc : IsCrossing (softInsertion P j q ε) {softParentEdge j k, softParentEdge j l}) :
    softInheritedPoint P j k l q ε =
      crossingPoint (⟨{softParentEdge j k, softParentEdge j l}, hc⟩ :
        Crossing (softInsertion P j q ε)) := by
  rw [softInheritedPoint, ← crossingParameter_eq_edgeParameter (by omega : 3 ≤ n + 1) hQ hc]
  exact (crossingParameter_spec (⟨{softParentEdge j k, softParentEdge j l}, hc⟩ :
    Crossing (softInsertion P j q ε)) (softParentEdge j k) (by simp)).2.2.symm

end
end SM
