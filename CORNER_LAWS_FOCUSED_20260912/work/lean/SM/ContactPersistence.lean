import SM.ContactPairGeometry
import SM.GeometricCrossingStability
import SM.NamedWallPredicates
import SM.GermNeighborhood

/-! Complete support persistence outside the two explicitly named contact pairs.
The central geometry is derived pair by pair, without a global Generic premise. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

theorem pair_persists_of_interior_geometry (i j : ZMod n)
    (hg : ∀ x, x ∈ edgeSegment P i → x ∈ edgeSegment P j →
      x ∈ edgeInterior P i ∧ x ∈ edgeInterior P j ∧ det (edge P i) (edge P j) ≠ 0) :
    ∀ᶠ Q in 𝓝 P, (edgeSegment Q i ∩ edgeSegment Q j).Nonempty ↔
      (edgeSegment P i ∩ edgeSegment P j).Nonempty := by
  have hp := segmentPair_persists (t₀ := P) (continuous_vertex i).continuousAt
    (continuous_vertex j).continuousAt (continuous_edge i).continuousAt (continuous_edge j).continuousAt
  filter_upwards [hp] with Q hQ
  rw [← segmentsMeet_edges_iff Q, ← segmentsMeet_edges_iff P]
  by_cases hm : segmentsMeet (P i) (P j) (edge P i) (edge P j)
  · obtain ⟨x, hi, hj⟩ := (segmentsMeet_edges_iff P i j).mp hm
    have h := hg x hi hj
    obtain ⟨s, hs0, hs1, hs⟩ := h.1
    obtain ⟨t, ht0, ht1, ht⟩ := h.2.1
    have htrans : TransverseInterior (P i) (P j) (edge P i) (edge P j) :=
      ⟨h.2.2, s, t, hs0, hs1, ht0, ht1, hs.symm.trans ht⟩
    have hnew := hQ.2 htrans
    have hmeet : segmentsMeet (Q i) (Q j) (edge Q i) (edge Q j) :=
      (segmentsMeet_iff _ _ _ _).mpr hnew.2.2.2.2.exists
    exact iff_of_true hmeet hm
  · exact iff_of_false (hQ.1 hm) hm

theorem contact_unaffected_supports_persist (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) (hz : pointZeroTriples P = {contactSupport M a}) :
    ∀ᶠ Q in 𝓝 P, ∀ s : Finset (ZMod n), ¬ ContactAffected M a s →
      (IsCrossing Q s ↔ IsCrossing P s) := by
  have hp : ∀ᶠ Q in 𝓝 P, ∀ i j, remote i j → ¬ ContactAffected M a {i, j} →
      ((edgeSegment Q i ∩ edgeSegment Q j).Nonempty ↔
        (edgeSegment P i ∩ edgeSegment P j).Nonempty) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hr : remote i j
    · by_cases ha : ContactAffected M a {i, j}
      · exact Eventually.of_forall (fun _ _ hn => (hn ha).elim)
      · exact (pair_persists_of_interior_geometry i j
          (fun x hi hj => contact_unaffected_pair_geometry hn hsep hz hr ha hi hj)).mono
          (fun _ h _ _ => h)
    · exact Eventually.of_forall (fun _ h => (hr h).elim)
  filter_upwards [hp] with Q hQ
  intro s hnot
  constructor
  · rintro ⟨i, j, hs, hr, hm⟩
    have hn' : ¬ ContactAffected M a {i, j} := by simpa only [hs] using hnot
    exact ⟨i, j, hs, hr, (hQ i j hr hn').mp hm⟩
  · rintro ⟨i, j, hs, hr, hm⟩
    have hn' : ¬ ContactAffected M a {i, j} := by simpa only [hs] using hnot
    exact ⟨i, j, hs, hr, (hQ i j hr hn').mpr hm⟩

namespace WallGerm

theorem vertexEdge_unaffected_crossings (hn : 3 ≤ n) (g : WallGerm n)
    {M a : ZMod n} (h : g.VertexEdgeAt M a) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ →
      ∀ s : Finset (ZMod n), ¬ ContactAffected M a s →
        (IsCrossing (g.curve t) s ↔ IsCrossing g.center s) :=
  (g.eventually_center_iff_radius _).mp
    (g.continuous_curve.continuousAt.eventually (contact_unaffected_supports_persist hn h.1 h.2.1))

end WallGerm
end SM
