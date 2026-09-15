import SM.CrossingGeometry
import SM.WeakTopology

/-! Complete actual crossing-support stability at any tuple with the proved
crossing geometry. G1 and nonzero turns are not required at the centre. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

theorem remote_pair_persists_of_geometry (hP : CrossingGeometry P) (i j : ZMod n)
    (hr : remote i j) :
    ∀ᶠ Q in 𝓝 P, (edgeSegment Q i ∩ edgeSegment Q j).Nonempty ↔
      (edgeSegment P i ∩ edgeSegment P j).Nonempty := by
  have hp := segmentPair_persists (t₀ := P) (continuous_vertex i).continuousAt
    (continuous_vertex j).continuousAt (continuous_edge i).continuousAt
    (continuous_edge j).continuousAt
  filter_upwards [hp] with Q hQ
  rw [← segmentsMeet_edges_iff Q, ← segmentsMeet_edges_iff P]
  by_cases hm : segmentsMeet (P i) (P j) (edge P i) (edge P j)
  · obtain ⟨x, hi, hj⟩ := (segmentsMeet_edges_iff P i j).mp hm
    have hg := hP.2.1 i j hr x hi hj
    obtain ⟨s, hs0, hs1, hs⟩ := hg.1
    obtain ⟨t, ht0, ht1, ht⟩ := hg.2.1
    have htrans : TransverseInterior (P i) (P j) (edge P i) (edge P j) :=
      ⟨hg.2.2, s, t, hs0, hs1, ht0, ht1, hs.symm.trans ht⟩
    have hnew := hQ.2 htrans
    have hmeet : segmentsMeet (Q i) (Q j) (edge Q i) (edge Q j) :=
      (segmentsMeet_iff _ _ _ _).mpr hnew.2.2.2.2.exists
    exact iff_of_true hmeet hm
  · exact iff_of_false (hQ.1 hm) hm

theorem crossing_support_persists_of_geometry (hP : CrossingGeometry P) :
    ∀ᶠ Q in 𝓝 P, ∀ s : Finset (ZMod n), IsCrossing Q s ↔ IsCrossing P s := by
  have hp : ∀ᶠ Q in 𝓝 P, ∀ i j, remote i j →
      ((edgeSegment Q i ∩ edgeSegment Q j).Nonempty ↔
        (edgeSegment P i ∩ edgeSegment P j).Nonempty) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hr : remote i j
    · exact (remote_pair_persists_of_geometry hP i j hr).mono (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ h => (hr h).elim)
  filter_upwards [hp] with Q hQ
  intro s
  constructor
  · rintro ⟨i, j, hs, hr, hm⟩
    exact ⟨i, j, hs, hr, (hQ i j hr).mp hm⟩
  · rintro ⟨i, j, hs, hr, hm⟩
    exact ⟨i, j, hs, hr, (hQ i j hr).mpr hm⟩

end SM
