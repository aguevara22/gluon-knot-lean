import SM.TurnSupports
import SM.RegularLocus
import SM.SingleTripleTransverse
import SM.CrossingGeometry

/-! Central geometry for single-triple walls whose zero triple is not a turn.
The support and vertex-exclusion premises here are intermediate properties;
the named-wall proofs must derive them from their actual source hypotheses. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

theorem nonzero_turns_regular (ht : ∀ i, turn P i ≠ 0) : Regular P := by
  have hd : ∀ i, det (edge P (i - 1)) (edge P i) ≠ 0 := by
    intro i
    have h := ht i
    rw [turn_det] at h
    exact sign_ne_zero.mp h
  have hedge : ∀ i, edge P i ≠ 0 := by
    intro i he
    apply hd i
    simp [he, det]
  intro i
  refine ⟨hedge (i - 1), hedge i, ?_⟩
  rintro ⟨r, _, hr⟩
  apply hd i
  rw [hr, det_smul_self]

theorem singlePointTriple_all_turns_nonzero (hn : 3 ≤ n)
    {S : Finset (ZMod n)} (hz : pointZeroTriples P = {S})
    (hs : ∀ i, S ≠ turnSupport i) : ∀ i, turn P i ≠ 0 := by
  letI : Fact (1 < n) := ⟨by omega⟩
  intro i
  exact chi_nonzero_outside_singleton hz (prev_ne_self i) (next_ne_self i).symm
    (prev_ne_next hn i) (hs i).symm

theorem nonzero_turns_g2 (ht : ∀ i, turn P i ≠ 0)
    (hc : concurrenceTriples P = ∅) : G2 P := by
  have hreg := nonzero_turns_regular ht
  have hedge : ∀ i, edge P i ≠ 0 := fun i => (hreg i).2.1
  rintro ⟨i, j, k, x, hij, hjk, hik, hi, hj, hk⟩
  have hrij := weak_base_common_interiors_remote hedge ht hij hi hj
  have hrjk := weak_base_common_interiors_remote hedge ht hjk hj hk
  have hrik := weak_base_common_interiors_remote hedge ht hik hi hk
  have hm := (mem_concurrenceTriples P {i, j, k}).mpr
    ((concurrenceTriple_iff hrij hrjk hrik).mpr ⟨x, hi, hj, hk⟩)
  simpa only [hc, Finset.notMem_empty] using hm

theorem singlePointTriple_nonflat_regular (hn : 3 ≤ n)
    {S : Finset (ZMod n)} (hz : pointZeroTriples P = {S})
    (hs : ∀ i, S ≠ turnSupport i) : Regular P :=
  nonzero_turns_regular (singlePointTriple_all_turns_nonzero hn hz hs)

theorem singlePointTriple_nonflat_g2 (hn : 3 ≤ n)
    {S : Finset (ZMod n)} (hz : pointZeroTriples P = {S})
    (hs : ∀ i, S ≠ turnSupport i) (hc : concurrenceTriples P = ∅) : G2 P :=
  nonzero_turns_g2 (singlePointTriple_all_turns_nonzero hn hz hs) hc

theorem singlePointTriple_nonflat_crossingGeometry (hn : 4 ≤ n)
    {S : Finset (ZMod n)} (hz : pointZeroTriples P = {S})
    (hs : ∀ i, S ≠ turnSupport i)
    (hv : ∀ k i, ¬ incident k i → P k ∉ edgeSegment P i)
    (hc : concurrenceTriples P = ∅) : CrossingGeometry P := by
  refine ⟨singlePointTriple_edge_ne_zero hn hz, ?_,
    singlePointTriple_nonflat_g2 (by omega) hz hs hc⟩
  intro i j hr x hi hj
  exact ⟨remote_closed_point_interior hv hr hi hj,
    remote_closed_point_interior hv (remote_symm hr) hj hi,
    singlePointTriple_remote_transverse hn hz hr hi hj⟩

end SM
