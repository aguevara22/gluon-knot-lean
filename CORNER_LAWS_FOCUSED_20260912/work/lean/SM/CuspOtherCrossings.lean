import SM.CuspUnusedPair
import SM.FlatIndices
import SM.FiniteChiStability

/-! Exhaustive endpoint-test classification and preservation of every actual
crossing support except the selected newborn pair. No thread-order claim. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n]

theorem cusp_critical_endpoint_pair (hn : 4 ≤ n) {i k j : ZMod n} (hr : remote i k)
    (he : ({i, i + 1, k} : Finset (ZMod n)) = turnSupport j ∨
      ({i, i + 1, k + 1} : Finset (ZMod n)) = turnSupport j) :
    ({i, k} : Finset (ZMod n)) = {j - 1, j + 1} ∨
      ({i, k} : Finset (ZMod n)) = {j - 2, j} := by
  have hk := remote_endpoints i k hr
  rcases he with he | he
  · rcases edge_vertex_turnSupport_cases hn hk.1 hk.2.1 he with ⟨hi, hk⟩ | ⟨hi, hk⟩
    · exact Or.inl (by rw [hi, hk])
    · exfalso
      apply hr
      left
      rw [hi, hk]
      ring
  · rcases edge_vertex_turnSupport_cases hn hk.2.2.1 hk.2.2.2 he with ⟨hi, hk⟩ | ⟨hi, hk⟩
    · have hk' : k = j := add_right_cancel hk
      exfalso
      apply hr
      right; right
      rw [hi, hk']
      ring
    · have hk' : k = j - 2 := by linear_combination hk
      right
      rw [hi, hk', Finset.pair_comm]

theorem cusp_noncritical_pair_chi (hn : 4 ≤ n) {P : LabelledTuple n} {j i k : ZMod n}
    (hz : pointZeroTriples P = {turnSupport j}) (hr : remote i k)
    (hA : ({i, k} : Finset (ZMod n)) ≠ {j - 1, j + 1})
    (hB : ({i, k} : Finset (ZMod n)) ≠ {j - 2, j}) :
    chi P i (i + 1) k ≠ 0 ∧ chi P i (i + 1) (k + 1) ≠ 0 ∧
      chi P k (k + 1) i ≠ 0 ∧ chi P k (k + 1) (i + 1) ≠ 0 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have first : ∀ a c : ZMod n, remote a c →
      ({a, c} : Finset (ZMod n)) ≠ {j - 1, j + 1} →
      ({a, c} : Finset (ZMod n)) ≠ {j - 2, j} →
      chi P a (a + 1) c ≠ 0 ∧ chi P a (a + 1) (c + 1) ≠ 0 := by
    intro a c hr hA hB
    have hh := remote_endpoints a c hr
    have hnone : ¬ (({a, a + 1, c} : Finset (ZMod n)) = turnSupport j ∨
        ({a, a + 1, c + 1} : Finset (ZMod n)) = turnSupport j) := by
      intro he
      exact (cusp_critical_endpoint_pair hn hr he).elim hA hB
    exact ⟨chi_nonzero_outside_singleton hz (next_ne_self a).symm hh.2.1.symm hh.1.symm
        (fun he => hnone (Or.inl he)),
      chi_nonzero_outside_singleton hz (next_ne_self a).symm hh.2.2.2.symm hh.2.2.1.symm
        (fun he => hnone (Or.inr he))⟩
  have hf := first i k hr hA hB
  have hg := first k i (remote_symm hr)
    (by simpa only [Finset.pair_comm k i] using hA)
    (by simpa only [Finset.pair_comm k i] using hB)
  exact ⟨hf.1, hf.2, hg⟩

def CuspCrossingControl (P : LabelledTuple n) (b : Bool) (j : ZMod n) (Q : LabelledTuple n) : Prop :=
  (∀ i k l : ZMod n, chi P i k l ≠ 0 → chi Q i k l = chi P i k l) ∧
    ¬ IsCrossing Q {cuspFirst (!b) j, cuspLast (!b) j}

theorem cusp_crossing_control_persists (hn : 4 ≤ n) {P : LabelledTuple n} {j : ZMod n}
    (hz : pointZeroTriples P = {turnSupport j}) {b : Bool} (hc : CuspCase P j b) :
    ∀ᶠ Q in 𝓝 P, CuspCrossingControl P b j Q := by
  filter_upwards [finite_nonzero_chi_persists (P := P), cusp_unused_disjoint_persists hn hz hc] with Q hQ hu
  exact ⟨hQ, hu⟩

theorem cusp_other_crossings_equal (hn : 4 ≤ n) {P Q R : LabelledTuple n} {j : ZMod n}
    (hz : pointZeroTriples P = {turnSupport j}) {b : Bool}
    (hQ : CuspCrossingControl P b j Q) (hR : CuspCrossingControl P b j R)
    (hQG : G1 Q) (hRG : G1 R) (s : Finset (ZMod n))
    (hne : s ≠ {cuspFirst b j, cuspLast b j}) : IsCrossing Q s ↔ IsCrossing R s := by
  have transfer : ∀ X Y : LabelledTuple n, CuspCrossingControl P b j X →
      CuspCrossingControl P b j Y → G1 X → G1 Y → IsCrossing X s → IsCrossing Y s := by
    intro X Y hX hY hXG hYG hcross
    obtain ⟨i, k, rfl, hr, hm⟩ := hcross
    have hu : ({i, k} : Finset (ZMod n)) ≠ {cuspFirst (!b) j, cuspLast (!b) j} := by
      intro he
      apply hX.2
      rw [← he]
      exact ⟨i, k, rfl, hr, hm⟩
    have hab : ({i, k} : Finset (ZMod n)) ≠ {j - 1, j + 1} ∧
        ({i, k} : Finset (ZMod n)) ≠ {j - 2, j} := by
      have hA := cusp_indices_A j
      have hB := cusp_indices_B j
      cases b
      · simpa only [Bool.not_false, hA.1, hA.2.1, hB.1, hB.2.1] using And.intro hu hne
      · simpa only [Bool.not_true, hA.1, hA.2.1, hB.1, hB.2.1] using And.intro hne hu
    have hc := cusp_noncritical_pair_chi hn hz hr hab.1 hab.2
    have hchi : ∀ a c d : ZMod n, chi P a c d ≠ 0 → chi Y a c d = chi X a c d :=
      fun a c d h => (hY.1 a c d h).trans (hX.1 a c d h).symm
    have hcrit := (crossing_test_iff (by omega) X hXG i k hr).mp hm
    apply (isCrossing_pair Y i k hr).mpr
    apply (crossing_test_iff (by omega) Y hYG i k hr).mpr
    rw [hchi _ _ _ hc.1, hchi _ _ _ hc.2.1, hchi _ _ _ hc.2.2.1, hchi _ _ _ hc.2.2.2]
    exact hcrit
  exact ⟨transfer Q R hQ hR hQG hRG, transfer R Q hR hQ hRG hQG⟩

end SM
