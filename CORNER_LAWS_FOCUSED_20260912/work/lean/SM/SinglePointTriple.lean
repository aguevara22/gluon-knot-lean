import SM.ZeroTriples

/-! Exact consequences of having one unordered collinear vertex triple.
The n>=4 condition is essential for the vertex-injectivity argument. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

theorem singlePointTriple_data {s : Finset (ZMod n)} (h : pointZeroTriples P = {s}) :
    PointZeroTriple P s := by
  apply (mem_pointZeroTriples P s).mp
  rw [h]
  simp

theorem chi_nonzero_outside_singleton {s : Finset (ZMod n)}
    (h : pointZeroTriples P = {s}) {i j k : ZMod n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hne : ({i, j, k} : Finset _) ≠ s) :
    chi P i j k ≠ 0 := by
  intro hz
  have hm := (mem_pointZeroTriples P {i, j, k}).mpr
    ((pointZeroTriple_iff hij hjk hik).mpr hz)
  rw [h, Finset.mem_singleton] at hm
  exact hne hm

theorem chi_zero_of_vertices_eq {i j : ZMod n} (he : P i = P j) (k : ZMod n) :
    chi P i j k = 0 := by simp [chi, he, det]

theorem singlePointTriple_vertices_injective (hn : 4 ≤ n)
    {s : Finset (ZMod n)} (h : pointZeroTriples P = {s}) : Function.Injective P := by
  intro i j he
  by_contra hij
  obtain ⟨k, hki, hkj⟩ := exists_third_index (by omega : 3 ≤ n) i j
  have hm := (mem_pointZeroTriples P {i, j, k}).mpr
    ((pointZeroTriple_iff hij hkj.symm hki.symm).mpr (chi_zero_of_vertices_eq he k))
  rw [h, Finset.mem_singleton] at hm
  have hi : i ∈ s := by rw [← hm]; simp
  have hj : j ∈ s := by rw [← hm]; simp
  have hcard : s.card < (Finset.univ : Finset (ZMod n)).card := by
    rw [(singlePointTriple_data h).1, Finset.card_univ, ZMod.card]
    omega
  obtain ⟨l, _, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hli : l ≠ i := fun heq => hl (heq ▸ hi)
  have hlj : l ≠ j := fun heq => hl (heq ▸ hj)
  have hnew := (mem_pointZeroTriples P {i, j, l}).mpr
    ((pointZeroTriple_iff hij hlj.symm hli.symm).mpr (chi_zero_of_vertices_eq he l))
  rw [h, Finset.mem_singleton] at hnew
  apply hl
  rw [← hnew]
  simp

theorem singlePointTriple_edge_ne_zero (hn : 4 ≤ n)
    {s : Finset (ZMod n)} (h : pointZeroTriples P = {s}) (i : ZMod n) :
    edge P i ≠ 0 := by
  letI : Fact (1 < n) := ⟨by omega⟩
  intro he
  exact next_ne_self i (singlePointTriple_vertices_injective hn h (sub_eq_zero.mp he))

end SM
