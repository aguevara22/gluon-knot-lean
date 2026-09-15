import SM.ContactHalfTuples

/-! Actual child edges and their inclusions in parent edge interiors.
The two cut parameters are lambda*t and lambda+(1-lambda)*t. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem edgePoint_firstHalf (P : LabelledTuple n) (M a : ZMod n)
    {i : ZMod (firstHalfSize M a)} (hi : i ≠ -1) (t : ℝ) :
    edgePoint (firstHalf P M a) i t = edgePoint P (firstHalfIndex M a i) t := by
  simp only [edgePoint, firstHalf, edge_firstHalf P M a hi]

theorem edgePoint_secondHalf (P : LabelledTuple n) (M a : ZMod n)
    {i : ZMod (secondHalfSize M a)} (hi : i ≠ 0) (t : ℝ) :
    edgePoint (secondHalf P M a) i t = edgePoint P (secondHalfEdgeIndex M a i) t := by
  simp only [edgePoint, secondHalf, secondHalfIndex_nonzero M a hi, edge_secondHalf P M a hi]

theorem firstHalf_cut_vector {P : LabelledTuple n} {M a : ZMod n} {r : ℝ}
    (hr : P M = edgePoint P a r) : edge (firstHalf P M a) (-1) = r • edge P a := by
  rw [edge_firstHalf_last, hr, edgePoint]
  abel

theorem secondHalf_cut_vector (hn : 3 ≤ n) {M a : ZMod n} (h : ContactSeparated M a)
    {P : LabelledTuple n} {r : ℝ} (hr : P M = edgePoint P a r) :
    edge (secondHalf P M a) 0 = (1 - r) • edge P a := by
  rw [edge_secondHalf_zero hn h, hr]
  simp only [edgePoint, edge]
  ext <;> dsimp <;> ring

theorem edgePoint_firstHalf_cut {P : LabelledTuple n} {M a : ZMod n} {r : ℝ}
    (hr : P M = edgePoint P a r) (t : ℝ) :
    edgePoint (firstHalf P M a) (-1) t = edgePoint P a (r * t) := by
  rw [edgePoint, firstHalf_last, firstHalf_cut_vector hr, smul_smul, mul_comm t r]
  rfl

theorem edgePoint_secondHalf_cut (hn : 3 ≤ n) {M a : ZMod n} (h : ContactSeparated M a)
    {P : LabelledTuple n} {r : ℝ} (hr : P M = edgePoint P a r) (t : ℝ) :
    edgePoint (secondHalf P M a) 0 t = edgePoint P a (r + (1 - r) * t) := by
  rw [edgePoint, secondHalf_zero, secondHalf_cut_vector hn h hr, hr]
  simp only [edgePoint, edge]
  ext <;> dsimp <;> ring

theorem firstHalf_interior_subset {P : LabelledTuple n} {M a : ZMod n}
    (hm : P M ∈ edgeInterior P a) (i : ZMod (firstHalfSize M a)) :
    edgeInterior (firstHalf P M a) i ⊆ edgeInterior P (firstHalfIndex M a i) := by
  intro x hx
  obtain ⟨t, ht0, ht1, ht⟩ := hx
  by_cases hi : i = -1
  · subst i
    rw [firstHalfIndex_last]
    obtain ⟨r, hr0, hr1, hr⟩ := hm
    refine ⟨r * t, mul_pos hr0 ht0, by nlinarith, ?_⟩
    exact ht.trans (edgePoint_firstHalf_cut hr t)
  · exact ⟨t, ht0, ht1, ht.trans (edgePoint_firstHalf P M a hi t)⟩

theorem secondHalf_interior_subset (hn : 3 ≤ n) {M a : ZMod n} (h : ContactSeparated M a)
    {P : LabelledTuple n} (hm : P M ∈ edgeInterior P a) (i : ZMod (secondHalfSize M a)) :
    edgeInterior (secondHalf P M a) i ⊆ edgeInterior P (secondHalfEdgeIndex M a i) := by
  intro x hx
  obtain ⟨t, ht0, ht1, ht⟩ := hx
  by_cases hi : i = 0
  · subst i
    rw [secondHalfEdgeIndex_zero]
    obtain ⟨r, hr0, hr1, hr⟩ := hm
    refine ⟨r + (1 - r) * t, by nlinarith, by nlinarith, ?_⟩
    exact ht.trans (edgePoint_secondHalf_cut hn h hr t)
  · exact ⟨t, ht0, ht1, ht.trans (edgePoint_secondHalf P M a hi t)⟩

theorem g2_of_injective_edge_interior_map {k : ℕ} {P : LabelledTuple n} {Q : LabelledTuple k}
    (f : ZMod k → ZMod n) (hf : Function.Injective f)
    (hi : ∀ i, edgeInterior Q i ⊆ edgeInterior P (f i)) (hP : G2 P) : G2 Q := by
  rintro ⟨i, j, l, x, hij, hjl, hil, hxi, hxj, hxl⟩
  exact hP ⟨f i, f j, f l, x, hf.ne hij, hf.ne hjl, hf.ne hil, hi i hxi, hi j hxj, hi l hxl⟩

theorem contact_halves_generic (hn : 3 ≤ n) {M a : ZMod n} (h : ContactSeparated M a)
    {P : LabelledTuple n} (hz : pointZeroTriples P = {contactSupport M a})
    (hc : concurrenceTriples P = ∅) (hm : P M ∈ edgeInterior P a) :
    Generic (firstHalf P M a) ∧ Generic (secondHalf P M a) := by
  have hg := contact_g2 hn h hz hc
  exact ⟨⟨g1_firstHalf hn h hz, g2_of_injective_edge_interior_map (firstHalfIndex M a)
      (firstHalfIndex_injective M a) (firstHalf_interior_subset hm) hg⟩,
    ⟨g1_secondHalf hn h hz, g2_of_injective_edge_interior_map (secondHalfEdgeIndex M a)
      (secondHalfEdgeIndex_injective M a) (secondHalf_interior_subset hn h hm) hg⟩⟩

end SM
