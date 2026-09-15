namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- A weakly generic center has no zero turn, whereas an actual flat wall
has its specified central turn equal to zero. -/
theorem weak_center_not_flat (w : WallGerm n) (hw : WeakGeneric w.center)
    (j : ZMod n) : ¬ w.FlatAt j := by
  intro hf
  exact hw.2.1 j (singlePointTriple_turn_zero hf.2.1)

/-- The same nonzero-turn condition excludes the actual cusp predicate,
without requiring a loop-side choice or any extra regularity hypothesis. -/
theorem weak_center_not_cusp (w : WallGerm n) (hw : WeakGeneric w.center)
    (j : ZMod n) : ¬ w.CuspAt j := by
  intro hc
  exact hw.2.1 j (singlePointTriple_turn_zero hc.2.1)

/-- The contact label is nonincident to the contacted edge. Its actual
interior point is therefore also a forbidden point on that closed segment. -/
theorem weak_center_not_vertex (w : WallGerm n) (hw : WeakGeneric w.center)
    (M a : ZMod n) : ¬ w.VertexEdgeAt M a := by
  intro hv
  have hnon : ¬ incident M a := by
    rintro (ha | ha)
    · exact hv.1.2.2.1 (by rw [ha, sub_add_cancel])
    · exact hv.1.2.1 ha.symm
  obtain ⟨r, hr0, hr1, hX⟩ := hv.2.2.2.1
  exact hw.2.2.1 M a hnon ⟨r, le_of_lt hr0, le_of_lt hr1, hX⟩

/-- The specified central concurrence supplies three distinct edge labels
and one common interior point, contradicting the actual G2 clause of WeakGeneric. -/
theorem weak_center_not_triple (w : WallGerm n) (hw : WeakGeneric w.center)
    (e f k : ZMod n) : ¬ w.TripleAt e f k := by
  intro ht
  have hm : ({e, f, k} : Finset (ZMod n)) ∈ w.concurrences := by
    rw [ht.2.1]
    simp
  have hc := (w.mem_concurrences {e, f, k}).mp hm
  have hne := Finset.card_triple_eq_three_iff.mp hc.1
  obtain ⟨x, hx⟩ := hc.2.2
  exact hw.2.2.2.2 ⟨e, f, k, x, hne.1, hne.2.2, hne.2.1,
    hx e (by simp), hx f (by simp), hx k (by simp)⟩

/-- In the continuation argument a simple event whose actual center remains
weakly generic can only be an exterior extension or pure cut. All other wall
exclusions are derived here; none is a caller-supplied premise. -/
theorem silent_of_simple_weak_center (w : WallGerm n) (hn : 3 ≤ n)
    (hs : w.Simple) (hw : WeakGeneric w.center) : w.Silent := by
  obtain ⟨kind, hk⟩ := hs
  cases kind with
  | flat =>
      obtain ⟨j, hj⟩ := hk
      exact (w.weak_center_not_flat hw j hj).elim
  | cusp =>
      obtain ⟨j, hj⟩ := hk
      exact (w.weak_center_not_cusp hw j hj).elim
  | vertex =>
      obtain ⟨M, a, hv⟩ := hk
      exact (w.weak_center_not_vertex hw M a hv).elim
  | triple =>
      obtain ⟨e, f, k, ht⟩ := hk
      exact (w.weak_center_not_triple hw e f k ht).elim
  | extension => exact Or.inl hk
  | cut => exact Or.inr hk

end
end SM.WallGerm
