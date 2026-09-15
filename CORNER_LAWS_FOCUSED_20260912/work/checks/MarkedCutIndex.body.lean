namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- Send an arbitrary set of interior indices to its actual marked cut
positions. Injectivity of the position map prevents duplicate marks. -/
def indexMarks (π : IntervalComposition I) (s : Finset (Fin (π.parts - 1))) : MarkedCuts π.cutSet :=
  ⟨s.image π.interiorPosition, by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    exact π.interiorPosition_mem k⟩

/-- Recover exactly the marked indices from a set of physical marked cuts. -/
def markIndices (π : IntervalComposition I) (m : MarkedCuts π.cutSet) : Finset (Fin (π.parts - 1)) :=
  Finset.univ.filter (fun k => π.interiorPosition k ∈ m.val)

theorem markIndices_indexMarks (π : IntervalComposition I) (s : Finset (Fin (π.parts - 1))) :
    π.markIndices (π.indexMarks s) = s := by
  ext k
  simp only [markIndices, indexMarks, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨l, hl, he⟩
    have h : l = k := π.interiorPosition_injective he
    subst l
    exact hl
  · intro hk
    exact ⟨k, hk, rfl⟩

theorem indexMarks_markIndices (π : IntervalComposition I) (m : MarkedCuts π.cutSet) :
    π.indexMarks (π.markIndices m) = m := by
  apply Subtype.ext
  ext x
  change x ∈ (π.markIndices m).image π.interiorPosition ↔ x ∈ m.val
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hk).2
  · intro hx
    obtain ⟨k, hk⟩ := (π.mem_interior_iff_exists_index x).mp (m.property hx)
    exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.symm ▸ hx⟩, hk⟩

/-- All index subsets and all physical marked subsets correspond exactly,
including the unary empty universe. -/
def marksIndexEquiv (π : IntervalComposition I) :
    Finset (Fin (π.parts - 1)) ≃ MarkedCuts π.cutSet where
  toFun := π.indexMarks
  invFun := π.markIndices
  left_inv := π.markIndices_indexMarks
  right_inv := π.indexMarks_markIndices

theorem position_mem_indexMarks (π : IntervalComposition I)
    (s : Finset (Fin (π.parts - 1))) (k : Fin (π.parts - 1)) :
    π.interiorPosition k ∈ (π.indexMarks s).val ↔ k ∈ s := by
  change π.interiorPosition k ∈ s.image π.interiorPosition ↔ k ∈ s
  constructor
  · intro h
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp h
    have hkl : l = k := π.interiorPosition_injective he
    subst l
    exact hl
  · intro h
    exact Finset.mem_image.mpr ⟨k, h, rfl⟩

/-- Complementary index selections map to exactly the unmarked physical
interior cuts, rather than the complement in the whole boundary domain. -/
theorem indexMarks_compl (π : IntervalComposition I) (s : Finset (Fin (π.parts - 1))) :
    (π.indexMarks sᶜ).val = π.cutSet.interior.val \ (π.indexMarks s).val := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_sdiff.mpr
    refine ⟨π.interiorPosition_mem k, ?_⟩
    intro hm
    exact (Finset.mem_compl.mp hk) ((π.position_mem_indexMarks s k).mp hm)
  · intro hx
    have hb := Finset.mem_sdiff.mp hx
    obtain ⟨k, hk⟩ := (π.mem_interior_iff_exists_index x).mp hb.1
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_compl.mpr ?_, hk⟩
    intro hks
    apply hb.2
    rw [← hk]
    exact (π.position_mem_indexMarks s k).mpr hks

/-- Products over selected cut indices preserve their actual physical
arguments under the marked-set bijection. -/
theorem prod_indexMarks {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (s : Finset (Fin (π.parts - 1))) (f : Fin n → R) :
    (∏ k ∈ s, f (π.interiorPosition k)) = ∏ x ∈ (π.indexMarks s).val, f x := by
  change (∏ k ∈ s, f (π.interiorPosition k)) = ∏ x ∈ s.image π.interiorPosition, f x
  symm
  exact Finset.prod_image (fun _ _ _ _ h => π.interiorPosition_injective h)

theorem prod_markIndices {R : Type*} [CommMonoid R]
    (π : IntervalComposition I) (m : MarkedCuts π.cutSet) (f : Fin n → R) :
    (∏ k ∈ π.markIndices m, f (π.interiorPosition k)) = ∏ x ∈ m.val, f x := by
  have h := π.prod_indexMarks (π.markIndices m) f
  rw [π.indexMarks_markIndices m] at h
  exact h

/-- Reindex a sum over every physical marking by all subsets of the exact
interior index universe. No marking is excluded or given multiplicity. -/
theorem sum_all_indexMarks {R : Type*} [AddCommMonoid R]
    (π : IntervalComposition I) (f : MarkedCuts π.cutSet → R) :
    (∑ s : Finset (Fin (π.parts - 1)), f (π.indexMarks s)) = ∑ m : MarkedCuts π.cutSet, f m :=
  Fintype.sum_equiv π.marksIndexEquiv _ _ (fun _ => rfl)

end
end SM.IntervalComposition
