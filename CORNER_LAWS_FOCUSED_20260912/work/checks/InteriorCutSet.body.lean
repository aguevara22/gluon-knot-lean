namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- An arbitrary finite selection of strictly interior positions. -/
abbrev InteriorCutSet (I : BoundaryInterval n) :=
  {s : Finset (Fin n) // ∀ x ∈ s, I.left < x ∧ x < I.right}

namespace BoundaryCutSet
variable {I : BoundaryInterval n}

/-- Remove exactly the two endpoint cuts. -/
def interior (S : BoundaryCutSet I) : InteriorCutSet I :=
  ⟨(S.cuts.erase I.left).erase I.right, by
    intro x hx
    simp only [Finset.mem_erase] at hx
    have hb := S.bounds x hx.2.2
    exact ⟨lt_of_le_of_ne hb.1 (Ne.symm hx.2.1), lt_of_le_of_ne hb.2 hx.1⟩⟩

/-- Adjoin exactly the interval endpoints to any interior selection. -/
def ofInterior (s : InteriorCutSet I) : BoundaryCutSet I where
  cuts := insert I.left (insert I.right s.val)
  left_mem := Finset.mem_insert_self _ _
  right_mem := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  bounds := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact ⟨le_rfl, le_of_lt I.increasing⟩
    · exact ⟨le_of_lt I.increasing, le_rfl⟩
    · exact ⟨le_of_lt (s.property x hx).1, le_of_lt (s.property x hx).2⟩

theorem interior_ofInterior (s : InteriorCutSet I) : (ofInterior s).interior = s := by
  apply Subtype.ext
  ext x
  simp only [interior, ofInterior, Finset.mem_erase, Finset.mem_insert]
  constructor
  · rintro ⟨hr, hl, hx | hx | hx⟩
    · exact False.elim (hl hx)
    · exact False.elim (hr hx)
    · exact hx
  · intro hx
    have h := s.property x hx
    exact ⟨ne_of_lt h.2, ne_of_gt h.1, Or.inr (Or.inr hx)⟩

theorem ofInterior_interior (S : BoundaryCutSet I) : ofInterior S.interior = S := by
  apply BoundaryCutSet.ext
  ext x
  simp only [ofInterior, interior, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro (rfl | rfl | ⟨_, _, hx⟩)
    · exact S.left_mem
    · exact S.right_mem
    · exact hx
  · intro hx
    by_cases hl : x = I.left
    · exact Or.inl hl
    · by_cases hr : x = I.right
      · exact Or.inr (Or.inl hr)
      · exact Or.inr (Or.inr ⟨hr, hl, hx⟩)

/-- Endpoints are fixed; every subset of interior positions is allowed. -/
def interiorEquiv (I : BoundaryInterval n) : BoundaryCutSet I ≃ InteriorCutSet I where
  toFun := interior
  invFun := ofInterior
  left_inv := ofInterior_interior
  right_inv := interior_ofInterior

/-- Restrict the actual cut positions to any interval whose endpoints occur
among them. No endpoint or interior cut inside the interval is lost. -/
def restrict (S : BoundaryCutSet I) (J : BoundaryInterval n)
    (hl : J.left ∈ S.cuts) (hr : J.right ∈ S.cuts) : BoundaryCutSet J where
  cuts := S.cuts.filter (fun x => J.left ≤ x ∧ x ≤ J.right)
  left_mem := Finset.mem_filter.mpr ⟨hl, le_rfl, le_of_lt J.increasing⟩
  right_mem := Finset.mem_filter.mpr ⟨hr, le_of_lt J.increasing, le_rfl⟩
  bounds := by intro x hx; exact (Finset.mem_filter.mp hx).2

theorem mem_restrict (S : BoundaryCutSet I) (J : BoundaryInterval n)
    (hl : J.left ∈ S.cuts) (hr : J.right ∈ S.cuts) (x : Fin n) :
    x ∈ (S.restrict J hl hr).cuts ↔ x ∈ S.cuts ∧ J.left ≤ x ∧ x ≤ J.right :=
  Finset.mem_filter

theorem restrict_self (S : BoundaryCutSet I) :
    S.restrict I S.left_mem S.right_mem = S := by
  apply BoundaryCutSet.ext
  ext x
  simp only [mem_restrict]
  exact ⟨fun h => h.1, fun h => ⟨h, S.bounds x h⟩⟩

theorem restrict_restrict (S : BoundaryCutSet I) (J K : BoundaryInterval n)
    (hjl : J.left ∈ S.cuts) (hjr : J.right ∈ S.cuts)
    (hkl : K.left ∈ (S.restrict J hjl hjr).cuts)
    (hkr : K.right ∈ (S.restrict J hjl hjr).cuts) :
    (S.restrict J hjl hjr).restrict K hkl hkr =
      S.restrict K (Finset.mem_filter.mp hkl).1 (Finset.mem_filter.mp hkr).1 := by
  apply BoundaryCutSet.ext
  ext x
  simp only [mem_restrict]
  constructor
  · rintro ⟨⟨hx, _, _⟩, hxl, hxr⟩
    exact ⟨hx, hxl, hxr⟩
  · rintro ⟨hx, hxl, hxr⟩
    have hleft := (Finset.mem_filter.mp hkl).2.1
    have hright := (Finset.mem_filter.mp hkr).2.2
    exact ⟨⟨hx, le_trans hleft hxl, le_trans hxr hright⟩, hxl, hxr⟩

end BoundaryCutSet

namespace IntervalComposition

/-- The source composition domain is exactly all subsets of its interior
boundary positions, with the empty subset retaining the unary term. -/
def interiorCutSetEquiv (I : BoundaryInterval n) : IntervalComposition I ≃ InteriorCutSet I :=
  (cutSetEquiv I).trans (BoundaryCutSet.interiorEquiv I)

end IntervalComposition

end
end SM
