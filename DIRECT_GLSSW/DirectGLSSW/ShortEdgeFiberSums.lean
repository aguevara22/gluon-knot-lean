import DirectGLSSW.ShortEdgeCutFibers

namespace DirectGLSSW.ShortEdgeFiberSums
open scoped BigOperators
open ShortEdgeCutFibers

theorem collapseAfter_monotone (a : ℕ) : Monotone (collapseAfter a) := by
  intro x y hxy
  unfold collapseAfter
  split_ifs <;> omega

theorem collapsedInteriorCuts_subset (a i j : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.Ioo i j) :
    collapsedInteriorCuts a i j T ⊆
      Finset.Ioo (collapseAfter a i) (collapseAfter a j) := by
  intro z hz
  obtain ⟨hzj, hz⟩ := Finset.mem_erase.mp hz
  obtain ⟨hzi, hz⟩ := Finset.mem_erase.mp hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  have hxI := Finset.mem_Ioo.mp (hT hx)
  have hlo := collapseAfter_monotone a hxI.1.le
  have hhi := collapseAfter_monotone a hxI.2.le
  exact Finset.mem_Ioo.mpr (by omega)

theorem sum_parent_eq_sum_fibers (a i j : ℕ) (f : Finset ℕ → ℚ) :
    (∑ T ∈ (Finset.Ioo i j).powerset, f T) =
      ∑ S ∈ (Finset.Ioo (collapseAfter a i) (collapseAfter a j)).powerset,
        ∑ T ∈ (Finset.Ioo i j).powerset with collapsedInteriorCuts a i j T = S,
          f T := by
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro T hT
  exact Finset.mem_powerset.mpr
    (collapsedInteriorCuts_subset a i j T (Finset.mem_powerset.mp hT))

theorem leftEndpoint_fiber_finset (a j : ℕ) (S : Finset ℕ)
    (hBj : a + 1 < j) (hS : S ⊆ Finset.Ioo a (collapseAfter a j)) :
    ((Finset.Ioo a j).powerset.filter fun T => collapsedInteriorCuts a a j T = S) =
      {leftEndpointCandidate a S .unsplit, leftEndpointCandidate a S .shortLeaf} := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hT, hc⟩
    have hd := leftEndpoint_fiber_decomposition a j S T hBj hS hT hc
    by_cases hb : a + 1 ∈ T
    · right
      simpa [leftEndpointCandidate, hb] using hd
    · left
      simpa [leftEndpointCandidate, hb] using hd
  · rintro (rfl | rfl)
    · exact leftEndpointCandidate_valid a j S .unsplit hBj hS
    · exact leftEndpointCandidate_valid a j S .shortLeaf hBj hS

theorem leftEndpoint_candidates_ne (a j : ℕ) (S : Finset ℕ)
    (hBj : a + 1 < j) (hS : S ⊆ Finset.Ioo a (collapseAfter a j)) :
    leftEndpointCandidate a S .unsplit ≠ leftEndpointCandidate a S .shortLeaf := by
  intro h
  let e := shortEdge_cutFiber_leftEndpoint a j S hBj hS
  have he : e.symm EndpointLiftMode.unsplit = e.symm EndpointLiftMode.shortLeaf :=
    Subtype.ext h
  have hm := e.symm.injective he
  cases hm

theorem sum_parent_leftEndpoint (a j : ℕ) (hBj : a + 1 < j)
    (f : Finset ℕ → ℚ) :
    (∑ T ∈ (Finset.Ioo a j).powerset, f T) =
      ∑ S ∈ (Finset.Ioo a (collapseAfter a j)).powerset,
        (f (leftEndpointCandidate a S .unsplit) +
          f (leftEndpointCandidate a S .shortLeaf)) := by
  rw [sum_parent_eq_sum_fibers a a j f]
  have hca : collapseAfter a a = a := by simp [collapseAfter]
  rw [hca]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub := Finset.mem_powerset.mp hS
  rw [leftEndpoint_fiber_finset a j S hBj hsub]
  exact Finset.sum_pair (leftEndpoint_candidates_ne a j S hBj hsub)

theorem rightEndpoint_fiber_finset (a i : ℕ) (S : Finset ℕ)
    (hiA : i < a) (hS : S ⊆ Finset.Ioo (collapseAfter a i) a) :
    ((Finset.Ioo i (a + 1)).powerset.filter fun T =>
        collapsedInteriorCuts a i (a + 1) T = S) =
      {rightEndpointCandidate a S .unsplit, rightEndpointCandidate a S .shortLeaf} := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hT, hc⟩
    have hd := rightEndpoint_fiber_decomposition a i S T hiA hS hT hc
    by_cases hb : a ∈ T
    · right
      simpa [rightEndpointCandidate, hb] using hd
    · left
      simpa [rightEndpointCandidate, hb] using hd
  · rintro (rfl | rfl)
    · exact rightEndpointCandidate_valid a i S .unsplit hiA hS
    · exact rightEndpointCandidate_valid a i S .shortLeaf hiA hS

theorem rightEndpoint_candidates_ne (a i : ℕ) (S : Finset ℕ)
    (hiA : i < a) (hS : S ⊆ Finset.Ioo (collapseAfter a i) a) :
    rightEndpointCandidate a S .unsplit ≠ rightEndpointCandidate a S .shortLeaf := by
  intro h
  let e := shortEdge_cutFiber_rightEndpoint a i S hiA hS
  have he : e.symm EndpointLiftMode.unsplit = e.symm EndpointLiftMode.shortLeaf :=
    Subtype.ext h
  have hm := e.symm.injective he
  cases hm

theorem sum_parent_rightEndpoint (a i : ℕ) (hiA : i < a)
    (f : Finset ℕ → ℚ) :
    (∑ T ∈ (Finset.Ioo i (a + 1)).powerset, f T) =
      ∑ S ∈ (Finset.Ioo (collapseAfter a i) a).powerset,
        (f (rightEndpointCandidate a S .unsplit) +
          f (rightEndpointCandidate a S .shortLeaf)) := by
  rw [sum_parent_eq_sum_fibers a i (a + 1) f]
  have hcb : collapseAfter a (a + 1) = a := by simp [collapseAfter]
  rw [hcb]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub := Finset.mem_powerset.mp hS
  rw [rightEndpoint_fiber_finset a i S hiA hsub]
  exact Finset.sum_pair (rightEndpoint_candidates_ne a i S hiA hsub)

theorem span_at_cut_fiber_finset (a i j : ℕ) (S : Finset ℕ)
    (hiA : i < a) (hBj : a + 1 < j) (haS : a ∈ S)
    (hS : S ⊆ Finset.Ioo i (collapseAfter a j)) :
    ((Finset.Ioo i j).powerset.filter fun T => collapsedInteriorCuts a i j T = S) =
      {spanCandidate a S .cutAtA, spanCandidate a S .cutAtB,
        spanCandidate a S .cutAtBoth} := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hT, hc⟩
    have hd := span_fiber_decomposition a i j S T hiA hBj haS hS hT hc
    have hp := span_fiber_pair_nonempty a i j S T hiA hBj haS hS hT hc
    by_cases hA : a ∈ T <;> by_cases hB : a + 1 ∈ T
    · right; right
      simpa [spanCandidate, hA, hB] using hd
    · left
      simpa [spanCandidate, hA, hB] using hd
    · right; left
      simpa [spanCandidate, hA, hB] using hd
    · exact False.elim (hp.elim hA hB)
  · rintro (rfl | rfl | rfl)
    · exact spanCandidate_valid a i j S .cutAtA hiA hBj haS hS
    · exact spanCandidate_valid a i j S .cutAtB hiA hBj haS hS
    · exact spanCandidate_valid a i j S .cutAtBoth hiA hBj haS hS

theorem span_no_cut_fiber_finset (a i j : ℕ) (S : Finset ℕ)
    (hiA : i < a) (hBj : a + 1 < j) (haS : a ∉ S)
    (hS : S ⊆ Finset.Ioo i (collapseAfter a j)) :
    ((Finset.Ioo i j).powerset.filter fun T => collapsedInteriorCuts a i j T = S) =
      {liftedCuts a S} := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
  constructor
  · rintro ⟨hT, hc⟩
    exact span_fiber_no_cut_decomposition a i j S T hiA hBj haS hS hT hc
  · rintro rfl
    exact span_no_cut_liftedCuts_valid a i j S hiA hBj haS hS

theorem spanCandidate_injective (a i j : ℕ) (S : Finset ℕ)
    (hiA : i < a) (hBj : a + 1 < j) (haS : a ∈ S)
    (hS : S ⊆ Finset.Ioo i (collapseAfter a j)) :
    Function.Injective (spanCandidate a S) := by
  intro m n h
  let e := shortEdge_cutFiber_span_at_cut a i j S hiA hBj haS hS
  have he : e.symm m = e.symm n := Subtype.ext h
  exact e.symm.injective he

theorem sum_parent_spanning (a i j : ℕ) (hiA : i < a) (hBj : a + 1 < j)
    (f : Finset ℕ → ℚ) :
    (∑ T ∈ (Finset.Ioo i j).powerset, f T) =
      ∑ S ∈ (Finset.Ioo i (collapseAfter a j)).powerset,
        if a ∈ S then
          f (spanCandidate a S .cutAtA) + f (spanCandidate a S .cutAtB) +
            f (spanCandidate a S .cutAtBoth)
        else f (liftedCuts a S) := by
  rw [sum_parent_eq_sum_fibers a i j f]
  have hci : collapseAfter a i = i := collapseAfter_eq_of_le a i hiA.le
  rw [hci]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub := Finset.mem_powerset.mp hS
  by_cases haS : a ∈ S
  · rw [if_pos haS, span_at_cut_fiber_finset a i j S hiA hBj haS hsub]
    have hinj := spanCandidate_injective a i j S hiA hBj haS hsub
    have hab : spanCandidate a S .cutAtA ≠ spanCandidate a S .cutAtB := by
      intro h; have hh := hinj h; cases hh
    have hac : spanCandidate a S .cutAtA ≠ spanCandidate a S .cutAtBoth := by
      intro h; have hh := hinj h; cases hh
    have hbc : spanCandidate a S .cutAtB ≠ spanCandidate a S .cutAtBoth := by
      intro h; have hh := hinj h; cases hh
    simp [hab, hac, hbc, add_assoc]
  · rw [if_neg haS, span_no_cut_fiber_finset a i j S hiA hBj haS hsub]
    exact Finset.sum_singleton _ _

end DirectGLSSW.ShortEdgeFiberSums
