import DirectGLSSW.ShortEdgeSignStability

namespace DirectGLSSW.TruncationCommonRadius

theorem exists_positive_common_lower_bound
    {ι : Type*} [Fintype ι] (δ : ι → ℝ)
    (hδ : ∀ i : ι, 0 < δ i) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ i : ι, ε₀ ≤ δ i := by
  classical
  have hlocal : ∀ i : ι, i ∈ Finset.univ → ∃ r : ℝ, 0 < r ∧
      ∀ ε : ℝ, 0 < ε → ε < r → ε < δ i := by
    intro i _
    exact ⟨δ i, hδ i, fun _ _ hε => hε⟩
  obtain ⟨r, hr, hgood⟩ :=
    ShortEdgeSignStability.exists_finset_common_radius Finset.univ
      (fun i ε => ε < δ i) hlocal
  refine ⟨r / 2, by linarith, ?_⟩
  intro i
  have hhalfpos : 0 < r / 2 := by linarith
  have hhalflt : r / 2 < r := by linarith
  exact le_of_lt (hgood (r / 2) hhalfpos hhalflt i (Finset.mem_univ i))

theorem exists_positive_common_lower_bound_with_parent
    {ι : Type*} [Fintype ι] (parentRadius : ℝ) (hparent : 0 < parentRadius)
    (δ : ι → ℝ) (hδ : ∀ i : ι, 0 < δ i) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ parentRadius ∧ ∀ i : ι, ε₀ ≤ δ i := by
  obtain ⟨bound, hbound, hbounds⟩ := exists_positive_common_lower_bound δ hδ
  refine ⟨min parentRadius bound, lt_min hparent hbound, ?_, ?_⟩
  · exact min_le_left _ _
  · intro i
    exact le_trans (min_le_right _ _) (hbounds i)

end DirectGLSSW.TruncationCommonRadius
