namespace SM

open Set
noncomputable section
variable {n : ℕ} [NeZero n]

/-- A compact actual path in an open set has one positive Euclidean tolerance
that keeps every uniformly close path inside that set. -/
theorem euclidean_path_open_tolerance (γ : unitInterval → LabelledTuple n)
    (hγ : Continuous γ) (S : Set (LabelledTuple n)) (hS : IsOpen S)
    (hγS : ∀ t, γ t ∈ S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : unitInterval → LabelledTuple n,
      (∀ t, dist (tupleCoordinates (p t)) (tupleCoordinates (γ t)) < δ) →
      ∀ t, p t ∈ S := by
  let K := Set.range (fun t => tupleCoordinates (γ t))
  have hK : IsCompact K := isCompact_range (continuous_tupleCoordinates.comp hγ)
  have hopen : IsOpen (coordinatesTuple ⁻¹' S) := hS.preimage continuous_coordinatesTuple
  have hsub : K ⊆ coordinatesTuple ⁻¹' S := by
    rintro z ⟨t, rfl⟩
    simpa only [mem_preimage, coordinatesTuple_tupleCoordinates] using hγS t
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hopen hsub
  refine ⟨δ, hδ, ?_⟩
  intro p hclose t
  have hmem : tupleCoordinates (p t) ∈ Metric.thickening δ K :=
    Metric.mem_thickening_iff.mpr ⟨tupleCoordinates (γ t), Set.mem_range_self t, hclose t⟩
  have hz := hthick hmem
  simpa only [mem_preimage, coordinatesTuple_tupleCoordinates] using hz

/-- Relative general position inside the actual weak locus. The positive
error tolerance and all weak membership are derived from the input path;
the caller does not supply a path or event-exclusion certificate. -/
theorem weak_relative_general_position (hn : 3 ≤ n)
    (γ : unitInterval → LabelledTuple n) (hγ : Continuous γ)
    (hw : ∀ t, WeakGeneric (γ t)) (hfirst : Generic (γ 0)) (hlast : Generic (γ 1)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ D : RelativeGeneralPositionPath γ δ,
      ∀ t, WeakGeneric (D.path t) := by
  obtain ⟨δ, hδ, hstay⟩ := euclidean_path_open_tolerance γ hγ (weakLocus n)
    isOpen_WeakGeneric hw
  obtain ⟨D⟩ := relative_general_position hn γ hγ
    (fun t => nonzero_turns_regular (hw t).2.1) hfirst hlast δ hδ
  exact ⟨δ, hδ, D, hstay D.path D.close⟩

end
end SM
