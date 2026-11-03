import RoundingCrossingOrientation

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Every literal crossing corner lies on its actual incoming supporting line. -/
theorem roundedCorner_crossing_on_line (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) (δ t : ℝ) : ∃ q : ℝ,
    roundedCorner D (D.incoming c i) δ t = cornerCenter D (D.incoming c i) +
      q • arcVector D (D.incoming c i) := by
  obtain ⟨a,ha,hv⟩ := crossing_arcVector_collinear D c i
  refine ⟨δ * (-a * (1 - t) ^ 2 + t ^ 2) / a,?_⟩
  rw [roundedCorner,hv]
  simp only [smul_smul, ← add_smul]
  have hscalar : δ * (-((1 - t) ^ 2) * a + t ^ 2) =
      (δ * (-a * (1 - t) ^ 2 + t ^ 2) / a) * a := by
    rw [div_mul_cancel₀ _ (ne_of_gt ha)]
    ring
  rw [hscalar]

/-- The two actual transverse crossing branches can only meet at their
original crossing center; the transversality comes from D itself. -/
theorem roundedCorner_crossing_intersection_iff_center (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (δ s t : ℝ) :
    roundedCorner D (D.incoming c 0) δ s = roundedCorner D (D.incoming c 1) δ t ↔
      roundedCorner D (D.incoming c 0) δ s = cornerCenter D (D.incoming c 0) ∧
      roundedCorner D (D.incoming c 1) δ t = cornerCenter D (D.incoming c 1) := by
  have hc : cornerCenter D (D.incoming c 0) = cornerCenter D (D.incoming c 1) := by
    simp only [cornerCenter,D.incoming_target]
  constructor
  · intro heq
    obtain ⟨q,hq⟩ := roundedCorner_crossing_on_line D c 0 δ s
    obtain ⟨r,hr⟩ := roundedCorner_crossing_on_line D c 1 δ t
    have hv : q • arcVector D (D.incoming c 0) = r • arcVector D (D.incoming c 1) := by
      apply add_left_cancel (a := cornerCenter D (D.incoming c 0))
      rw [← hc] at hr
      exact hq.symm.trans (heq.trans hr)
    have hp : q • strandTangent D c 0 = r • strandTangent D c 1 := by
      apply Prod.ext
      · simpa [Complex.real_smul,arcVector,strandTangent,D.incoming_target]
          using congrArg Complex.re hv
      · simpa [Complex.real_smul,arcVector,strandTangent,D.incoming_target]
          using congrArg Complex.im hv
    have hd := congrArg (fun w : PlanarPoint ℝ => planarDet w (strandTangent D c 1)) hp
    have hl : planarDet (q • strandTangent D c 0) (strandTangent D c 1) =
        q * planarDet (strandTangent D c 0) (strandTangent D c 1) := by
      simp [planarDet,smul_eq_mul]
      ring
    have hr0 : planarDet (r • strandTangent D c 1) (strandTangent D c 1) = 0 := by
      simp [planarDet,smul_eq_mul]
      ring
    dsimp only at hd
    rw [hl,hr0] at hd
    have hdet : planarDet (strandTangent D c 0) (strandTangent D c 1) ≠ 0 :=
      D.crossing_transverse c
    have hq0 : q = 0 := (mul_eq_zero.mp hd).resolve_right hdet
    have hz : roundedCorner D (D.incoming c 0) δ s = cornerCenter D (D.incoming c 0) := by
      simpa only [hq0,zero_smul,add_zero] using hq
    exact ⟨hz,heq.symm.trans (hz.trans hc)⟩
  · rintro ⟨hs,ht⟩
    exact hs.trans (hc.trans ht.symm)

/-- Every actual crossing branch reaches the actual center at exactly one
parameter; existence follows from its checked literal straight cut trace. -/
theorem roundedCorner_crossing_center_existsUnique (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (i : Fin 2) (δ : ℝ) (hδ : 0 < δ) :
    ∃! t : ℝ, t ∈ Set.Icc 0 1 ∧
      roundedCorner D (D.incoming c i) δ t = cornerCenter D (D.incoming c i) := by
  obtain ⟨a,ha,htrace⟩ := roundedCorner_crossing_trace D c i
  have hm : cornerCenter D (D.incoming c i) ∈
      roundedCorner D (D.incoming c i) δ '' Set.Icc 0 1 := by
    rw [htrace δ]
    exact ⟨0,⟨by linarith,by norm_num⟩,by simp⟩
  obtain ⟨t,hti,ht⟩ := hm
  refine ⟨t,⟨hti,ht⟩,?_⟩
  intro u hu
  exact roundedCorner_injOn D (D.incoming c i) δ hδ hu.1 hti (hu.2.trans ht.symm)

/-- Complete local same-crossing intersection classification, with actual
unique parameters on both original through branches. -/
theorem roundedCorner_crossing_unique_intersection (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₀ t₀ : ℝ, s₀ ∈ Set.Icc 0 1 ∧ t₀ ∈ Set.Icc 0 1 ∧
      roundedCorner D (D.incoming c 0) δ s₀ = cornerCenter D (D.incoming c 0) ∧
      roundedCorner D (D.incoming c 1) δ t₀ = cornerCenter D (D.incoming c 1) ∧
      ∀ s t : ℝ, s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
        (roundedCorner D (D.incoming c 0) δ s = roundedCorner D (D.incoming c 1) δ t ↔
          s = s₀ ∧ t = t₀) := by
  obtain ⟨s₀,hs₀,huniqueS⟩ := roundedCorner_crossing_center_existsUnique D c 0 δ hδ
  obtain ⟨t₀,ht₀,huniqueT⟩ := roundedCorner_crossing_center_existsUnique D c 1 δ hδ
  refine ⟨s₀,t₀,hs₀.1,ht₀.1,hs₀.2,ht₀.2,?_⟩
  intro s t hs ht
  rw [roundedCorner_crossing_intersection_iff_center]
  constructor
  · rintro ⟨hsc,htc⟩
    exact ⟨huniqueS s ⟨hs,hsc⟩,huniqueT t ⟨ht,htc⟩⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨hs₀.2,ht₀.2⟩

end DirectGLSSW.HOMFLY.PrincipalTurning




