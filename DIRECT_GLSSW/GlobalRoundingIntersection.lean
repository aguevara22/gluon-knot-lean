import NormalizedCellIntersection
import ActualTangentLift
import RoundingBasepointGerm

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Aggregate Gate6: unit phases select the literal zeroth orbit cell. -/
theorem roundedComponentCurve_unit (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (s : ℝ) (hs : s ∈ Set.Ico 0 1) :
    roundedComponentCurve D e δ s = normalizedRoundedCell D e δ s := by
  have hf : Int.floor s = 0 := Int.floor_eq_zero_iff.mpr hs
  have hfrac : Int.fract s = s := Int.fract_eq_self.mpr hs
  simp only [roundedComponentCurve,hf,hfrac,zpow_zero,Equiv.Perm.one_apply]

theorem roundedComponentVelocity_unit (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (s : ℝ) (hs : s ∈ Set.Ico 0 1) :
    roundedComponentVelocity D e δ s = normalizedRoundedVelocity D e δ s := by
  have hf : Int.floor s = 0 := Int.floor_eq_zero_iff.mpr hs
  have hfrac : Int.fract s = s := Int.fract_eq_self.mpr hs
  simp only [roundedComponentVelocity,hf,hfrac,zpow_zero,Equiv.Perm.one_apply]

/-- Actual normalized crossing velocity in arbitrary corner phase, rather
than a separately supplied orientation certificate. -/
theorem normalizedRoundedVelocity_crossing_positive (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (i : Fin 2) (δ : RoundingFraction) (s : ℝ)
    (hs : s ∈ Set.Icc 0 (2 * δ.val)) :
    ∃ k : ℝ, 0 < k ∧ Complex.equivRealProd (normalizedRoundedVelocity D (D.incoming c i) δ s) =
      k • strandTangent D c i := by
  obtain ⟨q,hq,htime,_⟩ := normalizedRoundedCell_corner_piece D (D.incoming c i) δ s hs
  obtain ⟨k,hk,hv⟩ := roundedCorner_crossing_planar_velocity_positive D c i δ.val q δ.property.1 hq
  have hp : 0 < 1 / (2 * δ.val) := one_div_pos.mpr (by linarith [δ.property.1])
  refine ⟨(1 / (2 * δ.val)) * k,mul_pos hp hk,?_⟩
  rw [← htime,normalizedRoundedVelocity_corner_time D _ δ q hq]
  have hmap : Complex.equivRealProd ((1 / (2 * δ.val)) •
      roundedCornerDerivative D (D.incoming c i) δ.val q) =
      (1 / (2 * δ.val)) • Complex.equivRealProd (roundedCornerDerivative D (D.incoming c i) δ.val q) := by
    apply Prod.ext <;> simp [Complex.equivRealProd_apply,Complex.real_smul]
  rw [hmap,hv,smul_smul]

/-- Literal global velocities at the original selected over/under visits. -/
noncomputable def globalRoundedCrossingDet (D : PLLinkDiagram) (δ : RoundingFraction)
    (θ : Fin D.nCrossing → Fin 2 → ℝ) (c : Fin D.nCrossing) : ℝ :=
  planarDet
    (Complex.equivRealProd (roundedComponentVelocity D (D.incoming c (D.overBranch c)) δ (θ c (D.overBranch c))))
    (Complex.equivRealProd (roundedComponentVelocity D
      (D.incoming c (otherBranch (D.overBranch c))) δ (θ c (otherBranch (D.overBranch c)))))

/-- Aggregate Gates5–6: actual global no-new-intersections, exact original
crossing visits/signs, and the protected literal basepoint germ. This is
separate from the full admissible-rounding/lift-shift/source-r aggregate. -/
theorem exists_global_rounding_intersection (D : PLLinkDiagram) (base : Fin D.nArc)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo 0 1) :
    ∃ (δ : RoundingFraction) (θ : Fin D.nCrossing → Fin 2 → ℝ) (η : ℝ),
      δ.val < τ ∧ δ.val < 1 - τ ∧ 0 < η ∧
      (∀ c i, θ c i ∈ Set.Ioo 0 (2 * δ.val) ∧
        Complex.equivRealProd (roundedComponentCurve D (D.incoming c i) δ (θ c i)) =
          D.vertexPoint (D.crossingVertex c) ∧
        ∃ k : ℝ, 0 < k ∧
          Complex.equivRealProd (roundedComponentVelocity D (D.incoming c i) δ (θ c i)) =
            k • strandTangent D c i) ∧
      (∀ c, ∃ hdet : globalRoundedCrossingDet D δ θ c ≠ 0,
        nonzeroScalarSign (globalRoundedCrossingDet D δ θ c) hdet = crossingSign D c) ∧
      (∀ u : ℝ, |u| < η → τ + δ.val + u ∈ Set.Ioo (2 * δ.val) 1 ∧
        Complex.equivRealProd (roundedComponentCurve D (D.continuation.symm base) δ (τ + δ.val + u)) =
          affinePoint (D.vertexPoint (D.arcSource base)) (D.vertexPoint (D.arcTarget base)) (τ + u)) ∧
      (∀ (e f : Fin D.nArc) (s t : ℝ),
        roundedComponentCurve D e δ s = roundedComponentCurve D f δ t ↔
        (((D.continuation ^ Int.floor s) e = (D.continuation ^ Int.floor t) f) ∧ Int.fract s = Int.fract t) ∨
        (∃ (c : Fin D.nCrossing) (i j : Fin 2), i ≠ j ∧
          (D.continuation ^ Int.floor s) e = D.incoming c i ∧
          (D.continuation ^ Int.floor t) f = D.incoming c j ∧
          Int.fract s = θ c i ∧ Int.fract t = θ c j)) := by
  classical
  obtain ⟨δ,θ,hleft,hright,hphases,hcells⟩ := exists_normalized_cell_intersection D base τ hτ
  obtain ⟨η,hη,hgerm⟩ := normalizedRoundedCell_basepoint_germ D base δ τ hleft hright
  have hglobalphases : ∀ c i, θ c i ∈ Set.Ioo 0 (2 * δ.val) ∧
      Complex.equivRealProd (roundedComponentCurve D (D.incoming c i) δ (θ c i)) =
        D.vertexPoint (D.crossingVertex c) ∧
      ∃ k : ℝ, 0 < k ∧ Complex.equivRealProd (roundedComponentVelocity D (D.incoming c i) δ (θ c i)) =
        k • strandTangent D c i := by
    intro c i
    have hunit : θ c i ∈ Set.Ico 0 1 := ⟨(hphases c i).1.1.le,by linarith [(hphases c i).1.2,δ.property.2]⟩
    refine ⟨(hphases c i).1,?_,?_⟩
    · rw [roundedComponentCurve_unit D _ δ _ hunit]
      exact (hphases c i).2
    · rw [roundedComponentVelocity_unit D _ δ _ hunit]
      exact normalizedRoundedVelocity_crossing_positive D c i δ _
        ⟨(hphases c i).1.1.le,(hphases c i).1.2.le⟩
  refine ⟨δ,θ,η,hleft,hright,hη,hglobalphases,?_,?_,?_⟩
  · intro c
    obtain ⟨a,ha,hva⟩ := (hglobalphases c (D.overBranch c)).2.2
    obtain ⟨b,hb,hvb⟩ := (hglobalphases c (otherBranch (D.overBranch c))).2.2
    have heq : globalRoundedCrossingDet D δ θ c = (a * b) * crossingDet D c := by
      simp only [globalRoundedCrossingDet,hva,hvb,crossingDet,planarDet,
        Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
      ring
    have hab : 0 < a * b := mul_pos ha hb
    have hdet : globalRoundedCrossingDet D δ θ c ≠ 0 := by
      rw [heq]
      exact mul_ne_zero (ne_of_gt hab) (selectedDet_ne_zero D c)
    refine ⟨hdet,?_⟩
    have hneg : (a * b) * crossingDet D c < 0 ↔ crossingDet D c < 0 := by
      constructor
      · intro h
        by_contra hn
        have hd : 0 ≤ crossingDet D c := le_of_not_gt hn
        have hnonneg := mul_nonneg hab.le hd
        linarith
      · exact fun h => mul_neg_of_pos_of_neg hab h
    simp only [nonzeroScalarSign,crossingSign,heq,hneg]
  · intro u hu
    have h := hgerm u hu
    have hclock : τ + u + δ.val = τ + δ.val + u := by ring
    rw [hclock] at h
    refine ⟨h.1,?_⟩
    have hunit : τ + δ.val + u ∈ Set.Ico 0 1 := ⟨by linarith [h.1.1,δ.property.1],h.1.2⟩
    rw [roundedComponentCurve_unit D _ δ _ hunit]
    exact h.2
  · intro e f s t
    have h := hcells ((D.continuation ^ Int.floor s) e) ((D.continuation ^ Int.floor t) f)
      (Int.fract s) (Int.fract t) ⟨Int.fract_nonneg s,Int.fract_lt_one s⟩
      ⟨Int.fract_nonneg t,Int.fract_lt_one t⟩
    constructor
    · intro heq
      apply h.mp
      simpa only [roundedComponentCurve] using congrArg Complex.equivRealProd heq
    · intro heq
      apply Complex.equivRealProd.injective
      simpa only [roundedComponentCurve] using h.mpr heq

end DirectGLSSW.HOMFLY.PrincipalTurning




