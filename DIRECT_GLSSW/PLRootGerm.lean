import ComplexPLLoop

set_option autoImplicit false

noncomputable section
namespace DirectGLSSW.HOMFLY

/-- On the first dyadic subinterval, a continuation path follows its first
literal diagram arc with the corresponding affine parameter. -/
theorem continuationPath_initial_arc (D : PLLinkDiagram) (e : Fin D.nArc)
    (n : ℕ) (u : unitInterval)
    (hu : (2 : ℝ) ^ n * u.val ≤ 1) :
    continuationPath D e (n + 1) u =
      diagramArcPath D e ⟨(2 : ℝ) ^ n * u.val,
        ⟨mul_nonneg (pow_nonneg (by norm_num) _) u.property.1, hu⟩⟩ := by
  induction n generalizing u with
  | zero =>
      simp [continuationPath, continuationArcPath, diagramArcPath_apply]
  | succ n ih =>
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n :=
        one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      have hpow' : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by rw [pow_succ]; ring
      have hu0 : 0 ≤ u.val := u.property.1
      have hpowu : u.val ≤ (2 : ℝ) ^ n * u.val := by
        simpa using mul_le_mul_of_nonneg_right hpow hu0
      have huHalf : u.val ≤ 1 / 2 := by
        rw [hpow'] at hu
        have hu' : 2 * ((2 : ℝ) ^ n * u.val) ≤ 1 := by
          calc
            2 * ((2 : ℝ) ^ n * u.val) = 2 * (2 : ℝ) ^ n * u.val := by ring
            _ ≤ 1 := hu
        calc
          u.val ≤ (2 : ℝ) ^ n * u.val := hpowu
          _ ≤ 1 / 2 := by linarith [hu']
      let v : unitInterval := ⟨2 * u.val, ⟨by nlinarith [hu0], by linarith⟩⟩
      have hv : (2 : ℝ) ^ n * v.val ≤ 1 := by
        dsimp [v]
        rw [pow_succ] at hu
        nlinarith [hu]
      have hrec := ih v hv
      rw [continuationPath.eq_def, Path.cast_coe, Path.trans_apply]
      simp only [dif_pos huHalf]
      rw [hrec]
      apply congrArg (diagramArcPath D e)
      apply Subtype.ext
      dsimp [v]
      ring_nf

/-- The literal complex loop has the expected affine germ at the unique
interior point of its initial root arc with parameter `τ`. -/
theorem exists_componentPLLoop_root_germ (D : PLLinkDiagram)
    (base : Fin D.nArc) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ t₀ : unitInterval, 0 < t₀.val ∧ t₀.val < 1 ∧
      ∃ η : ℝ, 0 < η ∧ ∃ κ : ℝ, 0 < κ ∧
        ∀ u : unitInterval, |u.val - t₀.val| < η →
          complexPLLoop D base u =
            Complex.equivRealProd.symm
              (affinePoint (D.vertexPoint (D.arcSource base))
                (D.vertexPoint (D.arcTarget base))
                (τ + κ * (u.val - t₀.val))) := by
  let n := componentArcLength D base - 1
  let κ : ℝ := (2 : ℝ) ^ n
  have hnpos : 0 < componentArcLength D base := componentArcLength_pos D base
  have hκ : 0 < κ := by positivity
  have hκ1 : 1 ≤ κ := by
    dsimp [κ]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hτκ : τ < κ := lt_of_lt_of_le hτ1 hκ1
  let t₀ : unitInterval := ⟨τ / κ, by
    constructor
    · exact div_nonneg (le_of_lt hτ0) (le_of_lt hκ)
    · exact le_of_lt ((div_lt_one hκ).2 hτκ)⟩
  have ht₀ : κ * t₀.val = τ := by
    dsimp [t₀]
    field_simp
  let η : ℝ := min (t₀.val / 2) ((1 - τ) / (2 * κ))
  have hη : 0 < η := by
    dsimp [η]
    apply lt_min
    · positivity
    · exact div_pos (by linarith) (by positivity)
  refine ⟨t₀, ?_, ?_, η, hη, κ, hκ, ?_⟩
  · exact div_pos hτ0 hκ
  · exact (div_lt_one hκ).2 hτκ
  · intro u hclose
    have hclose' := abs_lt.mp hclose
    have hηleft : η ≤ t₀.val / 2 := min_le_left _ _
    have hηright : η ≤ (1 - τ) / (2 * κ) := min_le_right _ _
    have hu0 : 0 < u.val := by linarith
    have hscale : κ * u.val < 1 := by
      have hmul : κ * u.val < κ * t₀.val + κ * η := by
        nlinarith [hκ, hclose'.2]
      have hηscaled : κ * η ≤ (1 - τ) / 2 := by
        have := hηright
        have hk2 : 0 < 2 * κ := by positivity
        have hmul' := (le_div_iff₀ hk2).mp this
        nlinarith [hκ]
      rw [ht₀] at hmul
      linarith [hηscaled, hτ1]
    have hloop := continuationPath_initial_arc D base n u (by
      simpa [κ] using hscale.le)
    have hcast : componentPLLoop D base u = continuationPath D base
        (componentArcLength D base) u := by
      simp [componentPLLoop, Path.cast_coe]
    have hparam : τ + κ * (u.val - t₀.val) = κ * u.val := by
      rw [← ht₀]
      ring
    have hn : n + 1 = componentArcLength D base := by
      dsimp [n]
      omega
    have hplane : componentPLLoop D base u =
        affinePoint (D.vertexPoint (D.arcSource base))
          (D.vertexPoint (D.arcTarget base)) (κ * u.val) := by
      rw [hcast, ← hn, hloop]
      simp [diagramArcPath_apply, κ]
    change Complex.equivRealProd.symm (componentPLLoop D base u) = _
    rw [hplane, hparam]

end DirectGLSSW.HOMFLY
end



