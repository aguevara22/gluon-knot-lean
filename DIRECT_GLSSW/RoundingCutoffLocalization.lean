import RoundingVertexClearance

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- One actual common vertex radius; its triple-radius neighborhoods exclude
all forbidden geometry, so its vertex balls are pairwise disjoint. -/
theorem exists_common_vertex_radius (D : PLLinkDiagram) (b : PlanarPoint ℝ)
    (hb : ∀ v, D.vertexPoint v ≠ b) :
    ∃ r : ℝ, 0 < r ∧
      (∀ v : Fin D.nVertex, ∀ x : PlanarPoint ℝ, dist x (D.vertexPoint v) < 3 * r →
        x ≠ b ∧ (∀ w : Fin D.nVertex, w ≠ v → x ≠ D.vertexPoint w) ∧
        (∀ e : Fin D.nArc, D.arcSource e ≠ v → D.arcTarget e ≠ v →
          ∀ t : ℝ, t ∈ Set.Icc 0 1 → x ≠ affinePoint (D.vertexPoint (D.arcSource e))
            (D.vertexPoint (D.arcTarget e)) t)) ∧
      (∀ v w : Fin D.nVertex, v ≠ w →
        Disjoint (Metric.ball (D.vertexPoint v) r) (Metric.ball (D.vertexPoint w) r)) := by
  classical
  choose ρ hρ hgood using exists_vertex_localization_radius D b hb
  obtain ⟨R,hR,hbounds⟩ := TruncationCommonRadius.exists_positive_common_lower_bound ρ hρ
  have hr : 0 < R / 3 := by linarith
  have hclear : ∀ v : Fin D.nVertex, ∀ x : PlanarPoint ℝ,
      dist x (D.vertexPoint v) < 3 * (R / 3) →
      x ≠ b ∧ (∀ w : Fin D.nVertex, w ≠ v → x ≠ D.vertexPoint w) ∧
      (∀ e : Fin D.nArc, D.arcSource e ≠ v → D.arcTarget e ≠ v →
        ∀ t : ℝ, t ∈ Set.Icc 0 1 → x ≠ affinePoint (D.vertexPoint (D.arcSource e))
          (D.vertexPoint (D.arcTarget e)) t) := by
    intro v x hx
    apply hgood v x
    linarith [hbounds v]
  refine ⟨R / 3,hr,hclear,?_⟩
  intro v w hvw
  apply Set.disjoint_left.mpr
  intro x hxv hxw
  have hdv : dist x (D.vertexPoint v) < R / 3 := hxv
  have hdw : dist x (D.vertexPoint w) < R / 3 := hxw
  have hd := dist_triangle (D.vertexPoint w) x (D.vertexPoint v)
  rw [dist_comm (D.vertexPoint w) x] at hd
  have hnear : dist (D.vertexPoint w) (D.vertexPoint v) < 3 * (R / 3) := by linarith
  exact (hclear v (D.vertexPoint w) hnear).2.1 w (Ne.symm hvw) rfl

/-- Explicit displacement estimate for the literal quadratic rounding. -/
theorem roundedCorner_displacement_bound (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ t : ℝ) (hδ : 0 ≤ δ) (ht : t ∈ Set.Icc 0 1) :
    ‖roundedCorner D e δ t - cornerCenter D e‖ ≤
      δ * (‖arcVector D e‖ + ‖arcVector D (D.continuation e)‖) := by
  have h1 : 0 ≤ (1 - t) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ t ^ 2 := sq_nonneg _
  have h1le : (1 - t) ^ 2 ≤ 1 := by nlinarith [ht.1,ht.2]
  have h2le : t ^ 2 ≤ 1 := by nlinarith [ht.1,ht.2]
  have heq : roundedCorner D e δ t - cornerCenter D e =
      δ • ((-((1 - t) ^ 2)) • arcVector D e + t ^ 2 • arcVector D (D.continuation e)) := by
    simp [roundedCorner]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]
  apply mul_le_mul_of_nonneg_left _ hδ
  calc
    ‖(-((1 - t) ^ 2)) • arcVector D e + t ^ 2 • arcVector D (D.continuation e)‖ ≤
        ‖(-((1 - t) ^ 2)) • arcVector D e‖ + ‖t ^ 2 • arcVector D (D.continuation e)‖ := norm_add_le _ _
    _ = (1 - t) ^ 2 * ‖arcVector D e‖ + t ^ 2 * ‖arcVector D (D.continuation e)‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg h1, abs_of_nonneg h2]
    _ ≤ ‖arcVector D e‖ + ‖arcVector D (D.continuation e)‖ := by
      nlinarith [norm_nonneg (arcVector D e),norm_nonneg (arcVector D (D.continuation e))]

/-- Complex-to-plane coordinates are nonexpanding, for the actual center. -/
theorem roundedCorner_planar_dist_le (D : PLLinkDiagram) (e : Fin D.nArc) (δ t : ℝ) :
    dist (Complex.equivRealProd (roundedCorner D e δ t)) (D.vertexPoint (D.arcTarget e)) ≤
      ‖roundedCorner D e δ t - cornerCenter D e‖ := by
  have h := Complex.lipschitz_equivRealProd.dist_le_mul
    (roundedCorner D e δ t) (cornerCenter D e)
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, cornerCenter, Complex.equivRealProd_apply] using h

end DirectGLSSW.HOMFLY.PrincipalTurning



