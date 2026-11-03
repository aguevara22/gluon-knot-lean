import RoundingCutoffLocalization
import GlobalRoundedCurve

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Literal closed-segment avoidance yields a uniform positive clearance. -/
theorem exists_closed_arc_clearance (D : PLLinkDiagram) (b : PlanarPoint ℝ)
    (hb : ∀ e : Fin D.nArc, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      b ≠ affinePoint (D.vertexPoint (D.arcSource e))
        (D.vertexPoint (D.arcTarget e)) t) :
    ∃ r : ℝ, 0 < r ∧ ∀ e : Fin D.nArc, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      r ≤ dist (affinePoint (D.vertexPoint (D.arcSource e))
        (D.vertexPoint (D.arcTarget e)) t) b := by
  classical
  let f : Fin D.nArc × ℝ → PlanarPoint ℝ := fun z =>
    affinePoint (D.vertexPoint (D.arcSource z.1))
      (D.vertexPoint (D.arcTarget z.1)) z.2
  have hl : Continuous (fun z : Fin D.nArc × ℝ => D.vertexPoint (D.arcSource z.1)) :=
    (continuous_of_discreteTopology (f := fun e : Fin D.nArc =>
      D.vertexPoint (D.arcSource e))).comp continuous_fst
  have hr : Continuous (fun z : Fin D.nArc × ℝ => D.vertexPoint (D.arcTarget z.1)) :=
    (continuous_of_discreteTopology (f := fun e : Fin D.nArc =>
      D.vertexPoint (D.arcTarget e))).comp continuous_fst
  have hf : Continuous f := by
    dsimp only [f, affinePoint]
    exact (hl.fst.add (continuous_snd.mul (hr.fst.sub hl.fst))).prodMk
      (hl.snd.add (continuous_snd.mul (hr.snd.sub hl.snd)))
  let K : Set (PlanarPoint ℝ) := f '' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
  have hK : IsCompact K := (Set.finite_univ.isCompact.prod isCompact_Icc).image hf
  have hbK : b ∉ K := by
    rintro ⟨⟨e,t⟩, ⟨_,ht⟩, h⟩
    exact hb e t ht h.symm
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp (hK.isClosed.isOpen_compl.mem_nhds hbK)
  refine ⟨r,hrpos,?_⟩
  intro e t ht
  by_contra h
  have hmem := hball (Metric.mem_ball.mpr (lt_of_not_ge h))
  exact hmem ⟨(e,t), ⟨Set.mem_univ _,ht⟩,rfl⟩

/-- Each cell retains clearance when its corner displacement is small. -/
theorem normalizedRoundedCell_clearance (D : PLLinkDiagram) (b : PlanarPoint ℝ)
    (r : ℝ) (hr : 0 < r) (δ : RoundingFraction)
    (hseg : ∀ e : Fin D.nArc, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      r ≤ dist (affinePoint (D.vertexPoint (D.arcSource e))
        (D.vertexPoint (D.arcTarget e)) t) b)
    (hsmall : ∀ e : Fin D.nArc,
      δ.val * (‖arcVector D e‖ + ‖arcVector D (D.continuation e)‖) < r / 2)
    (e : Fin D.nArc) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    r / 2 ≤ dist (Complex.equivRealProd (normalizedRoundedCell D e δ t)) b := by
  have hp : 0 < 2 * δ.val := mul_pos (by norm_num) δ.property.1
  unfold normalizedRoundedCell roundedStep
  split_ifs with hc
  · have ht' : t / (2 * δ.val) ∈ Set.Icc 0 1 := ⟨div_nonneg ht.1 hp.le,hc⟩
    have hcenter : r ≤ dist (D.vertexPoint (D.arcTarget e)) b := by
      simpa only [affinePoint_one] using hseg e 1 ⟨by norm_num,le_rfl⟩
    have hdisp := le_trans (roundedCorner_planar_dist_le D e δ.val (t / (2*δ.val)))
      (roundedCorner_displacement_bound D e δ.val _ δ.property.1.le ht')
    have htri := dist_triangle (D.vertexPoint (D.arcTarget e))
      (Complex.equivRealProd (roundedCorner D e δ.val (t / (2*δ.val)))) b
    rw [dist_comm (D.vertexPoint (D.arcTarget e))
      (Complex.equivRealProd (roundedCorner D e δ.val (t / (2*δ.val))))] at htri
    linarith [hsmall e]
  · have htδ : 2 * δ.val < t := by
      have hh := (lt_div_iff₀ hp).mp (lt_of_not_ge hc)
      nlinarith
    have hs : t - δ.val ∈ Set.Icc 0 1 := by
      constructor <;> linarith [δ.property.1,ht.2]
    have heq : Complex.equivRealProd (roundingStraight D e δ (t / (2 * δ.val))) =
        affinePoint (D.vertexPoint (D.arcSource (D.continuation e)))
          (D.vertexPoint (D.arcTarget (D.continuation e))) (t - δ.val) := by
      have hscale : (t / (2*δ.val) - 1) * (2*δ.val) = t - 2*δ.val := by
        rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hp), one_mul]
      rw [roundingStraight, smul_smul, hscale]
      have hi := congrArg D.vertexPoint (D.continuation_incidence e)
      apply Prod.ext <;>
        simp [Complex.equivRealProd_apply, cornerCenter, arcVector, affinePoint,
          Complex.real_smul, ← hi] <;> ring
    rw [heq]
    exact le_trans (by linarith : r / 2 ≤ r) (hseg _ _ hs)

/-- Every sufficiently small literal rounding, on every component and at every
time, stays a fixed positive distance from a point outside all closed arcs. -/
theorem exists_uniform_rounded_clearance (D : PLLinkDiagram) (b : PlanarPoint ℝ)
    (hb : ∀ e : Fin D.nArc, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      b ≠ affinePoint (D.vertexPoint (D.arcSource e))
        (D.vertexPoint (D.arcTarget e)) t) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ : RoundingFraction, δ.val < δ₀ → ∀ e : Fin D.nArc, ∀ u : ℝ,
        ρ ≤ dist (Complex.equivRealProd (roundedComponentCurve D e δ u)) b := by
  classical
  obtain ⟨r,hr,hseg⟩ := exists_closed_arc_clearance D b hb
  let cutoff : Fin D.nArc → ℝ := fun e =>
    r / (2 * (‖arcVector D e‖ + ‖arcVector D (D.continuation e)‖ + 1))
  have hcut : ∀ e, 0 < cutoff e := by
    intro e
    dsimp [cutoff]
    exact div_pos hr (by positivity)
  obtain ⟨δ₀,hδ₀,hbound⟩ := TruncationCommonRadius.exists_positive_common_lower_bound cutoff hcut
  refine ⟨r/2,by linarith,δ₀,hδ₀,?_⟩
  intro δ hδ e u
  apply normalizedRoundedCell_clearance D b r hr δ hseg
  · intro f
    have hlt : δ.val < cutoff f := lt_of_lt_of_le hδ (hbound f)
    have hp : 0 < 2 * (‖arcVector D f‖ + ‖arcVector D (D.continuation f)‖ + 1) := by positivity
    have hm := (lt_div_iff₀ hp).mp hlt
    nlinarith [δ.property.1]
  · exact ⟨Int.fract_nonneg u,(Int.fract_lt_one u).le⟩

end DirectGLSSW.HOMFLY.PrincipalTurning
