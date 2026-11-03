import CornerTangentLift
import HoleStarNeighbourConverse

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- All relative tangent angles in one actual corner lie on the same
side of zero. This gives a real angular span strictly less than pi. -/
theorem cornerAngleLift_same_side (D : PLLinkDiagram) (e : Fin D.nArc)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (0≤cornerAngleLift D e s ∧ 0≤cornerAngleLift D e t) ∨
    (cornerAngleLift D e s≤0 ∧ cornerAngleLift D e t≤0) := by
  by_cases hq : 0≤(arcVector D (D.continuation e)/arcVector D e).im
  · left
    have hnonneg (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0≤cornerAngleLift D e x := by
      apply Complex.arg_nonneg_iff.mpr
      simpa [cornerRelativeTangent] using mul_nonneg hx.1 hq
    exact ⟨hnonneg s hs,hnonneg t ht⟩
  · right
    have hnonpos (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : cornerAngleLift D e x≤0 := by
      by_cases hx0 : x=0
      · subst x
        simp [cornerAngleLift,cornerRelativeTangent_zero]
      · apply le_of_lt
        apply Complex.arg_neg_iff.mpr
        have hxp : 0<x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
        simpa [cornerRelativeTangent] using mul_neg_of_pos_of_neg hxp (lt_of_not_ge hq)
    exact ⟨hnonpos s hs,hnonpos t ht⟩

/-- Exact principal increment along the actual consecutive-vector cone.
The difference needs no modular reduction because the whole cone has
angular span less than pi. This will telescope along the diagonal collar. -/
theorem cornerRelativeTangent_ratio_arg (D : PLLinkDiagram) (e : Fin D.nArc)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Complex.arg (cornerRelativeTangent D e t / cornerRelativeTangent D e s) =
      cornerAngleLift D e t-cornerAngleLift D e s := by
  have hsb := cornerAngleLift_open_semicircle D e s hs
  have htb := cornerAngleLift_open_semicircle D e t ht
  have hdiff : -Real.pi < cornerAngleLift D e t-cornerAngleLift D e s ∧
      cornerAngleLift D e t-cornerAngleLift D e s < Real.pi := by
    rcases cornerAngleLift_same_side D e s t hs ht with hsign | hsign <;>
      constructor <;> linarith [hsign.1,hsign.2]
  have hangle : (Complex.arg (cornerRelativeTangent D e t / cornerRelativeTangent D e s) : Real.Angle) =
      ((cornerAngleLift D e t-cornerAngleLift D e s : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub]
    exact Complex.arg_div_coe_angle
      (Complex.slitPlane_ne_zero (cornerRelativeTangent_slitPlane D e t ht))
      (Complex.slitPlane_ne_zero (cornerRelativeTangent_slitPlane D e s hs))
  have hcanon : (((cornerAngleLift D e t-cornerAngleLift D e s : ℝ) : Real.Angle)).toReal =
      cornerAngleLift D e t-cornerAngleLift D e s :=
    Real.Angle.toReal_coe_eq_self_iff.mpr ⟨hdiff.1,hdiff.2.le⟩
  have hreal := congrArg Real.Angle.toReal hangle
  rw [Complex.arg_coe_angle_toReal_eq_arg,hcanon] at hreal
  exact hreal

/-- Any finite actual corner-cone refinement from its first arc direction
to its next arc direction has exactly the source principal turn. -/
theorem cornerRelativeTangent_finite_partition (D : PLLinkDiagram) (e : Fin D.nArc)
    (n : ℕ) (t : ℕ → ℝ) (ht : ∀ i≤n, t i ∈ Set.Icc (0 : ℝ) 1)
    (h0 : t 0=0) (hn : t n=1) :
    (∑ i ∈ Finset.range n, Complex.arg
      (cornerRelativeTangent D e (t (i+1))/cornerRelativeTangent D e (t i))) = turn D e := by
  calc
    _ = ∑ i ∈ Finset.range n, (cornerAngleLift D e (t (i+1))-cornerAngleLift D e (t i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i<n := Finset.mem_range.mp hi
      exact cornerRelativeTangent_ratio_arg D e _ _ (ht i (by omega)) (ht (i+1) (by omega))
    _ = cornerAngleLift D e (t n)-cornerAngleLift D e (t 0) :=
      Finset.sum_range_sub (fun i => cornerAngleLift D e (t i)) n
    _ = turn D e := by
      rw [hn,h0,(cornerAngleLift_endpoints D e).1,(cornerAngleLift_endpoints D e).2,sub_zero]

end DirectGLSSW.HOMFLY.PrincipalTurning




