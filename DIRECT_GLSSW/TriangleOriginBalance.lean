import TriangleSignedBalance
import HOMFLYTriangleRegularClosed

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
attribute [local instance] Classical.propDecidable

theorem barycentric_det_relations (a b c : ℂ) (α β γ : ℝ)
    (hs : α+β+γ=1) (hp : α • a+β • b+γ • c=0) :
    α*complexDet (b-a) (c-a)=complexDet b c ∧
    β*complexDet (b-a) (c-a)=complexDet c a ∧
    γ*complexDet (b-a) (c-a)=complexDet a b := by
  have hr : α*a.re+β*b.re+γ*c.re=0 := by
    simpa only [Complex.add_re,Complex.smul_re,smul_eq_mul,Complex.zero_re] using congrArg Complex.re hp
  have hi : α*a.im+β*b.im+γ*c.im=0 := by
    simpa only [Complex.add_im,Complex.smul_im,smul_eq_mul,Complex.zero_im] using congrArg Complex.im hp
  simp only [complexDet,Complex.sub_re,Complex.sub_im]
  constructor
  · linear_combination (b.re*c.im-b.im*c.re)*hs + (b.im-c.im)*hr + (c.re-b.re)*hi
  constructor
  · linear_combination (c.re*a.im-c.im*a.re)*hs + (c.im-a.im)*hr + (a.re-c.re)*hi
  · linear_combination (a.re*b.im-a.im*b.re)*hs + (a.im-b.im)*hr + (b.re-a.re)*hi

theorem origin_triangle_strict_weights (a b c : ℂ)
    (hab : (0 : ℂ) ∉ segment ℝ a b) (hbc : (0 : ℂ) ∉ segment ℝ b c)
    (hca : (0 : ℂ) ∉ segment ℝ c a)
    (hh : (0 : PlanarPoint ℝ) ∈ convexHull ℝ
      {Complex.equivRealProd a,Complex.equivRealProd b,Complex.equivRealProd c}) :
    ∃ α β γ : ℝ, 0<α ∧ 0<β ∧ 0<γ ∧ α+β+γ=1 ∧ α • a+β • b+γ • c=0 := by
  obtain ⟨α,β,γ,hα,hβ,hγ,hs,hp⟩ := triangle_barycentric_of_mem _ _ _ _ hh
  have hp' : α • a+β • b+γ • c=0 := by
    apply Complex.equivRealProd.injective
    simpa only [Complex.equivRealProd_apply,Complex.add_re,Complex.add_im,
      Complex.smul_re,Complex.smul_im,Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul] using hp
  have hα' : 0<α := by
    apply lt_of_le_of_ne hα
    intro he
    apply hbc
    refine ⟨β,γ,hβ,hγ,by linarith,?_⟩
    simpa [← he] using hp'
  have hβ' : 0<β := by
    apply lt_of_le_of_ne hβ
    intro he
    apply hca
    refine ⟨γ,α,hγ,hα,by linarith,?_⟩
    simpa [← he,add_comm] using hp'
  have hγ' : 0<γ := by
    apply lt_of_le_of_ne hγ
    intro he
    apply hab
    refine ⟨α,β,hα,hβ,by linarith,?_⟩
    simpa [← he] using hp'
  exact ⟨α,β,γ,hα',hβ',hγ',hs,hp'⟩

theorem origin_triangle_of_same_sign (a b c : ℂ)
    (h : (0<complexDet a b ∧ 0<complexDet b c ∧ 0<complexDet c a) ∨
      (complexDet a b<0 ∧ complexDet b c<0 ∧ complexDet c a<0)) :
    (0 : PlanarPoint ℝ) ∈ convexHull ℝ
      {Complex.equivRealProd a,Complex.equivRealProd b,Complex.equivRealProd c} := by
  let S := complexDet (b-a) (c-a)
  have hs : S=complexDet a b+complexDet b c+complexDet c a := complexDet_triangle_orientation a b c
  have hn : S≠0 := by rcases h with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;> dsimp [S] at * <;> linarith
  have hα : 0≤complexDet b c/S := by
    rcases h with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩
    · exact (div_pos h2 (by linarith)).le
    · exact (div_pos_of_neg_of_neg h2 (by linarith)).le
  have hβ : 0≤complexDet c a/S := by
    rcases h with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩
    · exact (div_pos h3 (by linarith)).le
    · exact (div_pos_of_neg_of_neg h3 (by linarith)).le
  have hγ : 0≤complexDet a b/S := by
    rcases h with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩
    · exact (div_pos h1 (by linarith)).le
    · exact (div_pos_of_neg_of_neg h1 (by linarith)).le
  have hsum : complexDet b c/S+complexDet c a/S+complexDet a b/S=1 := by
    rw [div_add_div_same,div_add_div_same]
    rw [show complexDet b c+complexDet c a+complexDet a b=S by linarith,div_self hn]
  have hpoint : (complexDet b c/S) • Complex.equivRealProd a+
      (complexDet c a/S) • Complex.equivRealProd b+
      (complexDet a b/S) • Complex.equivRealProd c=0 := by
    apply Prod.ext <;> dsimp [Complex.equivRealProd_apply,complexDet] <;>
      field_simp <;> ring
  have hm := triangle_mem_of_barycentric (Complex.equivRealProd a) (Complex.equivRealProd b)
    (Complex.equivRealProd c) (complexDet b c/S) (complexDet c a/S) (complexDet a b/S) hα hβ hγ hsum
  rw [hpoint] at hm
  exact hm

/-- Literal affine-triangle boundary angular sum equals the oriented origin
indicator. Boundary avoidance is the only geometric premise; the zero-area
case is included and gives zero. Convex-hull membership is used under the
explicit no-boundary-origin hypothesis, with strict weights derived above. -/
theorem triangle_origin_angle_balance (a b c : ℂ)
    (hab : (0 : ℂ) ∉ segment ℝ a b) (hbc : (0 : ℂ) ∉ segment ℝ b c)
    (hca : (0 : ℂ) ∉ segment ℝ c a) :
    Complex.arg (b/a)+Complex.arg (c/b)+Complex.arg (a/c) =
      if (0 : PlanarPoint ℝ) ∈ convexHull ℝ
          {Complex.equivRealProd a,Complex.equivRealProd b,Complex.equivRealProd c}
      then if 0<complexDet (b-a) (c-a) then 2*Real.pi
        else if complexDet (b-a) (c-a)<0 then -(2*Real.pi) else 0
      else 0 := by
  classical
  by_cases hh : (0 : PlanarPoint ℝ) ∈ convexHull ℝ
      {Complex.equivRealProd a,Complex.equivRealProd b,Complex.equivRealProd c}
  · rw [if_pos hh]
    obtain ⟨α,β,γ,hα,hβ,hγ,hs,hp⟩ := origin_triangle_strict_weights a b c hab hbc hca hh
    obtain ⟨hA,hB,hC⟩ := barycentric_det_relations a b c α β γ hs hp
    by_cases hpos : 0<complexDet (b-a) (c-a)
    · rw [if_pos hpos,triangle_signed_angle_balance a b c hab hbc hca,
        if_pos ⟨by nlinarith,by nlinarith,by nlinarith⟩]
    · rw [if_neg hpos]
      by_cases hneg : complexDet (b-a) (c-a)<0
      · have hn : complexDet a b<0 ∧ complexDet b c<0 ∧ complexDet c a<0 :=
          ⟨by nlinarith,by nlinarith,by nlinarith⟩
        rw [if_pos hneg,triangle_signed_angle_balance a b c hab hbc hca,
          if_neg (by rintro ⟨h,_,_⟩; linarith [hn.1]),if_pos hn]
      · rw [if_neg hneg]
        exact degenerate_triangle_angle_balance a b c hab hbc hca (by linarith)
  · rw [if_neg hh,triangle_signed_angle_balance a b c hab hbc hca]
    have hp : ¬(0<complexDet a b ∧ 0<complexDet b c ∧ 0<complexDet c a) :=
      fun h => hh (origin_triangle_of_same_sign a b c (Or.inl h))
    have hn : ¬(complexDet a b<0 ∧ complexDet b c<0 ∧ complexDet c a<0) :=
      fun h => hh (origin_triangle_of_same_sign a b c (Or.inr h))
    rw [if_neg hp,if_neg hn]

end DirectGLSSW.HOMFLY.PrincipalTurning




