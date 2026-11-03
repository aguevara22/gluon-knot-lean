import RoundingIncidentRaySeparation
import RetainedRoundingIntersections

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Aggregate Gate4: literal incoming retained point as the center-based ray. -/
theorem retainedArcPoint_incoming_ray (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) :
    Complex.equivRealProd (cornerCenter D e -
      (1 - (δ.val + (1 - 2 * δ.val) * t)) • arcVector D e) = retainedArcPoint D e δ t := by
  apply Prod.ext <;> simp [Complex.equivRealProd_apply,Complex.real_smul,
    cornerCenter,arcVector,retainedArcPoint,affinePoint] <;> ring

/-- Aggregate Gate4: literal outgoing retained point as the center-based ray. -/
theorem retainedArcPoint_outgoing_ray (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (t : ℝ) :
    Complex.equivRealProd (cornerCenter D e +
      (δ.val + (1 - 2 * δ.val) * t) • arcVector D (D.continuation e)) =
      retainedArcPoint D (D.continuation e) δ t := by
  have hi := congrArg D.vertexPoint (D.continuation_incidence e)
  apply Prod.ext <;> simp [Complex.equivRealProd_apply,Complex.real_smul,
    cornerCenter,arcVector,retainedArcPoint,affinePoint,← hi] <;> ring

theorem roundedCorner_incoming_cut (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) :
    Complex.equivRealProd (roundedCorner D e δ.val 0) = retainedArcPoint D e δ 1 := by
  rw [(roundedCorner_endpoints D e δ.val).1]
  have h := retainedArcPoint_incoming_ray D e δ 1
  have hcoef : 1 - (δ.val + (1 - 2 * δ.val) * 1) = δ.val := by ring
  simpa only [hcoef] using h

theorem roundedCorner_outgoing_cut (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) :
    Complex.equivRealProd (roundedCorner D e δ.val 1) =
      retainedArcPoint D (D.continuation e) δ 0 := by
  rw [(roundedCorner_endpoints D e δ.val).2]
  simpa only [mul_zero,add_zero] using retainedArcPoint_outgoing_ray D e δ 0

/-- The actual corner and incoming retained piece meet exactly at their
shared cut endpoint, with exact unit parameters. -/
theorem roundedCorner_retained_incoming_iff (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    Complex.equivRealProd (roundedCorner D e δ.val s) = retainedArcPoint D e δ t ↔
      s = 0 ∧ t = 1 := by
  have hc : 0 ≤ 1 - 2 * δ.val := by linarith [δ.property.2]
  have hb : δ.val ≤ 1 - (δ.val + (1 - 2 * δ.val) * t) := by
    have h := mul_le_mul_of_nonneg_left ht.2 hc
    nlinarith
  constructor
  · intro heq
    have hs0 : s = 0 := by
      by_contra hn
      have hsp : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hn)
      have hcomplex := Complex.equivRealProd.injective
        (heq.trans (retainedArcPoint_incoming_ray D e δ t).symm)
      exact roundedCorner_ne_retained_incoming D e δ.val s _ δ.property.1 ⟨hsp,hs.2⟩ hb hcomplex
    subst s
    have hret := (retainedArcPoint_intersection_iff D e e δ 1 t ⟨by norm_num,by norm_num⟩ ht).mp
      ((roundedCorner_incoming_cut D e δ).symm.trans heq)
    exact ⟨rfl,hret.2.symm⟩
  · rintro ⟨rfl,rfl⟩
    exact roundedCorner_incoming_cut D e δ

/-- The actual corner and outgoing retained piece meet exactly at their
shared cut endpoint, with exact unit parameters. -/
theorem roundedCorner_retained_outgoing_iff (D : PLLinkDiagram) (e : Fin D.nArc)
    (δ : RoundingFraction) (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    Complex.equivRealProd (roundedCorner D e δ.val s) =
      retainedArcPoint D (D.continuation e) δ t ↔ s = 1 ∧ t = 0 := by
  have hc : 0 ≤ 1 - 2 * δ.val := by linarith [δ.property.2]
  have hb : δ.val ≤ δ.val + (1 - 2 * δ.val) * t := by
    nlinarith [mul_nonneg hc ht.1]
  constructor
  · intro heq
    have hs1 : s = 1 := by
      by_contra hn
      have hsp : s < 1 := lt_of_le_of_ne hs.2 hn
      have hcomplex := Complex.equivRealProd.injective
        (heq.trans (retainedArcPoint_outgoing_ray D e δ t).symm)
      exact roundedCorner_ne_retained_outgoing D e δ.val s _ δ.property.1 ⟨hs.1,hsp⟩ hb hcomplex
    subst s
    have hret := (retainedArcPoint_intersection_iff D (D.continuation e) (D.continuation e)
      δ 0 t ⟨by norm_num,by norm_num⟩ ht).mp
      ((roundedCorner_outgoing_cut D e δ).symm.trans heq)
    exact ⟨rfl,hret.2.symm⟩
  · rintro ⟨rfl,rfl⟩
    exact roundedCorner_outgoing_cut D e δ

end DirectGLSSW.HOMFLY.PrincipalTurning






