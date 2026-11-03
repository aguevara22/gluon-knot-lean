import RootNormalCoordinates
import SupportedGermIndexOne

set_option autoImplicit false
open Topology unitInterval
namespace DirectGLSSW.HOMFLY.PositionalIndex
open DirectGLSSW.HOMFLY.PrincipalTurning

/-- Composition interface. The explicit point-preimage premise is discharged
by the literal PL root-preimage producer in the source wrapper. -/
theorem supported_pl_root_index_one_of_unique_preimage
    (D : PLLinkDiagram) (base : Fin D.nArc)
    (p q : PlanarPoint ℝ)
    (hp : D.vertexPoint (D.arcSource base) = p)
    (hq : D.vertexPoint (D.arcTarget base) = q)
    (hhalf : ∀ v, 0 ≤ planarDet (q-p) (D.vertexPoint v-p))
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hpoint : ∀ u v : I,
      complexPLLoop D base u = Complex.equivRealProd.symm (affinePoint p q τ) →
      complexPLLoop D base v = Complex.equivRealProd.symm (affinePoint p q τ) → u = v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ havoid : ∀ u : I, complexPLLoop D base u ≠ interiorRootProbe p q τ ε,
        unitPositionalIndex (complexPLLoop D base)
          (complexPLLoop_endpoint_eq D base).symm (interiorRootProbe p q τ ε) havoid = 1 := by
  have hpq : p ≠ q := by
    intro heq
    exact D.arc_endpoints_distinct base (D.vertexPoint_injective (hp.trans (heq.trans hq.symm)))
  let a := supportingRootNormal p q
  let b := Complex.equivRealProd.symm (affinePoint p q τ)
  let L : ℝ := (q.1-p.1)^2+(q.2-p.2)^2
  have hL : 0 < L := root_length_sq_pos p q hpq
  have ha : a ≠ 0 := supportingRootNormal_ne_zero p q hpq
  let γ := complexPLLoop D base
  let g : C(I,ℂ) := ⟨fun u => a*(γ u-b), continuous_const.mul (γ.continuous.sub continuous_const)⟩
  have hgclosed : g 1 = g 0 := by
    change a*(γ 1-b) = a*(γ 0-b)
    rw [show γ 1 = γ 0 from (complexPLLoop_endpoint_eq D base).symm]
  have hgHalf : ∀ u, 0 ≤ (g u).re := by
    have hv : ∀ v : Fin D.nVertex,
        (a * b).re ≤ (a * Complex.equivRealProd.symm (D.vertexPoint v)).re := by
      intro v
      have hh := hhalf v
      dsimp [a,b]
      simp [planarDet] at hh
      simp [supportingRootNormal, affinePoint, Complex.equivRealProd_symm_apply,
        Complex.mul_re, Complex.real_smul]
      nlinarith
    have hl := complexPLLoop_affine_halfplane D base a (a*b).re hv
    intro u
    change 0 ≤ (a*(γ u-b)).re
    rw [mul_sub,Complex.sub_re]
    exact sub_nonneg.mpr (hl u)
  obtain ⟨t₀,ht₀,ht₁,η,hη,κ,hκ,hgerm⟩ :=
    exists_componentPLLoop_root_germ D base τ hτ0 hτ1
  have hlocal : ∀ u : I, |u.val-t₀.val| < η →
      g u = ⟨0,(L*κ)*(t₀.val-u.val)⟩ := by
    intro u hu
    change a*(complexPLLoop D base u-b) = _
    rw [hgerm u hu,hp,hq]
    dsimp [a,b]
    rw [root_normal_affine_difference]
    apply Complex.ext <;> simp [L] <;> ring
  have htpoint : complexPLLoop D base t₀ = b := by
    have hh := hgerm t₀ (by simpa using hη)
    simpa [hp,hq,b] using hh
  have hzeroUnique : ∀ u : I, g u = 0 → u = t₀ := by
    intro u hu
    have hmul : a*(γ u-b) = 0 := hu
    have hγ : γ u = b := sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left ha)
    exact hpoint u t₀ hγ htpoint
  obtain ⟨r,hr,hindex⟩ := supported_germ_small_probe_index_one g hgclosed t₀
    ht₀ ht₁ (L*κ) η (mul_pos hL hκ) hη hgHalf hlocal hzeroUnique
  refine ⟨r/L,div_pos hr hL,?_⟩
  intro ε hε hεsmall
  have hscale : ε*L < r := (lt_div_iff₀ hL).mp hεsmall
  obtain ⟨hgavoid,hgindex⟩ := hindex (ε*L) (mul_pos hε hL) hscale
  let f : C(I,ℂ) := ⟨fun u => g u-(ε*L:ℝ),g.continuous.sub continuous_const⟩
  have hfclosed : f 1 = f 0 := by change g 1 - (ε*L:ℝ) = g 0 - (ε*L:ℝ); rw [hgclosed]
  have hfavoid : ∀ u, f u ≠ 0 := by
    intro u hu
    exact hgavoid u (sub_eq_zero.mp hu)
  have hfg : ∀ u, f u = (1:ℂ)*(g u-(ε*L:ℝ)) := by intro u; simp [f]
  have hfindex : unitPositionalIndex f hfclosed 0 hfavoid = 1 := by
    rw [unitPositionalIndex_affine_covariance g f hgclosed hfclosed (ε*L:ℝ) 1
      one_ne_zero hgavoid hfavoid hfg]
    exact hgindex
  have hformula : ∀ u, f u = a*(γ u-interiorRootProbe p q τ ε) := by
    intro u
    have hprobe := root_normal_interior_probe p q τ ε
    change a*(interiorRootProbe p q τ ε-b) = (ε*L:ℝ) at hprobe
    change a*(γ u-b)-(ε*L:ℝ) = a*(γ u-interiorRootProbe p q τ ε)
    rw [← hprobe]
    ring
  have havoid := avoids_probe_of_affine_position γ f (interiorRootProbe p q τ ε) a hfavoid hformula
  refine ⟨havoid,?_⟩
  rw [← unitPositionalIndex_affine_covariance γ f (complexPLLoop_endpoint_eq D base).symm
    hfclosed (interiorRootProbe p q τ ε) a ha havoid hfavoid hformula]
  exact hfindex

end DirectGLSSW.HOMFLY.PositionalIndex

