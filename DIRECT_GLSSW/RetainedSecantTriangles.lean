import FiniteSecantRetainedRectangles
import TriangleOriginBalance

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open Equiv
attribute [local instance] Classical.propDecidable

theorem weighted_three_mem_interval (a b x y z α β γ : ℝ)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (hz : z ∈ Set.Icc a b)
    (hα : 0≤α) (hβ : 0≤β) (hγ : 0≤γ) (hs : α+β+γ=1) :
    α*x+β*y+γ*z ∈ Set.Icc a b := by
  constructor
  · calc
      a = (α+β+γ)*a := by rw [hs]; ring
      _ = α*a+β*a+γ*a := by ring
      _ ≤ α*x+β*y+γ*z := add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hx.1 hα) (mul_le_mul_of_nonneg_left hy.1 hβ))
        (mul_le_mul_of_nonneg_left hz.1 hγ)
  · calc
      α*x+β*y+γ*z ≤ α*b+β*b+γ*b := add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hx.2 hα) (mul_le_mul_of_nonneg_left hy.2 hβ))
        (mul_le_mul_of_nonneg_left hz.2 hγ)
      _ = (α+β+γ)*b := by ring
      _ = b := by rw [hs]; ring

theorem affinePoint_three_combination (A B : PlanarPoint ℝ) (x y z α β γ : ℝ)
    (hs : α+β+γ=1) :
    affinePoint A B (α*x+β*y+γ*z) =
      α • affinePoint A B x + β • affinePoint A B y + γ • affinePoint A B z := by
  apply Prod.ext <;> dsimp [affinePoint]
  · linear_combination -A.1*hs
  · linear_combination -A.2*hs

theorem basedUniformPLCurve_axis_barycentric {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b x y z α β γ : ℝ)
    (hcell : secantAxisAdjacent T C a b)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (hz : z ∈ Set.Icc a b)
    (hα : 0≤α) (hβ : 0≤β) (hγ : 0≤γ) (hs : α+β+γ=1) :
    basedUniformPLCurve T C (α*x+β*y+γ*z) =
      α • basedUniformPLCurve T C x + β • basedUniformPLCurve T C y + γ • basedUniformPLCurve T C z := by
  rw [basedUniformPLCurve_axis_cell T C a b _ hcell
      (weighted_three_mem_interval a b x y z α β γ hx hy hz hα hβ hγ hs),
    basedUniformPLCurve_axis_cell T C a b x hcell hx,
    basedUniformPLCurve_axis_cell T C a b y hcell hy,
    basedUniformPLCurve_axis_cell T C a b z hcell hz]
  have ht : α*x+β*y+γ*z+1/2-(Int.floor (a+1/2) : ℝ) =
      α*(x+1/2-(Int.floor (a+1/2) : ℝ))+
      β*(y+1/2-(Int.floor (a+1/2) : ℝ))+
      γ*(z+1/2-(Int.floor (a+1/2) : ℝ)) := by
    linear_combination (-(1/2-(Int.floor (a+1/2) : ℝ)))*hs
  rw [ht]
  exact affinePoint_three_combination _ _ _ _ _ _ _ _ hs

theorem basedUniformSecant_rectangle_barycentric {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b u v s1 s2 s3 t1 t2 t3 α β γ : ℝ)
    (hc1 : secantAxisAdjacent T C a b) (hc2 : secantAxisAdjacent T C u v)
    (hs1 : s1 ∈ Set.Icc a b) (hs2 : s2 ∈ Set.Icc a b) (hs3 : s3 ∈ Set.Icc a b)
    (ht1 : t1 ∈ Set.Icc u v) (ht2 : t2 ∈ Set.Icc u v) (ht3 : t3 ∈ Set.Icc u v)
    (hα : 0≤α) (hβ : 0≤β) (hγ : 0≤γ) (hweight : α+β+γ=1) :
    basedUniformSecant T C (α*s1+β*s2+γ*s3) (α*t1+β*t2+γ*t3) =
      α • basedUniformSecant T C s1 t1 + β • basedUniformSecant T C s2 t2 +
        γ • basedUniformSecant T C s3 t3 := by
  apply Complex.equivRealProd.injective
  simp only [basedUniformSecant,Equiv.apply_symm_apply]
  rw [basedUniformPLCurve_axis_barycentric T C u v t1 t2 t3 α β γ hc2 ht1 ht2 ht3 hα hβ hγ hweight,
    basedUniformPLCurve_axis_barycentric T C a b s1 s2 s3 α β γ hc1 hs1 hs2 hs3 hα hβ hγ hweight]
  apply Prod.ext <;>
    simp [Complex.equivRealProd_apply,Complex.equivRealProd_symm_apply] <;> ring

/-- Covers either literal half-rectangle triangle, and any further triangle
whose three vertices lie in this actual retained rectangle. -/
theorem retainedSecantTriangle_origin_excluded {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b u v s1 s2 s3 t1 t2 t3 : ℝ)
    (hr : ((a,b),(u,v)) ∈ secantRetainedRectangles T C)
    (hs1 : s1 ∈ Set.Icc a b) (hs2 : s2 ∈ Set.Icc a b) (hs3 : s3 ∈ Set.Icc a b)
    (ht1 : t1 ∈ Set.Icc u v) (ht2 : t2 ∈ Set.Icc u v) (ht3 : t3 ∈ Set.Icc u v) :
    (0 : PlanarPoint ℝ) ∉ convexHull ℝ
      {Complex.equivRealProd (basedUniformSecant T C s1 t1),
       Complex.equivRealProd (basedUniformSecant T C s2 t2),
       Complex.equivRealProd (basedUniformSecant T C s3 t3)} := by
  intro hh
  obtain ⟨α,β,γ,hα,hβ,hγ,hweight,hpoint⟩ := triangle_barycentric_of_mem _ _ _ _ hh
  have hc := Finset.mem_product.mp (Finset.mem_filter.mp hr).1
  have hc1 : secantAxisAdjacent T C a b := (Finset.mem_filter.mp hc.1).2
  have hc2 : secantAxisAdjacent T C u v := (Finset.mem_filter.mp hc.2).2
  apply secantRetainedRectangle_nonzero T C a b u v _ _ hr
    (weighted_three_mem_interval a b s1 s2 s3 α β γ hs1 hs2 hs3 hα hβ hγ hweight)
    (weighted_three_mem_interval u v t1 t2 t3 α β γ ht1 ht2 ht3 hα hβ hγ hweight)
  rw [basedUniformSecant_rectangle_barycentric T C a b u v s1 s2 s3 t1 t2 t3 α β γ
    hc1 hc2 hs1 hs2 hs3 ht1 ht2 ht3 hα hβ hγ hweight]
  apply Complex.equivRealProd.injective
  simpa only [Complex.equivRealProd_apply,Complex.add_re,Complex.add_im,
    Complex.smul_re,Complex.smul_im,Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul] using hpoint

end DirectGLSSW.HOMFLY.PrincipalTurning





