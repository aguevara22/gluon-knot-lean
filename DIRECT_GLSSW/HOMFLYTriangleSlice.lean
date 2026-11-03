import HOMFLYFiniteDiskCertificate

/-! Exact triangle slicing for the shared finite parity/filling route.
Named consumers: generic-ray membership parity for finite disk certificates,
and convex-cell reconstruction in finite slab decomposition. -/
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

def horizontalCut (a b : PlanarPoint ℝ) : PlanarPoint ℝ :=
  affinePoint a b (-a.2 / (b.2-a.2))

theorem horizontalCut_parameter (a b : PlanarPoint ℝ) (ha : a.2 < 0) (hb : 0 < b.2) :
    0 < -a.2 / (b.2-a.2) ∧ -a.2 / (b.2-a.2) < 1 := by
  have hd : 0 < b.2-a.2 := by linarith
  exact ⟨div_pos (by linarith) hd, (div_lt_one hd).2 (by linarith)⟩

theorem horizontalCut_y (a b : PlanarPoint ℝ) (ha : a.2 < 0) (hb : 0 < b.2) :
    (horizontalCut a b).2 = 0 := by
  have hd : b.2-a.2 ≠ 0 := by linarith
  dsimp [horizontalCut, affinePoint]
  field_simp

theorem horizontalCut_mem_segment (a b : PlanarPoint ℝ) (ha : a.2 < 0)
    (hb : 0 < b.2) : horizontalCut a b ∈ segment ℝ a b := by
  obtain ⟨ht0,ht1⟩ := horizontalCut_parameter a b ha hb
  refine ⟨1-(-a.2/(b.2-a.2)), -a.2/(b.2-a.2), by linarith, le_of_lt ht0,
    by ring, ?_⟩
  ext <;> dsimp [horizontalCut, affinePoint] <;> ring

theorem triangle_barycentric_of_mem (a b c z : PlanarPoint ℝ)
    (hz : z ∈ convexHull ℝ {a,b,c}) :
    ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α+β+γ=1 ∧
      α • a + β • b + γ • c = z := by
  let S : Set (PlanarPoint ℝ) := {x | ∃ α β γ : ℝ,
    0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α+β+γ=1 ∧ α • a + β • b + γ • c = x}
  have hvertices : {a,b,c} ⊆ S := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨1,0,0,by norm_num,by norm_num,by norm_num,by norm_num,by simp⟩
    · exact ⟨0,1,0,by norm_num,by norm_num,by norm_num,by norm_num,by simp⟩
    · exact ⟨0,0,1,by norm_num,by norm_num,by norm_num,by norm_num,by simp⟩
  have hconvex : Convex ℝ S := by
    intro x hx y hy p q hp hq hpq
    obtain ⟨α,β,γ,hα,hβ,hγ,hs,hx⟩ := hx
    obtain ⟨α',β',γ',hα',hβ',hγ',hs',hy⟩ := hy
    refine ⟨p*α+q*α',p*β+q*β',p*γ+q*γ',
      add_nonneg (mul_nonneg hp hα) (mul_nonneg hq hα'),
      add_nonneg (mul_nonneg hp hβ) (mul_nonneg hq hβ'),
      add_nonneg (mul_nonneg hp hγ) (mul_nonneg hq hγ'),?_,?_⟩
    · calc
        _ = p*(α+β+γ)+q*(α'+β'+γ') := by ring
        _ = 1 := by rw [hs,hs']; nlinarith
    · rw [← hx, ← hy]
      ext <;> dsimp <;> ring
  exact convexHull_min hvertices hconvex hz

theorem triangle_horizontal_slice (a b c : PlanarPoint ℝ)
    (ha : a.2 < 0) (hb : 0 < b.2) (hc : 0 < c.2) :
    convexHull ℝ {a,b,c} ∩ {z : PlanarPoint ℝ | z.2 = 0} =
      segment ℝ (horizontalCut a b) (horizontalCut a c) := by
  have hd : -a.2 ≠ 0 := by linarith
  have hdb : b.2-a.2 ≠ 0 := by linarith
  have hdc : c.2-a.2 ≠ 0 := by linarith
  ext z
  constructor
  · rintro ⟨hz,hzy⟩
    change z.2 = 0 at hzy
    obtain ⟨α,β,γ,hα,hβ,hγ,hsum,hpoint⟩ := triangle_barycentric_of_mem a b c z hz
    have hy : α*a.2+β*b.2+γ*c.2=0 := by
      have hh : α*a.2+β*b.2+γ*c.2 = z.2 := congrArg Prod.snd hpoint
      exact hh.trans hzy
    let μ := β*(b.2-a.2)/(-a.2)
    let ν := γ*(c.2-a.2)/(-a.2)
    have hμ : 0 ≤ μ := div_nonneg (mul_nonneg hβ (by linarith)) (by linarith)
    have hν : 0 ≤ ν := div_nonneg (mul_nonneg hγ (by linarith)) (by linarith)
    have hnum : β*(b.2-a.2)+γ*(c.2-a.2) = -a.2 := by
      calc
        _ = (α*a.2+β*b.2+γ*c.2)-a.2*(α+β+γ) := by ring
        _ = -a.2 := by rw [hy, hsum]; ring
    have hμν : μ+ν=1 := by
      dsimp [μ,ν]
      rw [← add_div, hnum, div_self hd]
    have hμt : μ*(-a.2/(b.2-a.2))=β := by
      dsimp [μ]
      field_simp [ne_of_lt ha, hdb] <;> ring
    have hνt : ν*(-a.2/(c.2-a.2))=γ := by
      dsimp [ν]
      field_simp [ne_of_lt ha, hdc] <;> ring
    have hcoef : μ+ν-β-γ=α := by linarith
    refine ⟨μ,ν,hμ,hν,hμν,?_⟩
    rw [← hpoint]
    ext
    · change μ*(a.1+(-a.2/(b.2-a.2))*(b.1-a.1))+
        ν*(a.1+(-a.2/(c.2-a.2))*(c.1-a.1)) = α*a.1+β*b.1+γ*c.1
      calc
        _ = (μ+ν-μ*(-a.2/(b.2-a.2))-ν*(-a.2/(c.2-a.2)))*a.1+
          (μ*(-a.2/(b.2-a.2)))*b.1+(ν*(-a.2/(c.2-a.2)))*c.1 := by ring
        _ = _ := by rw [hμt,hνt,hcoef]
    · change μ*(a.2+(-a.2/(b.2-a.2))*(b.2-a.2))+
        ν*(a.2+(-a.2/(c.2-a.2))*(c.2-a.2)) = α*a.2+β*b.2+γ*c.2
      calc
        _ = (μ+ν-μ*(-a.2/(b.2-a.2))-ν*(-a.2/(c.2-a.2)))*a.2+
          (μ*(-a.2/(b.2-a.2)))*b.2+(ν*(-a.2/(c.2-a.2)))*c.2 := by ring
        _ = _ := by rw [hμt,hνt,hcoef]
  · intro hz
    constructor
    · have hp : horizontalCut a b ∈ convexHull ℝ {a,b,c} :=
        segment_subset_convexHull (by simp) (by simp) (horizontalCut_mem_segment a b ha hb)
      have hq : horizontalCut a c ∈ convexHull ℝ {a,b,c} :=
        segment_subset_convexHull (by simp) (by simp) (horizontalCut_mem_segment a c ha hc)
      exact (convex_convexHull ℝ _).segment_subset hp hq hz
    · rcases hz with ⟨u,v,hu,hv,hs,hz⟩
      change z.2 = 0
      have hy : u*(horizontalCut a b).2 + v*(horizontalCut a c).2 = z.2 :=
        congrArg Prod.snd hz
      rw [horizontalCut_y a b ha hb, horizontalCut_y a c ha hc] at hy
      linarith

end
end DirectGLSSW.HOMFLY






