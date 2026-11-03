import CornerSecantCombination

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open Equiv PermutationOrbits

/-- Any two parameters in one actual affine arc cell give its actual vector. -/
theorem basedUniformSecant_same_arc_cell {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (k : ℤ) (s t : ℝ)
    (hs : s ∈ Set.Icc ((k : ℝ)-1/2) ((k : ℝ)+1/2))
    (ht : t ∈ Set.Icc ((k : ℝ)-1/2) ((k : ℝ)+1/2)) :
    basedUniformSecant T C s t = ((t-s : ℝ) : ℂ)*
      arcVector D ((D.continuation ^ k) (T.baseArc C).val) := by
  have hsarc := uniformPLCurve_arc_cell D (T.baseArc C).val k (s+1/2-(k : ℝ))
    (by constructor <;> linarith [hs.1,hs.2])
  have htarc := uniformPLCurve_arc_cell D (T.baseArc C).val k (t+1/2-(k : ℝ))
    (by constructor <;> linarith [ht.1,ht.2])
  have hstime : (k : ℝ)+(s+1/2-(k : ℝ))=s+1/2 := by ring
  have httime : (k : ℝ)+(t+1/2-(k : ℝ))=t+1/2 := by ring
  rw [hstime] at hsarc
  rw [httime] at htarc
  apply Complex.equivRealProd.injective
  simp only [basedUniformSecant,Equiv.apply_symm_apply]
  change uniformPLCurve D (T.baseArc C).val (t+1/2) -
    uniformPLCurve D (T.baseArc C).val (s+1/2) = _
  rw [htarc,hsarc]
  apply Prod.ext <;> simp [Complex.equivRealProd_apply,arcVector,affinePoint] <;> ring

/-- Actual secants before, across and after one source vertex all use its
same consecutive-vector cone, with literal nonnegative travel lengths. -/
theorem basedUniformSecant_two_arc_cells {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (k : ℤ) (s t : ℝ)
    (hs : s ∈ Set.Icc ((k : ℝ)-1/2) ((k : ℝ)+3/2))
    (ht : t ∈ Set.Icc ((k : ℝ)-1/2) ((k : ℝ)+3/2)) (hst : s≤t) :
    basedUniformSecant T C s t =
      ((min t ((k : ℝ)+1/2)-min s ((k : ℝ)+1/2) : ℝ) : ℂ) *
        arcVector D ((D.continuation ^ k) (T.baseArc C).val) +
      ((max t ((k : ℝ)+1/2)-max s ((k : ℝ)+1/2) : ℝ) : ℂ) *
        arcVector D (D.continuation ((D.continuation ^ k) (T.baseArc C).val)) := by
  by_cases htp : t≤(k : ℝ)+1/2
  · have hsp := hst.trans htp
    rw [min_eq_left htp,min_eq_left hsp,max_eq_right htp,max_eq_right hsp]
    simp only [sub_self,Complex.ofReal_zero,zero_mul,add_zero]
    exact basedUniformSecant_same_arc_cell T C k s t ⟨hs.1,hsp⟩ ⟨ht.1,htp⟩
  · by_cases hps : (k : ℝ)+1/2≤s
    · have hpt := hps.trans hst
      rw [min_eq_right hpt,min_eq_right hps,max_eq_left hpt,max_eq_left hps]
      simp only [sub_self,Complex.ofReal_zero,zero_mul,zero_add]
      have hsame := basedUniformSecant_same_arc_cell T C (k+1) s t
        (by push_cast; constructor <;> linarith [hps,hs.2])
        (by push_cast; constructor <;> linarith [hpt,ht.2])
      have hp : (D.continuation ^ (k+1)) (T.baseArc C).val =
          D.continuation ((D.continuation ^ k) (T.baseArc C).val) := by
        rw [add_comm k 1,zpow_add,Equiv.Perm.mul_apply,zpow_one]
      simpa only [hp] using hsame
    · have hsp := (lt_of_not_ge hps).le
      have hpt := (lt_of_not_ge htp).le
      rw [min_eq_right hpt,min_eq_left hsp,max_eq_left hpt,max_eq_right hsp]
      convert basedUniformSecant_one_corner T C k s t ⟨hs.1,hsp⟩ ⟨hpt,ht.2⟩ using 1 <;> congr 2 <;> ring

end DirectGLSSW.HOMFLY.PrincipalTurning


