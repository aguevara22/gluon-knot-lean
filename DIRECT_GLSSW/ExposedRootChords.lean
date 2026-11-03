import OuterPotentialSums
import HalfPlaneChordAngle

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Literal finite supporting half-plane at this traversal's own directed base arc. -/
def actualRootVertexHalfplane {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) : Prop :=
  ∀ v : Fin D.nVertex, 0 ≤ planarDet
    (D.vertexPoint (D.arcTarget (T.baseArc C).val)-D.vertexPoint (D.arcSource (T.baseArc C).val))
    (D.vertexPoint v-D.vertexPoint (D.arcSource (T.baseArc C).val))

private theorem affine_halfplane (p u a b : PlanarPoint ℝ) (t : ℝ)
    (ht0 : 0≤t) (ht1 : t≤1)
    (ha : 0≤planarDet u (a-p)) (hb : 0≤planarDet u (b-p)) :
    0≤planarDet u (affinePoint a b t-p) := by
  have he : planarDet u (affinePoint a b t-p) =
      (1-t)*planarDet u (a-p)+t*planarDet u (b-p) := by
    simp only [planarDet,affinePoint,Prod.fst_sub,Prod.snd_sub]
    ring
  rw [he]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) ha) (mul_nonneg ht0 hb)

theorem actualRootVertexHalfplane_curve {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (hhalf : actualRootVertexHalfplane T C) (t : ℝ) :
    0≤planarDet
      (D.vertexPoint (D.arcTarget (T.baseArc C).val)-D.vertexPoint (D.arcSource (T.baseArc C).val))
      (basedUniformPLCurve T C t-D.vertexPoint (D.arcSource (T.baseArc C).val)) := by
  unfold basedUniformPLCurve uniformPLCurve
  exact affine_halfplane _ _ _ _ _ (Int.fract_nonneg _) (Int.fract_lt_one _).le
    (hhalf _) (hhalf _)

/-- Relative actual root chords lie in the closed upper half-plane. -/
theorem actualRootVertexHalfplane_relative_im {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (hhalf : actualRootVertexHalfplane T C) (t : ℝ) :
    0≤(basedUniformSecant T C 0 t/arcVector D (T.baseArc C).val).im := by
  have hh := actualRootVertexHalfplane_curve T C hhalf t
  have he : (basedUniformSecant T C 0 t).im * (arcVector D (T.baseArc C).val).re -
      (basedUniformSecant T C 0 t).re * (arcVector D (T.baseArc C).val).im =
      planarDet
        (D.vertexPoint (D.arcTarget (T.baseArc C).val)-D.vertexPoint (D.arcSource (T.baseArc C).val))
        (basedUniformPLCurve T C t-D.vertexPoint (D.arcSource (T.baseArc C).val)) := by
    simp [basedUniformSecant,basedUniformPLCurve_midpoint,arcVector,
      Complex.equivRealProd_symm_apply,Prod.fst_sub,Prod.snd_sub,planarDet,affinePoint]
    ring
  rw [Complex.div_im,←sub_div,he]
  exact div_nonneg hh (Complex.normSq_nonneg _)

/-- The actual basepoint has no other preimage in the open period. -/
theorem actualRootChord_ne_zero {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) (componentArcLength D (T.baseArc C).val : ℝ)) :
    basedUniformSecant T C 0 t≠0 := by
  intro hz
  have hm : (0 : ℝ)≤(componentArcLength D (T.baseArc C).val : ℝ) := by positivity
  rcases (basedUniformSecant_global_zero_iff T C 0 t ⟨le_rfl,hm⟩
    ⟨ht.1.le,ht.2.le⟩).mp hz with he | he | he | ⟨c,i,j,_,_,_,hi,_⟩
  · linarith [ht.1]
  · linarith [he.2,ht.2]
  · linarith [he.2,ht.1]
  · linarith [crossingVisitTime_positive T c i]

/-- Actual adjacent axis cells give affine normalized root chords. -/
theorem actualRootChord_axis_affine {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b r : ℝ) (hc : secantAxisAdjacent T C a b)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    basedUniformSecant T C 0 ((1-r)*a+r*b)/arcVector D (T.baseArc C).val =
      ((1-r : ℝ) : ℂ)*(basedUniformSecant T C 0 a/arcVector D (T.baseArc C).val)+
      (r : ℂ)*(basedUniformSecant T C 0 b/arcVector D (T.baseArc C).val) := by
  have hab : a≤b := hc.2.2.1.le
  have hp := basedUniformPLCurve_axis_barycentric T C a b a b a (1-r) r 0 hc
    ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ ⟨le_rfl,hab⟩ (by linarith [hr.2]) hr.1 le_rfl (by ring)
  simp only [zero_mul,add_zero,zero_smul,add_zero] at hp
  have he : basedUniformSecant T C 0 ((1-r)*a+r*b) =
      ((1-r : ℝ) : ℂ)*basedUniformSecant T C 0 a+(r : ℂ)*basedUniformSecant T C 0 b := by
    apply Complex.equivRealProd.injective
    simp only [basedUniformSecant,Equiv.apply_symm_apply]
    rw [hp]
    apply Prod.ext <;> simp [Complex.equivRealProd_apply,Complex.equivRealProd_symm_apply] <;> ring
  rw [he,add_div,mul_div_assoc,mul_div_assoc]

end
end DirectGLSSW.HOMFLY.PrincipalTurning




