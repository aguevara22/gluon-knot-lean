import ActualSplitAvoidance

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY

theorem ascendingClosure_range (D : PLLinkDiagram) (e : Fin D.nArc) (H : ℝ) :
    Set.range (ascendingClosure D e H) =
      Set.range (fun t : unitInterval => (splitBeta D e t,H+1-t.val)) := by
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    refine ⟨⟨1-t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩,?_⟩
    apply Prod.ext
    · apply Complex.ext <;>
        simp [splitBeta_apply, ascendingClosure, Complex.equivRealProd_symm_apply, affinePoint] <;> ring
    · simp [ascendingClosure]
      ring
  · rintro ⟨t,rfl⟩
    refine ⟨⟨1-t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩,?_⟩
    apply Prod.ext
    · apply Complex.ext <;>
        simp [splitBeta_apply, ascendingClosure, Complex.equivRealProd_symm_apply, affinePoint] <;> ring
    · simp [ascendingClosure]
      ring

/-- The actual spatial arcs meet only at the two selected base-arc points.
Every interior-avoidance input has been discharged from the diagram fields. -/
theorem actual_spatial_arcs_intersection (D : PLLinkDiagram) (e : Fin D.nArc) (H : ℝ) :
    Set.range (descendingMain D e H) ∩ Set.range (ascendingClosure D e H) =
      {(Complex.equivRealProd.symm (splitBaseA D e),H+1),
       (Complex.equivRealProd.symm (splitBaseB D e),H)} := by
  rw [ascendingClosure_range]
  have h := height_arcs_intersection (splitMainComplex D e) (splitBeta D e) H
    (splitMainComplex_endpoints D e).1 (splitMainComplex_endpoints D e).2
    (splitMain_avoids_beta D e)
  change Set.range (descendingMain D e H) ∩ _ = _ at h
  simpa only [splitMainComplex_apply, (splitMainPlanar_endpoints D e).1,
    (splitMainPlanar_endpoints D e).2] using h

theorem splitSpatialTrace_height_bounds (D : PLLinkDiagram) (e : Fin D.nArc)
    (H : ℝ) (x : ℂ × ℝ) (hx : x ∈ splitSpatialTrace D e H) : H ≤ x.2 ∧ x.2 ≤ H+1 := by
  rcases hx with ⟨t,rfl⟩ | ⟨t,rfl⟩
  · simp only [descendingMain]
    constructor <;> linarith [t.property.1,t.property.2]
  · simp only [ascendingClosure]
    constructor <;> linarith [t.property.1,t.property.2]

theorem splitSpatialTrace_disjoint_of_height (D E : PLLinkDiagram)
    (e : Fin D.nArc) (f : Fin E.nArc) (H K : ℝ) (hHK : H+1 < K) :
    Disjoint (splitSpatialTrace D e H) (splitSpatialTrace E f K) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hh := splitSpatialTrace_height_bounds D e H x hx
  have hk := splitSpatialTrace_height_bounds E f K x hy
  linarith

end DirectGLSSW.DescendingSpatial




