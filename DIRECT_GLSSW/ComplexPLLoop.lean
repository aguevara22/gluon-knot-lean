import HOMFLYComponentPLPath
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false

noncomputable section
namespace DirectGLSSW.HOMFLY

/-- Complex coordinates of the literal closed polygonal component path. -/
noncomputable def complexPLLoop (D : PLLinkDiagram) (e : Fin D.nArc) :
    C(unitInterval, ℂ) :=
  ⟨fun u => Complex.equivRealProd.symm (componentPLLoop D e u),
    Complex.equivRealProdCLM.symm.continuous.comp (componentPLLoop D e).continuous⟩

@[simp] theorem complexPLLoop_equivRealProd (D : PLLinkDiagram)
    (e : Fin D.nArc) (u : unitInterval) :
    Complex.equivRealProd (complexPLLoop D e u) = componentPLLoop D e u := by
  simp [complexPLLoop]

theorem complexPLLoop_start (D : PLLinkDiagram) (e : Fin D.nArc) :
    complexPLLoop D e 0 =
      Complex.equivRealProd.symm (D.vertexPoint (D.arcSource e)) := by
  simpa [complexPLLoop] using
    congrArg Complex.equivRealProd.symm (componentPLLoop D e).source

theorem complexPLLoop_end (D : PLLinkDiagram) (e : Fin D.nArc) :
    complexPLLoop D e 1 =
      Complex.equivRealProd.symm (D.vertexPoint (D.arcSource e)) := by
  simpa [complexPLLoop] using
    congrArg Complex.equivRealProd.symm (componentPLLoop D e).target

theorem complexPLLoop_endpoint_eq (D : PLLinkDiagram) (e : Fin D.nArc) :
    complexPLLoop D e 0 = complexPLLoop D e 1 :=
  (complexPLLoop_start D e).trans (complexPLLoop_end D e).symm

private theorem complexAffine_real_part (a : ℂ) (p q : PlanarPoint ℝ)
    (t : ℝ) :
    (a * Complex.equivRealProd.symm (affinePoint p q t)).re =
      (1 - t) * (a * Complex.equivRealProd.symm p).re +
        t * (a * Complex.equivRealProd.symm q).re := by
  simp [affinePoint, Complex.equivRealProd_symm_apply, Complex.mul_re,
    Complex.add_re, Complex.real_smul] <;> ring

/-- A complex affine functional that is bounded below at every diagram
vertex has the same lower bound along the literal component PL loop. -/
theorem complexPLLoop_affine_halfplane (D : PLLinkDiagram)
    (e : Fin D.nArc) (a : ℂ) (b : ℝ)
    (hvertices : ∀ v : Fin D.nVertex,
      b ≤ (a * Complex.equivRealProd.symm (D.vertexPoint v)).re) :
    ∀ u : unitInterval, b ≤ (a * complexPLLoop D e u).re := by
  intro u
  have hmem : componentPLLoop D e u ∈ Set.range (componentPLLoop D e) :=
    ⟨u,rfl⟩
  obtain ⟨f,_hf,htrace⟩ := (componentPLLoop_trace D e (componentPLLoop D e u)).mp hmem
  obtain ⟨t,ht⟩ := htrace
  change b ≤
    (a * Complex.equivRealProd.symm (componentPLLoop D e u)).re
  rw [← ht, diagramArcPath_apply]
  have hsource := hvertices (D.arcSource f)
  have htarget := hvertices (D.arcTarget f)
  have hconvex :
      b ≤
        (1 - t.val) *
            (a * Complex.equivRealProd.symm (D.vertexPoint (D.arcSource f))).re +
          t.val *
            (a * Complex.equivRealProd.symm (D.vertexPoint (D.arcTarget f))).re := by
    have hsource' := mul_le_mul_of_nonneg_left hsource
      (sub_nonneg.mpr t.property.2)
    have htarget' := mul_le_mul_of_nonneg_left htarget t.property.1
    calc
      b = (1 - t.val) * b + t.val * b := by ring
      _ ≤ _ := add_le_add hsource' htarget'
  rw [complexAffine_real_part]
  exact hconvex

/-- A positive planar distance lower bound transfers to complex distance
through the nonexpanding coordinate map. -/
theorem complexPLLoop_complex_distance_lower_bound
    (D : PLLinkDiagram) (e : Fin D.nArc) (u : unitInterval)
    (z : PlanarPoint ℝ) (ρ : ℝ)
    (h : ρ ≤ dist (componentPLLoop D e u) z) :
    ρ ≤ dist (complexPLLoop D e u) (Complex.equivRealProd.symm z) := by
  have hmap := Complex.lipschitz_equivRealProd.dist_le_mul
    (complexPLLoop D e u) (Complex.equivRealProd.symm z)
  have hdist :
      dist (componentPLLoop D e u) z ≤
        dist (complexPLLoop D e u) (Complex.equivRealProd.symm z) := by
    simpa only [NNReal.coe_one, one_mul, complexPLLoop_equivRealProd,
      Equiv.apply_symm_apply] using hmap
  exact le_trans h hdist

end DirectGLSSW.HOMFLY
end








