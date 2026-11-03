import UniformPLVisits

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits

theorem basedUniformPLCurve_secant01 {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hC : componentOf D.continuation (D.incoming c 0) = componentOf D.continuation (D.incoming c 1))
    (s t : ℝ) (hs : s ∈ Set.Icc (-1/2 : ℝ) (1/2)) (ht : t ∈ Set.Icc (-1/2 : ℝ) (1/2)) :
    Complex.equivRealProd (crossingStarSecant D c s t) =
      basedUniformPLCurve T (componentOf D.continuation (D.incoming c 0)) (crossingVisitTime T c 1+t) -
        basedUniformPLCurve T (componentOf D.continuation (D.incoming c 0)) (crossingVisitTime T c 0+s) := by
  have h0 := basedUniformPLCurve_crossing_star T c 0 s hs
  have h1 := basedUniformPLCurve_crossing_star T c 1 t ht
  rw [← hC] at h1
  rw [h0,h1,crossingStarPoint_eq_offset,crossingStarPoint_eq_offset]
  apply Prod.ext <;> simp [crossingStarSecant,Complex.equivRealProd_apply] <;> ring

theorem basedUniformPLCurve_secant10 {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hC : componentOf D.continuation (D.incoming c 0) = componentOf D.continuation (D.incoming c 1))
    (s t : ℝ) (hs : s ∈ Set.Icc (-1/2 : ℝ) (1/2)) (ht : t ∈ Set.Icc (-1/2 : ℝ) (1/2)) :
    Complex.equivRealProd (-crossingStarSecant D c t s) =
      basedUniformPLCurve T (componentOf D.continuation (D.incoming c 0)) (crossingVisitTime T c 0+t) -
        basedUniformPLCurve T (componentOf D.continuation (D.incoming c 0)) (crossingVisitTime T c 1+s) := by
  have h0 := basedUniformPLCurve_crossing_star T c 0 t ht
  have h1 := basedUniformPLCurve_crossing_star T c 1 s hs
  rw [← hC] at h1
  rw [h0,h1,crossingStarPoint_eq_offset,crossingStarPoint_eq_offset]
  apply Prod.ext <;> simp [crossingStarSecant,Complex.equivRealProd_apply] <;> ring

theorem basedUniformPLCurve_crossing_zero_iff {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hC : componentOf D.continuation (D.incoming c 0) = componentOf D.continuation (D.incoming c 1))
    (s t : ℝ) (hs : s ∈ Set.Icc (-1/2 : ℝ) (1/2)) (ht : t ∈ Set.Icc (-1/2 : ℝ) (1/2)) :
    basedUniformPLCurve T (componentOf D.continuation (D.incoming c 0)) (crossingVisitTime T c 1+t) =
      basedUniformPLCurve T (componentOf D.continuation (D.incoming c 0)) (crossingVisitTime T c 0+s) ↔
      s=0 ∧ t=0 := by
  rw [← sub_eq_zero, ← basedUniformPLCurve_secant01 T c hC s t hs ht]
  have hz : Complex.equivRealProd (crossingStarSecant D c s t) = (0 : PlanarPoint ℝ) ↔
      crossingStarSecant D c s t = 0 := by
    constructor
    · intro h
      exact Complex.equivRealProd.injective h
    · intro h
      rw [h]
      rfl
  rw [hz,crossingStarSecant_eq_zero_iff]

end DirectGLSSW.HOMFLY.PrincipalTurning



