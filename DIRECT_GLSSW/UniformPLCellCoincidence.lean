import UniformPLComponent

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning

/-- Literal affine-cell coincidence. Fractions lie in [0,1), so distinct
actual arcs can coincide only at their common source vertex. -/
theorem uniformPLCurve_cell_coincidence (D : PLLinkDiagram) (e : Fin D.nArc) (s t : ℝ) :
    uniformPLCurve D e s = uniformPLCurve D e t ↔
      ((D.continuation ^ Int.floor s) e = (D.continuation ^ Int.floor t) e ∧
        Int.fract s = Int.fract t) ∨
      (Int.fract s = 0 ∧ Int.fract t = 0 ∧
        D.arcSource ((D.continuation ^ Int.floor s) e) =
          D.arcSource ((D.continuation ^ Int.floor t) e)) := by
  let a := (D.continuation ^ Int.floor s) e
  let b := (D.continuation ^ Int.floor t) e
  let u := Int.fract s
  let v := Int.fract t
  have hu0 : 0 ≤ u := Int.fract_nonneg s
  have hv0 : 0 ≤ v := Int.fract_nonneg t
  have hu1 : u < 1 := Int.fract_lt_one s
  have hv1 : v < 1 := Int.fract_lt_one t
  change affinePoint (D.vertexPoint (D.arcSource a)) (D.vertexPoint (D.arcTarget a)) u =
      affinePoint (D.vertexPoint (D.arcSource b)) (D.vertexPoint (D.arcTarget b)) v ↔
    (a=b ∧ u=v) ∨ (u=0 ∧ v=0 ∧ D.arcSource a=D.arcSource b)
  constructor
  · intro heq
    by_cases hab : a=b
    · refine Or.inl ⟨hab,?_⟩
      rw [← hab] at heq
      exact affinePoint_injective (D.vertexPoint (D.arcSource a)) (D.vertexPoint (D.arcTarget a))
        (fun h => D.arc_endpoints_distinct a (D.vertexPoint_injective h)) heq
    · by_cases hu : u=0
      · by_cases hv : v=0
        · refine Or.inr ⟨hu,hv,?_⟩
          rw [hu,hv,affinePoint_zero,affinePoint_zero] at heq
          exact D.vertexPoint_injective heq
        · exfalso
          rw [hu,affinePoint_zero] at heq
          exact D.vertices_avoid_arc_interiors (D.arcSource a) b v (lt_of_le_of_ne hv0 (Ne.symm hv)) hv1 heq
      · by_cases hv : v=0
        · exfalso
          rw [hv,affinePoint_zero] at heq
          exact D.vertices_avoid_arc_interiors (D.arcSource b) a u (lt_of_le_of_ne hu0 (Ne.symm hu)) hu1 heq.symm
        · exact False.elim (D.arc_interiors_disjoint a b hab u v
            (lt_of_le_of_ne hu0 (Ne.symm hu)) hu1 (lt_of_le_of_ne hv0 (Ne.symm hv)) hv1 heq)
  · rintro (⟨hab,huv⟩ | ⟨hu,hv,hab⟩)
    · rw [hab,huv]
    · rw [hu,hv,affinePoint_zero,affinePoint_zero,hab]

end DirectGLSSW.HOMFLY.PrincipalTurning

