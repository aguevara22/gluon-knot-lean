import HOMFLYComponentPLPath
import PrincipalTurning
import DirectGLSSW.HOMFLY.BasedTraversal

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits

/-- Literal unrounded affine cells on exactly the continuation/floor/fract
orbit used by roundedComponentCurve. No alternate orbit or diagram data. -/
noncomputable def uniformPLCurve (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : ℝ) : PlanarPoint ℝ :=
  let a := (D.continuation ^ Int.floor t) e
  affinePoint (D.vertexPoint (D.arcSource a)) (D.vertexPoint (D.arcTarget a)) (Int.fract t)

theorem uniformPLCurve_periodic (D : PLLinkDiagram) (e : Fin D.nArc) :
    Function.Periodic (uniformPLCurve D e) (componentArcLength D e : ℝ) := by
  intro t
  unfold uniformPLCurve
  rw [Int.floor_add_natCast, Int.fract_add_natCast, zpow_add, Equiv.Perm.mul_apply,
    zpow_natCast, continuation_pow_componentArcLength]

theorem uniformPLCurve_arc_cell (D : PLLinkDiagram) (e : Fin D.nArc)
    (k : ℤ) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    uniformPLCurve D e ((k : ℝ) + u) =
      affinePoint (D.vertexPoint (D.arcSource ((D.continuation ^ k) e)))
        (D.vertexPoint (D.arcTarget ((D.continuation ^ k) e))) u := by
  by_cases hu1 : u < 1
  · have hf : Int.floor u = 0 := Int.floor_eq_zero_iff.mpr ⟨hu.1,hu1⟩
    have hfr : Int.fract u = u := Int.fract_eq_self.mpr ⟨hu.1,hu1⟩
    simp [uniformPLCurve, Int.floor_intCast_add, Int.fract_intCast_add, hf,hfr]
  · have heq : u = 1 := le_antisymm hu.2 (le_of_not_gt hu1)
    subst u
    have htime : (k : ℝ) + 1 = ((k+1 : ℤ) : ℝ) := by push_cast; ring
    have hp : (D.continuation ^ (k+1)) e = D.continuation ((D.continuation ^ k) e) := by
      rw [add_comm k 1,zpow_add,Equiv.Perm.mul_apply,zpow_one]
    rw [htime, affinePoint_one]
    simp only [uniformPLCurve,Int.floor_intCast,Int.fract_intCast,affinePoint_zero]
    rw [hp]
    exact congrArg D.vertexPoint (D.continuation_incidence _).symm

/-- Basepoint is the literal midpoint of the chosen root arc; no vertex is
inserted and no new G1 proof is asserted. -/
noncomputable def basedUniformPLCurve {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (t : ℝ) : PlanarPoint ℝ :=
  uniformPLCurve D (T.baseArc C).val (t + 1/2)

theorem basedUniformPLCurve_periodic {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    Function.Periodic (basedUniformPLCurve T C)
      (componentArcLength D (T.baseArc C).val : ℝ) := by
  intro t
  simpa only [basedUniformPLCurve, add_right_comm t] using
    uniformPLCurve_periodic D (T.baseArc C).val (t+1/2)

theorem basedUniformPLCurve_midpoint {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) : basedUniformPLCurve T C 0 =
    affinePoint (D.vertexPoint (D.arcSource (T.baseArc C).val))
      (D.vertexPoint (D.arcTarget (T.baseArc C).val)) (1/2) := by
  simpa [basedUniformPLCurve] using
    uniformPLCurve_arc_cell D (T.baseArc C).val 0 (1/2) (by constructor <;> norm_num)

theorem basedUniformPLCurve_midpoint_not_vertex {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (v : Fin D.nVertex) :
    basedUniformPLCurve T C 0 ≠ D.vertexPoint v := by
  rw [basedUniformPLCurve_midpoint]
  exact (D.vertices_avoid_arc_interiors v (T.baseArc C).val (1/2) (by norm_num) (by norm_num)).symm

end DirectGLSSW.HOMFLY.PrincipalTurning








