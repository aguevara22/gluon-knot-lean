import SplitTraversalTime
import UniformPLComponent
import ContinuousRoundedTangent

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY HOMFLY.PrincipalTurning

theorem uniformPLCurve_continuous (D : PLLinkDiagram) (e : Fin D.nArc) :
    Continuous (uniformPLCurve D e) := by
  apply continuous_integer_cells
    (fun k t => affinePoint (D.vertexPoint (D.arcSource ((D.continuation ^ k) e)))
      (D.vertexPoint (D.arcTarget ((D.continuation ^ k) e))) t)
  · intro k
    unfold affinePoint
    fun_prop
  · intro k
    rw [affinePoint_one, affinePoint_zero]
    rw [D.continuation_incidence ((D.continuation ^ (k-1)) e),
      continuation_previous_integer]

def splitBaseA (D : PLLinkDiagram) (e : Fin D.nArc) : PlanarPoint ℝ :=
  affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) (3/4)

def splitBaseB (D : PLLinkDiagram) (e : Fin D.nArc) : PlanarPoint ℝ :=
  affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) (1/4)

theorem splitBaseA_eq_literal (D : PLLinkDiagram) (e : Fin D.nArc) :
    splitBaseA D e = affinePoint (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcTarget e)) (3/4) := rfl

theorem splitBaseB_eq_literal (D : PLLinkDiagram) (e : Fin D.nArc) :
    splitBaseB D e = affinePoint (D.vertexPoint (D.arcSource e))
      (D.vertexPoint (D.arcTarget e)) (1/4) := rfl

/-- The actual continuation trace, beginning and ending inside the base arc. -/
def splitMainPlanar (D : PLLinkDiagram) (e : Fin D.nArc) :
    C(unitInterval, PlanarPoint ℝ) where
  toFun t := uniformPLCurve D e (splitTraversalTime (componentArcLength D e) t.val)
  continuous_toFun := (uniformPLCurve_continuous D e).comp
    ((splitTraversalTime_continuous _).comp continuous_subtype_val)

theorem splitMainPlanar_apply (D : PLLinkDiagram) (e : Fin D.nArc)
    (t : unitInterval) : splitMainPlanar D e t =
      uniformPLCurve D e (splitTraversalTime (componentArcLength D e) t.val) := rfl

theorem splitMainPlanar_endpoints (D : PLLinkDiagram) (e : Fin D.nArc) :
    splitMainPlanar D e 0 = splitBaseA D e ∧
      splitMainPlanar D e 1 = splitBaseB D e := by
  have ht := splitTraversalTime_endpoints (componentArcLength D e)
    (componentArcLength_pos D e)
  constructor
  · change uniformPLCurve D e (splitTraversalTime (componentArcLength D e) 0) = _
    rw [ht.1]
    simpa [splitBaseA] using uniformPLCurve_arc_cell D e 0 (3/4) (by norm_num)
  · change uniformPLCurve D e (splitTraversalTime (componentArcLength D e) 1) = _
    rw [ht.2, add_comm]
    rw [uniformPLCurve_periodic D e (1/4)]
    simpa [splitBaseB] using uniformPLCurve_arc_cell D e 0 (1/4) (by norm_num)

end DirectGLSSW.DescendingSpatial





