import SplitCircleClearance

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.SplitCircleConstructor
open DirectGLSSW

def shiftRight (R : ℝ) (p : PlanarPoint ℝ) : PlanarPoint ℝ :=
  (R + 1 + p.1, p.2)

theorem shiftRight_injective (R : ℝ) : Function.Injective (shiftRight R) := by
  intro a b h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;> simp only [shiftRight] at hx hy ⊢ <;> linarith

theorem shiftRight_affine (R : ℝ) (a b : PlanarPoint ℝ) (t : ℝ) :
    shiftRight R (affinePoint a b t) =
      affinePoint (shiftRight R a) (shiftRight R b) t := by
  apply Prod.ext <;> simp [shiftRight, affinePoint] <;> ring

/-- A geometrically translated, genuine crossing-free triangle diagram. -/
def rightTriangle (R : ℝ) : PLLinkDiagram := by
  let T := triangleUnknot
  refine { T with
    vertexPoint := shiftRight R ∘ T.vertexPoint
    vertexPoint_injective := ?_
    arc_interiors_disjoint := ?_
    vertices_avoid_arc_interiors := ?_
    through_tangents_positive_collinear := ?_
    crossing_transverse := ?_ }
  · intro a b h
    exact T.vertexPoint_injective ((shiftRight_injective R) h)
  · intro e f hef s t hs0 hs1 ht0 ht1 h
    have h' : affinePoint (T.vertexPoint (T.arcSource e))
        (T.vertexPoint (T.arcTarget e)) s =
        affinePoint (T.vertexPoint (T.arcSource f))
          (T.vertexPoint (T.arcTarget f)) t := by
      apply shiftRight_injective R
      simpa only [shiftRight_affine, Function.comp_apply] using h
    exact T.arc_interiors_disjoint e f hef s t hs0 hs1 ht0 ht1 h'
  · intro v e t ht0 ht1 h
    have h' : T.vertexPoint v =
        affinePoint (T.vertexPoint (T.arcSource e))
          (T.vertexPoint (T.arcTarget e)) t := by
      apply shiftRight_injective R
      simpa only [shiftRight_affine, Function.comp_apply] using h
    exact T.vertices_avoid_arc_interiors v e t ht0 ht1 h'
  · intro c
    exact Fin.elim0 c
  · intro c
    exact Fin.elim0 c

theorem rightTriangle_crossing_count (R : ℝ) : (rightTriangle R).nCrossing = 0 := rfl

end DirectGLSSW.HOMFLY.SplitCircleConstructor

