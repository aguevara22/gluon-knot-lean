import FreeCursorGammaM
import ActiveArcTerminalGammaM
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CornerProjector
open Cursor Split Primitive RetainedWords EndpointEventGeometry

theorem firstEdgeFree_GammaM_constancy {b : ℕ}
    (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (hfree : ∀ c : Crossing q, c.val.1≠0) (hRI : GLSSWRootIndependence)
    (hAux : ClosedAuxiliary q hR) (t : ℝ) (ht0 : 0≤t) (ht1 : t<1)
    (hcore : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (openCount q hR U.val-1))
    (hcoret : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (moveEndpoint (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (q 1-q 0) t)
      (openCount q hR U.val-1)) :
    GammaM (moveStart q t) (firstEdgeFree_regular_moveStart q hR hfree t ht0 ht1)
      (firstEdgeFree_closedAuxiliary_moveStart q hR hfree hAux t ht0 ht1) = GammaM q hR hAux := by
  by_cases ht : t=0
  · subst t
    have he : moveStart q 0=q := by
      funext i
      by_cases hi : i=0
      · subst i;rw [moveStart_zero,affinePoint_zero]
      · exact moveStart_eq q 0 i hi
    simp only [he]
  · exact firstEdgeFree_GammaM_constancy_pos q hR hfree hRI hAux t (lt_of_le_of_ne ht0 (Ne.symm ht)) ht1 hcore hcoret

theorem firstEdgeFree_normalized_GammaM_constancy {b : ℕ}
    (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (hfree : ∀ c : Crossing q, c.val.1≠0) (hRI : GLSSWRootIndependence)
    (hAux : ClosedAuxiliary q hR) (t : ℝ) (ht0 : 0≤t) (ht1 : t<1)
    (hcore : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (openCount q hR U.val-1))
    (hcoret : ∀ U : Support q hR, ShortEdgeSignStability.CoreHGeneric
      (moveEndpoint (rootedPolygonWord (OpenVertex q hR U) (openLast q hR U.val)) (q 1-q 0) t)
      (openCount q hR U.val-1)) :
    (-1 : ℚ)^(List.ofFn (moveStart q t)).length *
      GammaM (moveStart q t) (firstEdgeFree_regular_moveStart q hR hfree t ht0 ht1)
        (firstEdgeFree_closedAuxiliary_moveStart q hR hfree hAux t ht0 ht1) =
    (-1 : ℚ)^(List.ofFn q).length * GammaM q hR hAux := by
  rw [firstEdgeFree_GammaM_constancy q hR hfree hRI hAux t ht0 ht1 hcore hcoret]
  simp only [List.length_ofFn]

/-- The one-edge terminal branch requires neither a crossing nor an auxiliary
Core input; its actual ΓM is one throughout every regular cursor motion. -/
theorem singleEdge_normalized_cursor_constancy (q : Fin 2 → PlanarPoint ℝ)
    (hR : Regular q) (hAux : ClosedAuxiliary q hR) (t : ℝ) (ht0 : 0≤t) (ht1 : t<1) :
    let hfree : ∀ c : Crossing q, c.val.1≠0 := fun c => by have := c.property.1; have := c.val.2.isLt;omega
    (-1 : ℚ)^(List.ofFn (moveStart q t)).length *
      GammaM (moveStart q t) (firstEdgeFree_regular_moveStart q hR hfree t ht0 ht1)
        (singleEdge_closedAuxiliary _ _) =
    (-1 : ℚ)^(List.ofFn q).length * GammaM q hR hAux := by
  dsimp only
  rw [singleEdge_GammaM_one,singleEdge_GammaM_one]
  simp only [List.length_ofFn]
end DirectGLSSW.ActiveArc.CornerProjector
