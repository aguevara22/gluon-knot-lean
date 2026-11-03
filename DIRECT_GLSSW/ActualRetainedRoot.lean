import CanonicalRecursiveChild

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PositionalIndex
open DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW.HOMFLY.SmoothingCornerGeometry

theorem marked_trace_nArc_pos {s t : MarkedParentState}
    (h : MarkedParentTrace s t) (hs : 0 < s.1.nArc) : 0 < t.1.nArc := by
  induction h with
  | nil => exact hs
  | @cons s t u step tail ih =>
    apply ih
    cases step with
    | switched S c hc hgood => exact hs
    | smoothed S c hc hgood R => exact R.nonempty

theorem source_parent_nArc_pos {n : ℕ} (x : Fin (n+2) → PlanarPoint ℝ)
    (hx : CyclicGeneric x) {s : MarkedParentState}
    (htrace : MarkedParentTrace
      (positivePolygonMarkedState x hx (initialAnchorTraversal x hx)) s) :
    0 < s.1.nArc := by
  apply marked_trace_nArc_pos htrace
  exact (eventFin x (initialAnchor x hx)).isLt |> Nat.zero_lt_of_lt

/-- The stored traversal base arc of the actual parent's single component. -/
noncomputable def sourceRetainedBaseArc {n : ℕ} (x : Fin (n+2) → PlanarPoint ℝ)
    (hx : CyclicGeneric x) {s : MarkedParentState}
    (htrace : MarkedParentTrace
      (positivePolygonMarkedState x hx (initialAnchorTraversal x hx)) s) : Fin s.1.nArc :=
  (s.2.1.baseArc (PermutationOrbits.componentOf s.1.continuation
    ⟨0,source_parent_nArc_pos x hx htrace⟩)).val

end DirectGLSSW.HOMFLY.PositionalIndex



