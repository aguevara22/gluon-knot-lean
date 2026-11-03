import DirectGLSSW.HOMFLY.PLDiagrams
import DirectGLSSW.HOMFLY.BasedTraversal

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

/-- Switching distinct crossings commutes on the concrete diagram object. -/
theorem switchCrossing_commute_of_ne (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : c ≠ d) :
    switchCrossing (switchCrossing D c) d =
      switchCrossing (switchCrossing D d) c := by
  cases D with
  | mk nVertex nArc nCrossing vertexPoint arcSource arcTarget crossingVertex
      crossingVertex_injective incoming outgoing incoming_target outgoing_source
      four_ports_distinct crossing_incidence_complete regular_degree_one through
      continuation continuation_incidence continuation_crossing overBranch
      vertexPoint_injective arc_endpoints_distinct arc_interiors_disjoint
      vertices_avoid_arc_interiors through_tangents_positive_collinear crossing_transverse =>
    simp only [switchCrossing]
    congr 1
    funext x
    by_cases hxc : x = c
    · subst x
      have hxd : c ≠ d := hcd
      simp [Function.update, hxd]
    · by_cases hxd : x = d
      · subst x
        simp [Function.update, hcd.symm]
      · simp [Function.update, hxc, hxd]

/-- A switch leaves the geometric determinant at any other labelled crossing
unchanged, since it changes only the over-branch label at the selected site. -/
theorem crossingDet_switchCrossing_of_ne (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : d ≠ c) :
    crossingDet (switchCrossing D c) d = crossingDet D d := by
  simp [crossingDet, strandTangent, switchCrossing, Function.update_of_ne hcd]

/-- Consequently, the crossing sign at a distinct site is unchanged. -/
theorem crossingSign_switchCrossing_of_ne (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hcd : d ≠ c) :
    crossingSign (switchCrossing D c) d = crossingSign D d := by
  simp only [crossingSign, crossingDet_switchCrossing_of_ne D c d hcd]

/-- Badness at a distinct labelled crossing is unchanged by switching. -/
theorem badAt_switchTraversal_of_ne {D : PLLinkDiagram}
    (T : BasedTraversal D) (c d : Fin D.nCrossing) (hcd : d ≠ c) :
    badAt (switchTraversal T c) d ↔ badAt T d :=
  badAt_switch_same T c d hcd

/-- When two distinct crossings are bad, switching either one leaves the
other bad, and the two bad sets each lose exactly the selected labels. -/
theorem two_bad_crossings_survive_switch {D : PLLinkDiagram}
    (T : BasedTraversal D) (c d : Fin D.nCrossing)
    (hc : c ∈ badCrossings T) (hd : d ∈ badCrossings T)
    (hcd : c ≠ d) :
    d ∈ badCrossings (switchTraversal T c) ∧
    c ∈ badCrossings (switchTraversal T d) ∧
    badCrossings (switchTraversal T c) = (badCrossings T).erase c ∧
    badCrossings (switchTraversal T d) = (badCrossings T).erase d := by
  constructor
  · rw [badCrossings_switch_erase T c hc]
    exact Finset.mem_erase.mpr ⟨hcd.symm, hd⟩
  constructor
  · rw [badCrossings_switch_erase T d hd]
    exact Finset.mem_erase.mpr ⟨hcd, hc⟩
  constructor
  · exact badCrossings_switch_erase T c hc
  · exact badCrossings_switch_erase T d hd







end DirectGLSSW.HOMFLY
