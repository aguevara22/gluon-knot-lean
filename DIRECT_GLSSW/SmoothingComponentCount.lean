import SmoothingSubdividedCycles
import DirectGLSSW.HOMFLY.HOMFYSmoothingDiagram

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open PermutationOrbits
noncomputable section

/-- The parent continuation after the oriented branch exchange, before
inserting the two connector arcs. -/
def cutContinuation (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Equiv.Perm (Fin D.nArc) :=
  D.continuation * Equiv.swap (D.incoming c 0) (D.incoming c 1)

theorem cutContinuation_incoming (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) :
    cutContinuation D c (D.incoming c i) =
      D.outgoing c (D.through c (otherBranch i)) := by
  fin_cases i <;> simp [cutContinuation, D.continuation_crossing,
    otherBranch_zero, otherBranch_one]

theorem smoothContinuationGeometryCode_other_arc (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (e : Fin D.nArc)
    (he : ∀ i, e ≠ D.incoming c i) :
    smoothContinuationGeometryCode D c (Sum.inl e) = Sum.inl (D.continuation e) := by
  have hout (j : Fin 2) : D.continuation e ≠ D.outgoing c j := by
    intro hj
    apply he ((D.through c).symm j)
    apply D.continuation.injective
    rw [D.continuation_crossing, Equiv.apply_symm_apply]
    exact hj
  by_cases h0 : D.through c 0 = 0 <;>
    simp [smoothContinuationGeometryCode, smoothContinuationGeometryAdjust,
      smoothContinuationCodeLocal, smoothContinuationAdjustLocal, h0,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def, hout 0, hout 1]

theorem smooth_code_componentCount (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    componentCount (smoothContinuationGeometryCode D c) =
      componentCount (cutContinuation D c) := by
  apply SmoothingSubdividedCycles.componentCount_eq (cutContinuation D c)
    (smoothContinuationGeometryCode D c) (D.incoming c)
  · intro i
    rw [smoothContinuationGeometryCode_connector, cutContinuation_incoming]
  · intro i
    fin_cases i
    · exact smoothContinuationGeometryCode_incoming_zero D c
    · exact smoothContinuationGeometryCode_incoming_one D c
  · intro e he
    rw [smoothContinuationGeometryCode_other_arc D c e he]
    simp [cutContinuation, Equiv.swap_apply_of_ne_of_ne (he 0) (he 1)]

/-- The actual geometric smoothing has the component count of the parent
branch exchange. Connector insertion does not change the count. -/
theorem smooth_componentCount_eq_cut (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    diagramComponentCount (smoothCrossing D c) =
      componentCount (cutContinuation D c) := by
  have h := componentCount_eq_of_intertwining (smoothArcEquiv D)
    (smoothContinuationGeometryCode D c) (smoothCrossing D c).continuation
    (by
      intro x
      change smoothArcEquiv D (smoothContinuationGeometryCode D c x) =
        smoothContinuation D c (smoothArcEquiv D x)
      simp [smoothContinuation])
  exact h.symm.trans (smooth_code_componentCount D c)

/-- Oriented smoothing at a self-crossing splits one component into two. -/
theorem smooth_componentCount_self (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (h : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) :
    diagramComponentCount (smoothCrossing D c) = diagramComponentCount D + 1 := by
  rw [smooth_componentCount_eq_cut]
  exact componentCount_mul_swap_of_sameCycle D.continuation (D.four_ports_distinct c).1 h

/-- Oriented smoothing between distinct components joins them. -/
theorem smooth_componentCount_mixed (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (h : ¬D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) :
    diagramComponentCount (smoothCrossing D c) + 1 = diagramComponentCount D := by
  rw [smooth_componentCount_eq_cut]
  exact componentCount_mul_swap_of_not_sameCycle D.continuation h

theorem smooth_componentCount_le (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    diagramComponentCount (smoothCrossing D c) ≤ diagramComponentCount D + 1 := by
  classical
  by_cases h : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)
  · exact (smooth_componentCount_self D c h).le
  · have hj := smooth_componentCount_mixed D c h
    omega









end
end DirectGLSSW.HOMFLY
