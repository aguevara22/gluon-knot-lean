import HOMFLYSubdividedVisitOrder
import HOMFLYOrbitEmbedding
import HOMFLYCutUnaffectedOrder
import SmoothingComponentCount

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits
noncomputable section

/-- Exact successor equations used to transport traversal through the two
geometric connector arcs. -/
theorem smoothCode_new_step (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    smoothContinuationGeometryCode D c (Sum.inr i) =
      Sum.inl (cutContinuation D c (D.incoming c i)) := by
  rw [smoothContinuationGeometryCode_connector, cutContinuation_incoming]

theorem smoothCode_cut_step (D : PLLinkDiagram) (c : Fin D.nCrossing) (i : Fin 2) :
    smoothContinuationGeometryCode D c (Sum.inl (D.incoming c i)) = Sum.inr i := by
  fin_cases i
  · exact smoothContinuationGeometryCode_incoming_zero D c
  · exact smoothContinuationGeometryCode_incoming_one D c

theorem smoothCode_old_step (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (x : Fin D.nArc) (hx : ∀ i, x ≠ D.incoming c i) :
    smoothContinuationGeometryCode D c (Sum.inl x) =
      Sum.inl (cutContinuation D c x) := by
  rw [smoothContinuationGeometryCode_other_arc D c x hx]
  simp [cutContinuation, Equiv.swap_apply_of_ne_of_ne (hx 0) (hx 1)]

def smoothCutCodeComponentEquiv (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Component (cutContinuation D c) ≃ Component (smoothContinuationGeometryCode D c) :=
  SmoothingSubdividedCycles.componentEquiv (cutContinuation D c)
    (smoothContinuationGeometryCode D c) (D.incoming c)
    (smoothCode_new_step D c) (smoothCode_cut_step D c) (smoothCode_old_step D c)

theorem smoothCode_actual_step (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (x : SmoothArcCode D) :
    smoothArcEquiv D (smoothContinuationGeometryCode D c x) =
      (smoothCrossing D c).continuation (smoothArcEquiv D x) := by
  change smoothArcEquiv D (smoothContinuationGeometryCode D c x) =
    smoothContinuation D c (smoothArcEquiv D x)
  simp [smoothContinuation]

def smoothCutComponentEquiv (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    Component (cutContinuation D c) ≃ diagramComponent (smoothCrossing D c) :=
  (smoothCutCodeComponentEquiv D c).trans
    (componentEquivOfIntertwining (smoothArcEquiv D)
      (smoothContinuationGeometryCode D c) (smoothCrossing D c).continuation
      (smoothCode_actual_step D c))

@[simp] theorem smoothCutComponentEquiv_old (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (x : Fin D.nArc) :
    smoothCutComponentEquiv D c (componentOf (cutContinuation D c) x) =
      componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl x)) := rfl

theorem smoothCutComponentEquiv_connector (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (i : Fin 2) :
    smoothCutComponentEquiv D c (componentOf (cutContinuation D c) (D.incoming c i)) =
      componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inr i)) := by
  change componentEquivOfIntertwining (smoothArcEquiv D)
    (smoothContinuationGeometryCode D c) (smoothCrossing D c).continuation
    (smoothCode_actual_step D c)
      (smoothCutCodeComponentEquiv D c (componentOf (cutContinuation D c) (D.incoming c i))) = _
  rw [show smoothCutCodeComponentEquiv D c
      (componentOf (cutContinuation D c) (D.incoming c i)) =
      componentOf (smoothContinuationGeometryCode D c) (Sum.inr i) from
    SmoothingSubdividedCycles.componentEquiv_new _ _ _ _ _ _ i]
  rfl

theorem selfCut_ports_separated (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (i j : Fin 2) (hji : j ≠ i) :
    ¬ (cutContinuation D c).SameCycle (D.incoming c i) (D.incoming c j) := by
  have h := not_sameCycle_mul_swap_of_sameCycle D.continuation
    (D.four_ports_distinct c).1 hself
  fin_cases i <;> fin_cases j
  · exact False.elim (hji rfl)
  · exact h
  · exact fun h' => h h'.symm
  · exact False.elim (hji rfl)

/-- The actual geometric smoothing, based at a connector, has exactly the
same retained old-port positions as its pre-connector cut permutation. -/
theorem smoothConnector_actual_orbitPosition (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (i : Fin 2)
    (x : Fibre (cutContinuation D c) (componentOf (cutContinuation D c) (D.incoming c i)))
    (hx : x.val ≠ D.incoming c i) :
    let y : Fibre (smoothContinuationGeometryCode D c)
        (componentOf (smoothContinuationGeometryCode D c) (Sum.inr i)) :=
      ⟨Sum.inl x.val, by
        rw [← SmoothingSubdividedCycles.componentEquiv_old (cutContinuation D c)
          (smoothContinuationGeometryCode D c) (D.incoming c)
          (smoothCode_new_step D c) (smoothCode_cut_step D c) (smoothCode_old_step D c),
          x.property, SmoothingSubdividedCycles.componentEquiv_new]⟩
    ((orbitEnumeration (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inr i))).symm
      (orbitFibreEquivOfEmbedding (smoothContinuationGeometryCode D c)
        (smoothCrossing D c).continuation (smoothArcEquiv D) (smoothArcEquiv D).injective
        (smoothCode_actual_step D c) (Sum.inr i) y)).val =
      ((orbitEnumeration (cutContinuation D c) (D.incoming c i)).symm x).val := by
  dsimp only
  refine (orbitPosition_embedding (smoothContinuationGeometryCode D c)
    (smoothCrossing D c).continuation (smoothArcEquiv D) (smoothArcEquiv D).injective
    (smoothCode_actual_step D c) (Sum.inr i) _).trans ?_
  exact SmoothingSubdividedCycles.selected_orbitPosition
    (cutContinuation D c) (smoothContinuationGeometryCode D c) (D.incoming c)
    (smoothCode_new_step D c) (smoothCode_cut_step D c) (smoothCode_old_step D c)
    i (selfCut_ports_separated D c hself i) x hx

/-- The actual smoothing leaves every orbit position on an unaffected old
component unchanged, using that component's original chosen base arc. -/
theorem smoothUnaffected_actual_orbitPosition (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (root : Fin D.nArc)
    (ha : ¬ D.continuation.SameCycle root (D.incoming c 0))
    (x : Fibre D.continuation (componentOf D.continuation root)) :
    let hb : ¬ D.continuation.SameCycle root (D.incoming c 1) :=
      fun h => ha (h.trans hself.symm)
    let xcut := cutUnaffectedFibreEquiv D.continuation
      (D.incoming c 0) (D.incoming c 1) root ha hb x
    let y : Fibre (smoothContinuationGeometryCode D c)
        (componentOf (smoothContinuationGeometryCode D c) (Sum.inl root)) :=
      ⟨Sum.inl xcut.val, by
        rw [← SmoothingSubdividedCycles.componentEquiv_old (cutContinuation D c)
          (smoothContinuationGeometryCode D c) (D.incoming c)
          (smoothCode_new_step D c) (smoothCode_cut_step D c) (smoothCode_old_step D c),
          (show componentOf (cutContinuation D c) xcut.val =
            componentOf (cutContinuation D c) root from xcut.property),
          SmoothingSubdividedCycles.componentEquiv_old]⟩
    ((orbitEnumeration (smoothCrossing D c).continuation
        (smoothArcEquiv D (Sum.inl root))).symm
      (orbitFibreEquivOfEmbedding (smoothContinuationGeometryCode D c)
        (smoothCrossing D c).continuation (smoothArcEquiv D) (smoothArcEquiv D).injective
        (smoothCode_actual_step D c) (Sum.inl root) y)).val =
      ((orbitEnumeration D.continuation root).symm x).val := by
  dsimp only
  refine (orbitPosition_embedding (smoothContinuationGeometryCode D c)
    (smoothCrossing D c).continuation (smoothArcEquiv D) (smoothArcEquiv D).injective
    (smoothCode_actual_step D c) (Sum.inl root) _).trans ?_
  have hroot : ∀ j, ¬ (cutContinuation D c).SameCycle root (D.incoming c j) := by
    intro j h
    have hp := sameCycle_mul_swap_refines D.continuation hself h
    fin_cases j
    · exact ha hp
    · exact ha (hp.trans hself.symm)
  refine (SmoothingSubdividedCycles.unselected_orbitPosition
    (cutContinuation D c) (smoothContinuationGeometryCode D c) (D.incoming c)
    (smoothCode_new_step D c) (smoothCode_cut_step D c) (smoothCode_old_step D c)
    root hroot _).trans ?_
  exact cutUnaffected_orbitPosition D.continuation (D.incoming c 0) (D.incoming c 1)
    root ha (fun h => ha (h.trans hself.symm)) x

end
end DirectGLSSW.HOMFLY













