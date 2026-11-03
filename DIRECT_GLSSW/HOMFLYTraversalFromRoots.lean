import DirectGLSSW.HOMFLY.HOMFYSmoothingTraversalBridge

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

/-- Assemble a based traversal from explicitly labelled components and one
actual root arc on each component. -/
noncomputable def basedTraversalOfComponentRoots {D : PLLinkDiagram} {L : Type}
    (components : L ≃ diagramComponent D)
    (order : L ≃ Fin (diagramComponentCount D))
    (roots : L → Fin D.nArc)
    (hroots : ∀ l, PermutationOrbits.componentOf D.continuation (roots l) = components l) :
    BasedTraversal D where
  componentIndex := components.symm.trans order
  baseArc C := ⟨roots (components.symm C), by rw [hroots, Equiv.apply_symm_apply]⟩

@[simp] theorem basedTraversalOfComponentRoots_index {D : PLLinkDiagram} {L : Type}
    (components : L ≃ diagramComponent D)
    (order : L ≃ Fin (diagramComponentCount D))
    (roots : L → Fin D.nArc)
    (hroots : ∀ l, PermutationOrbits.componentOf D.continuation (roots l) = components l)
    (l : L) :
    (basedTraversalOfComponentRoots components order roots hroots).componentIndex
      (components l) = order l := by
  simp [basedTraversalOfComponentRoots]

@[simp] theorem basedTraversalOfComponentRoots_baseArc {D : PLLinkDiagram} {L : Type}
    (components : L ≃ diagramComponent D)
    (order : L ≃ Fin (diagramComponentCount D))
    (roots : L → Fin D.nArc)
    (hroots : ∀ l, PermutationOrbits.componentOf D.continuation (roots l) = components l)
    (l : L) :
    ((basedTraversalOfComponentRoots components order roots hroots).baseArc
      (components l)).val = roots l := by
  simp [basedTraversalOfComponentRoots]

/-- Rank-order transport at a retained crossing implies first-branch transport
for the actual geometric smoothing's retained crossing label. -/
theorem firstVisitedBranch_smooth_eq_of_rankBefore
    (D : PLLinkDiagram) (T : BasedTraversal D) (c : Fin D.nCrossing)
    (U : BasedTraversal (smoothCrossing D c))
    (d : Fin D.nCrossing) (hd : d ≠ c)
    (horder : rankBefore (visitRank U (smoothArcEquiv D (Sum.inl (D.incoming d 0))))
        (visitRank U (smoothArcEquiv D (Sum.inl (D.incoming d 1)))) ↔
      rankBefore (visitRank T (D.incoming d 0)) (visitRank T (D.incoming d 1))) :
    firstVisitedBranch U (smoothCrossingEquiv D c ⟨d, hd⟩) = firstVisitedBranch T d := by
  classical
  have hi (i : Fin 2) :
      (smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨d, hd⟩) i =
        smoothArcEquiv D (Sum.inl (D.incoming d i)) := by
    change smoothArcEquiv D (Sum.inl (D.incoming
      (((smoothCrossingEquiv D c).symm (smoothCrossingEquiv D c ⟨d, hd⟩)).val) i)) = _
    rw [Equiv.symm_apply_apply]
  unfold firstVisitedBranch
  rw [hi 0, hi 1]
  exact if_congr horder rfl rfl

end DirectGLSSW.HOMFLY





