import ProcessedParentHistory
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.LowestRowContract.ComponentRestriction
open PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- Exact extraction cannot create self-crossings: its crossing map is an injection
into the actual ambient crossing labels. -/
theorem nCrossing_le {D : PLLinkDiagram} {C : Component D.continuation}
    (R : ComponentRestriction D C) : R.diagram.nCrossing ≤ D.nCrossing := by
  have hcard := Fintype.card_le_of_injective
    (fun x : Fin R.diagram.nCrossing => (R.crossingEquiv x).val)
    (by
      intro x y h
      exact R.crossingEquiv.injective (Subtype.ext h))
  simpa only [Fintype.card_fin] using hcard

/-- Either actual extracted component after a smoothing has fewer crossings
than the original diagram; no particular traversal or chosen component is needed. -/
theorem nCrossing_lt_before_smoothing (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (C : Component (smoothCrossing D c).continuation)
    (R : ComponentRestriction (smoothCrossing D c) C) :
    R.diagram.nCrossing < D.nCrossing := by
  have hsub := R.nCrossing_le
  have hdrop := smoothCrossing_crossing_count_drop D c
  omega

end DirectGLSSW.HOMFLY.LowestRowContract.ComponentRestriction
