import DescendingRankHeights

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY PermutationOrbits

/-- Actual over/under branches occur at the actual crossing projection and in
the required strict height order. Empty bad crossings is the essential input. -/
theorem actual_descending_crossing_representation {D : PLLinkDiagram}
    (T : BasedTraversal D) (hbad : badCrossings T = ∅) (c : Fin D.nCrossing) :
    let e := D.incoming c (D.overBranch c)
    let f := D.incoming c (otherBranch (D.overBranch c))
    let He : ℝ := 3*((diagramComponentCount D:ℝ)-1-(T.componentIndex (componentOf D.continuation e)).val)
    let Hf : ℝ := 3*((diagramComponentCount D:ℝ)-1-(T.componentIndex (componentOf D.continuation f)).val)
    ∃ t u : unitInterval,
      descendingMain D (T.baseArc (componentOf D.continuation e)).val He t =
        (Complex.equivRealProd.symm (D.vertexPoint (D.crossingVertex c)),He+1-t.val) ∧
      descendingMain D (T.baseArc (componentOf D.continuation f)).val Hf u =
        (Complex.equivRealProd.symm (D.vertexPoint (D.crossingVertex c)),Hf+1-u.val) ∧
      Hf+1-u.val < He+1-t.val := by
  dsimp only
  obtain ⟨t,ht,hpt⟩ := exists_actual_crossing_visit T c (D.overBranch c)
    (3*((diagramComponentCount D:ℝ)-1-(T.componentIndex (componentOf D.continuation (D.incoming c (D.overBranch c)))).val))
  obtain ⟨u,hu,hpu⟩ := exists_actual_crossing_visit T c (otherBranch (D.overBranch c))
    (3*((diagramComponentCount D:ℝ)-1-(T.componentIndex (componentOf D.continuation (D.incoming c (otherBranch (D.overBranch c))))).val))
  refine ⟨t,u,hpt,hpu,?_⟩
  rw [ht,hu]
  exact descending_crossing_height_order T hbad c

end DirectGLSSW.DescendingSpatial

