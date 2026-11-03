import ActualSpatialEmbedding
import SplitTraversalRanks

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY HOMFLY.PrincipalTurning PermutationOrbits

theorem visitPosition_lt_component {D : PLLinkDiagram} (T : BasedTraversal D) (e : Fin D.nArc) :
    visitPosition T e < componentArcLength D (T.baseArc (componentOf D.continuation e)).val := by
  unfold visitPosition
  exact Fin.isLt _

theorem visit_fraction_bounds {D : PLLinkDiagram} (T : BasedTraversal D) (e : Fin D.nArc) :
    0 < ((visitPosition T e:ℝ)+1)/
      ((componentArcLength D (T.baseArc (componentOf D.continuation e)).val:ℝ)+1) ∧
    ((visitPosition T e:ℝ)+1)/
      ((componentArcLength D (T.baseArc (componentOf D.continuation e)).val:ℝ)+1) < 1 := by
  have hp := visitPosition_lt_component T e
  have hp' : (visitPosition T e:ℝ) < componentArcLength D
      (T.baseArc (componentOf D.continuation e)).val := by exact_mod_cast hp
  constructor
  · positivity
  · apply (div_lt_one (by positivity)).mpr
    linarith

/-- Literal source traversal order gives strict descending height, including
components with different numbers of arcs. -/
theorem rankBefore_height_order {D : PLLinkDiagram} (T : BasedTraversal D)
    (e f : Fin D.nArc) (h : rankBefore (visitRank T e) (visitRank T f)) :
    3*((diagramComponentCount D:ℝ)-1-(T.componentIndex (componentOf D.continuation f)).val)+1-
      ((visitPosition T f:ℝ)+1)/
        ((componentArcLength D (T.baseArc (componentOf D.continuation f)).val:ℝ)+1) <
    3*((diagramComponentCount D:ℝ)-1-(T.componentIndex (componentOf D.continuation e)).val)+1-
      ((visitPosition T e:ℝ)+1)/
        ((componentArcLength D (T.baseArc (componentOf D.continuation e)).val:ℝ)+1) := by
  have he := visit_fraction_bounds T e
  have hf := visit_fraction_bounds T f
  change T.componentIndex (componentOf D.continuation e) <
      T.componentIndex (componentOf D.continuation f) ∨
    (T.componentIndex (componentOf D.continuation e) = T.componentIndex (componentOf D.continuation f) ∧
      visitPosition T e < visitPosition T f) at h
  rcases h with h | ⟨hC,hp⟩
  · have hi : ((T.componentIndex (componentOf D.continuation e)).val:ℝ)+1 ≤
        (T.componentIndex (componentOf D.continuation f)).val := by exact_mod_cast h
    linarith
  · have hcomp := T.componentIndex.injective hC
    have hn := congrArg (fun C => componentArcLength D (T.baseArc C).val) hcomp
    have hp' : (visitPosition T e:ℝ)+1 < (visitPosition T f:ℝ)+1 := by exact_mod_cast Nat.add_lt_add_right hp 1
    dsimp only at hn
    have hd := div_lt_div_of_pos_right hp'
      (by positivity : 0 < (componentArcLength D (T.baseArc (componentOf D.continuation e)).val:ℝ)+1)
    rw [← hC,← hn]
    linarith

/-- The actual empty-bad-crossing condition, not an assumed height order. -/
theorem descending_crossing_height_order {D : PLLinkDiagram} (T : BasedTraversal D)
    (hbad : badCrossings T = ∅) (c : Fin D.nCrossing) :
    let e := D.incoming c (D.overBranch c)
    let f := D.incoming c (otherBranch (D.overBranch c))
    3*((diagramComponentCount D:ℝ)-1-(T.componentIndex (componentOf D.continuation f)).val)+1-
      ((visitPosition T f:ℝ)+1)/
        ((componentArcLength D (T.baseArc (componentOf D.continuation f)).val:ℝ)+1) <
    3*((diagramComponentCount D:ℝ)-1-(T.componentIndex (componentOf D.continuation e)).val)+1-
      ((visitPosition T e:ℝ)+1)/
        ((componentArcLength D (T.baseArc (componentOf D.continuation e)).val:ℝ)+1) := by
  apply rankBefore_height_order
  have h := firstVisitedBranch_is_first T c
  rw [(badCrossings_eq_empty_iff_firstVisited_over T).mp hbad c] at h
  exact h

/-- The visit fraction is realized by the actual main arc at the target
of the original arc e, using its selected component base arc. -/
theorem descendingMain_at_actual_visit {D : PLLinkDiagram} (T : BasedTraversal D)
    (e : Fin D.nArc) (H : ℝ) (t : unitInterval)
    (ht : t.val = ((visitPosition T e:ℝ)+1)/
      ((componentArcLength D (T.baseArc (componentOf D.continuation e)).val:ℝ)+1)) :
    descendingMain D (T.baseArc (componentOf D.continuation e)).val H t =
      (Complex.equivRealProd.symm (D.vertexPoint (D.arcTarget e)),H+1-t.val) := by
  rw [descendingMain_apply,splitMainComplex_apply,
    splitMainPlanar_visit D _ _ (visitPosition_lt_component T e) t ht,
    visitPosition_reconstruct]

/-- The literal ordered slab choice separates every distinct actual component. -/
theorem traversal_component_traces_disjoint {D : PLLinkDiagram} (T : BasedTraversal D)
    (C E : diagramComponent D) (hCE : C ≠ E) :
    Disjoint
      (splitSpatialTrace D (T.baseArc C).val
        (3*((diagramComponentCount D:ℝ)-1-(T.componentIndex C).val)))
      (splitSpatialTrace D (T.baseArc E).val
        (3*((diagramComponentCount D:ℝ)-1-(T.componentIndex E).val))) := by
  have hne : T.componentIndex C ≠ T.componentIndex E := fun h => hCE (T.componentIndex.injective h)
  rcases lt_or_gt_of_ne hne with h | h
  · apply Disjoint.symm
    apply splitSpatialTrace_disjoint_of_height
    have hi : ((T.componentIndex C).val:ℝ)+1 ≤ (T.componentIndex E).val := by exact_mod_cast h
    linarith
  · apply splitSpatialTrace_disjoint_of_height
    have hi : ((T.componentIndex E).val:ℝ)+1 ≤ (T.componentIndex C).val := by exact_mod_cast h
    linarith

theorem exists_actual_crossing_visit {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) (H : ℝ) :
    ∃ t : unitInterval,
      t.val = ((visitPosition T (D.incoming c i):ℝ)+1)/
        ((componentArcLength D (T.baseArc (componentOf D.continuation (D.incoming c i))).val:ℝ)+1) ∧
      descendingMain D (T.baseArc (componentOf D.continuation (D.incoming c i))).val H t =
        (Complex.equivRealProd.symm (D.vertexPoint (D.crossingVertex c)),H+1-t.val) := by
  have hb := visit_fraction_bounds T (D.incoming c i)
  refine ⟨⟨_,⟨hb.1.le,hb.2.le⟩⟩,rfl,?_⟩
  rw [descendingMain_at_actual_visit T (D.incoming c i) H _ rfl,D.incoming_target]

end DirectGLSSW.DescendingSpatial








