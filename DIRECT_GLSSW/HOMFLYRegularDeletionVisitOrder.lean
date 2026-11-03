import HOMFLYRegularDeletionWords
import RootedWordOrder

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open PermutationOrbits
noncomputable section
namespace SignedRegularDeletion
variable {D E : PLLinkDiagram} (R : SignedRegularDeletion D E)

theorem visitPosition_eq_filtered_idx (T : BasedTraversal D) (e : Fin D.nArc)
    (he : e ≠ R.deleted) :
    visitPosition (R.transportTraversal T) (R.arcMap e) =
      ((orbitWord D.continuation (T.baseArc (componentOf D.continuation e)).val).filter
        (fun x => decide (x ≠ R.deleted))).idxOf e := by
  classical
  rw [visitPosition_eq_idxOf, ← R.componentEquiv_map,
    R.transportTraversal_baseArc, R.orbitWord_transport]
  apply idxOf_map_eq_of_preimage
  intro y hy hmap
  have hyl : y ≠ R.deleted := by simpa using (List.mem_filter.mp hy).2
  rcases (R.arcMap_fibers y e).mp hmap with h | h | h
  · exact h
  · exact False.elim (hyl h.1)
  · exact False.elim (he h.2)

theorem visitPosition_lt_iff (T : BasedTraversal D) (e f : Fin D.nArc)
    (he : e ≠ R.deleted) (hf : f ≠ R.deleted)
    (hcomp : componentOf D.continuation e = componentOf D.continuation f) :
    visitPosition (R.transportTraversal T) (R.arcMap e) <
        visitPosition (R.transportTraversal T) (R.arcMap f) ↔
      visitPosition T e < visitPosition T f := by
  classical
  rw [R.visitPosition_eq_filtered_idx T e he,
    R.visitPosition_eq_filtered_idx T f hf,
    visitPosition_eq_idxOf T e, visitPosition_eq_idxOf T f, hcomp]
  exact idxOf_filter_lt_iff _ _ e f (by simp [he]) (by simp [hf])

theorem rankBefore_iff (T : BasedTraversal D) (e f : Fin D.nArc)
    (he : e ≠ R.deleted) (hf : f ≠ R.deleted) :
    rankBefore (visitRank (R.transportTraversal T) (R.arcMap e))
      (visitRank (R.transportTraversal T) (R.arcMap f)) ↔
    rankBefore (visitRank T e) (visitRank T f) := by
  have hi (x : Fin D.nArc) :
      ((R.transportTraversal T).componentIndex
        (componentOf E.continuation (R.arcMap x))).val =
      (T.componentIndex (componentOf D.continuation x)).val := by
    rw [← R.componentEquiv_map]
    exact R.transportTraversal_componentIndex T _
  have hlt : (R.transportTraversal T).componentIndex
        (componentOf E.continuation (R.arcMap e)) <
      (R.transportTraversal T).componentIndex
        (componentOf E.continuation (R.arcMap f)) ↔
      T.componentIndex (componentOf D.continuation e) <
        T.componentIndex (componentOf D.continuation f) := by
    rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val, hi e, hi f]
  have heq : (R.transportTraversal T).componentIndex
        (componentOf E.continuation (R.arcMap e)) =
      (R.transportTraversal T).componentIndex
        (componentOf E.continuation (R.arcMap f)) ↔
      T.componentIndex (componentOf D.continuation e) =
        T.componentIndex (componentOf D.continuation f) := by
    rw [Fin.ext_iff, Fin.ext_iff, hi e, hi f]
  dsimp only [rankBefore, visitRank]
  rw [hlt, heq]
  by_cases hc : componentOf D.continuation e = componentOf D.continuation f
  · rw [R.visitPosition_lt_iff T e f he hf hc]
  · have hn : T.componentIndex (componentOf D.continuation e) ≠
        T.componentIndex (componentOf D.continuation f) := fun h => hc (T.componentIndex.injective h)
    simp only [hn, false_and, or_false]

theorem crossing_visit_order (T : BasedTraversal D)
    (c d : Fin D.nCrossing) (i j : Fin 2) :
    rankBefore (visitRank (R.transportTraversal T) (E.incoming (R.crossingEquiv c) i))
      (visitRank (R.transportTraversal T) (E.incoming (R.crossingEquiv d) j)) ↔
    rankBefore (visitRank T (D.incoming c i)) (visitRank T (D.incoming d j)) := by
  rw [← R.incoming_map c i, ← R.incoming_map d j]
  exact R.rankBefore_iff T _ _ (R.selected_not_ports c i).1 (R.selected_not_ports d j).1

theorem firstVisitedBranch_map (T : BasedTraversal D) (c : Fin D.nCrossing) :
    firstVisitedBranch (R.transportTraversal T) (R.crossingEquiv c) = firstVisitedBranch T c := by
  classical
  simp only [firstVisitedBranch, R.crossing_visit_order T c c 0 1]

theorem badAt_map (T : BasedTraversal D) (c : Fin D.nCrossing) :
    badAt (R.transportTraversal T) (R.crossingEquiv c) ↔ badAt T c := by
  simp only [badAt, R.firstVisitedBranch_map, ← R.overBranch_map]

theorem badCrossings_map (T : BasedTraversal D) :
    badCrossings (R.transportTraversal T) = (badCrossings T).map R.crossingEquiv.toEmbedding := by
  classical
  ext e
  obtain ⟨c, rfl⟩ := R.crossingEquiv.surjective e
  rw [Finset.mem_map]
  constructor
  · intro hc
    refine ⟨c, ?_, rfl⟩
    simpa only [badCrossings, Finset.mem_filter, Finset.mem_univ, true_and, R.badAt_map] using hc
  · rintro ⟨d, hd, hdc⟩
    have he : d = c := R.crossingEquiv.injective hdc
    subst d
    simpa only [badCrossings, Finset.mem_filter, Finset.mem_univ, true_and, R.badAt_map] using hd

end SignedRegularDeletion
end
end DirectGLSSW.HOMFLY






