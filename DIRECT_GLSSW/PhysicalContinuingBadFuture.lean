import PhysicalContinuingParentTransport
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalParentHistory
open PermutationOrbits LowestRowContract ProcessedParentMarks MarkedG
attribute [local instance] Classical.propDecidable

/-- On an actual marked connected state, the first visited incoming port has the least position. -/
theorem first_incoming_position_le (s : MarkedParentState) (d : Fin s.1.nCrossing) (i : Fin 2) :
    visitPosition s.2.1 (s.1.incoming d (firstVisitedBranch s.2.1 d)) ≤
      visitPosition s.2.1 (s.1.incoming d i) := by
  have he : componentOf s.1.continuation (s.1.incoming d 0) =
      componentOf s.1.continuation (s.1.incoming d 1) :=
    (componentOf_eq_iff _ _ _).mpr (s.2.2.connected _ _)
  have H : rankBefore (visitRank s.2.1 (s.1.incoming d 0))
      (visitRank s.2.1 (s.1.incoming d 1)) ↔
      visitPosition s.2.1 (s.1.incoming d 0)<visitPosition s.2.1 (s.1.incoming d 1) := by
    simp only [rankBefore,visitRank,he,lt_self_iff_false,false_or,true_and]
  unfold firstVisitedBranch
  split_ifs with h
  · have hh := H.mp h
    fin_cases i
    · exact le_refl _
    · exact le_of_lt hh
  · have hh := H.not.mp h
    fin_cases i
    · exact le_of_not_gt hh
    · exact le_refl _

/-- Every actual bad crossing of the canonical continuing parent lies completely
in the matched future. No post-cut prefix or ordering hypothesis is supplied. -/
theorem continuing_bad_in_future {t : MarkedParentState}
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) (hgood : GoodBefore t c)
    (d : Fin (continuingState t c hc hgood).1.nCrossing)
    (hd : badAt (continuingState t c hc hgood).2.1 d) :
    ∀ i : Fin 2,
      visitPosition (continuingState t c hc hgood).2.1 (connector t c) <
      visitPosition (continuingState t c hc hgood).2.1
        ((continuingState t c hc hgood).1.incoming d i) := by
  have hm : connector t c ∈ (continuingState t c hc hgood).2.2.marks := by
    change liftConnector t.1 t.2.1 c (continuingRestriction t c) ∈
      t.2.2.smoothedMarks c hc (continuingRestriction t c)
    exact Finset.mem_insert_self _ _
  have hh := (continuingState t c hc hgood).2.2.mark_before_cut d hd ⟨connector t c,hm⟩
  intro i
  exact lt_of_lt_of_le hh (first_incoming_position_le (continuingState t c hc hgood) d i)
end DirectGLSSW.HOMFLY.PhysicalParentHistory
