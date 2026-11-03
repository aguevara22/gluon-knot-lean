import PhysicalContinuingFutureData
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits MarkedG PhysicalParentHistory
attribute [local instance] Classical.propDecidable

/-- A literal rank boundary in the stored traversal. Processed marks precede
it and every bad crossing is wholly ahead of it. No physical/current matching
or value equation is part of this state invariant. The terminal boundary is nArc. -/
structure CursorBoundary (t : MarkedParentState) (k : ℕ) : Prop where
  bound : k ≤ t.1.nArc
  marksBefore : ∀ a : Fin t.1.nArc, a ∈ t.2.2.marks → visitPosition t.2.1 a < k
  badAfter : ∀ c : Fin t.1.nCrossing, badAt t.2.1 c →
    ∀ i : Fin 2, k ≤ visitPosition t.2.1 (t.1.incoming c i)

theorem visitPosition_lt_nArc (t : MarkedParentState) (a : Fin t.1.nArc) :
    visitPosition t.2.1 a < t.1.nArc := by
  have hh := visitPosition_lt_orbitCard t.2.1 a
  exact lt_of_lt_of_le hh (by
    change Fintype.card (Fibre t.1.continuation (componentOf t.1.continuation
      (t.2.1.baseArc (componentOf t.1.continuation a)).val)) ≤ t.1.nArc
    simpa only [Fintype.card_fin] using
      (Fintype.card_le_of_injective (fun x : Fibre t.1.continuation (componentOf t.1.continuation
        (t.2.1.baseArc (componentOf t.1.continuation a)).val) => x.val)
        Subtype.val_injective))

theorem selected_cursorBoundary (t : MarkedParentState) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) :
    CursorBoundary t (visitPosition t.2.1 (t.1.incoming c (firstVisitedBranch t.2.1 c))) := by
  refine ⟨le_of_lt (visitPosition_lt_nArc t _),?_,?_⟩
  · intro a ha
    exact t.2.2.mark_before_cut c hc ⟨a,ha⟩
  · intro d hd i
    have hmin : visitPosition t.2.1 (t.1.incoming c (firstVisitedBranch t.2.1 c)) ≤
        visitPosition t.2.1 (t.1.incoming d (firstVisitedBranch t.2.1 d)) := by
      apply le_of_not_gt
      intro hh
      exact hgood d ((marked_rankBefore_iff t _ _).mpr hh) hd
    exact le_trans hmin (first_incoming_position_le t d i)

theorem switched_cursorBoundary (t : MarkedParentState) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) :
    CursorBoundary (switchedState t c hc hgood)
      (visitPosition t.2.1 (t.1.incoming c (firstVisitedBranch t.2.1 c))+1) := by
  let u := switchedState t c hc hgood
  have hbound := visitPosition_lt_nArc t (t.1.incoming c (firstVisitedBranch t.2.1 c))
  refine ⟨by change _ ≤ t.1.nArc;omega,?_,?_⟩
  · intro a ha
    change a ∈ insert (t.1.incoming c (firstVisitedBranch t.2.1 c)) t.2.2.marks at ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · change visitPosition t.2.1 (t.1.incoming c (firstVisitedBranch t.2.1 c)) < _
      omega
    · have hm := t.2.2.mark_before_cut c hc ⟨a,ha⟩
      exact lt_trans hm (Nat.lt_succ_self _)
  · intro d hd i
    have hh := firstBad_switch_remaining_after t.1 t.2.1 c hc hgood d hd
    have hp := (marked_rankBefore_iff u _ _).mp hh
    have hl := first_incoming_position_le u d i
    have hp' : visitPosition t.2.1 (t.1.incoming c (firstVisitedBranch t.2.1 c)) <
        visitPosition u.2.1 (u.1.incoming d (firstVisitedBranch u.2.1 d)) := hp
    exact Nat.succ_le_of_lt (lt_of_lt_of_le hp' hl)

theorem continuing_cursorBoundary (t : MarkedParentState) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) :
    CursorBoundary (continuingState t c hc hgood)
      (visitPosition (continuingState t c hc hgood).2.1 (connector t c)+1) := by
  have hb := visitPosition_lt_nArc (continuingState t c hc hgood) (connector t c)
  refine ⟨by omega,?_,?_⟩
  · intro a ha
    have hh := mark_le_connector c hc hgood a ha
    omega
  · intro d hd i
    have hh := continuing_bad_in_future c hc hgood d hd i
    omega

theorem CursorBoundary.future_not_marked {t : MarkedParentState} {k : ℕ}
    (B : CursorBoundary t k) (a : Fin t.1.nArc) (ha : k ≤ visitPosition t.2.1 a) :
    a ∉ t.2.2.marks := by
  intro hm
  have hh := B.marksBefore a hm
  omega

theorem CursorBoundary.terminal {t : MarkedParentState} (B : CursorBoundary t t.1.nArc) :
    ∀ c : Fin t.1.nCrossing, ¬ badAt t.2.1 c := by
  intro c hc
  have hh := B.badAfter c hc 0
  have hb := visitPosition_lt_nArc t (t.1.incoming c 0)
  omega
end DirectGLSSW.HOMFLY
