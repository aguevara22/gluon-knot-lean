import MarkedCursorBoundary
import OriginalSuffixSurjective
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits
attribute [local instance] Classical.propDecidable

private theorem incoming_pair_injective (D : PLLinkDiagram)
    {c d : Fin D.nCrossing} {i j : Fin 2} (he : D.incoming c i=D.incoming d j) :
    c=d ∧ i=j := by
  have hc : c=d := D.crossingVertex_injective (by
    rw [← D.incoming_target c i,he,D.incoming_target d j])
  subst d
  refine ⟨rfl,?_⟩
  by_contra hn
  fin_cases i <;> fin_cases j
  · exact hn rfl
  · exact (D.four_ports_distinct c).1 he
  · exact (D.four_ports_distinct c).1 he.symm
  · exact hn rfl

private theorem CursorBoundary.advance {t : MarkedParentState} {a : Fin t.1.nArc}
    (B : CursorBoundary t (visitPosition t.2.1 a))
    (hne : t.1.continuation a ≠ markedOrbitRoot t a)
    (hport : ∀ c : Fin t.1.nCrossing, badAt t.2.1 c → ∀ i : Fin 2,t.1.incoming c i ≠ a) :
    CursorBoundary t (visitPosition t.2.1 (t.1.continuation a)) := by
  have hp : visitPosition t.2.1 (t.1.continuation a)=visitPosition t.2.1 a+1 :=
    visitPosition_continuation_of_ne_root t.1 t.2.1 a hne
  refine ⟨le_of_lt (visitPosition_lt_nArc t _),?_,?_⟩
  · intro e he
    have hh := B.marksBefore e he
    omega
  · intro c hc i
    have hh := B.badAfter c hc i
    have hn : visitPosition t.2.1 (t.1.incoming c i) ≠ visitPosition t.2.1 a :=
      fun he => hport c hc i (marked_visitPosition_injective t he)
    omega

/-- Moving past an actual ordinary corner keeps the same marked diagram,
original root, framing and complete history. -/
theorem CursorBoundary.advance_corner {t : MarkedParentState} {a : Fin t.1.nArc}
    (B : CursorBoundary t (visitPosition t.2.1 a))
    (hne : t.1.continuation a ≠ markedOrbitRoot t a)
    (hcorner : ∀ c : Fin t.1.nCrossing,t.1.crossingVertex c ≠ t.1.arcTarget a) :
    CursorBoundary t (visitPosition t.2.1 (t.1.continuation a)) := by
  apply B.advance hne
  intro c hc i he
  apply hcorner c
  rw [← t.1.incoming_target c i,he]

/-- An already-good crossing can be passed at either actual port. -/
theorem CursorBoundary.advance_good_port {t : MarkedParentState} {a : Fin t.1.nArc}
    (B : CursorBoundary t (visitPosition t.2.1 a))
    (hne : t.1.continuation a ≠ markedOrbitRoot t a)
    (c : Fin t.1.nCrossing) (hc : ¬badAt t.2.1 c)
    (i : Fin 2) (ha : a=t.1.incoming c i) :
    CursorBoundary t (visitPosition t.2.1 (t.1.continuation a)) := by
  apply B.advance hne
  intro d hd j hj
  have he := (incoming_pair_injective t.1 (hj.trans ha)).1
  exact hc (he ▸ hd)

/-- A second visit is already good because its earlier incoming port is in the
processed prefix. This covers under second visits skipped by physical crossings. -/
theorem CursorBoundary.advance_second_visit {t : MarkedParentState} {a : Fin t.1.nArc}
    (B : CursorBoundary t (visitPosition t.2.1 a))
    (hne : t.1.continuation a ≠ markedOrbitRoot t a)
    (c : Fin t.1.nCrossing) (i j : Fin 2) (ha : a=t.1.incoming c i)
    (hj : visitPosition t.2.1 (t.1.incoming c j)<visitPosition t.2.1 a) :
    CursorBoundary t (visitPosition t.2.1 (t.1.continuation a)) := by
  apply B.advance_good_port hne c ?_ i ha
  intro hc
  exact (not_lt_of_ge (B.badAfter c hc j)) hj

/-- Moving past an actual over port cannot pass a bad first visit. The
boundary condition rules out a bad crossing's earlier port. -/
theorem CursorBoundary.advance_over {t : MarkedParentState} {a : Fin t.1.nArc}
    (B : CursorBoundary t (visitPosition t.2.1 a))
    (hne : t.1.continuation a ≠ markedOrbitRoot t a)
    (c : Fin t.1.nCrossing) (hover : a=t.1.incoming c (t.1.overBranch c)) :
    CursorBoundary t (visitPosition t.2.1 (t.1.continuation a)) := by
  apply B.advance hne
  intro d hd i hi
  have he := incoming_pair_injective t.1 (hi.trans hover)
  rcases he with ⟨rfl,rfl⟩
  have hfirst := PhysicalParentHistory.first_incoming_position_le t d (t.1.overBranch d)
  have hafter := B.badAfter d hd (firstVisitedBranch t.2.1 d)
  rw [hover] at hafter
  have heq : t.1.incoming d (firstVisitedBranch t.2.1 d)=t.1.incoming d (t.1.overBranch d) :=
    marked_visitPosition_injective t (le_antisymm hfirst hafter)
  exact hd (incoming_pair_injective t.1 heq).2

end DirectGLSSW.HOMFLY
