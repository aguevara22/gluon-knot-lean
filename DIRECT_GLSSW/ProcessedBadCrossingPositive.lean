import ProcessedCrossingSignsInitial
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract

theorem PositiveOrMarked.bad_crossing_positive {s : MarkedParentState}
    (hs : PositiveOrMarked s) (c : Fin s.1.nCrossing) (hc : badAt s.2.1 c) :
    crossingSign s.1 c = Sign.pos := by
  rcases hs c with hp | ⟨i, hi⟩
  · exact hp
  · have hb := s.2.2.beforeBad _ hi c hc
    by_cases he : i = firstVisitedBranch s.2.1 c
    · subst i
      exact (rankBefore_asymm hb hb).elim
    · have he' : i = otherBranch (firstVisitedBranch s.2.1 c) := by
        by_contra hne
        exact (neq_otherBranch_iff _ _).mp hne he
      rw [he'] at hb
      exact (rankBefore_asymm (firstVisitedBranch_is_first s.2.1 c) hb).elim

theorem MarkedParentTrace.bad_crossing_positive_of_initial
    (D : PLLinkDiagram) (T : BasedTraversal D)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (hpos : ∀ d : Fin D.nCrossing, crossingSign D d = Sign.pos)
    (t : MarkedParentState)
    (h : MarkedParentTrace ⟨D,T,ProcessedParentMarks.initial D T hconn⟩ t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) :
    crossingSign t.1 c = Sign.pos := by
  apply (h.positiveOrMarked ?_).bad_crossing_positive c hc
  intro d
  exact Or.inl (hpos d)
end DirectGLSSW.HOMFLY

#check @DirectGLSSW.HOMFLY.PositiveOrMarked.bad_crossing_positive

#check @DirectGLSSW.HOMFLY.MarkedParentTrace.bad_crossing_positive_of_initial

