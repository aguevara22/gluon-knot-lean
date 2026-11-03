import OriginalSuffixPositions
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- Connected actual marked states have injective numerical visit coordinates. -/
theorem marked_visitPosition_injective (t : MarkedParentState) :
    Function.Injective (visitPosition t.2.1) := by
  intro a b hab
  apply visitRank_injective t.2.1
  apply Prod.ext
  · exact congrArg t.2.1.componentIndex ((componentOf_eq_iff _ _ _).mpr (t.2.2.connected a b))
  · exact hab

namespace MarkedParentTrace
variable {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
include h c hc

/-- The ancestor at each suffix position is the literal original terminal-suffix arc at that position. -/
theorem suffixOriginalArc_eq_markedSuffixArc
    (i : Fin (markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c)))) :
    h.suffixOriginalArc c hc i = markedSuffixArc s
      (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c))
      (Fin.cast (h.suffixOriginalArc_length c hc) i) := by
  apply marked_visitPosition_injective s
  rw [h.suffixOriginalArc_visitPosition c hc i,markedSuffixArc_visitPosition]
  rfl

/-- Exact original suffix surjectivity, derived from history and actual root retention. -/
theorem suffixOriginalArc_range (b : Fin s.1.nArc) :
    (∃ i, h.suffixOriginalArc c hc i = b) ↔
      visitPosition s.2.1 (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) ≤
        visitPosition s.2.1 b := by
  constructor
  · rintro ⟨i,rfl⟩
    rw [h.suffixOriginalArc_visitPosition c hc i]
    omega
  · intro hle
    have hb := visitPosition_lt_markedOrbitSize s b
    rw [markedOrbitSize_eq s b (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c))] at hb
    let i : Fin (markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c))) :=
      ⟨visitPosition s.2.1 b -
        visitPosition s.2.1 (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)),by
          rw [h.suffixOriginalArc_length c hc]
          unfold markedSuffixSize
          omega⟩
    refine ⟨i,?_⟩
    apply marked_visitPosition_injective s
    rw [h.suffixOriginalArc_visitPosition c hc i]
    change visitPosition s.2.1 (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) +
      (visitPosition s.2.1 b-visitPosition s.2.1 (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c))) =
      visitPosition s.2.1 b
    omega

/-- Exact occurrence order, without global first-branch or traversal transport. -/
theorem suffixOriginalArc_order
    (i j : Fin (markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c)))) :
    visitPosition s.2.1 (h.suffixOriginalArc c hc i) < visitPosition s.2.1 (h.suffixOriginalArc c hc j) ↔ i.val<j.val := by
  rw [h.suffixOriginalArc_visitPosition c hc i,h.suffixOriginalArc_visitPosition c hc j]
  omega

end MarkedParentTrace
end DirectGLSSW.HOMFLY
