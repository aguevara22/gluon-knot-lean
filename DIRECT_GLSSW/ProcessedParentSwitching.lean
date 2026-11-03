import ProcessedParentMarks
import HOMFLYFirstBadPrefix
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ProcessedParentMarks
attribute [local instance] Classical.propDecidable
variable {D : PLLinkDiagram} {T : BasedTraversal D}

/-- A literal switch keeps all old marks and marks the processed first visit. -/
def switchStep (S : ProcessedParentMarks D T) (c : Fin D.nCrossing) (hc : badAt T c)
    (hgood : ∀ d : Fin D.nCrossing,
      rankBefore (visitRank T (D.incoming d (firstVisitedBranch T d)))
        (visitRank T (D.incoming c (firstVisitedBranch T c))) → ¬ badAt T d) :
    ProcessedParentMarks (switchCrossing D c) (switchTraversal T c) where
  marks := insert (D.incoming c (firstVisitedBranch T c)) S.marks
  connected := S.connected
  beforeBad := by
    intro x hx d hd
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact firstBad_switch_remaining_after D T c hc hgood d hd
    · have hdc : d ≠ c := by
        intro he
        subst d
        exact (badAt_switch_toggle T c).mp hd hc
      exact S.beforeBad x hx d ((badAt_switch_same T c d hdc).mp hd)

theorem oldMark_mem_switchStep (S : ProcessedParentMarks D T) (c : Fin D.nCrossing) (hc : badAt T c)
    (hgood : ∀ d : Fin D.nCrossing,
      rankBefore (visitRank T (D.incoming d (firstVisitedBranch T d)))
        (visitRank T (D.incoming c (firstVisitedBranch T c))) → ¬ badAt T d)
    (x : {x : Fin D.nArc // x ∈ S.marks}) :
    x.val ∈ (S.switchStep c hc hgood).marks := Finset.mem_insert_of_mem x.property

end DirectGLSSW.HOMFLY.ProcessedParentMarks
