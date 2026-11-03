import FutureCrossingEquivalence
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits
attribute [local instance] Classical.propDecidable

theorem marked_rankBefore_iff (t : MarkedParentState) (a b : Fin t.1.nArc) :
    rankBefore (visitRank t.2.1 a) (visitRank t.2.1 b) ↔
      visitPosition t.2.1 a < visitPosition t.2.1 b := by
  have he := (componentOf_eq_iff _ _ _).mpr (t.2.2.connected a b)
  simp only [rankBefore,visitRank,he,lt_self_iff_false,true_and,false_or]

/-- The selected first-under crossing itself has both ports in its actual suffix. -/
def selectedSuffixCrossing (t : MarkedParentState) (c : Fin t.1.nCrossing) :
    SuffixCrossing t (t.1.incoming c (firstVisitedBranch t.2.1 c)) := by
  refine ⟨c,?_⟩
  intro i
  by_cases hi : i=firstVisitedBranch t.2.1 c
  · rw [hi]
  · rw [Gemini.eq_otherBranch_of_ne i (firstVisitedBranch t.2.1 c) hi]
    exact le_of_lt ((marked_rankBefore_iff t _ _).mp (firstVisitedBranch_is_first t.2.1 c))

namespace MarkedParentTrace
variable {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
include h c hc

/-- Relative order of every pair of retained suffix visits is produced by their exact common offsets. -/
theorem suffixCrossing_visit_order
    (d e : SuffixCrossing t (t.1.incoming c (firstVisitedBranch t.2.1 c))) (i j : Fin 2) :
    visitPosition t.2.1 (t.1.incoming d.val i) < visitPosition t.2.1 (t.1.incoming e.val j) ↔
      visitPosition s.2.1 (s.1.incoming (h.crossingOrigin d.val) i) <
        visitPosition s.2.1 (s.1.incoming (h.crossingOrigin e.val) j) := by
  obtain ⟨k,hk,hko⟩ := h.suffixCrossing_incoming_offset c hc d i
  obtain ⟨l,hl,hlo⟩ := h.suffixCrossing_incoming_offset c hc e j
  rw [← hk,← hl,← hko,← hlo,markedSuffixArc_visitPosition,markedSuffixArc_visitPosition,
    h.suffixOriginalArc_visitPosition c hc k,h.suffixOriginalArc_visitPosition c hc l]
  omega

/-- No historical global branch-order hypothesis is needed on the exact future carrier. -/
theorem suffixCrossing_firstVisitedBranch
    (d : SuffixCrossing t (t.1.incoming c (firstVisitedBranch t.2.1 c))) :
    firstVisitedBranch t.2.1 d.val = firstVisitedBranch s.2.1 (h.crossingOrigin d.val) := by
  have he : rankBefore (visitRank t.2.1 (t.1.incoming d.val 0)) (visitRank t.2.1 (t.1.incoming d.val 1)) ↔
      rankBefore (visitRank s.2.1 (s.1.incoming (h.crossingOrigin d.val) 0))
        (visitRank s.2.1 (s.1.incoming (h.crossingOrigin d.val) 1)) := by
    rw [marked_rankBefore_iff t,marked_rankBefore_iff s]
    exact h.suffixCrossing_visit_order c hc d d 0 1
  unfold firstVisitedBranch
  rw [he]

theorem suffixCrossing_incoming_not_marked
    (d : SuffixCrossing t (t.1.incoming c (firstVisitedBranch t.2.1 c))) (i : Fin 2) :
    t.1.incoming d.val i ∉ t.2.2.marks := by
  intro hm
  have hh := t.2.2.mark_before_cut c hc ⟨_,hm⟩
  exact (not_lt_of_ge (d.property i)) hh

theorem suffixCrossing_overBranch
    (d : SuffixCrossing t (t.1.incoming c (firstVisitedBranch t.2.1 c))) :
    t.1.overBranch d.val = s.1.overBranch (h.crossingOrigin d.val) := by
  rcases h.crossingOrigin_over_or_marked d.val with he | ⟨i,hi⟩
  · exact he
  · exact (h.suffixCrossing_incoming_not_marked c hc d i hi).elim

theorem suffixCrossing_sign
    (d : SuffixCrossing t (t.1.incoming c (firstVisitedBranch t.2.1 c))) :
    crossingSign t.1 d.val = crossingSign s.1 (h.crossingOrigin d.val) := by
  rcases h.crossingOrigin_sign_or_marked d.val with he | ⟨i,hi⟩
  · exact he
  · exact (h.suffixCrossing_incoming_not_marked c hc d i hi).elim

theorem suffixCrossing_bad_iff
    (d : SuffixCrossing t (t.1.incoming c (firstVisitedBranch t.2.1 c))) :
    badAt t.2.1 d.val ↔ badAt s.2.1 (h.crossingOrigin d.val) := by
  unfold badAt
  rw [h.suffixCrossing_firstVisitedBranch c hc d,h.suffixCrossing_overBranch c hc d]

/-- Actual selected first-under branch agrees with the original traversal, derived without supplied restriction or order. -/
theorem selectedSuffix_firstVisitedBranch :
    firstVisitedBranch t.2.1 c = firstVisitedBranch s.2.1 (h.crossingOrigin c) :=
  h.suffixCrossing_firstVisitedBranch c hc (selectedSuffixCrossing t c)

theorem selectedSuffix_bad : badAt s.2.1 (h.crossingOrigin c) :=
  (h.suffixCrossing_bad_iff c hc (selectedSuffixCrossing t c)).mp hc

end MarkedParentTrace
end DirectGLSSW.HOMFLY
