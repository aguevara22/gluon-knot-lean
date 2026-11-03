import HOMFLYParentGoodPrefix
import Mathlib.Data.Finset.Max

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY

/-- A genuine first-under cut exists whenever the actual traversal is not descending. -/
theorem exists_firstBad_goodPrefix (D : PLLinkDiagram) (T : BasedTraversal D)
    (hbad : (badCrossings T).Nonempty) :
    ∃ c : Fin D.nCrossing, badAt T c ∧
      ∀ d : Fin D.nCrossing,
        rankBefore (visitRank T (D.incoming d (firstVisitedBranch T d)))
          (visitRank T (D.incoming c (firstVisitedBranch T c))) → ¬ badAt T d := by
  classical
  let first := fun d : Fin D.nCrossing => visitRank T (D.incoming d (firstVisitedBranch T d))
  obtain ⟨b, hb, hminComp⟩ := (badCrossings T).exists_min_image (fun d => (first d).1) hbad
  let s := (badCrossings T).filter (fun d => (first d).1 = (first b).1)
  have hs : s.Nonempty := ⟨b, by simp [s, hb]⟩
  obtain ⟨c, hc, hminPos⟩ := s.exists_min_image (fun d => (first d).2) hs
  have hcBad : c ∈ badCrossings T := (Finset.mem_filter.mp hc).1
  have hcComp : (first c).1 = (first b).1 := (Finset.mem_filter.mp hc).2
  refine ⟨c, by simpa [badCrossings] using hcBad, ?_⟩
  intro d hbefore hd
  have hdBad : d ∈ badCrossings T := by simpa [badCrossings] using hd
  change rankBefore (first d) (first c) at hbefore
  rcases hbefore with hcomp | ⟨hcomp, hpos⟩
  · have hm := hminComp d hdBad
    rw [← hcComp] at hm
    exact (not_lt_of_ge hm) hcomp
  · have hdS : d ∈ s := Finset.mem_filter.mpr ⟨hdBad, hcomp.trans hcComp⟩
    exact (not_lt_of_ge (hminPos d hdS)) hpos

/-- Distinct crossing labels have distinct first incoming visit ranks. -/
theorem firstVisitRank_injective (D : PLLinkDiagram) (T : BasedTraversal D) :
    Function.Injective (fun c : Fin D.nCrossing =>
      visitRank T (D.incoming c (firstVisitedBranch T c))) := by
  intro c d h
  have ha := visitRank_injective T h
  apply D.crossingVertex_injective
  simpa only [D.incoming_target] using congrArg D.arcTarget ha

/-- After switching the first bad crossing, every remaining bad crossing comes later. -/
theorem firstBad_switch_remaining_after (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing) (hc : badAt T c)
    (hgood : ∀ d : Fin D.nCrossing,
      rankBefore (visitRank T (D.incoming d (firstVisitedBranch T d)))
        (visitRank T (D.incoming c (firstVisitedBranch T c))) → ¬ badAt T d)
    (d : Fin D.nCrossing) (hd : badAt (switchTraversal T c) d) :
    rankBefore
      (visitRank (switchTraversal T c)
        ((switchCrossing D c).incoming c (firstVisitedBranch (switchTraversal T c) c)))
      (visitRank (switchTraversal T c)
        ((switchCrossing D c).incoming d (firstVisitedBranch (switchTraversal T c) d))) := by
  have hdc : d ≠ c := by
    intro h
    subst d
    exact (badAt_switch_toggle T c).mp hd hc
  have hdOld := (badAt_switch_same T c d hdc).mp hd
  have hne : visitRank T (D.incoming c (firstVisitedBranch T c)) ≠
      visitRank T (D.incoming d (firstVisitedBranch T d)) := by
    intro h
    exact hdc ((firstVisitRank_injective D T h).symm)
  change rankBefore (visitRank T (D.incoming c (firstVisitedBranch T c)))
    (visitRank T (D.incoming d (firstVisitedBranch T d)))
  exact (rankBefore_total_of_ne hne).resolve_right (fun h => hgood d h hdOld)

end DirectGLSSW.HOMFLY
end
