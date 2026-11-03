import BoundaryOriginalTail
import FutureCrossingData
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits
attribute [local instance] Classical.propDecidable
namespace MarkedParentTrace
variable {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (a : Fin t.1.nArc) (B : CursorBoundary t (visitPosition t.2.1 a))
include h a B

/-- Exact common suffix offsets for every incoming port at an actual boundary. -/
theorem boundaryCrossing_incoming_offset (d : SuffixCrossing t a) (i : Fin 2) :
    ∃ k : Fin (markedSuffixSize t a),
      markedSuffixArc t a k=t.1.incoming d.val i ∧
      h.boundaryOriginalArc a B k=s.1.incoming (h.crossingOrigin d.val) i := by
  obtain ⟨k,hk⟩ := (markedSuffixArc_range t a (t.1.incoming d.val i)).mpr (d.property i)
  refine ⟨k,hk,?_⟩
  have hh := h.boundaryOriginalArc_spec a B k
  rw [hk,h.crossingOrigin_incoming] at hh
  exact (Option.some.inj hh).symm

theorem boundaryCrossing_origin_mem (d : SuffixCrossing t a) :
    ∀ i : Fin 2, visitPosition s.2.1 (h.boundaryOrigin a B) ≤
      visitPosition s.2.1 (s.1.incoming (h.crossingOrigin d.val) i) := by
  intro i
  obtain ⟨k,_,ho⟩ := h.boundaryCrossing_incoming_offset a B d i
  exact (h.boundaryOriginalArc_range a B _).mp ⟨k,ho⟩

/-- Original two-port future crossings survive in the actual boundary suffix. -/
theorem boundaryCrossing_origin_complete (d : SuffixCrossing s (h.boundaryOrigin a B)) :
    ∃ e : SuffixCrossing t a, h.crossingOrigin e.val=d.val := by
  have hports : ∀ i : Fin 2, ∃ e : Fin t.1.nArc,
      h.arcOrigin e=some (s.1.incoming d.val i) ∧
      visitPosition t.2.1 a ≤ visitPosition t.2.1 e := by
    intro i
    obtain ⟨k,hk⟩ := (h.boundaryOriginalArc_range a B (s.1.incoming d.val i)).mpr (d.property i)
    refine ⟨markedSuffixArc t a k,?_,?_⟩
    · rw [h.boundaryOriginalArc_spec a B k,hk]
    · rw [markedSuffixArc_visitPosition];omega
  obtain ⟨e,he⟩ := h.crossingOrigin_complete d.val (by
    intro i
    obtain ⟨z,hz,_⟩ := hports i
    exact ⟨z,hz⟩)
  have hef : ∀ i : Fin 2, visitPosition t.2.1 a ≤ visitPosition t.2.1 (t.1.incoming e i) := by
    intro i
    obtain ⟨z,hz,hle⟩ := hports i
    have hi := h.crossingOrigin_incoming e i
    rw [he] at hi
    have heq := h.arcOrigin_some_injective z (t.1.incoming e i) _ hz hi
    exact heq ▸ hle
  exact ⟨⟨e,hef⟩,he⟩

/-- Every actual boundary suffix has the complete original suffix crossing carrier. -/
def boundaryCrossingEquiv : SuffixCrossing t a ≃ SuffixCrossing s (h.boundaryOrigin a B) :=
  Equiv.ofBijective (fun d => ⟨h.crossingOrigin d.val,h.boundaryCrossing_origin_mem a B d⟩) (by
    constructor
    · intro d e he
      exact Subtype.ext (h.crossingOrigin.injective (congrArg Subtype.val he))
    · intro d
      obtain ⟨e,he⟩ := h.boundaryCrossing_origin_complete a B d
      exact ⟨e,Subtype.ext he⟩)

theorem boundaryCrossingEquiv_val (d : SuffixCrossing t a) :
    (h.boundaryCrossingEquiv a B d).val=h.crossingOrigin d.val := rfl

/-- Relative order is derived from exact common offsets, without a rank gate. -/
theorem boundaryCrossing_visit_order (d e : SuffixCrossing t a) (i j : Fin 2) :
    visitPosition t.2.1 (t.1.incoming d.val i) < visitPosition t.2.1 (t.1.incoming e.val j) ↔
      visitPosition s.2.1 (s.1.incoming (h.crossingOrigin d.val) i) <
        visitPosition s.2.1 (s.1.incoming (h.crossingOrigin e.val) j) := by
  obtain ⟨k,hk,hko⟩ := h.boundaryCrossing_incoming_offset a B d i
  obtain ⟨l,hl,hlo⟩ := h.boundaryCrossing_incoming_offset a B e j
  rw [← hk,← hl,← hko,← hlo,markedSuffixArc_visitPosition,markedSuffixArc_visitPosition,
    h.boundaryOriginalArc_visitPosition a B k,h.boundaryOriginalArc_visitPosition a B l]
  omega

theorem boundaryCrossing_firstVisitedBranch (d : SuffixCrossing t a) :
    firstVisitedBranch t.2.1 d.val=firstVisitedBranch s.2.1 (h.crossingOrigin d.val) := by
  have he : rankBefore (visitRank t.2.1 (t.1.incoming d.val 0)) (visitRank t.2.1 (t.1.incoming d.val 1)) ↔
      rankBefore (visitRank s.2.1 (s.1.incoming (h.crossingOrigin d.val) 0))
        (visitRank s.2.1 (s.1.incoming (h.crossingOrigin d.val) 1)) := by
    rw [marked_rankBefore_iff t,marked_rankBefore_iff s]
    exact h.boundaryCrossing_visit_order a B d d 0 1
  unfold firstVisitedBranch
  rw [he]

theorem boundaryCrossing_incoming_not_marked (d : SuffixCrossing t a) (i : Fin 2) :
    t.1.incoming d.val i ∉ t.2.2.marks :=
  B.future_not_marked _ (d.property i)

theorem boundaryCrossing_overBranch (d : SuffixCrossing t a) :
    t.1.overBranch d.val=s.1.overBranch (h.crossingOrigin d.val) := by
  rcases h.crossingOrigin_over_or_marked d.val with he|⟨i,hi⟩
  · exact he
  · exact (h.boundaryCrossing_incoming_not_marked a B d i hi).elim

theorem boundaryCrossing_sign (d : SuffixCrossing t a) :
    crossingSign t.1 d.val=crossingSign s.1 (h.crossingOrigin d.val) := by
  rcases h.crossingOrigin_sign_or_marked d.val with he|⟨i,hi⟩
  · exact he
  · exact (h.boundaryCrossing_incoming_not_marked a B d i hi).elim

theorem boundaryCrossing_bad_iff (d : SuffixCrossing t a) :
    badAt t.2.1 d.val ↔ badAt s.2.1 (h.crossingOrigin d.val) := by
  unfold badAt
  rw [h.boundaryCrossing_firstVisitedBranch a B d,h.boundaryCrossing_overBranch a B d]

end MarkedParentTrace

/-- All remaining bad crossings are present in the actual boundary suffix. -/
def CursorBoundary.badSuffix {t : MarkedParentState} {a : Fin t.1.nArc}
    (B : CursorBoundary t (visitPosition t.2.1 a)) (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) :
    SuffixCrossing t a := ⟨c,B.badAfter c hc⟩



end DirectGLSSW.HOMFLY
