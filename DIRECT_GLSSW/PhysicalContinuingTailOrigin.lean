import MarkedGRecursion
import FutureCrossingEquivalence
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalParentHistory
open PermutationOrbits LowestRowContract ProcessedParentMarks MarkedG
attribute [local instance] Classical.propDecidable

variable {s t : MarkedParentState}

theorem arcOrigin_append (h : MarkedParentTrace s t) {u : MarkedParentState}
    (k : MarkedParentTrace t u) (e : Fin u.1.nArc) :
    (MarkedPolynomial.append h k).arcOrigin e = (k.arcOrigin e).bind h.arcOrigin := by
  induction h with
  | nil s => simp only [MarkedPolynomial.append,MarkedParentTrace.arcOrigin,Option.bind_some]
  | cons step tail ih =>
    change ((MarkedPolynomial.append tail k).arcOrigin e).bind step.arcOrigin = _
    rw [ih,Option.bind_assoc]
    rfl

def connector (t : MarkedParentState) (c : Fin t.1.nCrossing) :
    Fin (continuingRestriction t c).diagram.nArc :=
  liftConnector t.1 t.2.1 c (continuingRestriction t c)

def continuingTrace (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) :
    MarkedParentTrace s (continuingState t c hc hgood) :=
  MarkedPolynomial.append h (.cons (.smoothed t.2.2 c hc hgood (continuingRestriction t c))
    (.nil (continuingState t c hc hgood)))

def tailSize (t : MarkedParentState) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) : ℕ :=
  markedSuffixSize (continuingState t c hc hgood) (connector t c)-1

def tailArc (t : MarkedParentState) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c)
    (i : Fin (tailSize t c hc hgood)) : Fin (continuingState t c hc hgood).1.nArc :=
  markedSuffixArc (continuingState t c hc hgood) (connector t c)
    ⟨i.val+1,by have := i.isLt;unfold tailSize at this;omega⟩

/-- All actual processed marks are at or before the new continuing connector. -/
theorem mark_le_connector (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (hgood : GoodBefore t c) (e : Fin (continuingState t c hc hgood).1.nArc)
    (he : e ∈ (continuingState t c hc hgood).2.2.marks) :
    visitPosition (continuingState t c hc hgood).2.1 e ≤
      visitPosition (continuingState t c hc hgood).2.1 (connector t c) := by
  change e ∈ t.2.2.smoothedMarks c hc (continuingRestriction t c) at he
  rcases Finset.mem_insert.mp he with he | he
  · rw [he];exact le_refl _
  · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp he
    have hh := t.2.2.liftOldMark_before_connector c hc (continuingRestriction t c) x
    have hcomp : componentOf (continuingState t c hc hgood).1.continuation
        (t.2.2.liftOldMark c hc (continuingRestriction t c) x) =
        componentOf (continuingState t c hc hgood).1.continuation (connector t c) :=
      (componentOf_eq_iff _ _ _).mpr ((continuingState t c hc hgood).2.2.connected _ _)
    change rankBefore
      (visitRank (continuingState t c hc hgood).2.1
        (t.2.2.liftOldMark c hc (continuingRestriction t c) x))
      (visitRank (continuingState t c hc hgood).2.1 (connector t c)) at hh
    have hl : visitPosition (continuingState t c hc hgood).2.1
        (t.2.2.liftOldMark c hc (continuingRestriction t c) x) <
        visitPosition (continuingState t c hc hgood).2.1 (connector t c) := by
      simpa only [rankBefore,visitRank,hcomp,lt_self_iff_false,false_or,true_and] using hh
    exact le_of_lt hl

theorem tailArc_not_marked (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (hgood : GoodBefore t c) (i : Fin (tailSize t c hc hgood)) :
    tailArc t c hc hgood i ∉ (continuingState t c hc hgood).2.2.marks := by
  intro hm
  have hl := mark_le_connector c hc hgood _ hm
  unfold tailArc at hl
  rw [markedSuffixArc_visitPosition] at hl
  change visitPosition (continuingState t c hc hgood).2.1 (connector t c) + (i.val+1) ≤ _ at hl
  omega

theorem tail_has_origin (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) (i : Fin (tailSize t c hc hgood)) :
    ∃ a : Fin s.1.nArc,
      (continuingTrace h c hc hgood).arcOrigin (tailArc t c hc hgood i)=some a := by
  cases ho : (continuingTrace h c hc hgood).arcOrigin (tailArc t c hc hgood i) with
  | some a => exact ⟨a,rfl⟩
  | none => exact (tailArc_not_marked c hc hgood i
      ((continuingTrace h c hc hgood).arcOrigin_none_marked _ ho)).elim

def tailOriginalArc (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) (i : Fin (tailSize t c hc hgood)) :
    Fin s.1.nArc := Classical.choose (tail_has_origin h c hc hgood i)

theorem tailOriginalArc_spec (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) (i : Fin (tailSize t c hc hgood)) :
    (continuingTrace h c hc hgood).arcOrigin (tailArc t c hc hgood i)=
      some (tailOriginalArc h c hc hgood i) :=
  Classical.choose_spec (tail_has_origin h c hc hgood i)

/-- Literal old successor transport along the complete unprocessed parent tail. -/
theorem tailOriginalArc_successor (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c)
    (i j : Fin (tailSize t c hc hgood)) (hij : j.val=i.val+1) :
    s.1.continuation (tailOriginalArc h c hc hgood i)=tailOriginalArc h c hc hgood j := by
  apply (continuingTrace h c hc hgood).arcOrigin_continuation
    (tailArc t c hc hgood i) (tailArc t c hc hgood j)
    (tailOriginalArc h c hc hgood i) (tailOriginalArc h c hc hgood j)
  · unfold tailArc
    exact markedSuffixArc_successor _ _ _ _ (by dsimp;omega)
  · exact tailOriginalArc_spec h c hc hgood i
  · exact tailOriginalArc_spec h c hc hgood j
end DirectGLSSW.HOMFLY.PhysicalParentHistory
