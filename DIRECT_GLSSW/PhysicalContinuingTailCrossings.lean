import PhysicalContinuingTailOrder
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalParentHistory
open PermutationOrbits LowestRowContract ProcessedParentMarks MarkedG
attribute [local instance] Classical.propDecidable
variable {s t : MarkedParentState}

def StrictFutureCrossing (s : MarkedParentState) (e : Fin s.1.nArc) :=
  {d : Fin s.1.nCrossing // ∀ i : Fin 2,
    visitPosition s.2.1 e < visitPosition s.2.1 (s.1.incoming d i)}

theorem tailArc_range (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c) (hgood : GoodBefore t c)
    (e : Fin (continuingState t c hc hgood).1.nArc) :
    (∃ i,tailArc t c hc hgood i=e) ↔
      visitPosition (continuingState t c hc hgood).2.1 (connector t c) <
      visitPosition (continuingState t c hc hgood).2.1 e := by
  constructor
  · rintro ⟨i,rfl⟩
    unfold tailArc
    rw [markedSuffixArc_visitPosition]
    change _ < _+(i.val+1)
    omega
  · intro hlt
    obtain ⟨i,hi⟩ := (markedSuffixArc_range (continuingState t c hc hgood) (connector t c) e).mpr (le_of_lt hlt)
    have hp := markedSuffixArc_visitPosition (continuingState t c hc hgood) (connector t c) i
    rw [hi] at hp
    have hip : (0 : Nat) < (i.val : Nat) := by omega
    let j : Fin (tailSize t c hc hgood) := ⟨i.val-1,by have := i.isLt;unfold tailSize;omega⟩
    refine ⟨j,?_⟩
    unfold tailArc
    convert hi using 2
    apply Fin.ext
    change i.val-1+1=i.val
    omega

/-- Exact old-label offsets of every actual future parent crossing port. -/
theorem tailCrossing_incoming_offset (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c)
    (d : StrictFutureCrossing (continuingState t c hc hgood) (connector t c)) (i : Fin 2) :
    ∃ k : Fin (tailSize t c hc hgood),
      tailArc t c hc hgood k=(continuingState t c hc hgood).1.incoming d.val i ∧
      tailOriginalArc h c hc hgood k =
        s.1.incoming ((continuingTrace h c hc hgood).crossingOrigin d.val) i := by
  obtain ⟨k,hk⟩ := (tailArc_range c hc hgood _).mpr (d.property i)
  refine ⟨k,hk,?_⟩
  have hs := tailOriginalArc_spec h c hc hgood k
  rw [hk,(continuingTrace h c hc hgood).crossingOrigin_incoming] at hs
  exact (Option.some.inj hs).symm

theorem tailCrossing_origin_mem (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c)
    (d : StrictFutureCrossing (continuingState t c hc hgood) (connector t c)) :
    ∀ i : Fin 2,
      visitPosition s.2.1 (s.1.incoming (h.crossingOrigin c) (otherBranch (firstVisitedBranch t.2.1 c))) <
      visitPosition s.2.1 (s.1.incoming ((continuingTrace h c hc hgood).crossingOrigin d.val) i) := by
  intro i
  obtain ⟨k,_,hk⟩ := tailCrossing_incoming_offset h c hc hgood d i
  exact (tailOriginalArc_range h c hc hgood _).mp ⟨k,hk⟩

/-- Every original crossing strictly after the second cut port survives in the
actual continuing state, with both incoming ports in its unprocessed tail. -/
theorem tailCrossing_origin_complete (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c)
    (d : StrictFutureCrossing s
      (s.1.incoming (h.crossingOrigin c) (otherBranch (firstVisitedBranch t.2.1 c)))) :
    ∃ e : StrictFutureCrossing (continuingState t c hc hgood) (connector t c),
      (continuingTrace h c hc hgood).crossingOrigin e.val=d.val := by
  have hports : ∀ i : Fin 2, ∃ k : Fin (tailSize t c hc hgood),
      tailOriginalArc h c hc hgood k=s.1.incoming d.val i := by
    intro i
    exact (tailOriginalArc_range h c hc hgood _).mpr (d.property i)
  obtain ⟨e,he⟩ := (continuingTrace h c hc hgood).crossingOrigin_complete d.val (by
    intro i
    obtain ⟨k,hk⟩ := hports i
    refine ⟨tailArc t c hc hgood k,?_⟩
    rw [tailOriginalArc_spec,hk])
  have hef : ∀ i : Fin 2,
      visitPosition (continuingState t c hc hgood).2.1 (connector t c) <
      visitPosition (continuingState t c hc hgood).2.1
        ((continuingState t c hc hgood).1.incoming e i) := by
    intro i
    obtain ⟨k,hk⟩ := hports i
    have ho := tailOriginalArc_spec h c hc hgood k
    rw [hk] at ho
    have hi := (continuingTrace h c hc hgood).crossingOrigin_incoming e i
    rw [he] at hi
    have heq := (continuingTrace h c hc hgood).arcOrigin_some_injective _ _ _ ho hi
    exact (tailArc_range c hc hgood _).mp ⟨k,heq⟩
  exact ⟨⟨e,hef⟩,he⟩

/-- Canonical continuing-parent future crossing equivalence. History, old roots,
processed switches and framing remain in the actual state; no closed active arc is substituted. -/
def continuingFutureCrossingEquiv (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c) :
    StrictFutureCrossing (continuingState t c hc hgood) (connector t c) ≃
      StrictFutureCrossing s
        (s.1.incoming (h.crossingOrigin c) (otherBranch (firstVisitedBranch t.2.1 c))) :=
  Equiv.ofBijective
    (fun d => ⟨(continuingTrace h c hc hgood).crossingOrigin d.val,
      tailCrossing_origin_mem h c hc hgood d⟩) (by
      constructor
      · intro d e he
        exact Subtype.ext ((continuingTrace h c hc hgood).crossingOrigin.injective (congrArg Subtype.val he))
      · intro d
        obtain ⟨e,he⟩ := tailCrossing_origin_complete h c hc hgood d
        exact ⟨e,Subtype.ext he⟩)

/-- Exact occurrence order for all matched future crossing incoming ports. -/
theorem continuingFutureCrossing_incoming_order (h : MarkedParentTrace s t) (c : Fin t.1.nCrossing)
    (hc : badAt t.2.1 c) (hgood : GoodBefore t c)
    (d e : StrictFutureCrossing (continuingState t c hc hgood) (connector t c)) (i j : Fin 2) :
    visitPosition (continuingState t c hc hgood).2.1 ((continuingState t c hc hgood).1.incoming d.val i) <
      visitPosition (continuingState t c hc hgood).2.1 ((continuingState t c hc hgood).1.incoming e.val j) ↔
    visitPosition s.2.1 (s.1.incoming ((continuingFutureCrossingEquiv h c hc hgood) d).val i) <
      visitPosition s.2.1 (s.1.incoming ((continuingFutureCrossingEquiv h c hc hgood) e).val j) := by
  obtain ⟨k,hk,hok⟩ := tailCrossing_incoming_offset h c hc hgood d i
  obtain ⟨l,hl,hol⟩ := tailCrossing_incoming_offset h c hc hgood e j
  change _ ↔ visitPosition s.2.1 (s.1.incoming ((continuingTrace h c hc hgood).crossingOrigin d.val) i) <
    visitPosition s.2.1 (s.1.incoming ((continuingTrace h c hc hgood).crossingOrigin e.val) j)
  rw [← hk,← hl,← hok,← hol,tailOriginalArc_visitPosition,tailOriginalArc_visitPosition]
  unfold tailArc
  rw [markedSuffixArc_visitPosition,markedSuffixArc_visitPosition]
  change (_+(k.val+1) < _+(l.val+1)) ↔ _
  omega
end DirectGLSSW.HOMFLY.PhysicalParentHistory
