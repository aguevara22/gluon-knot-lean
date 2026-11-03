import OriginalSuffixSurjective
import ProcessedCrossingCompleteness
import ProcessedCrossingDataTrace
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits
attribute [local instance] Classical.propDecidable

/-- Literal crossing carrier with both incoming ports in the specified actual
rooted suffix. This does not yet assert identification with an ActiveArc. -/
def SuffixCrossing (t : MarkedParentState) (a : Fin t.1.nArc) :=
  {d : Fin t.1.nCrossing // ∀ i : Fin 2,
    visitPosition t.2.1 a ≤ visitPosition t.2.1 (t.1.incoming d i)}

namespace MarkedParentTrace
variable {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
include h c hc

/-- Each future incoming port has the exact same suffix offset in the current
and original diagrams. Neither rank transport nor branch order is supplied. -/
theorem suffixCrossing_incoming_offset
    (d : SuffixCrossing t (t.1.incoming c (firstVisitedBranch t.2.1 c))) (i : Fin 2) :
    ∃ k : Fin (markedSuffixSize t (t.1.incoming c (firstVisitedBranch t.2.1 c))),
      markedSuffixArc t (t.1.incoming c (firstVisitedBranch t.2.1 c)) k = t.1.incoming d.val i ∧
      h.suffixOriginalArc c hc k = s.1.incoming (h.crossingOrigin d.val) i := by
  obtain ⟨k,hk⟩ := (markedSuffixArc_range t _ (t.1.incoming d.val i)).mpr (d.property i)
  refine ⟨k,hk,?_⟩
  have hh := h.suffixOriginalArc_spec c hc k
  rw [hk,h.crossingOrigin_incoming] at hh
  exact (Option.some.inj hh).symm

theorem suffixCrossing_origin_mem
    (d : SuffixCrossing t (t.1.incoming c (firstVisitedBranch t.2.1 c))) :
    ∀ i : Fin 2,
      visitPosition s.2.1 (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) ≤
        visitPosition s.2.1 (s.1.incoming (h.crossingOrigin d.val) i) := by
  intro i
  obtain ⟨k,hk,ho⟩ := h.suffixCrossing_incoming_offset c hc d i
  exact (h.suffixOriginalArc_range c hc _).mp ⟨k,ho⟩

/-- Every original two-port suffix crossing still occurs in the actual current
diagram and both of its incoming ports occur in the current suffix. -/
theorem suffixCrossing_origin_complete
    (d : SuffixCrossing s (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c))) :
    ∃ e : SuffixCrossing t (t.1.incoming c (firstVisitedBranch t.2.1 c)), h.crossingOrigin e.val = d.val := by
  have hports : ∀ i : Fin 2, ∃ e : Fin t.1.nArc,
      h.arcOrigin e = some (s.1.incoming d.val i) ∧
      visitPosition t.2.1 (t.1.incoming c (firstVisitedBranch t.2.1 c)) ≤ visitPosition t.2.1 e := by
    intro i
    obtain ⟨k,hk⟩ := (h.suffixOriginalArc_range c hc (s.1.incoming d.val i)).mpr (d.property i)
    refine ⟨markedSuffixArc t (t.1.incoming c (firstVisitedBranch t.2.1 c)) k,?_,?_⟩
    · rw [h.suffixOriginalArc_spec c hc k,hk]
    · rw [markedSuffixArc_visitPosition];omega
  obtain ⟨e,he⟩ := h.crossingOrigin_complete d.val (by
    intro i
    obtain ⟨a,ha,_⟩ := hports i
    exact ⟨a,ha⟩)
  have hef : ∀ i : Fin 2,
      visitPosition t.2.1 (t.1.incoming c (firstVisitedBranch t.2.1 c)) ≤ visitPosition t.2.1 (t.1.incoming e i) := by
    intro i
    obtain ⟨a,ha,hle⟩ := hports i
    have hi := h.crossingOrigin_incoming e i
    rw [he] at hi
    have heq := h.arcOrigin_some_injective a (t.1.incoming e i) _ ha hi
    exact heq ▸ hle
  exact ⟨⟨e,hef⟩,he⟩

/-- Exact equivalence of the two actual suffix crossing carriers. -/
def suffixCrossingEquiv :
    SuffixCrossing t (t.1.incoming c (firstVisitedBranch t.2.1 c)) ≃
      SuffixCrossing s (s.1.incoming (h.crossingOrigin c) (firstVisitedBranch t.2.1 c)) :=
  Equiv.ofBijective (fun d => ⟨h.crossingOrigin d.val,h.suffixCrossing_origin_mem c hc d⟩) (by
    constructor
    · intro d e he
      exact Subtype.ext (h.crossingOrigin.injective (congrArg Subtype.val he))
    · intro d
      obtain ⟨e,he⟩ := h.suffixCrossing_origin_complete c hc d
      exact ⟨e,Subtype.ext he⟩)

theorem suffixCrossingEquiv_val
    (d : SuffixCrossing t (t.1.incoming c (firstVisitedBranch t.2.1 c))) :
    (h.suffixCrossingEquiv c hc d).val = h.crossingOrigin d.val := rfl

end MarkedParentTrace
end DirectGLSSW.HOMFLY
