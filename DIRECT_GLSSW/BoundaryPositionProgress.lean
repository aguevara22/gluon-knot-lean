import BoundaryOriginalTail
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.MarkedParentTrace
open PermutationOrbits
variable {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (a : Fin t.1.nArc) (B : CursorBoundary t (visitPosition t.2.1 a))

/-- Original and actual suffix positions differ by the fixed boundary offset. -/
theorem boundary_position_offset (e : Fin t.1.nArc) (E : Fin s.1.nArc)
    (he : visitPosition t.2.1 a ≤ visitPosition t.2.1 e)
    (hE : h.arcOrigin e=some E) :
    visitPosition t.2.1 e + visitPosition s.2.1 (h.boundaryOrigin a B) =
      visitPosition t.2.1 a + visitPosition s.2.1 E := by
  obtain ⟨i,hi⟩ := (markedSuffixArc_range t a e).mpr he
  have hs := h.boundaryOriginalArc_spec a B i
  rw [hi,hE] at hs
  have ho := (Option.some.inj hs).symm
  rw [← hi,← ho,markedSuffixArc_visitPosition,h.boundaryOriginalArc_visitPosition a B i]
  omega

/-- Any requested original future arc has an actual future representative,
constructed from complete ancestry rather than assumed in a state package. -/
theorem exists_boundary_arc_of_original (E : Fin s.1.nArc)
    (hE : visitPosition s.2.1 (h.boundaryOrigin a B) ≤ visitPosition s.2.1 E) :
    ∃ e : Fin t.1.nArc, h.arcOrigin e=some E ∧
      visitPosition t.2.1 a ≤ visitPosition t.2.1 e := by
  obtain ⟨i,hi⟩ := (h.boundaryOriginalArc_range a B E).mpr hE
  refine ⟨markedSuffixArc t a i,?_,?_⟩
  · rw [h.boundaryOriginalArc_spec a B i,hi]
  · rw [markedSuffixArc_visitPosition]
    omega
end DirectGLSSW.HOMFLY.MarkedParentTrace
