import DirectGLSSW.HOMFLY.PLDiagrams

/-!
# Positive overstrand selection for finite PL diagrams

This separate construction selects the overstrand that makes the oriented
crossing determinant positive. The general `PLLinkDiagram.overBranch` remains
arbitrary so switched diagrams remain representable.
-/

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

open DirectGLSSW

/-- Select the first incoming strand when its ordered determinant is positive;
otherwise select the second. Transversality excludes the zero case. -/
noncomputable def positiveOverBranch (D : PLLinkDiagram) (c : Fin D.nCrossing) : Fin 2 :=
  if 0 < planarDet (strandTangent D c 0) (strandTangent D c 1) then 0 else 1

/-- Retain the given drawing and continuation while choosing the positive
overstrand independently at every crossing. -/
noncomputable def positiveDiagram (D : PLLinkDiagram) : PLLinkDiagram :=
  { D with overBranch := positiveOverBranch D }

theorem positiveOverBranch_determinant_pos (D : PLLinkDiagram)
    (c : Fin D.nCrossing) :
    0 < planarDet (strandTangent D c (positiveOverBranch D c))
      (strandTangent D c (otherBranch (positiveOverBranch D c))) := by
  by_cases h : 0 < planarDet (strandTangent D c 0) (strandTangent D c 1)
  · simpa [positiveOverBranch, h, otherBranch_zero] using h
  · have hne := D.crossing_transverse c
    have hneg : planarDet (strandTangent D c 0) (strandTangent D c 1) < 0 :=
      lt_of_le_of_ne (le_of_not_gt h) hne
    have hswap : planarDet (strandTangent D c 1) (strandTangent D c 0) =
        -planarDet (strandTangent D c 0) (strandTangent D c 1) :=
      planarDet_swap _ _
    have hpos : 0 < planarDet (strandTangent D c 1) (strandTangent D c 0) := by
      rw [hswap]
      linarith
    simpa [positiveOverBranch, h, otherBranch_one] using hpos

/-- Every crossing determinant of the positive diagram is strictly positive. -/
theorem positiveDiagram_crossingDet_pos (D : PLLinkDiagram)
    (c : Fin D.nCrossing) :
    0 < crossingDet (positiveDiagram D) c := by
  simpa [crossingDet, positiveDiagram, strandTangent] using
    positiveOverBranch_determinant_pos D c

/-- The induced exact crossing sign is positive at every crossing. -/
theorem positiveDiagram_crossingSign (D : PLLinkDiagram)
    (c : Fin D.nCrossing) :
    crossingSign (positiveDiagram D) c = Sign.pos := by
  have h := positiveDiagram_crossingDet_pos D c
  unfold crossingSign nonzeroScalarSign
  rw [if_neg (not_lt_of_gt h)]

theorem positiveDiagram_overBranch (D : PLLinkDiagram) :
    (positiveDiagram D).overBranch = positiveOverBranch D := rfl

/-- The positive-choice construction changes only the over-branch field. -/
theorem positiveDiagram_preserves_drawing_and_continuation (D : PLLinkDiagram) :
    (positiveDiagram D).vertexPoint = D.vertexPoint ∧
    (positiveDiagram D).arcSource = D.arcSource ∧
    (positiveDiagram D).arcTarget = D.arcTarget ∧
    (positiveDiagram D).crossingVertex = D.crossingVertex ∧
    (positiveDiagram D).incoming = D.incoming ∧
    (positiveDiagram D).outgoing = D.outgoing ∧
    (positiveDiagram D).through = D.through ∧
    (positiveDiagram D).continuation = D.continuation := by
  simp [positiveDiagram]

theorem positiveDiagram_components (D : PLLinkDiagram) :
    diagramComponent (positiveDiagram D) = diagramComponent D := rfl

theorem positiveDiagram_componentCount (D : PLLinkDiagram) :
    diagramComponentCount (positiveDiagram D) = diagramComponentCount D := rfl

end DirectGLSSW.HOMFLY
