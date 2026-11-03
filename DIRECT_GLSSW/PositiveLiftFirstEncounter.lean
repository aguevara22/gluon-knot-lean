import PolygonEventPLLinkDiagram
import PolygonPositiveDiagram
import DirectGLSSW.PolygonEvents
import DirectGLSSW.PolygonCrossings
import DirectGLSSW.SpinorGates
import DirectGLSSW.OrderedEventSuccessor

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge

open DirectGLSSW
open DirectGLSSW.HOMFLY.PolygonDrawing

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ)

/-- The lower-labelled visit precedes the upper-labelled visit in the exact
lexicographic key used by `polygonEventOrder`. -/
theorem polygonCrossing_lowerVisit_key_before_upperVisit
    (c : Cr q) :
    toLex (polygonEventKey q (Sum.inr (c, false))) <
      toLex (polygonEventKey q (Sum.inr (c, true))) := by
  rw [Prod.Lex.toLex_lt_toLex]
  left
  simpa [polygonEventKey, polygonEventEdge, crossingVisitEdge] using c.property.1

private theorem scalarSignValue_one_iff_pos (x : ℝ) (hx : x ≠ 0) :
    scalarSignValue x = 1 ↔ 0 < x := by
  constructor
  · intro h
    by_cases hn : x < 0
    · have hfalse : (-1 : ℚ) = 1 := by
        simpa [scalarSignValue, hx, hn] using h
      norm_num at hfalse
    · exact lt_of_le_of_ne (le_of_not_gt hn) hx.symm
  · intro hp
    simp [scalarSignValue, ne_of_gt hp, not_lt_of_gt hp]

private theorem scalarSignValue_neg_one_iff_neg (x : ℝ) (hx : x ≠ 0) :
    scalarSignValue x = -1 ↔ x < 0 := by
  constructor
  · intro h
    by_cases hp : 0 < x
    · have hfalse : (1 : ℚ) = -1 := by
        simpa [scalarSignValue, ne_of_gt hp, not_lt_of_gt hp] using h
      norm_num at hfalse
    · exact lt_of_le_of_ne (le_of_not_gt hp) hx
  · intro hn
    simp [scalarSignValue, hx, hn]

/-- The determinant sign is positive exactly when the canonical first
(lower-edge) visit is the positive-lift overstrand, and negative exactly when
it is under. -/
theorem polygonCrossing_firstVisit_overUnder_sign (hn : 3 ≤ n)
    (hgeneric : cyclicNoncollinear q) (c : Cr q) :
    (scalarSignValue (planarDet (cyclicTangent q c.val.1)
        (cyclicTangent q c.val.2)) = 1 ↔ crossingOver q c = c.val.1) ∧
    (scalarSignValue (planarDet (cyclicTangent q c.val.1)
        (cyclicTangent q c.val.2)) = -1 ↔ crossingUnder q c = c.val.1) := by
  let d := planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2)
  have hne : d ≠ 0 := crossing_transverse hn q hgeneric c
  have hedges : c.val.1 ≠ c.val.2 := crossing_edges_ne q c
  have hOver : crossingOver q c = c.val.1 ↔ 0 < d := by
    change (if 0 < d then c.val.1 else c.val.2) = c.val.1 ↔ 0 < d
    by_cases hp : 0 < d
    · simp [hp]
    · constructor
      · intro h
        have he : c.val.2 = c.val.1 := by simpa [hp] using h
        exact False.elim (hedges he.symm)
      · intro h
        exact False.elim (hp h)
  have hUnder : crossingUnder q c = c.val.1 ↔ d < 0 := by
    change (if 0 < d then c.val.2 else c.val.1) = c.val.1 ↔ d < 0
    by_cases hp : 0 < d
    · constructor
      · intro h
        have he : c.val.2 = c.val.1 := by simpa [hp] using h
        exact False.elim (hedges he.symm)
      · intro h
        exact False.elim (not_lt_of_ge (le_of_lt hp) h)
    · have hn' : d < 0 := lt_of_le_of_ne (le_of_not_gt hp) hne
      simp [hp, hn']

  constructor
  · rw [scalarSignValue_one_iff_pos d hne, hOver]
  · rw [scalarSignValue_neg_one_iff_neg d hne, hUnder]

end DirectGLSSW.HOMFLY.PolygonDrawingBridge
