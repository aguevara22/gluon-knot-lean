import HistoricalChildOffsetWord
import ActualTerminalFramedValue
import FirstChildEvaluatorZero
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PolygonDrawingBridge
open DirectGLSSW Coefficients LowestRowContract PrincipalTurning PermutationOrbits SmoothingCornerGeometry

theorem pointWord_eq_of_ofFn_eq {m n : ℕ}
    (p : Fin m → PlanarPoint ℝ) (q : Fin n → PlanarPoint ℝ)
    (hw : List.ofFn p = List.ofFn q) :
    ∃ hn : m=n, ∀ i, p i = q (Fin.cast hn i) := by
  have hn : m=n := by simpa only [List.length_ofFn] using congrArg List.length hw
  subst n
  refine ⟨rfl,?_⟩
  intro i
  have hh := congrArg (fun l : List (PlanarPoint ℝ) => l[i.val]?) hw
  simpa using hh

theorem cyclicGeneric_of_pointWord_eq {m n : ℕ}
    (p : Fin m → PlanarPoint ℝ) (hp : CyclicGeneric p)
    (q : Fin n → PlanarPoint ℝ) (hw : List.ofFn p = List.ofFn q) :
    CyclicGeneric q := by
  obtain ⟨hn,hh⟩ := pointWord_eq_of_ofFn_eq p q hw
  subst n
  have he : p=q := by funext i; exact hh i
  subst q
  exact hp

/-- Literal point-word equality preserves the existing prescribed HOMFLY
corner coefficient, including its actual count and integer-turn exponent. -/
theorem prescribed_corner_of_pointWord_eq {m n : ℕ}
    (p : Fin m → PlanarPoint ℝ) (hp : CyclicGeneric p)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hw : List.ofFn p = List.ofFn q) :
    coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram p hp)
      (positivePolygonEventDiagram_nArc_pos p hp))
      (1-((positivePolygonEventDiagram p hp).nCrossing : ℤ)-
        |turnInteger (positivePolygonEventDiagram p hp)|) 0 =
    coeff (Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
      (positivePolygonEventDiagram_nArc_pos q hq))
      (1-((positivePolygonEventDiagram q hq).nCrossing : ℤ)-
        |turnInteger (positivePolygonEventDiagram q hq)|) 0 := by
  obtain ⟨hn,hh⟩ := pointWord_eq_of_ofFn_eq p q hw
  subst n
  have he : p=q := by funext i; exact hh i
  subst q
  rfl

theorem framed_row_of_pointWord_eq {m n : ℕ}
    (p : Fin m → PlanarPoint ℝ) (hp : CyclicGeneric p)
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hw : List.ofFn p = List.ofFn q) :
    framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram p hp)
      (positivePolygonEventDiagram_nArc_pos p hp)
      (componentOf (positivePolygonEventDiagram p hp).continuation
        ⟨0,positivePolygonEventDiagram_nArc_pos p hp⟩) =
    framedKnotRow Gemini.candidateEvaluator (positivePolygonEventDiagram q hq)
      (positivePolygonEventDiagram_nArc_pos q hq)
      (componentOf (positivePolygonEventDiagram q hq).continuation
        ⟨0,positivePolygonEventDiagram_nArc_pos q hq⟩) := by
  obtain ⟨hn,hh⟩ := pointWord_eq_of_ofFn_eq p q hw
  subst n
  have he : p=q := by funext i; exact hh i
  subst q
  rfl
end DirectGLSSW.HOMFLY.PolygonDrawingBridge
