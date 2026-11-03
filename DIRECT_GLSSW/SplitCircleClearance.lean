import DirectGLSSW.HOMFLY.PLDiagrams
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.SplitCircleConstructor
open DirectGLSSW

theorem affine_x_lt {a b : PlanarPoint ℝ} {R t : ℝ}
    (ha : a.1 < R) (hb : b.1 < R) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (affinePoint a b t).1 < R := by
  change a.1 + t * (b.1 - a.1) < R
  by_cases ht : t = 1
  · subst t
    norm_num
    linarith
  · have hlt : t < 1 := lt_of_le_of_ne ht1 ht
    have hpos : 0 < (1 - t) * (R - a.1) :=
      mul_pos (by linarith) (by linarith)
    have hnonneg : 0 ≤ t * (R - b.1) :=
      mul_nonneg ht0 (by linarith)
    nlinarith

theorem affine_x_gt {a b : PlanarPoint ℝ} {R t : ℝ}
    (ha : R < a.1) (hb : R < b.1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    R < (affinePoint a b t).1 := by
  change R < a.1 + t * (b.1 - a.1)
  by_cases ht : t = 1
  · subst t
    norm_num
    linarith
  · have hlt : t < 1 := lt_of_le_of_ne ht1 ht
    have hpos : 0 < (1 - t) * (a.1 - R) :=
      mul_pos (by linarith) (by linarith)
    have hnonneg : 0 ≤ t * (b.1 - R) :=
      mul_nonneg ht0 (by linarith)
    nlinarith

/-- Place every triangle point and its straight edges to the right of all
original vertices and straight edges. The bound depends on the actual input
diagram and assumes only its positive arc count. -/
theorem exists_right_triangle_clearance (D : PLLinkDiagram) (hD : 0 < D.nArc) :
    ∃ R : ℝ,
      (∀ v : Fin D.nVertex, (D.vertexPoint v).1 < R) ∧
      (∀ e : Fin D.nArc, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        (affinePoint (D.vertexPoint (D.arcSource e))
          (D.vertexPoint (D.arcTarget e)) t).1 < R) ∧
      (∀ v : Fin triangleUnknot.nVertex,
        R < ((R + 1 + (triangleUnknot.vertexPoint v).1))) ∧
      (∀ e : Fin triangleUnknot.nArc, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        R < (affinePoint
          (R + 1 + (triangleUnknot.vertexPoint (triangleUnknot.arcSource e)).1,
            (triangleUnknot.vertexPoint (triangleUnknot.arcSource e)).2)
          (R + 1 + (triangleUnknot.vertexPoint (triangleUnknot.arcTarget e)).1,
            (triangleUnknot.vertexPoint (triangleUnknot.arcTarget e)).2) t).1) := by
  classical
  let v0 : Fin D.nVertex := D.arcSource ⟨0, hD⟩
  have hnonempty : (Finset.univ : Finset (Fin D.nVertex)).Nonempty :=
    ⟨v0, Finset.mem_univ _⟩
  let M : ℝ := (Finset.univ : Finset (Fin D.nVertex)).sup' hnonempty
    (fun v => (D.vertexPoint v).1)
  let R := M + 1
  have htri : ∀ v : Fin triangleUnknot.nVertex,
      0 ≤ (triangleUnknot.vertexPoint v).1 := by
    intro v
    fin_cases v <;>
      (first | change (0 : ℝ) ≤ 0 | change (0 : ℝ) ≤ 1) <;> norm_num
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · intro v
    have hv : (D.vertexPoint v).1 ≤ M :=
      Finset.le_sup' (fun w : Fin D.nVertex => (D.vertexPoint w).1) (Finset.mem_univ v)
    dsimp [R]
    linarith
  · intro e t ht0 ht1
    exact affine_x_lt
      (by have hv : (D.vertexPoint (D.arcSource e)).1 ≤ M :=
            Finset.le_sup' (fun w : Fin D.nVertex => (D.vertexPoint w).1) (Finset.mem_univ _)
          dsimp [R]; linarith)
      (by have hv : (D.vertexPoint (D.arcTarget e)).1 ≤ M :=
            Finset.le_sup' (fun w : Fin D.nVertex => (D.vertexPoint w).1) (Finset.mem_univ _)
          dsimp [R]; linarith) ht0 ht1
  · intro v
    have hv := htri v
    linarith
  · intro e t ht0 ht1
    apply affine_x_gt _ _ ht0 ht1
    · have hv := htri (triangleUnknot.arcSource e)
      change R < R + 1 + (triangleUnknot.vertexPoint (triangleUnknot.arcSource e)).1
      linarith
    · have hv := htri (triangleUnknot.arcTarget e)
      change R < R + 1 + (triangleUnknot.vertexPoint (triangleUnknot.arcTarget e)).1
      linarith

end DirectGLSSW.HOMFLY.SplitCircleConstructor

