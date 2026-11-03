import DirectGLSSW.HOMFLY.HOMFYSmoothingRegularDegree
import Mathlib.Tactic.Ring

namespace DirectGLSSW.HOMFLY

theorem smoothIncomingCutPoint_interior (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c) (i : Fin 2) :
    ∃ t, 0 < t ∧ t < 1 ∧
      incomingCutPoint D c ε i =
        DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource (D.incoming c i)))
          (smoothingCenter D c) t := by
  have hε1 : ε < 1 := lt_of_lt_of_le hεr (min_le_left 1 _)
  refine ⟨1 - ε, by linarith, by linarith, ?_⟩
  apply Prod.ext <;>
    simp [incomingCutPoint, smoothingCenter, strandTangent, DirectGLSSW.affinePoint,
      D.incoming_target, smul_eq_mul] <;> ring

theorem smoothOutgoingCutPoint_interior (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε < crossingCutoffRadius D c) (i : Fin 2) :
    ∃ t, 0 < t ∧ t < 1 ∧
      outgoingCutPoint D c ε i =
        DirectGLSSW.affinePoint (smoothingCenter D c)
          (D.vertexPoint (D.arcTarget (D.outgoing c (D.through c i)))) t := by
  let s := outgoingTangentScale D c i
  have hs : 0 < s := outgoingTangentScale_pos D c i
  have hεinv : ε < 1 / s := by
    have hle : crossingCutoffRadius D c ≤ 1 / s := by
      fin_cases i
      · change min 1 (min (1 / outgoingTangentScale D c 0)
          (1 / outgoingTangentScale D c 1)) ≤ 1 / outgoingTangentScale D c 0
        exact le_trans (min_le_right (1 : ℝ) _) (min_le_left _ _)
      · change min 1 (min (1 / outgoingTangentScale D c 0)
          (1 / outgoingTangentScale D c 1)) ≤ 1 / outgoingTangentScale D c 1
        exact le_trans (min_le_right (1 : ℝ) _) (min_le_right _ _)
    exact lt_of_lt_of_le hεr hle
  have hεs : ε * s < 1 := (lt_div_iff₀ hs).mp hεinv
  refine ⟨ε * s, mul_pos hε hs, hεs, ?_⟩
  have hspec := outgoingTangentScale_spec D c i
  rw [outgoingCutPoint, hspec]
  apply Prod.ext <;>
    simp [s, smoothingCenter, DirectGLSSW.affinePoint, smul_eq_mul] <;> ring

end DirectGLSSW.HOMFLY
