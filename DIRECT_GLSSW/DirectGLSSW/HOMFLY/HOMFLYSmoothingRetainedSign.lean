import DirectGLSSW.HOMFLY.HOMFYSmoothingDiagram
import DirectGLSSW.HOMFLY.HOMFYSmoothingOtherCrossingTangent
import DirectGLSSW.HOMFLY.HOMFYSmoothingTraversalBridge
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

private theorem crossingVertex_ne_selected {D : PLLinkDiagram}
    {c d : Fin D.nCrossing} (hd : d ≠ c) :
    D.crossingVertex d ≠ D.crossingVertex c := by
  intro h
  exact hd (D.crossingVertex_injective h)

/-- Each retained incoming tangent changes only by a positive scalar when a
crossing is smoothed. This is the geometric reason retained crossing signs
are preserved by the concrete child construction. -/
theorem smoothRetained_strandTangent_positive_multiple (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hd : d ≠ c) (i : Fin 2) :
    ∃ α : ℝ, 0 < α ∧
      strandTangent (smoothCrossing D c)
          (smoothCrossingEquiv D c ⟨d, hd⟩) i =
        α • strandTangent D d i := by
  let d' := smoothCrossingEquiv D c ⟨d, hd⟩
  have hgeom := smoothIncomingSourceVector_positive_multiple D c d i
    (smoothEpsilon D c) (smoothEpsilon_pos D c)
    (lt_of_lt_of_le (smoothEpsilon_lt_radius D c) (smoothRadius_le_cutoff D c)) hd
  rcases hgeom with ⟨α, hα, hvec⟩
  refine ⟨α, hα, ?_⟩
  have hcv : D.crossingVertex d ≠ D.crossingVertex c := crossingVertex_ne_selected hd
  simpa [d', strandTangent, smoothCrossing, smoothCrossingVertex, smoothVertexPoint,
    smoothIncoming, smoothArcSource, Equiv.symm_apply_apply,
    smoothVertexPointGeometryCode, hcv] using hvec

private theorem planarDet_smul_smul (α β : ℝ) (u v : PlanarPoint ℝ) :
    planarDet (α • u) (β • v) = (α * β) * planarDet u v := by
  simp [planarDet, smul_eq_mul]
  ring

/-- The determinant at any retained crossing has the same sign after
smoothing a distinct site, because both ordered tangents are rescaled by
positive factors. -/
theorem crossingSign_smoothRetained (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) (hd : d ≠ c) :
    crossingSign (smoothCrossing D c) (smoothCrossingEquiv D c ⟨d, hd⟩) =
      crossingSign D d := by
  let d' := smoothCrossingEquiv D c ⟨d, hd⟩
  let i := D.overBranch d
  let j := otherBranch i
  obtain ⟨α, hα, htα⟩ := smoothRetained_strandTangent_positive_multiple D c d hd i
  obtain ⟨β, hβ, htβ⟩ := smoothRetained_strandTangent_positive_multiple D c d hd j
  have hover : (smoothCrossing D c).overBranch d' = D.overBranch d := by
    simp [d', smoothCrossing]
  have hdet : crossingDet (smoothCrossing D c) d' =
      (α * β) * crossingDet D d := by
    unfold crossingDet
    rw [hover]
    change planarDet (strandTangent (smoothCrossing D c) d' i)
        (strandTangent (smoothCrossing D c) d' j) =
      (α * β) * planarDet (strandTangent D d i) (strandTangent D d j)
    rw [htα, htβ, planarDet_smul_smul]
  have hscale : 0 < α * β := mul_pos hα hβ
  have hnew : crossingDet (smoothCrossing D c) d' ≠ 0 :=
    selectedDet_ne_zero (smoothCrossing D c) d'
  have hold : crossingDet D d ≠ 0 := selectedDet_ne_zero D d
  by_cases hneg : crossingDet D d < 0
  · have hnewneg : crossingDet (smoothCrossing D c) d' < 0 := by
      rw [hdet]
      exact mul_neg_of_pos_of_neg hscale hneg
    unfold crossingSign nonzeroScalarSign
    rw [if_pos hnewneg, if_pos hneg]
  · have hpos : 0 < crossingDet D d := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hold)
    have hnewpos : 0 < crossingDet (smoothCrossing D c) d' := by
      rw [hdet]
      exact mul_pos hscale hpos
    have hnewneg : ¬ crossingDet (smoothCrossing D c) d' < 0 := not_lt_of_gt hnewpos
    unfold crossingSign nonzeroScalarSign
    rw [if_neg hnewneg, if_neg hneg]




end DirectGLSSW.HOMFLY
