import DirectGLSSW.TruncationDaughterUniform
import DirectGLSSW.TruncationComponentWeights
import DirectGLSSW.GeometricSmoothingSumTransport

set_option autoImplicit false

namespace DirectGLSSW.TruncationSeparatingSum

open TruncationDirection TruncationEdgeLift GeometricSmoothingWeights

theorem exists_leftCorner_truncation_separating_sum
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hAux : auxiliaryGenericity q hq)
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (q a - q p) (q (cyclicSuccessor a) - q a)) :
    ∃ scale : ℝ, 0 < scale ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ε < 1 ∧ ε * scale < 1 ∧
        ∃ ht : CyclicGeneric (truncateCyclicCorner q a p scale ε),
        ∃ hAuxt : auxiliaryGenericity (truncateCyclicCorner q a p scale ε) ht,
          polygonAmplitude (truncateCyclicCorner q a p scale ε) ht =
            -polygonAmplitude q hq ∧
          separatingSmoothingSum (truncateCyclicCorner q a p scale ε) ht hAuxt =
            -separatingSmoothingSum q hq hAux ∧
          (-1 : ℚ) ^ (n + 1) * polygonAmplitude (truncateCyclicCorner q a p scale ε) ht =
            (-1 : ℚ) ^ n * polygonAmplitude q hq ∧
          (-1 : ℚ) ^ (n + 1) * separatingSmoothingSum (truncateCyclicCorner q a p scale ε) ht hAuxt =
            (-1 : ℚ) ^ n * separatingSmoothingSum q hq hAux
 := by
  classical
  obtain ⟨scale, hscale, δ, hδ, hgood⟩ :=
    TruncationDaughterUniform.exists_leftCorner_truncation_all_affected_amplitudes
      hRI q hq a p hp hturn (fun S hS => hAux S hS (Sum.inl a))
  refine ⟨scale, hscale, δ, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨hε1, hεscale1, ht, hamp, E, hlabels, hpoint, hsep, hAffected⟩ := hgood ε hε hεδ
  have hleft (c : PolygonCrossing q) : (E c).val.1 = edgeLift a c.val.1 := congrArg Prod.fst (hlabels c)
  have hright (c : PolygonCrossing q) : (E c).val.2 = edgeLift a c.val.2 := congrArg Prod.snd (hlabels c)
  have hAuxt : auxiliaryGenericity (truncateCyclicCorner q a p scale ε) ht :=
    TruncationDaughterGenericity.auxiliaryGenericity_transport q hq a p hp scale ε
      hε hε1 (mul_pos hε hscale) hεscale1 ht E hleft hright hpoint hAux
      (fun S hS => (hAffected S hS).choose)
  have hsum : separatingSmoothingSum (truncateCyclicCorner q a p scale ε) ht hAuxt =
      -separatingSmoothingSum q hq hAux := by
    apply GeometricSmoothingSumTransport.separatingSmoothingSum_transport_neg
      q hq (truncateCyclicCorner q a p scale ε) ht E hsep hAux hAuxt
    intro S hS
    exact TruncationComponentWeights.componentAmplitudeProduct_truncation
      hRI q hq a p hp scale ε hε hε1 (mul_pos hε hscale) hεscale1 ht E hleft hright hpoint
      hAux hAuxt S hS ((hsep S).mp hS) (hAffected S hS)
  refine ⟨hε1, hεscale1, ht, hAuxt, hamp, hsum, ?_, ?_⟩
  · rw [hamp, pow_succ]
    ring
  · rw [hsum, pow_succ]
    ring

end DirectGLSSW.TruncationSeparatingSum
