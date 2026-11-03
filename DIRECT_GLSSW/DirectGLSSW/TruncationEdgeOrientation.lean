import DirectGLSSW.TruncationEdgeParameter

namespace DirectGLSSW.TruncationDirection

open DirectGLSSW
open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.TruncationEdgeLift

theorem truncateCyclicCorner_edge_tangent_scale {n : ℕ}
    (hn : 2 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hpa : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (e : Fin n) :
    cyclicTangent (truncateCyclicCorner q a p scale ε) (edgeLift a e) =
      (if e = p then 1 - ε else if e = a then 1 - ε * scale else (1 : ℝ)) •
        cyclicTangent q e := by
  let parent := truncateCyclicCorner q a p scale ε
  let U := parent (edgeLift a e)
  let V := parent (cyclicSuccessor (edgeLift a e))
  let A := q e
  let B := q (cyclicSuccessor e)
  let slope : ℝ := if e = p then 1 - ε else if e = a then 1 - ε * scale else 1
  have hparam (t : ℝ) :
      affinePoint U V t = affinePoint A B (oldEdgeParameter a p e ε scale t) := by
    dsimp [U, V, parent, A, B]
    exact truncateCyclicCorner_edge_affineParameter hn q a p hpa scale ε
      hε hε1 hscale hscale1 e t
  have hU : U = affinePoint A B (oldEdgeParameter a p e ε scale 0) := by
    simpa only [affinePoint_zero] using hparam 0
  have hV : V = affinePoint A B (oldEdgeParameter a p e ε scale 1) := by
    simpa only [affinePoint_one] using hparam 1
  have hnot : a ≠ p := by
    intro h
    have hfix : cyclicSuccessor p = p := hpa.trans h
    exact cyclicSuccessor_ne_self hn p hfix
  have hdiff : oldEdgeParameter a p e ε scale 1 -
      oldEdgeParameter a p e ε scale 0 = slope := by
    by_cases hep : e = p
    · simp [oldEdgeParameter, slope, hep]
    · by_cases hea : e = a
      · simp [oldEdgeParameter, slope, hep, hea, hnot]
      · simp [oldEdgeParameter, slope, hep, hea]
  change V - U = slope • (q (cyclicSuccessor e) - q e)
  rw [hV, hU]
  have hseg : affinePoint A B (oldEdgeParameter a p e ε scale 1) -
      affinePoint A B (oldEdgeParameter a p e ε scale 0) =
        (oldEdgeParameter a p e ε scale 1 -
          oldEdgeParameter a p e ε scale 0) • (B - A) := by
    ext <;> simp [affinePoint] <;> ring_nf
  rw [hdiff] at hseg
  simpa [A, B] using hseg

theorem truncateCyclicCorner_edge_determinant_sign_iff {n : ℕ}
    (hn : 2 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hpa : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (e f : Fin n) :
    0 < planarDet
      (cyclicTangent (truncateCyclicCorner q a p scale ε) (edgeLift a e))
      (cyclicTangent (truncateCyclicCorner q a p scale ε) (edgeLift a f)) ↔
    0 < planarDet (cyclicTangent q e) (cyclicTangent q f) := by
  let se : ℝ := if e = p then 1 - ε else if e = a then 1 - ε * scale else 1
  let sf : ℝ := if f = p then 1 - ε else if f = a then 1 - ε * scale else 1
  have hse : 0 < se := by
    dsimp [se]
    exact oldEdgeParameter_slope_pos a p e ε scale hε hε1 hscale hscale1
  have hsf : 0 < sf := by
    dsimp [sf]
    exact oldEdgeParameter_slope_pos a p f ε scale hε hε1 hscale hscale1
  have hte := truncateCyclicCorner_edge_tangent_scale hn q a p hpa scale ε
    hε hε1 hscale hscale1 e
  have htf := truncateCyclicCorner_edge_tangent_scale hn q a p hpa scale ε
    hε hε1 hscale hscale1 f
  have hdet :
      planarDet
        (cyclicTangent (truncateCyclicCorner q a p scale ε) (edgeLift a e))
        (cyclicTangent (truncateCyclicCorner q a p scale ε) (edgeLift a f)) =
      (se * sf) * planarDet (cyclicTangent q e) (cyclicTangent q f) := by
    rw [hte, htf]
    change planarDet (se • cyclicTangent q e) (sf • cyclicTangent q f) = _
    simp [planarDet, smul_eq_mul]
    <;> ring_nf
  have hprod : 0 < se * sf := mul_pos hse hsf
  constructor
  · intro h
    rw [hdet] at h
    by_contra hbase
    have hbase' : planarDet (cyclicTangent q e) (cyclicTangent q f) ≤ 0 := le_of_not_gt hbase
    have hnonpos : (se * sf) * planarDet (cyclicTangent q e) (cyclicTangent q f) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hprod.le hbase'
    exact (not_le_of_gt h) hnonpos
  · intro hbase
    rw [hdet]
    exact mul_pos hprod hbase

theorem oldEdgeParameter_strictMono {n : ℕ} (a p e : Fin n)
    (ε scale : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hscale : 0 < ε * scale) (hscale1 : ε * scale < 1) :
    StrictMono (oldEdgeParameter a p e ε scale) := by
  intro x y hxy
  by_cases hep : e = p
  · simpa [oldEdgeParameter, hep] using
      (mul_lt_mul_of_pos_left hxy (sub_pos.mpr hε1))
  · by_cases hea : e = a
    · have hslope : 0 < 1 - ε * scale := sub_pos.mpr hscale1
      have hnot : a ≠ p := fun h => hep (hea.trans h)
      simp only [oldEdgeParameter, hep, hea, hnot]
      exact add_lt_add_left (mul_lt_mul_of_pos_left hxy hslope) _
    · simp only [oldEdgeParameter, hep, hea]
      exact hxy

end DirectGLSSW.TruncationDirection
