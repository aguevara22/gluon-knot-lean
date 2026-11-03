import DirectGLSSW.TruncationPointGeometry
import DirectGLSSW.TruncationEdgeLift
import DirectGLSSW.AffineSegments

namespace DirectGLSSW.TruncationDirection

open DirectGLSSW
open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.TruncationEdgeLift

/-- The parameter on the old edge represented by a point on its lifted parent edge. -/
def oldEdgeParameter {n : ℕ} (a p e : Fin n) (ε scale t : ℝ) : ℝ :=
  if e = p then (1 - ε) * t else
  if e = a then ε * scale + (1 - ε * scale) * t else t

theorem oldEdgeParameter_slope_pos {n : ℕ} (a p e : Fin n) (ε scale : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) :
    0 < if e = p then 1 - ε else if e = a then 1 - ε * scale else (1 : ℝ) := by
  by_cases hep : e = p
  · simp [hep]; linarith
  · by_cases hea : e = a
    · have hnot : a ≠ p := fun h => hep (hea.trans h)
      simp [hep, hea, hnot]; linarith
    · simp [hep, hea]

theorem oldEdgeParameter_mem_unit {n : ℕ} (a p e : Fin n) (ε scale t : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (ht : 0 < t) (ht1 : t < 1) :
    0 < oldEdgeParameter a p e ε scale t ∧
      oldEdgeParameter a p e ε scale t < 1 := by
  by_cases hep : e = p
  · simp [oldEdgeParameter, hep]
    constructor <;> nlinarith
  · by_cases hea : e = a
    · have hnot : a ≠ p := fun h => hep (hea.trans h)
      simp [oldEdgeParameter, hep, hea, hnot]
      constructor <;> nlinarith
    · simp [oldEdgeParameter, hep, hea, ht, ht1]

theorem truncateCyclicCorner_edge_affineParameter {n : ℕ}
    (hn : 2 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hpa : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (e : Fin n) (t : ℝ) :
    affinePoint
      (truncateCyclicCorner q a p scale ε (edgeLift a e))
      (truncateCyclicCorner q a p scale ε (cyclicSuccessor (edgeLift a e))) t =
    affinePoint (q e) (q (cyclicSuccessor e))
      (oldEdgeParameter a p e ε scale t) := by
  have hshort : edgeLift a e ≠ a.castSucc := edgeLift_ne_short a e
  have hstart := truncateCyclicCorner_off_short q a p scale ε (edgeLift a e) hshort
  have hend := truncateCyclicCorner_successor_off_short q a p scale ε (edgeLift a e) hshort
  rw [collapseFin_edgeLift] at hstart hend
  by_cases hep : e = p
  · have hpaNe : p ≠ a := by
      intro h
      have hfix : cyclicSuccessor p = p := hpa.trans h.symm
      exact (cyclicSuccessor_ne_self hn p) hfix
    subst e
    rw [hstart, hend]
    ext <;> simp [oldEdgeParameter, hpa, hpaNe, affinePoint] <;> ring
  · by_cases hea : e = a
    · subst e
      have hnot : a ≠ p := fun h => hep h
      have hneq : cyclicSuccessor a ≠ a := cyclicSuccessor_ne_self hn a
      rw [hstart, hend]
      ext <;> simp [oldEdgeParameter, hnot, hneq, affinePoint] <;> ring
    · have hsucc : cyclicSuccessor e ≠ a := by
        intro h
        apply hep
        exact (cyclicSuccessor_bijective (n := n)).1 (h.trans hpa.symm)
      rw [hstart, hend]
      ext <;> simp [oldEdgeParameter, hep, hea, hsucc, affinePoint] <;> ring

theorem edgeInterior_transfer_to_old {n : ℕ}
    (hn : 2 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p e : Fin n)
    (hpa : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (x : PlanarPoint ℝ)
    (hx : edgeInterior (truncateCyclicCorner q a p scale ε)
      (edgeLift a e) x) :
    edgeInterior q e x := by
  obtain ⟨t, ht0, ht1, hpoint⟩ := hx
  refine ⟨oldEdgeParameter a p e ε scale t, ?_, ?_, ?_⟩
  · exact (oldEdgeParameter_mem_unit a p e ε scale t hε hε1 hscale hscale1 ht0 ht1).1
  · exact (oldEdgeParameter_mem_unit a p e ε scale t hε hε1 hscale hscale1 ht0 ht1).2
  · rw [← truncateCyclicCorner_edge_affineParameter hn q a p hpa scale ε hε hε1 hscale hscale1 e t]
    exact hpoint

end DirectGLSSW.TruncationDirection
