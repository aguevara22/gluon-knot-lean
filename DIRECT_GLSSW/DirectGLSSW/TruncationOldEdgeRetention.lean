import DirectGLSSW.TruncationPointGeometry
import DirectGLSSW.TruncationEdgeLift
import DirectGLSSW.TruncationEdgeParameter
import DirectGLSSW.AffineRetention

namespace DirectGLSSW.TruncationDirection

open DirectGLSSW
open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.TruncationEdgeLift

theorem edgeInterior_transfer_from_old_outside_vertex_ball {n : ℕ}
    (hn : 2 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p e : Fin n)
    (hpa : cyclicSuccessor p = a) (scale ε ρ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hscale : 0 < ε * scale) (hscale1 : ε * scale < 1)
    (hB : dist (q a + ε • (q p - q a)) (q a) < ρ)
    (hC : dist (q a + (ε * scale) •
      (q (cyclicSuccessor a) - q a)) (q a) < ρ)
    (x : PlanarPoint ℝ) (hout : ρ ≤ dist x (q a))
    (hx : edgeInterior q e x) :
    edgeInterior (truncateCyclicCorner q a p scale ε) (edgeLift a e) x := by
  obtain ⟨t, ht0, ht1, hxseg⟩ := hx
  have hshort : p ≠ a := by
    intro h
    have hfix : cyclicSuccessor p = p := hpa.trans h.symm
    exact (cyclicSuccessor_ne_self hn p) hfix
  by_cases hep : e = p
  · subst e
    have hxseg' : x = affinePoint (q p) (q a) t := by
      simpa [hpa] using hxseg
    have hB' : dist (affinePoint (q a) (q p) ε) (q a) < ρ := by
      convert hB using 2 <;> ext <;> simp [affinePoint]
    obtain ⟨_, hu0, hu1, hxret⟩ :=
      affinePoint_incoming_outside_ball_retained_after_shortening
        (q p) (q a) x ε t ρ hxseg' hε hε1 ht0 ht1 hout hB'
    have hparam : oldEdgeParameter a p p ε scale (t / (1 - ε)) = t := by
      simp [oldEdgeParameter, hshort]
      field_simp [ne_of_gt (sub_pos.mpr hε1)]
    have hidentity := truncateCyclicCorner_edge_affineParameter
      hn q a p hpa scale ε hε hε1 hscale hscale1 p (t / (1 - ε))
    refine ⟨t / (1 - ε), hu0, hu1, ?_⟩
    rw [hidentity, hparam]
    simpa [hpa] using hxseg'
  · by_cases hea : e = a
    · subst e
      have hC' : dist (affinePoint (q a) (q (cyclicSuccessor a)) (ε * scale))
          (q a) < ρ := by
        convert hC using 2 <;> ext <;> simp [affinePoint]
      obtain ⟨_, hu0, hu1, hxret⟩ :=
        affinePoint_outside_ball_retained_after_shortening
          (q a) (q (cyclicSuccessor a)) x (ε * scale) t ρ
          hxseg hscale hscale1 ht0 ht1 hout hC'
      have hnot : a ≠ p := hshort.symm
      have hparam : oldEdgeParameter a p a ε scale
          ((t - ε * scale) / (1 - ε * scale)) = t := by
        simp [oldEdgeParameter, hnot]
        field_simp [ne_of_gt (sub_pos.mpr hscale1)]
      have hidentity := truncateCyclicCorner_edge_affineParameter
        hn q a p hpa scale ε hε hε1 hscale hscale1 a
        ((t - ε * scale) / (1 - ε * scale))
      refine ⟨(t - ε * scale) / (1 - ε * scale), hu0, hu1, ?_⟩
      rw [hidentity, hparam]
      exact hxseg
    · have hparam : oldEdgeParameter a p e ε scale t = t := by
        simp [oldEdgeParameter, hep, hea]
      have hidentity := truncateCyclicCorner_edge_affineParameter
        hn q a p hpa scale ε hε hε1 hscale hscale1 e t
      refine ⟨t, ht0, ht1, ?_⟩
      rw [hidentity, hparam]
      exact hxseg

end DirectGLSSW.TruncationDirection
