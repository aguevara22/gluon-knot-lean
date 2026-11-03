import DirectGLSSW.HorizontalShortEdge
import DirectGLSSW.CapMarkedPairing

namespace DirectGLSSW.HorizontalShortEdge

theorem horizontal_word_top_sign (q : ℕ → PlanarPoint ℝ) (j : ℕ)
    (t epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hstart : q 0 = (t - epsilon, 0)) (hfinish : q j = (t, 0)) (k : ℕ) :
    polygonSignArray q 0 k j = scalarSignValue (q k).2 := by
  have hdet : polygonHDet q 0 k j = epsilon * (q k).2 := by
    simp [polygonHDet, hstart, hfinish, planarDet]
    ring
  unfold polygonSignArray
  rw [hdet]
  exact scalarSignValue_positive_mul epsilon (q k).2 hepsilon

theorem horizontal_word_marked_cap_expansion (q : ℕ → PlanarPoint ℝ) (j : ℕ)
    (t epsilon : ℝ) (hepsilon : 0 < epsilon) (hgap : 1 < j)
    (hstart : q 0 = (t - epsilon, 0)) (hfinish : q j = (t, 0)) :
    markedAmplitude (fun _ k _ => scalarSignValue (q k).2) (polygonSignArray q) 0 j =
      capCutExpansion (j := j) (fun k => scalarSignValue (q k).2)
        (ordinaryCurrent (fun _ k _ => scalarSignValue (q k).2) (polygonSignArray q)) 0 := by
  apply markedAmplitude_eq_capCutExpansion_middleNear _ _ hgap
  intro k _
  exact horizontal_word_top_sign q j t epsilon hepsilon hstart hfinish k




end DirectGLSSW.HorizontalShortEdge
