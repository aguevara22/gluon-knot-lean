import DirectGLSSW.ShortEdgeSignRealization

namespace DirectGLSSW.ShortEdgeGenericity

open DirectGLSSW.ShortEdgeSignRealization DirectGLSSW.ShortEdgeSignStability

noncomputable def attachmentFactor (A B P C : PlanarPoint ℝ) : ℚ :=
  (scalarSignValue (planarDet (A - B) (P - B)) +
    scalarSignValue (planarDet (A - B) (C - B))) / 2

theorem inserted_short_det (q : ℕ → PlanarPoint ℝ) (a x : ℕ)
    (ε : ℝ) (v : PlanarPoint ℝ) :
    planarDet (q a - insertAfter q a ε v (a + 1))
      (q x - insertAfter q a ε v (a + 1)) =
        -ε * planarDet v (q x - q a) := by
  have hnot : ¬ a + 1 ≤ a := by omega
  simp [insertAfter, hnot, planarDet]
  ring

theorem kappa_eq_attachmentFactor (q : ℕ → PlanarPoint ℝ)
    (N a : ℕ) (v : PlanarPoint ℝ) (ε : ℝ) (hε : 0 < ε)
    (ha : 0 < a) (haN : a < N) (hdir : DirectionGeneric q N a v) :
    ShortEdgeWeighted.kappa a ha (shortSign q a v) =
      attachmentFactor (q a) (insertAfter q a ε v (a + 1))
        (q (a - 1)) (q (a + 1)) := by
  unfold ShortEdgeWeighted.kappa ShortEdgeWeighted.alpha ShortEdgeWeighted.beta
    attachmentFactor
  rw [inserted_short_det, inserted_short_det]
  rw [shortSign_value_eq_scaled_det q N a v ε hε hdir (a - 1)
    (by omega) (by omega)]
  rw [shortSign_value_eq_scaled_det q N a v ε hε hdir (a + 1)
    (by omega) (by omega)]

end DirectGLSSW.ShortEdgeGenericity
