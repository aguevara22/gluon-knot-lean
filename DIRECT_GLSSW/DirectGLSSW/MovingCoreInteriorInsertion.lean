import DirectGLSSW.ShortEdgeInteriorInsertion
import DirectGLSSW.ShortEdgeDirectionExistence
import DirectGLSSW.MovingCoreShortEdge
import DirectGLSSW.MovingCoreCyclicG2
import DirectGLSSW.PolygonLocalAmplitude

namespace DirectGLSSW.ShortEdgePolygonAmplitude

open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.ShortEdgeGenericity
open DirectGLSSW.ShortEdgeSignStability
open DirectGLSSW.ShortEdgeSignRealization

theorem exists_movingCore_interior_polygonAmplitude_insert_eq
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (Q : ℝ → Fin n → PlanarPoint ℝ)
    (hQ : ∀ x : Fin n, Continuous (fun ε : ℝ => Q ε x))
    (h0 : CyclicGeneric (Q 0)) (a : Fin n) (v : PlanarPoint ℝ)
    (ha : 0 < a.val) (haN : a.val < n - 1)
    (havoid0 : ∀ x : Fin n, x ≠ a → planarDet v (Q 0 x - Q 0 a) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hp : CyclicGeneric (insertCyclicAfter (Q ε) a ε v),
        polygonAmplitude (insertCyclicAfter (Q ε) a ε v) hp =
          attachmentFactor (Q ε a)
            (insertCyclicAfter (Q ε) a ε v ⟨a.val + 1, by omega⟩)
            (Q ε ⟨a.val - 1, by omega⟩) (Q ε ⟨a.val + 1, by omega⟩) *
          polygonAmplitude (Q 0) h0 := by
  have hn : 3 ≤ n := h0.size_ge_three
  have hnPos : 0 < n := by omega
  let W : ℝ → ℕ → PlanarPoint ℝ := fun ε => coreWord (Q ε) hnPos
  have hW : ∀ i, i ≤ n - 1 → Continuous (fun ε : ℝ => W ε i) := by
    intro i hi
    have hi' : i < n := by omega
    have heq : (fun ε : ℝ => W ε i) = (fun ε : ℝ => Q ε ⟨i, hi'⟩) := by
      funext ε
      exact coreLastRootWord_eval hnPos (Q ε) i hi'
    rw [heq]
    exact hQ ⟨i, hi'⟩
  have hc0 : CoreHGeneric (W 0) (n - 1) :=
    coreHGeneric_of_cyclicNoncollinear hn (Q 0) h0.g1
  have hd0 : DirectionGeneric (W 0) (n - 1) a.val v :=
    ShortEdgeDirectionExistence.directionGeneric_lastRoot_of_pointwise_avoidance
      hnPos (Q 0) a v havoid0
  obtain ⟨δsign, hδsign, hsign⟩ :=
    exists_moving_core_shortEdge_stability W (n - 1) a.val v hW ha haN hc0 hd0
  obtain ⟨δG2, hδG2, hG2⟩ :=
    exists_insertCyclicAfter_movingCore_G2_radius Q hQ h0 a v
  obtain ⟨δcore, hδcore, hcore⟩ := exists_local_polygonAmplitude_stability Q hQ h0
  refine ⟨min δsign (min δG2 δcore), lt_min hδsign (lt_min hδG2 hδcore), ?_⟩
  intro ε hε hεδ
  have hεsign : ε < δsign := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεrest : ε < min δG2 δcore := lt_of_lt_of_le hεδ (min_le_right _ _)
  have hεG2 : ε < δG2 := lt_of_lt_of_le hεrest (min_le_left _ _)
  have hεcore : ε < δcore := lt_of_lt_of_le hεrest (min_le_right _ _)
  obtain ⟨hc, hd, hst⟩ := hsign ε hε hεsign
  obtain ⟨hq, hamp⟩ := hcore ε (by simpa [abs_of_pos hε] using hεcore)
  have hparentG1 := ShortEdgeCyclicG1.inserted_cyclicNoncollinear_of_openStability
    hn (Q ε) a ε v hc hd hst
  have hparentG2 := hG2 ε hε hεG2 hparentG1
  let hp : CyclicGeneric (insertCyclicAfter (Q ε) a ε v) :=
    ⟨by omega, hparentG1, hparentG2⟩
  have hpoly := polygonAmplitude_insert_eq hRI hn (Q ε) hq a ε v hε hc hd hst
    ha haN hparentG2
  rw [kappa_eq_cyclicAttachmentFactor (Q ε) a v ε hε ha haN hd, hamp] at hpoly
  exact ⟨hp, hpoly⟩

end DirectGLSSW.ShortEdgePolygonAmplitude
