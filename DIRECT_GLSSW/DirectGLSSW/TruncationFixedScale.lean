import DirectGLSSW.MovingCoreAllAnchor
import DirectGLSSW.TruncationCoordinates
import DirectGLSSW.TruncationDirection

namespace DirectGLSSW.TruncationFixedScale
open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.ShortEdgeGenericity

/-- For a prescribed positive truncation scale avoiding every non-anchor
vertex line, all sufficiently small positive truncations are generic and
reverse the polygon amplitude. -/
theorem exists_fixedScale_leftCorner_truncation_amplitude
    (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (a p : Fin n) (hp : cyclicSuccessor p = a)
    (hturn : 0 < planarDet (q a - q p) (q (cyclicSuccessor a) - q a))
    (scale : ℝ) (hscale : 0 < scale)
    (havoid : ∀ x : Fin n, x ≠ a →
      planarDet
        (scale • (q (cyclicSuccessor a) - q a) - (q p - q a))
        (q x - q a) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ε < 1 ∧ ε * scale < 1 ∧
          ∃ ht : CyclicGeneric (DirectGLSSW.TruncationDirection.truncateCyclicCorner q a p scale ε),
            polygonAmplitude (DirectGLSSW.TruncationDirection.truncateCyclicCorner q a p scale ε) ht =
              -polygonAmplitude q hq := by
  have hn := hq.size_ge_three
  have hpa : p ≠ a := by
    intro h
    exact cyclicSuccessor_ne_self (by omega) p (hp.trans h.symm)
  have hca : cyclicSuccessor a ≠ a := cyclicSuccessor_ne_self (by omega) a
  have hpc : p ≠ cyclicSuccessor a := by
    intro h
    apply cyclicSuccessor_twice_ne_self hn a
    rw [← h, hp]
  let Q : ℝ → Fin n → PlanarPoint ℝ :=
    fun ε => Function.update q a (q a + ε • (q p - q a))
  let v : PlanarPoint ℝ :=
    scale • (q (cyclicSuccessor a) - q a) - (q p - q a)
  have hQ : ∀ x : Fin n, Continuous (fun ε : ℝ => Q ε x) := by
    intro x
    by_cases hx : x = a
    · subst x
      simp only [Q, Function.update_self]
      exact continuous_const.add (continuous_id.smul continuous_const)
    · simpa only [Q, Function.update_of_ne hx] using
        (continuous_const : Continuous (fun _ : ℝ => q x))
  have hQ0 : Q 0 = q := by
    funext x
    by_cases hx : x = a <;> simp [Q, hx]
  have h0 : CyclicGeneric (Q 0) := by rw [hQ0]; exact hq
  have havoid0 : ∀ x : Fin n, x ≠ a →
      planarDet v (Q 0 x - Q 0 a) ≠ 0 := by
    rw [hQ0]
    exact havoid
  have hamp0 : polygonAmplitude (Q 0) h0 = polygonAmplitude q hq := by
    simp only [hQ0]
  obtain ⟨δ, hδ, hgood⟩ := exists_movingCore_shortEdge_insertion
    hRI Q hQ h0 a v havoid0 p hp
  refine ⟨min δ (min 1 (1 / scale)),
    lt_min hδ (lt_min zero_lt_one (div_pos zero_lt_one hscale)), ?_⟩
  intro ε hε hεδ
  have hεinsert : ε < δ := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεrest : ε < min 1 (1 / scale) := lt_of_lt_of_le hεδ (min_le_right _ _)
  have hε1 : ε < 1 := lt_of_lt_of_le hεrest (min_le_left _ _)
  have hεinv : ε < 1 / scale := lt_of_lt_of_le hεrest (min_le_right _ _)
  have hεscale1 : ε * scale < 1 := (lt_div_iff₀ hscale).mp hεinv
  obtain ⟨ht, hamp⟩ := hgood ε hε hεinsert
  have hnew : insertCyclicAfter (Q ε) a ε v ⟨a.val + 1, by omega⟩ =
      q a + (ε * scale) • (q (cyclicSuccessor a) - q a) :=
    DirectGLSSW.TruncationDirection.truncateCyclicCorner_new q a p scale ε
  have hfactor : attachmentFactor (Q ε a)
      (insertCyclicAfter (Q ε) a ε v ⟨a.val + 1, by omega⟩)
      (Q ε p) (Q ε (cyclicSuccessor a)) = -1 := by
    rw [hnew]
    simp only [Q, Function.update_self, Function.update_of_ne hpa,
      Function.update_of_ne hca]
    exact DirectGLSSW.TruncationDirection.truncation_attachmentFactor_eq_neg q a p (cyclicSuccessor a)
      scale ε hturn hscale hε hε1 hεscale1
  rw [hfactor, hamp0, neg_one_mul] at hamp
  exact ⟨hε1, hεscale1, ht, hamp⟩

end DirectGLSSW.TruncationFixedScale
