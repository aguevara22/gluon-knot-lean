import DirectGLSSW.TruncationShortEdgeClearance
import DirectGLSSW.TruncationOldEdgeRetention
import DirectGLSSW.PolygonCrossings

namespace DirectGLSSW.TruncationDirection

open DirectGLSSW
open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.TruncationEdgeLift
open DirectGLSSW.ShortEdgeGenericity

noncomputable def polygonCrossing_truncationEquiv {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε ρ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1)
    (hQ : cyclicNoncollinear (truncateCyclicCorner q a p scale ε))
    (hclear : ∀ e : Fin n, e ≠ a → cyclicSuccessor e ≠ a →
      ∀ x : PlanarPoint ℝ, dist x (q a) < ρ → ¬ edgeClosed q e x)
    (hfree : ∀ x : PlanarPoint ℝ, dist x (q a) < ρ → ¬ IsCrossingPoint q x)
    (hB : dist (q a + ε • (q p - q a)) (q a) < ρ)
    (hC : dist (q a + (ε * scale) •
      (q (cyclicSuccessor a) - q a)) (q a) < ρ) :
    PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε) := by
  classical
  let q' : Fin (n + 1) → PlanarPoint ℝ := truncateCyclicCorner q a p scale ε
  let f : PolygonCrossing q → PolygonCrossing q' := fun c =>
    ⟨(edgeLift a c.val.1, edgeLift a c.val.2), by
      constructor
      · exact edgeLift_strictMono a c.property.1
      · obtain ⟨x, hl, hr⟩ := c.property.2
        have hout : ρ ≤ dist x (q a) := by
          by_contra hnot
          exact hfree x (lt_of_not_ge hnot)
            ⟨c.val.1, c.val.2, ne_of_lt c.property.1, hl, hr⟩
        exact ⟨x,
          edgeInterior_transfer_from_old_outside_vertex_ball
            (by omega) q a p c.val.1 hp scale ε ρ hε hε1 hscale hscale1
            hB hC x hout hl,
          edgeInterior_transfer_from_old_outside_vertex_ball
            (by omega) q a p c.val.2 hp scale ε ρ hε hε1 hscale hscale1
            hB hC x hout hr⟩⟩
  let g : PolygonCrossing q' → PolygonCrossing q := fun c => by
    let x : PlanarPoint ℝ := Classical.choose c.property.2
    have hl : edgeInterior q' c.val.1 x := (Classical.choose_spec c.property.2).1
    have hr : edgeInterior q' c.val.2 x := (Classical.choose_spec c.property.2).2
    have hi : c.val.1 ≠ a.castSucc := by
      intro hi
      have hj : c.val.2 ≠ a.castSucc := by
        intro hj
        exact (ne_of_lt c.property.1) (hi.trans hj.symm)
      have hlshort : edgeInterior (truncateCyclicCorner q a p scale ε) a.castSucc x := by
        simpa [hi] using hl
      have hdis := truncation_shortEdge_disjoint (by omega) q a p hp scale ε ρ
        hε hε1 hscale hscale1 hQ hclear hB hC c.val.2 hj x hlshort
      exact hdis hr
    have hj : c.val.2 ≠ a.castSucc := by
      intro hj
      have hrshort : edgeInterior (truncateCyclicCorner q a p scale ε) a.castSucc x := by
        simpa [hj] using hr
      have hdis := truncation_shortEdge_disjoint (by omega) q a p hp scale ε ρ
        hε hε1 hscale hscale1 hQ hclear hB hC c.val.1 hi x hrshort
      exact hdis hl
    have heLift : edgeLift a (collapseFin a c.val.1) = c.val.1 :=
      edgeLift_collapseFin a c.val.1 hi
    have hdLift : edgeLift a (collapseFin a c.val.2) = c.val.2 :=
      edgeLift_collapseFin a c.val.2 hj
    have hed : collapseFin a c.val.1 < collapseFin a c.val.2 := by
      by_contra hnot
      have hle : collapseFin a c.val.2 ≤ collapseFin a c.val.1 := by omega
      by_cases heq : collapseFin a c.val.2 = collapseFin a c.val.1
      · have hEqLift := congrArg (edgeLift a) heq
        rw [hdLift, heLift] at hEqLift
        exact (ne_of_lt c.property.1) hEqLift.symm
      · have hlt : collapseFin a c.val.2 < collapseFin a c.val.1 := by omega
        have hLift := edgeLift_strictMono a hlt
        rw [hdLift, heLift] at hLift
        exact (not_lt_of_ge (le_of_lt c.property.1)) hLift
    have hl' : edgeInterior (truncateCyclicCorner q a p scale ε)
        (edgeLift a (collapseFin a c.val.1)) x := by simpa [heLift] using hl
    have hr' : edgeInterior (truncateCyclicCorner q a p scale ε)
        (edgeLift a (collapseFin a c.val.2)) x := by simpa [hdLift] using hr
    have hleOld := edgeInterior_transfer_to_old
      (by omega) q a p (collapseFin a c.val.1) hp scale ε hε hε1 hscale hscale1 x hl'
    have hriOld := edgeInterior_transfer_to_old
      (by omega) q a p (collapseFin a c.val.2) hp scale ε hε hε1 hscale hscale1 x hr'
    exact ⟨(collapseFin a c.val.1, collapseFin a c.val.2), hed, ⟨x, hleOld, hriOld⟩⟩
  refine ⟨f, g, ?_, ?_⟩
  · intro c
    apply Subtype.ext
    dsimp only [f, g]
    change (collapseFin a (edgeLift a c.val.1),
      collapseFin a (edgeLift a c.val.2)) = c.val
    simp [collapseFin_edgeLift]
  · intro c
    apply Subtype.ext
    dsimp only [g, f]
    change (edgeLift a (collapseFin a c.val.1),
      edgeLift a (collapseFin a c.val.2)) = c.val
    have hi : c.val.1 ≠ a.castSucc := by
      intro hi
      have hj : c.val.2 ≠ a.castSucc := by
        intro hj
        exact (ne_of_lt c.property.1) (hi.trans hj.symm)
      obtain ⟨x, hl, hr⟩ := c.property.2
      have hlshort : edgeInterior (truncateCyclicCorner q a p scale ε) a.castSucc x := by
        simpa [hi] using hl
      have hdis := truncation_shortEdge_disjoint (by omega) q a p hp scale ε ρ
        hε hε1 hscale hscale1 hQ hclear hB hC c.val.2 hj x hlshort
      exact hdis hr
    have hj : c.val.2 ≠ a.castSucc := by
      intro hj
      obtain ⟨x, hl, hr⟩ := c.property.2
      have hrshort : edgeInterior (truncateCyclicCorner q a p scale ε) a.castSucc x := by
        simpa [hj] using hr
      have hdis := truncation_shortEdge_disjoint (by omega) q a p hp scale ε ρ
        hε hε1 hscale hscale1 hQ hclear hB hC c.val.1 hi x hrshort
      exact hdis hl
    exact Prod.ext (edgeLift_collapseFin a c.val.1 hi)
      (edgeLift_collapseFin a c.val.2 hj)


theorem polygonCrossing_truncationEquiv_left_label {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε ρ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1)
    (hQ : cyclicNoncollinear (truncateCyclicCorner q a p scale ε))
    (hclear : ∀ e : Fin n, e ≠ a → cyclicSuccessor e ≠ a →
      ∀ x : PlanarPoint ℝ, dist x (q a) < ρ → ¬ edgeClosed q e x)
    (hfree : ∀ x : PlanarPoint ℝ, dist x (q a) < ρ → ¬ IsCrossingPoint q x)
    (hB : dist (q a + ε • (q p - q a)) (q a) < ρ)
    (hC : dist (q a + (ε * scale) •
      (q (cyclicSuccessor a) - q a)) (q a) < ρ) (c : PolygonCrossing q) :
    (polygonCrossing_truncationEquiv hn q a p hp scale ε ρ hε hε1 hscale hscale1
      hQ hclear hfree hB hC c).val.1 = edgeLift a c.val.1 := rfl

theorem polygonCrossing_truncationEquiv_right_label {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε ρ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1)
    (hQ : cyclicNoncollinear (truncateCyclicCorner q a p scale ε))
    (hclear : ∀ e : Fin n, e ≠ a → cyclicSuccessor e ≠ a →
      ∀ x : PlanarPoint ℝ, dist x (q a) < ρ → ¬ edgeClosed q e x)
    (hfree : ∀ x : PlanarPoint ℝ, dist x (q a) < ρ → ¬ IsCrossingPoint q x)
    (hB : dist (q a + ε • (q p - q a)) (q a) < ρ)
    (hC : dist (q a + (ε * scale) •
      (q (cyclicSuccessor a) - q a)) (q a) < ρ) (c : PolygonCrossing q) :
    (polygonCrossing_truncationEquiv hn q a p hp scale ε ρ hε hε1 hscale hscale1
      hQ hclear hfree hB hC c).val.2 = edgeLift a c.val.2 := rfl

end DirectGLSSW.TruncationDirection
