import DirectGLSSW.TruncationEdgeParameter
import DirectGLSSW.ShortEdgeGenericity
import Mathlib.Topology.Instances.Real.Lemmas

namespace DirectGLSSW.TruncationDirection
open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.TruncationEdgeLift
open DirectGLSSW.ShortEdgeGenericity

theorem affinePoint_dist_lt_of_endpoints (A B O : PlanarPoint ℝ) (t ρ : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hA : dist A O < ρ) (hB : dist B O < ρ) :
    dist (affinePoint A B t) O < ρ := by
  have hc : ∀ u v o : ℝ, |u - o| < ρ → |v - o| < ρ →
      |u + t * (v - u) - o| < ρ := by
    intro u v o hu hv
    rcases abs_lt.mp hu with ⟨hu0, hu1⟩
    rcases abs_lt.mp hv with ⟨hv0, hv1⟩
    apply abs_lt.mpr
    by_cases huv : u ≤ v
    · have h0 := mul_nonneg ht0 (sub_nonneg.mpr huv)
      have h1 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr huv)
      constructor <;> nlinarith
    · have h0 := mul_nonneg ht0 (sub_nonneg.mpr (le_of_not_ge huv))
      have h1 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (le_of_not_ge huv))
      constructor <;> nlinarith
  simp only [Prod.dist_eq, Real.dist_eq] at hA hB
  simp only [Prod.dist_eq, Real.dist_eq, affinePoint]
  exact max_lt (hc A.1 B.1 O.1 (max_lt_iff.mp hA).1 (max_lt_iff.mp hB).1)
    (hc A.2 B.2 O.2 (max_lt_iff.mp hA).2 (max_lt_iff.mp hB).2)

theorem truncation_shortEdge_disjoint {n : ℕ} (hn : 3 ≤ n)
    (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε ρ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1)
    (hQ : cyclicNoncollinear (truncateCyclicCorner q a p scale ε))
    (hclear : ∀ e : Fin n, e ≠ a → cyclicSuccessor e ≠ a →
      ∀ x : PlanarPoint ℝ, dist x (q a) < ρ → ¬ edgeClosed q e x)
    (hB : dist (q a + ε • (q p - q a)) (q a) < ρ)
    (hC : dist (q a + (ε * scale) • (q (cyclicSuccessor a) - q a)) (q a) < ρ)
    (j : Fin (n + 1)) (hj : j ≠ a.castSucc) (x : PlanarPoint ℝ)
    (hx : edgeInterior (truncateCyclicCorner q a p scale ε) a.castSucc x) :
    ¬ edgeInterior (truncateCyclicCorner q a p scale ε) j x := by
  intro hxj
  have hxball : dist x (q a) < ρ := by
    obtain ⟨t, ht0, ht1, hxt⟩ := hx
    have hanchor : truncateCyclicCorner q a p scale ε a.castSucc =
        q a + ε • (q p - q a) := truncateCyclicCorner_anchor q a p scale ε
    rw [cyclicSuccessor_shortEdge, hanchor, truncateCyclicCorner_new] at hxt
    rw [hxt]
    exact affinePoint_dist_lt_of_endpoints _ _ _ t ρ
      (le_of_lt ht0) (le_of_lt ht1) hB hC
  by_cases he : collapseFin a j = a
  · rcases (collapseFin_eq_a_iff a j).mp he with heq | heq
    · exact hj heq
    · have hnew : j = cyclicSuccessor a.castSucc :=
        heq.trans (cyclicSuccessor_shortEdge a).symm
      rw [hnew] at hxj
      exact cyclic_adjacent_interiors_disjoint (by omega)
        (truncateCyclicCorner q a p scale ε) hQ a.castSucc x hx hxj
  · by_cases hs : cyclicSuccessor (collapseFin a j) = a
    · have hc : collapseFin a (cyclicSuccessor j) = a :=
        (collapseFin_cyclicSuccessor a j hj).trans hs
      rcases (collapseFin_eq_a_iff a (cyclicSuccessor j)).mp hc with heq | heq
      · have hx' : edgeInterior (truncateCyclicCorner q a p scale ε)
            (cyclicSuccessor j) x := by
          rw [heq]
          exact hx
        exact cyclic_adjacent_interiors_disjoint (by omega)
          (truncateCyclicCorner q a p scale ε) hQ j x hxj hx'
      · apply hj
        exact (cyclicSuccessor_bijective (n := n + 1)).injective
          (heq.trans (cyclicSuccessor_shortEdge a).symm)
    · have hold : edgeInterior q (collapseFin a j) x := by
        apply edgeInterior_transfer_to_old (by omega) q a p (collapseFin a j)
          hp scale ε hε hε1 hscale hscale1 x
        rw [edgeLift_collapseFin a j hj]
        exact hxj
      obtain ⟨t, ht0, ht1, hxt⟩ := hold
      exact hclear (collapseFin a j) he hs x hxball
        ⟨t, le_of_lt ht0, le_of_lt ht1, hxt⟩

end DirectGLSSW.TruncationDirection
