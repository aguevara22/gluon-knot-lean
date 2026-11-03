import DirectGLSSW.CyclicWords
import DirectGLSSW.ShortEdgeSignStability
import DirectGLSSW.ShortEdgeCyclicAdapter

namespace DirectGLSSW.ShortEdgeDirectionExistence

open DirectGLSSW

theorem exists_direction_avoiding_vertex_lines
    {n : ℕ} (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ)
    (hq : cyclicNoncollinear q) (a : Fin n) :
    ∃ v : PlanarPoint ℝ,
      ∀ x : Fin n, x ≠ a → planarDet v (q x - q a) ≠ 0 := by
  classical
  letI : Infinite ℝ := Infinite.of_injective (fun m : ℕ => (m : ℝ)) Nat.cast_injective
  let xset : Finset (Fin n) :=
    Finset.univ.filter (fun x => x ≠ a ∧ (q x).1 ≠ (q a).1)
  let slopes : Finset ℝ := xset.image
    (fun x => ((q x).2 - (q a).2) / ((q x).1 - (q a).1))
  obtain ⟨t, ht⟩ := Finset.exists_not_mem slopes
  refine ⟨(1, t), ?_⟩
  intro x hxa
  have hqx : q x ≠ q a := by
    intro h
    exact hxa ((cyclicNoncollinear_injective hn q hq) h)
  by_cases hdx : (q x).1 - (q a).1 = 0
  · have hdy : (q x).2 - (q a).2 ≠ 0 := by
      intro h
      apply hqx
      exact Prod.ext (sub_eq_zero.mp hdx) (sub_eq_zero.mp h)
    intro hdet
    have hdet' : (q x).2 - (q a).2 = 0 := by
      simpa [planarDet, hdx] using hdet
    exact hdy hdet'
  · have hxset : x ∈ xset := by
      have hdx' : (q x).1 ≠ (q a).1 := fun h => hdx (sub_eq_zero.mpr h)
      simp [xset, hxa, hdx']
    have hmem :
        ((q x).2 - (q a).2) / ((q x).1 - (q a).1) ∈ slopes :=
      Finset.mem_image.mpr ⟨x, hxset, rfl⟩
    intro hdet
    have hmul : (q x).2 - (q a).2 = t * ((q x).1 - (q a).1) := by
      have : ((q x).2 - (q a).2) - t * ((q x).1 - (q a).1) = 0 := by
        simpa [planarDet] using hdet
      linarith
    have hslope :
        ((q x).2 - (q a).2) / ((q x).1 - (q a).1) = t :=
      (div_eq_iff hdx).2 hmul
    exact ht (Finset.mem_image.mpr ⟨x, hxset, hslope⟩)

theorem directionGeneric_lastRoot_of_pointwise_avoidance
    {n : ℕ} (hn : 0 < n) (q : Fin n → PlanarPoint ℝ)
    (a : Fin n) (v : PlanarPoint ℝ)
    (havoid : ∀ x : Fin n, x ≠ a → planarDet v (q x - q a) ≠ 0) :
    ShortEdgeSignStability.DirectionGeneric
      (fun k => rootedPolygonWord q
        (DirectGLSSW.ShortEdgeCyclicAdapter.lastCoreRoot hn) k)
      (n - 1) a.val v := by
  intro x hx hxa
  have hxlt : x < n := by omega
  have hwordx := DirectGLSSW.ShortEdgeCyclicAdapter.coreLastRootWord_eval hn q x hxlt
  have hworda := DirectGLSSW.ShortEdgeCyclicAdapter.coreLastRootWord_eval hn q a.val a.isLt
  change planarDet v
    (rootedPolygonWord q (DirectGLSSW.ShortEdgeCyclicAdapter.lastCoreRoot hn) x -
      rootedPolygonWord q (DirectGLSSW.ShortEdgeCyclicAdapter.lastCoreRoot hn) a.val) ≠ 0
  rw [hwordx, hworda]
  have hindex : (⟨a.val, a.isLt⟩ : Fin n) = a := Fin.ext rfl
  rw [hindex]
  exact havoid ⟨x, hxlt⟩ (by
    intro h
    exact hxa (congrArg Fin.val h))

theorem exists_directionGeneric_lastRoot
    {n : ℕ} (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ)
    (hq : cyclicNoncollinear q) (a : Fin n) :
    ∃ v : PlanarPoint ℝ,
      ShortEdgeSignStability.DirectionGeneric
        (fun k => rootedPolygonWord q
          (DirectGLSSW.ShortEdgeCyclicAdapter.lastCoreRoot (by omega : 0 < n)) k)
        (n - 1) a.val v := by
  obtain ⟨v, havoid⟩ := exists_direction_avoiding_vertex_lines hn q hq a
  exact ⟨v, directionGeneric_lastRoot_of_pointwise_avoidance
    (by omega) q a v havoid⟩

end DirectGLSSW.ShortEdgeDirectionExistence
