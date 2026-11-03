import DirectGLSSW.TruncationCoordinates
import DirectGLSSW.ShortEdgeCyclicGeometry

namespace DirectGLSSW.TruncationDirection
open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.ShortEdgeCutFibers

theorem truncateCyclicCorner_of_collapse_ne {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p : Fin n) (scale ε : ℝ)
    (i : Fin (n + 1)) (hi : collapseFin a i ≠ a) :
    truncateCyclicCorner q a p scale ε i = q (collapseFin a i) := by
  by_cases hle : i.val ≤ a.val
  · have hne : (⟨i.val, lt_of_le_of_lt hle a.isLt⟩ : Fin n) ≠ a := by
      simpa [collapseFin, collapseAfter, hle] using hi
    simp [truncateCyclicCorner, insertCyclicAfter, collapseFin, collapseAfter, hle, hne]
  · have hmid : i.val ≠ a.val + 1 := by
      intro h
      apply hi
      apply (collapseFin_eq_a_iff a i).mpr
      exact Or.inr (Fin.ext h)
    have hne : (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin n) ≠ a := by
      simpa [collapseFin, collapseAfter, hle] using hi
    simp [truncateCyclicCorner, insertCyclicAfter, collapseFin, collapseAfter, hle, hmid, hne]

theorem cyclicSuccessor_shortEdge {n : ℕ} (a : Fin n) :
    cyclicSuccessor a.castSucc = (⟨a.val + 1, by omega⟩ : Fin (n + 1)) := by
  apply Fin.ext
  change (cyclicVertexIndex a.castSucc 0).val = a.val + 1
  rw [cyclicVertexIndex_val a.castSucc (k := 0) (by omega)]
  have hval : a.castSucc.val = a.val := rfl
  rw [hval]
  have ha := a.isLt
  split_ifs <;> omega

theorem truncateCyclicCorner_off_short {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p : Fin n) (scale ε : ℝ)
    (i : Fin (n + 1)) (hi : i ≠ a.castSucc) :
    truncateCyclicCorner q a p scale ε i =
      if collapseFin a i = a then
        q a + (ε * scale) • (q (cyclicSuccessor a) - q a)
      else q (collapseFin a i) := by
  by_cases hc : collapseFin a i = a
  · rw [if_pos hc]
    have heq := (collapseFin_eq_a_iff a i).mp hc
    rcases heq with heq | heq
    · exact False.elim (hi heq)
    · rw [heq]
      exact truncateCyclicCorner_new q a p scale ε
  · rw [if_neg hc]
    exact truncateCyclicCorner_of_collapse_ne q a p scale ε i hc

theorem truncateCyclicCorner_successor_off_short {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p : Fin n) (scale ε : ℝ)
    (i : Fin (n + 1)) (hi : i ≠ a.castSucc) :
    truncateCyclicCorner q a p scale ε (cyclicSuccessor i) =
      if cyclicSuccessor (collapseFin a i) = a then
        q a + ε • (q p - q a)
      else q (cyclicSuccessor (collapseFin a i)) := by
  have hsucc := collapseFin_cyclicSuccessor a i hi
  by_cases hc : cyclicSuccessor (collapseFin a i) = a
  · rw [if_pos hc]
    have hcollapse : collapseFin a (cyclicSuccessor i) = a := hsucc.trans hc
    rcases (collapseFin_eq_a_iff a (cyclicSuccessor i)).mp hcollapse with heq | heq
    · rw [heq]
      exact truncateCyclicCorner_anchor q a p scale ε
    · have hi' : i = a.castSucc :=
        (cyclicSuccessor_bijective (n := n + 1)).injective
          (heq.trans (cyclicSuccessor_shortEdge a).symm)
      exact False.elim (hi hi')
  · rw [if_neg hc]
    have hcollapse : collapseFin a (cyclicSuccessor i) ≠ a := by
      rw [hsucc]
      exact hc
    rw [truncateCyclicCorner_of_collapse_ne q a p scale ε (cyclicSuccessor i) hcollapse]
    rw [hsucc]

end DirectGLSSW.TruncationDirection
