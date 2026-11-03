import DirectGLSSW.ShortEdgeCyclicAdapter
import DirectGLSSW.PolygonGeometry
import DirectGLSSW.ShortEdgeCutFibers

namespace DirectGLSSW.ShortEdgeCyclicAdapter

open DirectGLSSW
open DirectGLSSW.ShortEdgeCutFibers

/-- Collapse the duplicate vertex label in the inserted polygon. -/
def collapseFin {n : ℕ} (a : Fin n) (i : Fin (n + 1)) : Fin n :=
  ⟨collapseAfter a.val i.val, by
    by_cases h : i.val ≤ a.val
    · rw [collapseAfter_eq_of_le a.val i.val h]
      exact lt_of_le_of_lt h a.isLt
    · rw [collapseAfter_eq_sub_one_of_lt a.val i.val (by omega)]
      have hi := i.isLt
      omega⟩

theorem collapseFin_eq_a_iff {n : ℕ} (a : Fin n) (i : Fin (n + 1)) :
    collapseFin a i = a ↔
      i = a.castSucc ∨ i = ⟨a.val + 1, by omega⟩ := by
  constructor
  · intro h
    have hv : collapseAfter a.val i.val = a.val := congrArg Fin.val h
    by_cases hle : i.val ≤ a.val
    · rw [collapseAfter_eq_of_le a.val i.val hle] at hv
      left
      exact Fin.ext hv
    · rw [collapseAfter_eq_sub_one_of_lt a.val i.val (by omega)] at hv
      right
      apply Fin.ext
      change i.val = a.val + 1
      have hi := i.isLt
      have ha := a.isLt
      omega
  · rintro (h | h)
    · apply Fin.ext
      have hv : i.val = a.val := congrArg Fin.val h
      change collapseAfter a.val i.val = a.val
      rw [hv]
      simp [collapseAfter]
    · apply Fin.ext
      have hv : i.val = a.val + 1 := congrArg Fin.val h
      change collapseAfter a.val i.val = a.val
      rw [hv]
      simp [collapseAfter]

theorem collapseFin_injective_off_shortEdge {n : ℕ} (a : Fin n)
    (i j : Fin (n + 1)) (hi : i ≠ a.castSucc) (hj : j ≠ a.castSucc)
    (hcollapse : collapseFin a i = collapseFin a j) : i = j := by
  have hv : collapseAfter a.val i.val = collapseAfter a.val j.val := congrArg Fin.val hcollapse
  have hi' : i.val ≠ a.val := fun h => hi (Fin.ext h)
  have hj' : j.val ≠ a.val := fun h => hj (Fin.ext h)
  have hiLt := i.isLt
  have hjLt := j.isLt
  have haLt := a.isLt
  by_cases hii : i.val ≤ a.val <;> by_cases hjj : j.val ≤ a.val
  · rw [collapseAfter_eq_of_le a.val i.val hii,
        collapseAfter_eq_of_le a.val j.val hjj] at hv
    exact Fin.ext hv
  · rw [collapseAfter_eq_of_le a.val i.val hii,
        collapseAfter_eq_sub_one_of_lt a.val j.val (by omega)] at hv
    apply Fin.ext
    omega
  · rw [collapseAfter_eq_sub_one_of_lt a.val i.val (by omega),
        collapseAfter_eq_of_le a.val j.val hjj] at hv
    apply Fin.ext
    omega
  · rw [collapseAfter_eq_sub_one_of_lt a.val i.val (by omega),
        collapseAfter_eq_sub_one_of_lt a.val j.val (by omega)] at hv
    apply Fin.ext
    omega

private theorem cyclicSuccessor_val_formula {n : ℕ} (i : Fin n) :
    (cyclicSuccessor i).val = if i.val + 1 < n then i.val + 1 else 0 := by
  change (cyclicVertexIndex i 0).val = _
  rw [cyclicVertexIndex_val i (k := 0) (by have := i.isLt; omega)]
  split_ifs <;> omega

theorem collapseFin_cyclicSuccessor {n : ℕ} (a : Fin n)
    (i : Fin (n + 1)) (hi : i ≠ a.castSucc) :
    collapseFin a (cyclicSuccessor i) = cyclicSuccessor (collapseFin a i) := by
  have hi' : i.val ≠ a.val := fun h => hi (Fin.ext h)
  have hsuccP := cyclicSuccessor_val_formula i
  have hsuccC := cyclicSuccessor_val_formula (collapseFin a i)
  apply Fin.ext
  change collapseAfter a.val (cyclicSuccessor i).val =
    (cyclicSuccessor (collapseFin a i)).val
  by_cases hia : i.val < a.val
  · have hci : (collapseFin a i).val = i.val := by
      simp [collapseFin, collapseAfter, Nat.le_of_lt hia]
    rw [hsuccP, if_pos (by omega : i.val + 1 < n + 1)]
    rw [collapseAfter_eq_of_le a.val (i.val + 1) (by omega)]
    rw [hsuccC, hci, if_pos (by omega : i.val + 1 < n)]
  · by_cases hin : i.val = n
    · have hci : (collapseFin a i).val = n - 1 := by
        change collapseAfter a.val i.val = n - 1
        rw [hin]
        exact collapseAfter_eq_sub_one_of_lt a.val n (by omega)
      rw [hsuccP, if_neg (by omega : ¬ i.val + 1 < n + 1)]
      rw [collapseAfter_eq_of_le a.val 0 (by omega)]
      rw [hsuccC, hci, if_neg (by omega : ¬ (n - 1) + 1 < n)]
    · have hia' : a.val < i.val := by omega
      have hci : (collapseFin a i).val = i.val - 1 := by
        simp [collapseFin, collapseAfter, Nat.not_le.mpr hia']
      rw [hsuccP, if_pos (by omega : i.val + 1 < n + 1)]
      rw [collapseAfter_eq_sub_one_of_lt a.val (i.val + 1) (by omega)]
      rw [hsuccC, hci, if_pos (by omega : (i.val - 1) + 1 < n)]
      omega

theorem insertCyclicAfter_zero {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (a : Fin n) (v : PlanarPoint ℝ) (i : Fin (n + 1)) :
    insertCyclicAfter q a 0 v i = q (collapseFin a i) := by
  by_cases hle : i.val ≤ a.val
  · simp [insertCyclicAfter, collapseFin, collapseAfter, hle]
  · by_cases hmid : i.val = a.val + 1
    · simp [insertCyclicAfter, collapseFin, collapseAfter, hle, hmid]
    · simp [insertCyclicAfter, collapseFin, collapseAfter, hle, hmid]

end DirectGLSSW.ShortEdgeCyclicAdapter
