import DirectGLSSW.ShortEdgeCyclicGeometry

namespace DirectGLSSW.TruncationEdgeLift

open DirectGLSSW
open DirectGLSSW.ShortEdgeCyclicAdapter
open DirectGLSSW.ShortEdgeCutFibers

def edgeLift {n : ℕ} (a e : Fin n) : Fin (n + 1) :=
  ⟨if e.val < a.val then e.val else e.val + 1, by
    by_cases h : e.val < a.val
    · simp only [if_pos h]
      have he := e.isLt
      omega
    · simp only [if_neg h]
      have he := e.isLt
      omega⟩

theorem collapseFin_edgeLift {n : ℕ} (a e : Fin n) :
    DirectGLSSW.ShortEdgeCyclicAdapter.collapseFin a (edgeLift a e) = e := by
  apply Fin.ext
  change collapseAfter a.val (if e.val < a.val then e.val else e.val + 1) = e.val
  by_cases hlt : e.val < a.val
  · rw [if_pos hlt]
    exact collapseAfter_eq_of_le a.val e.val (Nat.le_of_lt hlt)
  · by_cases heq : e.val = a.val
    · rw [if_neg hlt, heq]
      exact collapseAfter_eq_sub_one_of_lt a.val (a.val + 1) (by omega)
    · have hgt : a.val < e.val := by omega
      rw [if_neg hlt]
      exact collapseAfter_eq_sub_one_of_lt a.val (e.val + 1) (by omega)

theorem edgeLift_ne_short {n : ℕ} (a e : Fin n) :
    edgeLift a e ≠ a.castSucc := by
  intro h
  have hv := congrArg Fin.val h
  simp only [edgeLift, Fin.val_mk] at hv
  by_cases he : e.val < a.val <;> simp [he] at hv <;> omega

theorem edgeLift_injective {n : ℕ} (a : Fin n) : Function.Injective (edgeLift a) := by
  intro e f h
  have hcoll := congrArg (DirectGLSSW.ShortEdgeCyclicAdapter.collapseFin a) h
  rw [collapseFin_edgeLift, collapseFin_edgeLift] at hcoll
  exact hcoll

theorem edgeLift_strictMono {n : ℕ} (a : Fin n) : StrictMono (edgeLift a) := by
  intro e f hef
  apply Fin.mk_lt_mk.mpr
  change (if e.val < a.val then e.val else e.val + 1) <
    (if f.val < a.val then f.val else f.val + 1)
  by_cases he : e.val < a.val <;> by_cases hf : f.val < a.val <;> simp [he, hf] <;> omega

theorem edgeLift_collapseFin {n : ℕ} (a : Fin n) (i : Fin (n + 1))
    (hi : i ≠ a.castSucc) : edgeLift a (DirectGLSSW.ShortEdgeCyclicAdapter.collapseFin a i) = i := by
  have hval : i.val ≠ a.val := fun h => hi (Fin.ext h)
  apply Fin.ext
  simp only [edgeLift, Fin.val_mk]
  change (if (DirectGLSSW.ShortEdgeCyclicAdapter.collapseFin a i).val < a.val then (DirectGLSSW.ShortEdgeCyclicAdapter.collapseFin a i).val
    else (DirectGLSSW.ShortEdgeCyclicAdapter.collapseFin a i).val + 1) = i.val
  by_cases hlt : i.val < a.val
  · have hc : (DirectGLSSW.ShortEdgeCyclicAdapter.collapseFin a i).val = i.val := by
      change collapseAfter a.val i.val = i.val
      exact collapseAfter_eq_of_le a.val i.val (Nat.le_of_lt hlt)
    rw [if_pos (by simpa [hc] using hlt), hc]
  · have hgt : a.val < i.val := by omega
    have hc : (DirectGLSSW.ShortEdgeCyclicAdapter.collapseFin a i).val = i.val - 1 := by
      change collapseAfter a.val i.val = i.val - 1
      exact collapseAfter_eq_sub_one_of_lt a.val i.val hgt
    have hnot : ¬ (DirectGLSSW.ShortEdgeCyclicAdapter.collapseFin a i).val < a.val := by omega
    rw [if_neg hnot, hc]
    omega

end DirectGLSSW.TruncationEdgeLift
