import DirectGLSSW.CurrentTranslation
import DirectGLSSW.OpenMarkedCurrent
import DirectGLSSW.EndpointActualRecurrence

set_option autoImplicit false
namespace DirectGLSSW.OpenMarkedCurrent
open scoped BigOperators

/-- Shift every actual internal cut and every branch endpoint by one. -/
theorem weightedCutSum_succ (w : ℕ → ℚ) (b : IntervalArray) (i j : ℕ) :
    weightedCutSum (fun k => w (k+1)) (fun x y => b (x+1) (y+1)) i j =
      weightedCutSum w b (i+1) (j+1) := by
  classical
  unfold weightedCutSum
  apply Finset.sum_bij (fun S _ => S.image Nat.succ)
  · intro S hS
    apply Finset.mem_powerset.mpr
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y,hy,rfl⟩
    have hyI := Finset.mem_Ioo.mp (Finset.mem_powerset.mp hS hy)
    simp only [Finset.mem_Ioo]
    omega
  · intro S hS T hT hST
    exact Finset.image_injective Nat.succ_injective hST
  · intro T hT
    refine ⟨T.image Nat.pred, ?_, ?_⟩
    · apply Finset.mem_powerset.mpr
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨y,hy,rfl⟩
      have hyI := Finset.mem_Ioo.mp (Finset.mem_powerset.mp hT hy)
      simp only [Finset.mem_Ioo, Nat.pred_eq_sub_one]
      omega
    · ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨y,⟨z,hz,hzy⟩,hyx⟩
        have hzI := Finset.mem_Ioo.mp (Finset.mem_powerset.mp hT hz)
        have hzpos : 0 < z := by omega
        rw [← hzy, Nat.succ_pred_eq_of_pos hzpos] at hyx
        exact hyx ▸ hz
      · intro hx
        have hxI := Finset.mem_Ioo.mp (Finset.mem_powerset.mp hT hx)
        refine ⟨Nat.pred x,⟨x,hx,rfl⟩,?_⟩
        exact Nat.succ_pred_eq_of_pos (by omega)
  · intro S hS
    rw [ShortEdgeWeighted.cutVertices_succ_image,
      ShortEdgeWeighted.branchProduct_map]
    rw [Finset.prod_image]
    intro x hx y hy hxy
    exact Nat.succ_injective hxy

/-- Translation of the literal open current; only strict intervals are used. -/
theorem entry_translate_succ (H : TripleArray) {i j : ℕ} (hij : i < j) :
    entry (CurrentTranslation.translateTriple 1 H) i j = entry H (i+1) (j+1) := by
  unfold entry
  rw [← weightedCutSum_succ]
  apply EndpointCurrent.weightedCutSum_congr_of_branch_eq _ hij
  intro a b hia hab hbj
  simpa only [CurrentTranslation.translateTriple] using
    CurrentTranslation.ordinaryCurrent_translate_succ (fun _ _ _ => -1) H a b hab

/-- Dropping a literal first vertex shifts the current's two endpoints. -/
theorem entry_tail_word (q : ℕ → PlanarPoint ℝ) {n : ℕ} (hn : 0<n) :
    entry (polygonSignArray (fun k => q (k+1))) 0 n =
      entry (polygonSignArray q) 1 (n+1) := by
  have hs : polygonSignArray (fun k => q (k+1)) =
      CurrentTranslation.translateTriple 1 (polygonSignArray q) := by
    funext x y z
    simp only [CurrentTranslation.translateTriple,polygonSignArray,polygonHDet]
    simp only [Nat.add_comm]
  rw [hs]
  exact entry_translate_succ _ hn

end DirectGLSSW.OpenMarkedCurrent
