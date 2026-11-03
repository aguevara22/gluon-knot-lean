import DirectGLSSW.CurrentTranslation
import DirectGLSSW.EndpointCurrent
import DirectGLSSW.EndpointActualRecurrence
import DirectGLSSW.OpenMarkedCurrent
import DirectGLSSW.RealPolygons

set_option autoImplicit false
namespace DirectGLSSW.OpenMarkedCurrent
open DirectGLSSW.EndpointCurrent
open scoped BigOperators

theorem weightedCutSum_succ_local (w : ℕ → ℚ) (b : IntervalArray) (i j : ℕ) :
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

theorem entry_translate_succ_local (H : TripleArray) {i j : ℕ} (hij : i < j) :
    entry (CurrentTranslation.translateTriple 1 H) i j = entry H (i+1) (j+1) := by
  unfold entry
  rw [← weightedCutSum_succ_local]
  apply EndpointCurrent.weightedCutSum_congr_of_branch_eq _ hij
  intro a b hia hab hbj
  simpa only [CurrentTranslation.translateTriple] using
    CurrentTranslation.ordinaryCurrent_translate_succ
      (fun _ _ _ => -1) H a b hab

/-- Reindexing every used interval and cut by an arbitrary fixed offset
reindexes the literal open current by that offset. -/
theorem entry_translate_offset (H : TripleArray) (K : ℕ) {i j : ℕ}
    (hij : i < j) :
    entry (CurrentTranslation.translateTriple K H) i j =
      entry H (i + K) (j + K) := by
  induction K generalizing i j with
  | zero =>
      have hzero : CurrentTranslation.translateTriple 0 H = H := by
        funext a b c
        simp [CurrentTranslation.translateTriple]
      rw [hzero]
      simp
  | succ K ih =>
      have hcompose (A : TripleArray) :
          CurrentTranslation.translateTriple (K + 1) A =
            CurrentTranslation.translateTriple 1
              (CurrentTranslation.translateTriple K A) := by
        funext a b c
        simp only [CurrentTranslation.translateTriple]
        congr 1 <;> omega
      rw [hcompose H, entry_translate_succ_local _ hij]
      calc
        entry (CurrentTranslation.translateTriple K H) (i + 1) (j + 1) =
            entry H ((i + 1) + K) ((j + 1) + K) :=
          ih (i := i + 1) (j := j + 1) (by omega)
        _ = entry H (i + (K + 1)) (j + (K + 1)) := by
          congr 1 <;> omega

/-- The endpoint-parent current is the ordinary marked current of its literal
point word `W 0, W (K+1), …`; only ordered triples on the used interval matter. -/
theorem endpointFar_entry_reindexed
    (W : ℕ → PlanarPoint ℝ) (K N : ℕ) (hKN : K < N) :
    entry (EndpointCurrent.endpointFar K (polygonSignArray W)) K N =
      entry (polygonSignArray (fun i => if i = 0 then W 0 else W (K + i))) 0 (N - K) := by
  let Hparent : TripleArray := EndpointCurrent.endpointFar K (polygonSignArray W)
  let Wlocal : ℕ → PlanarPoint ℝ := fun i => if i = 0 then W 0 else W (K + i)
  have hlocal : ∀ a b c, a < b → b < c →
      CurrentTranslation.translateTriple K Hparent a b c =
        polygonSignArray Wlocal a b c := by
    intro a b c hab hbc
    by_cases ha : a = 0
    · subst a
      have hb : b ≠ 0 := by omega
      have hc : c ≠ 0 := by omega
      simp [CurrentTranslation.translateTriple, Hparent, Wlocal,
        EndpointCurrent.endpointFar, endpointFar, polygonSignArray,
        polygonHDet, hb, hc]
    · have hb : b ≠ 0 := by omega
      have hc : c ≠ 0 := by omega
      have hKa : K + a ≠ K := by omega
      simp [CurrentTranslation.translateTriple, Hparent, Wlocal,
        EndpointCurrent.endpointFar, endpointFar, polygonSignArray,
        polygonHDet, ha, hb, hc, hKa]
  have htrans := entry_translate_offset Hparent K (i := 0) (j := N - K) (by omega)
  have htranslate :
      entry (CurrentTranslation.translateTriple K Hparent) 0 (N - K) =
        entry Hparent K N := by
    simpa [Nat.sub_add_cancel (Nat.le_of_lt hKN)] using htrans
  calc
    entry (EndpointCurrent.endpointFar K (polygonSignArray W)) K N =
        entry (CurrentTranslation.translateTriple K Hparent) 0 (N - K) := by
          simpa [Hparent] using htranslate.symm
    _ = entry (polygonSignArray Wlocal) 0 (N - K) := by
      change weightedCutSum (fun _ : ℕ => -1)
          (ordinaryCurrent (fun _ _ _ => -1)
            (CurrentTranslation.translateTriple K Hparent)) 0 (N - K) =
        weightedCutSum (fun _ : ℕ => -1)
          (ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray Wlocal)) 0 (N - K)
      apply EndpointCurrent.weightedCutSum_congr_of_branch_eq (fun _ => -1) (by omega)
      intro a b ha hab hb
      apply ordinaryCurrent_congr_interval_fixed_near _ _ _ hab
      intro x y z hax hxy hyz hzb
      exact hlocal x y z hxy hyz




end DirectGLSSW.OpenMarkedCurrent
