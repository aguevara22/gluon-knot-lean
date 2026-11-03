import DescendingHeightArcs

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial

/-- Uniform first/last quarter cells and whole intermediate cells. -/
def splitTraversalTime (m : ℕ) (t : ℝ) : ℝ :=
  3/4 + ((m:ℝ)+1)*t/4 +
    3/4 * min (max (((m:ℝ)+1)*t-1) 0) ((m:ℝ)-1)

theorem splitTraversalTime_eq_literal (m : ℕ) (t : ℝ) :
    splitTraversalTime m t = 3/4 + ((m:ℝ)+1)*t/4 +
      3/4 * min (max (((m:ℝ)+1)*t-1) 0) ((m:ℝ)-1) := rfl

theorem splitTraversalTime_continuous (m : ℕ) :
    Continuous (splitTraversalTime m) := by
  unfold splitTraversalTime
  fun_prop

theorem splitTraversalTime_first (m : ℕ) (hm : 0 < m) (t : ℝ)
    (ht : ((m:ℝ)+1)*t ≤ 1) :
    splitTraversalTime m t = 3/4 + ((m:ℝ)+1)*t/4 := by
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  simp only [splitTraversalTime, max_eq_right (by linarith : ((m:ℝ)+1)*t-1 ≤ 0),
    min_eq_left (by linarith : (0:ℝ) ≤ (m:ℝ)-1), mul_zero, add_zero]

theorem splitTraversalTime_middle (m : ℕ) (t : ℝ)
    (ht : 1 ≤ ((m:ℝ)+1)*t) (ht' : ((m:ℝ)+1)*t ≤ m) :
    splitTraversalTime m t = ((m:ℝ)+1)*t := by
  rw [splitTraversalTime, max_eq_left (by linarith : 0 ≤ ((m:ℝ)+1)*t-1),
    min_eq_left (by linarith : ((m:ℝ)+1)*t-1 ≤ (m:ℝ)-1)]
  ring

theorem splitTraversalTime_last (m : ℕ) (hm : 0 < m) (t : ℝ)
    (ht : (m:ℝ) ≤ ((m:ℝ)+1)*t) :
    splitTraversalTime m t = (m:ℝ) + (((m:ℝ)+1)*t-m)/4 := by
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  rw [splitTraversalTime, max_eq_left (by linarith : 0 ≤ ((m:ℝ)+1)*t-1),
    min_eq_right (by linarith : (m:ℝ)-1 ≤ ((m:ℝ)+1)*t-1)]
  ring

theorem splitTraversalTime_endpoints (m : ℕ) (hm : 0 < m) :
    splitTraversalTime m 0 = 3/4 ∧ splitTraversalTime m 1 = (m:ℝ)+1/4 := by
  constructor
  · rw [splitTraversalTime_first m hm 0 (by simp)]
    ring
  · rw [splitTraversalTime_last m hm 1 (by linarith)]
    ring

end DirectGLSSW.DescendingSpatial






