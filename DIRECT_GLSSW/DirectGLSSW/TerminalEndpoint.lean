import DirectGLSSW.EndpointDirectSource
import DirectGLSSW.SpinorVertices

set_option autoImplicit false

namespace DirectGLSSW.TerminalEndpoint
open DirectGLSSW

/-- Replace every far gate ending at the terminal vertex by the closing gate to q₀. -/
def terminalFar (z : ℕ) (H : TripleArray) : TripleArray :=
  fun i k j => if j = z then H i k 0 else H i k j

/-- Close a finite polygon word at the fixed point q₀. -/
def terminalWord {K : Type*} (q : ℕ → PlanarPoint K) (z x : ℕ) : PlanarPoint K :=
  if x = z then q 0 else q x

/-- The terminal current for the word q_(a+1), …, q_(b+1), q₀. -/
noncomputable def terminalCurrent (d : ℕ → ℚ) (H : TripleArray) (a b : ℕ) : ℚ :=
  if a ≤ b then
    ordinaryCurrent (fun _ k _ => d k) (terminalFar (b + 2) H) (a + 1) (b + 2)
  else 0

/-- The actual sign array of the closed terminal word is its terminal far array. -/
theorem terminalFar_polygonSignArray_congr {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (q : ℕ → PlanarPoint K) {i k j z : ℕ}
    (hik : i < k) (hkj : k < j) (hjz : j ≤ z) :
    polygonSignArray (terminalWord q z) i k j =
      terminalFar z (polygonSignArray q) i k j := by
  by_cases hj : j = z
  · have hi : i ≠ z := by omega
    have hk : k ≠ z := by omega
    simp [polygonSignArray, polygonHDet, terminalWord, terminalFar, hj, hi, hk]
  · have hi : i ≠ z := by omega
    have hk : k ≠ z := by omega
    simp [polygonSignArray, polygonHDet, terminalWord, terminalFar, hj, hi, hk]

/-- The terminal current is the actual ordinary current on the closed polygon word. -/
theorem terminalCurrent_polygon_eq {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (q : ℕ → PlanarPoint K) (d : ℕ → ℚ) {a b : ℕ} (hab : a ≤ b) :
    terminalCurrent d (polygonSignArray q) a b =
      ordinaryCurrent (fun _ k _ => d k)
        (polygonSignArray (terminalWord q (b + 2))) (a + 1) (b + 2) := by
  rw [terminalCurrent, if_pos hab]
  apply ordinaryCurrent_congr_interval_fixed_near _ _ _ (by omega)
  intro i k j _ hik hkj hjz
  exact (terminalFar_polygonSignArray_congr q hik hkj hjz).symm

/-- Diagonal entries of the terminal-current array are one. -/
theorem terminalCurrent_diagonal (d : ℕ → ℚ) (H : TripleArray) (a : ℕ) :
    terminalCurrent d H a a = 1 := by
  simp [terminalCurrent]

/-- Entries below the diagonal vanish. -/
theorem terminalCurrent_below (d : ℕ → ℚ) (H : TripleArray)
    {a b : ℕ} (hba : b < a) : terminalCurrent d H a b = 0 := by
  have hnot : ¬ a ≤ b := by omega
  simp [terminalCurrent, hnot]









end DirectGLSSW.TerminalEndpoint
