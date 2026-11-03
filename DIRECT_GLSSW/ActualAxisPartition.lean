import ActualAxisIntervalSplit

set_option autoImplicit false
noncomputable section
open DirectGLSSW
attribute [local instance] Classical.propDecidable

namespace DirectGLSSW.HOMFLY.PLWinding

/-- Iterating the actual-cut split partitions the secant-axis cells from
the first original knot through any later original knot into the full
nonbase edge windows. The summand is arbitrary. -/
theorem actualAxis_nonbase_windows_partition {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D)
    (n : ℕ) (hn : n + 1 < componentArcLength D (T.baseArc C).val)
    (f : ℝ × ℝ → ℝ) :
    let S : ℝ → ℝ → ℝ := fun L R =>
      ∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
        (fun ab => L ≤ ab.1 ∧ ab.2 ≤ R), f ab
    S (1/2) ((n : ℝ) + 3/2) =
      ∑ k ∈ Finset.range (n+1),
        S ((k : ℝ) + 1/2) ((k : ℝ) + 3/2) := by
  intro S
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_add, Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, Nat.zero_add]
  | succ n ih =>
      have hn' : n + 1 < componentArcLength D (T.baseArc C).val := by omega
      have hih := ih hn'
      have hcut : (n : ℝ) + 3/2 ∈ PrincipalTurning.secantAxisCuts T C := by
        have h := PrincipalTurning.secantAxisCuts_original_knot T C (n+1) (by omega)
        convert h using 1 <;> push_cast <;> ring
      have hsplit : S (1/2) ((n : ℝ) + 5/2) =
          S (1/2) ((n : ℝ) + 3/2) +
          S ((n : ℝ) + 3/2) ((n : ℝ) + 5/2) := by
        exact actualAxis_interval_sum_split T C (1/2) ((n : ℝ) + 3/2)
          ((n : ℝ) + 5/2) (by linarith) (by linarith) hcut f
      calc
        S (1/2) (((n+1 : ℕ) : ℝ) + 3/2) =
            S (1/2) ((n : ℝ) + 5/2) := by congr 1; push_cast; ring
        _ = S (1/2) ((n : ℝ) + 3/2) +
            S ((n : ℝ) + 3/2) ((n : ℝ) + 5/2) := hsplit
        _ = (∑ k ∈ Finset.range (n+1),
              S ((k : ℝ) + 1/2) ((k : ℝ) + 3/2)) +
            S ((n : ℝ) + 3/2) ((n : ℝ) + 5/2) := by rw [hih]
        _ = ∑ k ∈ Finset.range ((n+1)+1),
              S ((k : ℝ) + 1/2) ((k : ℝ) + 3/2) := by
            conv_rhs => rw [Finset.sum_range_succ]
            congr 1 <;> push_cast <;> ring

end DirectGLSSW.HOMFLY.PLWinding
