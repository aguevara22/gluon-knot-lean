import ActualAxisBaseFragments

set_option autoImplicit false
noncomputable section
open DirectGLSSW
attribute [local instance] Classical.propDecidable

namespace DirectGLSSW.HOMFLY.PLWinding

/-- An actual diagram component contains at least two arcs: a one-arc
continuation orbit would identify that arc's distinct endpoints. -/
theorem actualComponentArcLength_ge_two {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    2 ≤ componentArcLength D (T.baseArc C).val := by
  let e := (T.baseArc C).val
  let m := componentArcLength D e
  have hmpos : 0 < m := componentArcLength_pos D e
  by_contra hn
  have hn' : ¬ 2 ≤ m := by simpa [m, e] using hn
  have hm1 : m = 1 := by omega
  have hpow := continuation_pow_componentArcLength D e
  change (D.continuation ^ m) e = e at hpow
  rw [hm1, pow_one] at hpow
  have hinc := D.continuation_incidence e
  rw [hpow] at hinc
  exact D.arc_endpoints_distinct e hinc.symm

/-- The whole exterior secant-axis interior sum is precisely the sum of
the full actual nonbase edge windows. The two omitted base fragments
are zero by their literal secant geometry. -/
theorem actualAxis_whole_nonbase_window_sum {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    let m := componentArcLength D (T.baseArc C).val
    let S : ℝ → ℝ → ℝ := fun L R =>
      ∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
        (fun ab => L ≤ ab.1 ∧ ab.2 ≤ R),
        Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
          PrincipalTurning.basedUniformSecant T C 0 ab.2)
    S (1/4) ((m : ℝ) - 1/4) =
      ∑ k ∈ Finset.range (m-1),
        S ((k : ℝ) + 1/2) ((k : ℝ) + 3/2) := by
  intro m S
  have hm : 2 ≤ m := actualComponentArcLength_ge_two T C
  have hmr : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hfirstCut : (1/2 : ℝ) ∈ PrincipalTurning.secantAxisCuts T C := by
    simpa using PrincipalTurning.secantAxisCuts_original_knot T C 0 (by omega)
  have hlastCut : (m : ℝ) - 1/2 ∈ PrincipalTurning.secantAxisCuts T C := by
    have h := PrincipalTurning.secantAxisCuts_original_knot T C (m-1) (by omega)
    convert h using 1 <;> rw [Nat.cast_sub (by omega : 1 ≤ m)] <;>
      push_cast <;> ring
  have hsplit1 : S (1/4) ((m : ℝ) - 1/4) =
      S (1/4) (1/2) + S (1/2) ((m : ℝ) - 1/4) :=
    actualAxis_interval_sum_split T C (1/4) (1/2) ((m : ℝ)-1/4)
      (by norm_num) (by linarith) hfirstCut _
  have hsplit2 : S (1/2) ((m : ℝ) - 1/4) =
      S (1/2) ((m : ℝ) - 1/2) +
      S ((m : ℝ) - 1/2) ((m : ℝ) - 1/4) :=
    actualAxis_interval_sum_split T C (1/2) ((m : ℝ)-1/2)
      ((m : ℝ)-1/4) (by linarith)
      (by linarith) hlastCut _
  have hzero1 : S (1/4) (1/2) = 0 :=
    actualAxis_initial_base_fragment_zero T C
  have hzero2 : S ((m : ℝ)-1/2) ((m : ℝ)-1/4) = 0 :=
    actualAxis_return_base_fragment_zero T C
  have hmid : S (1/2) ((m : ℝ)-1/2) =
      ∑ k ∈ Finset.range (m-1),
        S ((k : ℝ)+1/2) ((k : ℝ)+3/2) := by
    have hn := actualAxis_nonbase_windows_partition T C (m-2)
      (by omega : m-2+1 < m)
      (fun ab => Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.2))
    have hnum : m-2+1=m-1 := by omega
    have hreal : (((m-2 : ℕ) : ℝ)+3/2) = (m : ℝ)-1/2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ m)]
      push_cast
      ring
    simpa only [hnum, hreal] using hn
  rw [hsplit1, hzero1, zero_add, hsplit2, hzero2, add_zero, hmid]

end DirectGLSSW.HOMFLY.PLWinding
