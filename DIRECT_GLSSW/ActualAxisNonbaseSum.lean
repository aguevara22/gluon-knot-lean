import ActualAxisReindex

set_option autoImplicit false
noncomputable section
open DirectGLSSW
attribute [local instance] Classical.propDecidable

namespace DirectGLSSW.HOMFLY.PLWinding

/-- The actual secant-axis interior sum is minus the literal sum of
principal arguments over the nonbase edges of the original component
word, evaluated at its actual base midpoint. -/
theorem actualAxis_whole_eq_neg_nonBaseArgSum {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0, componentArcLength_pos D e⟩
    let z := normalAtEdgeMidpoint q i₀ 0
    (∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
      (fun ab => (1/4 : ℝ) ≤ ab.1 ∧ ab.2 ≤ (m : ℝ)-1/4),
      Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.2)) =
      -nonBaseArgSum q i₀ z := by
  intro e m q i₀ z
  let S : ℝ → ℝ → ℝ := fun L R =>
    ∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
      (fun ab => L ≤ ab.1 ∧ ab.2 ≤ R),
      Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.2)
  let g : Fin m → ℝ := fun j =>
    Complex.arg ((q (cyclicSuccessorPerm m j)-z)/(q j-z))
  have hwindow (k : ℕ) (hk : k ∈ Finset.range (m-1)) :
      S ((k : ℝ)+1/2) ((k : ℝ)+3/2) =
        -g (⟨(k+1)%m, Nat.mod_lt _ (componentArcLength_pos D e)⟩ : Fin m) := by
    have hkm : k+1 < m := by
      have := Finset.mem_range.mp hk
      omega
    let j : Fin m := ⟨k+1,hkm⟩
    have hj : j ≠ i₀ := by
      intro heq
      have hv := congrArg Fin.val heq
      dsimp [j,i₀] at hv
      omega
    have h := actualWord_nonbase_axis_interval_sum_actual T C j hj
    have hL : (j.val : ℝ)-1/2 = (k : ℝ)+1/2 := by
      dsimp [j]
      push_cast
      ring
    have hR : (j.val : ℝ)+1/2 = (k : ℝ)+3/2 := by
      dsimp [j]
      push_cast
      ring
    have hmod : (⟨(k+1)%m, Nat.mod_lt _ (componentArcLength_pos D e)⟩ : Fin m) = j := by
      apply Fin.ext
      dsimp [j]
      rw [Nat.mod_eq_of_lt hkm]
    rw [hmod]
    change S ((j.val : ℝ)-1/2) ((j.val : ℝ)+1/2) = -g j at h
    rw [hL,hR] at h
    exact h
  have hrange : (∑ k ∈ Finset.range (m-1),
        S ((k : ℝ)+1/2) ((k : ℝ)+3/2)) =
      -(∑ k ∈ Finset.range (m-1),
        g (⟨(k+1)%m, Nat.mod_lt _ (componentArcLength_pos D e)⟩ : Fin m)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hwindow
  have hreindex : nonBaseArgSum q i₀ z =
      ∑ k ∈ Finset.range (m-1),
        g (⟨(k+1)%m, Nat.mod_lt _ (componentArcLength_pos D e)⟩ : Fin m) :=
    actualWord_sum_erase_zero_eq_range m (componentArcLength_pos D e) g
  change S (1/4) ((m : ℝ)-1/4) = -nonBaseArgSum q i₀ z
  calc
    S (1/4) ((m : ℝ)-1/4) =
        ∑ k ∈ Finset.range (m-1), S ((k : ℝ)+1/2) ((k : ℝ)+3/2) :=
      actualAxis_whole_nonbase_window_sum T C
    _ = -(∑ k ∈ Finset.range (m-1),
        g (⟨(k+1)%m, Nat.mod_lt _ (componentArcLength_pos D e)⟩ : Fin m)) := hrange
    _ = -nonBaseArgSum q i₀ z := by rw [hreindex]

end DirectGLSSW.HOMFLY.PLWinding
