import ActualAxisNonbase
import ActualAxisPotentialSum

set_option autoImplicit false
noncomputable section
open DirectGLSSW
attribute [local instance] Classical.propDecidable

namespace DirectGLSSW.HOMFLY.PLWinding

/-- On a full actual nonbase edge, the finite secant-axis subdivision
telescopes to its one original principal-angle increment. The endpoint
cut membership is made explicit here and discharged from the actual
finite cut set in the next assembly. -/
theorem actualWord_nonbase_axis_interval_sum {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D)
    (j : Fin (componentArcLength D (T.baseArc C).val))
    (hj : j ≠ (⟨0, componentArcLength_pos D (T.baseArc C).val⟩ :
      Fin (componentArcLength D (T.baseArc C).val)))
    (hL : (j.val : ℝ) - 1/2 ∈ PrincipalTurning.secantAxisCuts T C)
    (hR : (j.val : ℝ) + 1/2 ∈ PrincipalTurning.secantAxisCuts T C) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0, componentArcLength_pos D e⟩
    let L : ℝ := (j.val : ℝ) - 1/2
    let R : ℝ := (j.val : ℝ) + 1/2
    (∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
      (fun ab => L ≤ ab.1 ∧ ab.2 ≤ R),
      Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.2)) =
      -Complex.arg ((q (cyclicSuccessorPerm m j) - normalAtEdgeMidpoint q i₀ 0) /
        (q j - normalAtEdgeMidpoint q i₀ 0)) := by
  intro e m q i₀ L R
  let A : ℂ := q j - normalAtEdgeMidpoint q i₀ 0
  let F : ℝ → ℝ := fun x =>
    Complex.arg (PrincipalTurning.basedUniformSecant T C 0 x / A)
  have hLR : L < R := by dsimp [L,R]; linarith
  have hsum := PrincipalTurning.actualAxis_interval_potential_sum
    T C L R hL hR hLR F
  have hpoint (ab : ℝ × ℝ)
      (hab : ab ∈ (PrincipalTurning.secantAxisCells T C).filter
        (fun ab => L ≤ ab.1 ∧ ab.2 ≤ R)) :
      Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
        PrincipalTurning.basedUniformSecant T C 0 ab.2) =
        F ab.1 - F ab.2 := by
    have hc : PrincipalTurning.secantAxisAdjacent T C ab.1 ab.2 :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hab).1).2
    have hbounds := (Finset.mem_filter.mp hab).2
    let s : ℝ := ab.1 - L
    let t : ℝ := ab.2 - L
    have hs : 0 ≤ s := by dsimp [s]; linarith [hbounds.1]
    have hst : s ≤ t := by dsimp [s,t]; linarith [hc.2.2.1]
    have ht : t ≤ 1 := by dsimp [t,L,R] at *; linarith [hbounds.2]
    have hp := actualWord_nonbase_subcell_arg_potential T C j hj s t hs hst ht
    have hsa : (j.val : ℝ) + s - 1/2 = ab.1 := by dsimp [s,L]; ring
    have hta : (j.val : ℝ) + t - 1/2 = ab.2 := by dsimp [t,L]; ring
    rw [hsa, hta] at hp
    exact hp
  have hsum' :
      (∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
        (fun ab => L ≤ ab.1 ∧ ab.2 ≤ R),
        Complex.arg (PrincipalTurning.basedUniformSecant T C 0 ab.1 /
          PrincipalTurning.basedUniformSecant T C 0 ab.2)) =
        F L - F R := by
    calc
      _ = ∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
          (fun ab => L ≤ ab.1 ∧ ab.2 ≤ R), (F ab.1 - F ab.2) :=
        Finset.sum_congr rfl (fun ab hab => hpoint ab hab)
      _ = -(∑ ab ∈ (PrincipalTurning.secantAxisCells T C).filter
          (fun ab => L ≤ ab.1 ∧ ab.2 ≤ R), (F ab.2 - F ab.1)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro ab _
        ring
      _ = F L - F R := by rw [hsum]; ring
  have hzero : (0 : ℂ) ∉ segment ℝ A
      (q (cyclicSuccessorPerm m j) - normalAtEdgeMidpoint q i₀ 0) :=
    actualWord_nonbase_chord_zeroFree T C j hj
  have hA : A ≠ 0 := by
    intro heq
    exact hzero (heq ▸ left_mem_segment ℝ A _)
  have hLsec : PrincipalTurning.basedUniformSecant T C 0 L = A := by
    have h := actualWordSecant_affine_cell T C j 0 (by constructor <;> norm_num)
    simpa [L, A, affineChord] using h
  have hRsec : PrincipalTurning.basedUniformSecant T C 0 R =
      q (cyclicSuccessorPerm m j) - normalAtEdgeMidpoint q i₀ 0 := by
    have h := actualWordSecant_affine_cell T C j 1 (by constructor <;> norm_num)
    have ht : (j.val : ℝ) + 1 - 1/2 = R := by dsimp [R]; ring
    rw [ht] at h
    simpa [affineChord] using h
  dsimp [F] at hsum'
  rw [hLsec, hRsec] at hsum'
  simp [F, A, hA] at hsum' ⊢
  exact hsum'

end DirectGLSSW.HOMFLY.PLWinding
