import AffineAxisArgument
import ActualAxisPotentialSum

set_option autoImplicit false
noncomputable section
open DirectGLSSW

namespace DirectGLSSW.HOMFLY.PLWinding

/-- The selected actual base midpoint is the literal based-curve value
at time zero. -/
theorem actualBaseMidpoint_eq_basedCurve {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0, componentArcLength_pos D e⟩
    normalAtEdgeMidpoint q i₀ 0 =
      Complex.equivRealProd.symm (PrincipalTurning.basedUniformPLCurve T C 0) := by
  intro e m q i₀
  have hcell := actualComponentWord_based_edge_cell T C i₀ (1/2)
    (by constructor <;> norm_num)
  have htime : ((i₀.val : ℝ) + 1/2 - 1/2) = 0 := by simp [i₀]
  rw [htime] at hcell
  simpa [normalAtEdgeMidpoint] using hcell.symm

/-- Actual secants from the selected base midpoint are exactly the
translated affine cells of the original component word. -/
theorem actualWordSecant_affine_cell {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D)
    (j : Fin (componentArcLength D (T.baseArc C).val))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0, componentArcLength_pos D e⟩
    PrincipalTurning.basedUniformSecant T C 0 ((j.val : ℝ) + t - 1/2) =
      affineChord (q j - normalAtEdgeMidpoint q i₀ 0)
        (q (cyclicSuccessorPerm m j) - normalAtEdgeMidpoint q i₀ 0) t := by
  intro e m q i₀
  have hcell := actualComponentWord_based_edge_cell T C j t ht
  have hmid := actualBaseMidpoint_eq_basedCurve T C
  unfold PrincipalTurning.basedUniformSecant affineChord
  have hsub (x y : PlanarPoint ℝ) :
      Complex.equivRealProd.symm (x - y) =
        Complex.equivRealProd.symm x - Complex.equivRealProd.symm y := by
    apply Complex.ext <;>
      simp [Complex.equivRealProd_symm_apply, Prod.fst_sub, Prod.snd_sub]
  rw [hsub]
  rw [hcell, ← hmid]
  ring

/-- Every non-base actual component edge gives a zero-free chord from
the selected base midpoint. This is exactly the literal edge-trace
avoidance already proved for that midpoint. -/
theorem actualWord_nonbase_chord_zeroFree {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D)
    (j : Fin (componentArcLength D (T.baseArc C).val))
    (hj : j ≠ (⟨0, componentArcLength_pos D (T.baseArc C).val⟩ :
      Fin (componentArcLength D (T.baseArc C).val))) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0, componentArcLength_pos D e⟩
    (0 : ℂ) ∉ segment ℝ
      (q j - normalAtEdgeMidpoint q i₀ 0)
      (q (cyclicSuccessorPerm m j) - normalAtEdgeMidpoint q i₀ 0) := by
  intro e m q i₀ hz
  obtain ⟨u,v,hu,hv,hs,hp⟩ := hz
  have hp' : (0 : ℂ) = (u : ℂ) * (q j - normalAtEdgeMidpoint q i₀ 0) +
      (v : ℂ) * (q (cyclicSuccessorPerm m j) - normalAtEdgeMidpoint q i₀ 0) := by
    simpa only [Complex.real_smul] using hp.symm
  have hcast : (u : ℂ) + (v : ℂ) = 1 := by
    exact_mod_cast hs
  have heq : normalAtEdgeMidpoint q i₀ 0 =
      q j + (v : ℂ) * (q (cyclicSuccessorPerm m j) - q j) := by
    linear_combination hp' +
      (q j - normalAtEdgeMidpoint q i₀ 0) * hcast
  exact (actualComponentWord_base_midpoint_regular T C j hj)
    ((edgeTrace_iff_literal q j _).mpr ⟨v,hv,by linarith [hu,hs],heq⟩)

/-- Every actual nonbase subcell's exterior chord increment is the
difference of one literal edge-local principal-angle potential. -/
theorem actualWord_nonbase_subcell_arg_potential {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D)
    (j : Fin (componentArcLength D (T.baseArc C).val))
    (hj : j ≠ (⟨0, componentArcLength_pos D (T.baseArc C).val⟩ :
      Fin (componentArcLength D (T.baseArc C).val)))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    let e := (T.baseArc C).val
    let m := componentArcLength D e
    let q := actualComponentWord T C
    let i₀ : Fin m := ⟨0, componentArcLength_pos D e⟩
    let A := q j - normalAtEdgeMidpoint q i₀ 0
    Complex.arg (PrincipalTurning.basedUniformSecant T C 0
        ((j.val : ℝ) + s - 1/2) /
      PrincipalTurning.basedUniformSecant T C 0
        ((j.val : ℝ) + t - 1/2)) =
      Complex.arg (PrincipalTurning.basedUniformSecant T C 0
        ((j.val : ℝ) + s - 1/2) / A) -
      Complex.arg (PrincipalTurning.basedUniformSecant T C 0
        ((j.val : ℝ) + t - 1/2) / A) := by
  intro e m q i₀ A
  let B := q (cyclicSuccessorPerm m j) - normalAtEdgeMidpoint q i₀ 0
  have hzero : (0 : ℂ) ∉ segment ℝ A B :=
    actualWord_nonbase_chord_zeroFree T C j hj
  have hsI : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs, le_trans hst ht⟩
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hs hst, ht⟩
  have hsa := actualWordSecant_affine_cell T C j s hsI
  have hta := actualWordSecant_affine_cell T C j t htI
  dsimp only at hsa hta
  have hmem (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      affineChord A B u ∈ segment ℝ A B := by
    refine ⟨1-u,u,by linarith [hu.2],hu.1,by ring,?_⟩
    simp [affineChord, Complex.real_smul]
    ring
  have hsub : segment ℝ (affineChord A B s) (affineChord A B t) ⊆
      segment ℝ A B :=
    (convex_segment A B).segment_subset (hmem s hsI) (hmem t htI)
  have hzero' : (0 : ℂ) ∉ segment ℝ (affineChord A B s) (affineChord A B t) :=
    fun hz => hzero (hsub hz)
  rw [hsa, hta]
  have hrev := PrincipalTurning.segment_arg_reverse
    (affineChord A B s) (affineChord A B t) hzero'
  rw [hrev, affineChord_arg_eq_potential_sub A B hzero s t hs hst ht]
  ring

end DirectGLSSW.HOMFLY.PLWinding


