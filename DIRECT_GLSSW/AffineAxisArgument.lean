import PairedNormalBoundary
import SegmentArgumentAdditivity
import RootHalfArcChords

set_option autoImplicit false
noncomputable section
open DirectGLSSW

namespace DirectGLSSW.HOMFLY.PLWinding

def affineChord (A B : ℂ) (t : ℝ) : ℂ :=
  A + (t : ℂ) * (B - A)

theorem affineChord_eq_literal (A B : ℂ) (t : ℝ) :
    affineChord A B t = A + (t : ℂ) * (B - A) := rfl

private theorem affineChord_mem_segment (A B : ℂ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    affineChord A B t ∈ segment ℝ A B := by
  refine ⟨1-t,t,by linarith [ht.2],ht.1,by ring,?_⟩
  simp [affineChord, Complex.real_smul]
  ring

private theorem affineChord_subsegment (A B : ℂ) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    affineChord A B s ∈ segment ℝ A (affineChord A B t) := by
  by_cases ht0 : t = 0
  · have hs0 : s = 0 := by linarith
    simp [hs0, ht0, affineChord, left_mem_segment]
  have htpos : 0 < t := lt_of_le_of_ne (le_trans hs hst) (Ne.symm ht0)
  let r : ℝ := s / t
  have hr0 : 0 ≤ r := div_nonneg hs htpos.le
  have hr1 : r ≤ 1 := (div_le_iff₀ htpos).mpr (by simpa using hst)
  refine ⟨1-r,r,by linarith,hr0,by ring,?_⟩
  simp only [Complex.real_smul]
  dsimp [affineChord, r]
  push_cast
  field_simp [ht0]
  ring

/-- On any zero-free affine chord, each forward subchord's principal
argument is the difference of the same literal basepoint potential. -/
theorem affineChord_arg_eq_potential_sub (A B : ℂ)
    (havoid : (0 : ℂ) ∉ segment ℝ A B)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    Complex.arg ((affineChord A B t) / (affineChord A B s)) =
      Complex.arg ((affineChord A B t) / A) -
        Complex.arg ((affineChord A B s) / A) := by
  have hsub : segment ℝ A (affineChord A B t) ⊆ segment ℝ A B :=
    (convex_segment A B).segment_subset (left_mem_segment ℝ A B)
      (affineChord_mem_segment A B t ⟨le_trans hs hst, ht⟩)
  have havoid' : (0 : ℂ) ∉ segment ℝ A (affineChord A B t) :=
    fun hz => havoid (hsub hz)
  have hsum := PrincipalTurning.segment_arg_additive A
    (affineChord A B s) (affineChord A B t)
    (affineChord_subsegment A B s t hs hst ht) havoid'
  linarith

/-- Every exterior secant cell in the first base half-edge has zero
chord increment, independently of exposedness. -/
theorem initial_base_secant_cell_arg_zero {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1/2) :
    Complex.arg (PrincipalTurning.basedUniformSecant T C 0 a /
      PrincipalTurning.basedUniformSecant T C 0 b) = 0 := by
  have hva := PrincipalTurning.basedUniformSecant_initial_half_arc T C a
    ⟨ha.le, le_trans hab hb⟩
  have hvb := PrincipalTurning.basedUniformSecant_initial_half_arc T C b
    ⟨le_trans ha.le hab, hb⟩
  rw [hva, hvb]
  have hv : PrincipalTurning.arcVector D (T.baseArc C).val ≠ 0 :=
    PrincipalTurning.arcVector_ne_zero D _
  rw [mul_div_mul_right _ _ hv]
  have hratio : (a : ℂ) / (b : ℂ) = ((a / b : ℝ) : ℂ) := by norm_cast
  rw [hratio]
  exact Complex.arg_ofReal_of_nonneg (div_nonneg ha.le (le_trans ha.le hab))

/-- Every exterior secant cell in the returning base half-edge also has
zero chord increment, with no half-plane premise. -/
theorem return_base_secant_cell_arg_zero {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D)
    (a b : ℝ)
    (ha : (componentArcLength D (T.baseArc C).val : ℝ) - 1/2 ≤ a)
    (hab : a ≤ b)
    (hb : b < (componentArcLength D (T.baseArc C).val : ℝ)) :
    Complex.arg (PrincipalTurning.basedUniformSecant T C 0 a /
      PrincipalTurning.basedUniformSecant T C 0 b) = 0 := by
  let m : ℝ := componentArcLength D (T.baseArc C).val
  have hva := PrincipalTurning.basedUniformSecant_return_half_arc T C a
    ⟨ha, by linarith [hab, hb]⟩
  have hvb := PrincipalTurning.basedUniformSecant_return_half_arc T C b
    ⟨le_trans ha hab, hb.le⟩
  rw [hva, hvb]
  have hv : PrincipalTurning.arcVector D (T.baseArc C).val ≠ 0 :=
    PrincipalTurning.arcVector_ne_zero D _
  rw [mul_div_mul_right _ _ hv]
  have hratio : (((a-m : ℝ) : ℂ) / ((b-m : ℝ) : ℂ)) =
      (((a-m)/(b-m) : ℝ) : ℂ) := by norm_cast
  rw [hratio]
  exact Complex.arg_ofReal_of_nonneg
    (div_nonneg_of_nonpos (by dsimp [m]; linarith [hab, hb])
      (by dsimp [m]; linarith [hb]))

end DirectGLSSW.HOMFLY.PLWinding


