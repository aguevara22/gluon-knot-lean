import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import DirectGLSSW.AffineSegments

namespace DirectGLSSW.TruncationCommonScale

open DirectGLSSW

theorem planarDet_left_ne_zero_of_pair_ne_zero
    (U D X : PlanarPoint ℝ) (hUD : planarDet U D ≠ 0)
    (hX : X ≠ 0) (hDX : planarDet D X = 0) :
    planarDet U X ≠ 0 := by
  intro hUX
  have hcoord₁ : X.1 * planarDet U D = 0 := by
    calc
      X.1 * planarDet U D = planarDet U X * D.1 - planarDet D X * U.1 := by
        simp [planarDet]
        ring
      _ = 0 := by rw [hUX, hDX]; ring
  have hcoord₂ : X.2 * planarDet U D = 0 := by
    calc
      X.2 * planarDet U D = planarDet U X * D.2 - planarDet D X * U.2 := by
        simp [planarDet]
        ring
      _ = 0 := by rw [hUX, hDX]; ring
  have hcoord : X.1 ≠ 0 ∨ X.2 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hX
    ext
    · simpa using h.1
    · simpa using h.2
  rcases hcoord with hX₁ | hX₂
  · rcases mul_eq_zero.mp hcoord₁ with hzero | hzero
    · exact hX₁ hzero
    · exact hUD hzero
  · rcases mul_eq_zero.mp hcoord₂ with hzero | hzero
    · exact hX₂ hzero
    · exact hUD hzero

theorem exists_positive_scale_avoiding_finite_vectors
    (U D : PlanarPoint ℝ) (hUD : planarDet U D ≠ 0)
    {ι : Type*} [Fintype ι] (X : ι → PlanarPoint ℝ) :
    ∃ scale : ℝ, 0 < scale ∧
      ∀ i, X i ≠ 0 → planarDet (scale • D - U) (X i) ≠ 0 := by
  classical
  let ratio (i : ι) : ℝ := planarDet U (X i) / planarDet D (X i)
  let term (i : ι) : ℝ :=
    if h : planarDet D (X i) ≠ 0 then |ratio i| else 0
  let scale : ℝ := 1 + ∑ i : ι, term i
  have hterm_nonneg : ∀ i, 0 ≤ term i := by
    intro i
    simp only [term]
    split_ifs <;> positivity
  have hterm_le_sum (i : ι) : term i ≤ ∑ j : ι, term j := by
    simpa using Finset.single_le_sum (s := Finset.univ) (f := term)
      (fun j hj => hterm_nonneg j) (Finset.mem_univ i)
  have hscalePos : 0 < scale := by
    dsimp [scale]
    have hsum : 0 ≤ ∑ i : ι, term i :=
      Finset.sum_nonneg (fun i hi => hterm_nonneg i)
    linarith
  refine ⟨scale, hscalePos, ?_⟩
  intro i hXi
  by_cases hDi : planarDet D (X i) = 0
  · have hUi : planarDet U (X i) ≠ 0 :=
      planarDet_left_ne_zero_of_pair_ne_zero U D (X i) hUD hXi hDi
    calc
      planarDet (scale • D - U) (X i) =
          scale * planarDet D (X i) - planarDet U (X i) := by
            simp [planarDet]
            ring
      _ = -planarDet U (X i) := by rw [hDi]; ring
      _ ≠ 0 := neg_ne_zero.mpr hUi
  · have hDi' : planarDet D (X i) ≠ 0 := hDi
    have hterm : term i = |ratio i| := by simp [term, hDi']
    have hratio_le : |ratio i| ≤ ∑ j : ι, term j := by
      rw [← hterm]
      exact hterm_le_sum i
    have hratio_lt : ratio i < scale := by
      dsimp [scale]
      have habs : ratio i ≤ |ratio i| := le_abs_self _
      linarith
    intro hzero
    have hformula : planarDet (scale • D - U) (X i) =
        scale * planarDet D (X i) - planarDet U (X i) := by
      simp [planarDet]
      ring
    rw [hformula] at hzero
    have hmul : scale * planarDet D (X i) = planarDet U (X i) := by
      linarith
    have hquot : scale = ratio i := by
      dsimp [ratio]
      exact (eq_div_iff hDi').2 hmul
    rw [← hquot] at hratio_lt
    exact (lt_irrefl _ hratio_lt)

theorem exists_positive_scale_avoiding_finite_point_lines
    (A U D : PlanarPoint ℝ) (hUD : planarDet U D ≠ 0)
    {ι : Type*} [Fintype ι] (P : ι → PlanarPoint ℝ) :
    ∃ scale : ℝ, 0 < scale ∧
      ∀ i, P i ≠ A → planarDet (scale • D - U) (P i - A) ≠ 0 := by
  obtain ⟨scale, hscale, havoid⟩ :=
    exists_positive_scale_avoiding_finite_vectors U D hUD (fun i => P i - A)
  refine ⟨scale, hscale, ?_⟩
  intro i hi
  apply havoid i
  exact sub_ne_zero.mpr hi





end DirectGLSSW.TruncationCommonScale
