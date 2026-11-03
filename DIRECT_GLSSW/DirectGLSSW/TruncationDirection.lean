import Mathlib.Algebra.Order.BigOperators.Group.Finset

import DirectGLSSW.RealPolygons
import DirectGLSSW.ShortEdgeAttachmentFactor
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace DirectGLSSW.TruncationDirection

open DirectGLSSW

theorem exists_positive_cone_direction_avoiding_vertex_lines {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : cyclicNoncollinear q)
    (a p c : Fin n) (hpa : p ≠ a) (hca : c ≠ a) (hpc : p ≠ c) :
    ∃ scale : ℝ, 0 < scale ∧
      ∀ x : Fin n, x ≠ a →
        planarDet (scale • (q c - q a) - (q p - q a)) (q x - q a) ≠ 0 := by
  classical
  let U : PlanarPoint ℝ := q p - q a
  let D : PlanarPoint ℝ := q c - q a
  let ratio (x : Fin n) : ℝ :=
    planarDet U (q x - q a) / planarDet D (q x - q a)
  let term (x : Fin n) : ℝ :=
    if hx : x ≠ a ∧ x ≠ c then |ratio x| else 0
  let scale : ℝ := 1 + ∑ x : Fin n, term x
  have hterm_nonneg : ∀ x : Fin n, 0 ≤ term x := by
    intro x
    simp only [term]
    split_ifs <;> positivity
  have hterm_le_sum (x : Fin n) : term x ≤ ∑ y : Fin n, term y := by
    simpa using Finset.single_le_sum (s := Finset.univ) (f := term)
      (fun y hy => hterm_nonneg y) (Finset.mem_univ x)
  have hscalePos : 0 < scale := by
    dsimp [scale]
    have hsum : 0 ≤ ∑ x : Fin n, term x := Finset.sum_nonneg (fun x hx => hterm_nonneg x)
    linarith
  refine ⟨scale, hscalePos, ?_⟩
  intro x hxa
  by_cases hxc : x = c
  · subst x
    have hDU : planarDet D U ≠ 0 := by
      exact hq p c a hpc hca hpa
    have hUD : planarDet U D ≠ 0 := by
      intro h
      apply hDU
      have hskew : planarDet D U = -planarDet U D := by
        simp [planarDet] <;> ring
      rw [hskew, h]
      simp
    have hcalc : planarDet (scale • D - U) D = -planarDet U D := by
      simp [planarDet] <;> ring
    rw [hcalc]
    exact neg_ne_zero.mpr hUD
  · have hxne : x ≠ c := hxc
    have hDx : planarDet D (q x - q a) ≠ 0 := by
      exact hq x c a hxne hca hxa
    have hterm : term x = |ratio x| := by simp [term, hxa, hxne]
    have hratio_le : |ratio x| ≤ ∑ y : Fin n, term y := by
      rw [← hterm]
      exact hterm_le_sum x
    have hratio_lt : ratio x < scale := by
      dsimp [scale]
      have habs : ratio x ≤ |ratio x| := le_abs_self _
      linarith
    intro hzero
    have hlinear : scale * planarDet D (q x - q a) -
        planarDet U (q x - q a) = 0 := by
      have hformula : planarDet (scale • D - U) (q x - q a) =
          scale * planarDet D (q x - q a) - planarDet U (q x - q a) := by
        simp [planarDet] <;> ring
      rw [hformula] at hzero
      exact hzero
    have hmul : scale * planarDet D (q x - q a) = planarDet U (q x - q a) := by
      linarith
    have hquot : scale = ratio x := by
      dsimp [ratio]
      exact (eq_div_iff hDx).2 hmul
    rw [← hquot] at hratio_lt
    exact (lt_irrefl _ hratio_lt)


open DirectGLSSW.ShortEdgeGenericity

theorem truncation_attachmentFactor_eq_neg {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p c : Fin n)
    (scale ε : ℝ)
    (hturn : 0 < planarDet (q a - q p) (q c - q a))
    (hscale : 0 < scale) (hε : 0 < ε)
    (hε1 : ε < 1) (hεscale1 : ε * scale < 1) :
    attachmentFactor
      (q a + ε • (q p - q a))
      (q a + (ε * scale) • (q c - q a))
      (q p) (q c) = -1 := by
  let U : PlanarPoint ℝ := q p - q a
  let D : PlanarPoint ℝ := q c - q a
  let B : PlanarPoint ℝ := q a + ε • U
  let Cnew : PlanarPoint ℝ := q a + (ε * scale) • D
  have hturn' : planarDet U D < 0 := by
    have hdet : planarDet (q a - q p) D = -planarDet U D := by
      simp [U, D, planarDet] <;> ring
    rw [hdet] at hturn
    linarith
  have hfirst : planarDet (B - Cnew) (q p - Cnew) =
      ε * (1 - ε) * scale * planarDet U D := by
    simp [B, Cnew, U, D, planarDet]
    ring
  have hsecond : planarDet (B - Cnew) (q c - Cnew) =
      ε * (1 - ε * scale) * planarDet U D := by
    simp [B, Cnew, U, D, planarDet]
    ring
  have hεfactor : 0 < 1 - ε := by linarith
  have hfirst_pos : 0 < ε * (1 - ε) * scale := by positivity
  have hsecond_pos : 0 < ε * (1 - ε * scale) := by
    have hfactor : 0 < 1 - ε * scale := by linarith
    positivity
  have hfirst_neg : ε * (1 - ε) * scale * planarDet U D < 0 :=
    mul_neg_of_pos_of_neg hfirst_pos hturn'
  have hsecond_neg : ε * (1 - ε * scale) * planarDet U D < 0 :=
    mul_neg_of_pos_of_neg hsecond_pos hturn'
  unfold DirectGLSSW.ShortEdgeGenericity.attachmentFactor
  rw [show planarDet (q a + ε • (q p - q a) -
      (q a + (ε * scale) • (q c - q a)))
      (q p - (q a + (ε * scale) • (q c - q a))) =
        ε * (1 - ε) * scale * planarDet U D by simpa [B, Cnew] using hfirst,
      show planarDet (q a + ε • (q p - q a) -
      (q a + (ε * scale) • (q c - q a)))
      (q c - (q a + (ε * scale) • (q c - q a))) =
        ε * (1 - ε * scale) * planarDet U D by simpa [B, Cnew] using hsecond]
  simp [scalarSignValue, ne_of_lt hfirst_neg, ne_of_lt hsecond_neg,
    hfirst_neg, hsecond_neg]

end DirectGLSSW.TruncationDirection
