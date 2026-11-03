import ActualTerminalFramedValue
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open Coefficients LowestRowContract
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem zRow_apply (P : HOMFLYCoeff) (n i j : ℤ) :
    zRow P n (i,j) = if j = 0 then P (i,n) else 0 := by
  classical
  change (Finsupp.applyAddHom (i,j))
    (∑ x ∈ P.support, if x.2 = n then Finsupp.single (x.1,0) (P x) else 0) = _
  rw [map_sum]
  simp only [apply_ite, map_zero, Finsupp.applyAddHom_apply]
  by_cases hj : j = 0
  · subst j
    rw [Finset.sum_eq_single (i,n)]
    · simp
    · intro x hx hxi
      by_cases hx2 : x.2 = n
      · rw [if_pos hx2]
        apply Finsupp.single_eq_of_ne
        intro he
        apply hxi
        have hfst : x.1 = i := congrArg (fun p : ℤ × ℤ => p.1) he
        exact Prod.ext hfst hx2
      · simp [hx2]
    · intro hnot
      have hz : P (i,n) = 0 := Finsupp.not_mem_support_iff.mp hnot
      simp [hz]
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro x _
    split_ifs with hx
    · apply Finsupp.single_eq_of_ne
      intro he
      exact hj (congrArg Prod.snd he).symm
    · rfl



theorem zRow_sub (P Q : HOMFLYCoeff) (n : ℤ) :
    zRow (P - Q) n = zRow P n - zRow Q n := by
  ext ⟨i,j⟩
  change zRow (P - Q) n (i,j) = zRow P n (i,j) - zRow Q n (i,j)
  simp only [zRow_apply]
  change (if j = 0 then P (i,n) - Q (i,n) else 0) = _
  by_cases hj : j = 0 <;> simp [hj]

theorem zRow_aMonomial_mul (P : HOMFLYCoeff) (n : ℤ) :
    zRow (aMonomial * P) n = aMonomial * zRow P n := by
  ext ⟨i,j⟩
  rw [zRow_apply]
  change (if j = 0 then coeff (aMonomial * P) i n else 0) =
    coeff (aMonomial * zRow P n) i j
  rw [coeff_aMonomial_mul, coeff_aMonomial_mul]
  simp [coeff, zRow_apply]

theorem zRow_aInvMonomial_mul (P : HOMFLYCoeff) (n : ℤ) :
    zRow (aInvMonomial * P) n = aInvMonomial * zRow P n := by
  ext ⟨i,j⟩
  rw [zRow_apply]
  change (if j = 0 then coeff (aInvMonomial * P) i n else 0) =
    coeff (aInvMonomial * zRow P n) i j
  rw [coeff_aInvMonomial_mul, coeff_aInvMonomial_mul]
  simp [coeff, zRow_apply]

theorem zRow_zMonomial_mul (P : HOMFLYCoeff) (n : ℤ) :
    zRow (zMonomial * P) n = zRow P (n - 1) := by
  ext ⟨i,j⟩
  rw [zRow_apply, zRow_apply]
  change (if j = 0 then coeff (zMonomial * P) i n else 0) = _
  rw [coeff_zMonomial_mul]
  rfl

theorem normalizedEvaluator_positive_skein_row
    (H : (D : PLLinkDiagram) → 0 < D.nArc → HOMFLYCoeff)
    (hH : IsNormalizedDescendingSkeinEvaluator H)
    (D : PLLinkDiagram) (hD : 0 < D.nArc) (c : Fin D.nCrossing)
    (hc : crossingSign D c = .pos) (n : ℤ) :
    aMonomial * zRow (H D hD) n -
      aInvMonomial * zRow (H (switchCrossing D c) hD) n =
      zRow (H (smoothCrossing D c) (by change 0 < D.nArc + 2; omega)) (n - 1) := by
  have hs := hH.2 D hD c
  simp only [hc] at hs
  have hr := congrArg (fun P => zRow P n) hs
  simpa only [zRow_sub, zRow_aMonomial_mul, zRow_aInvMonomial_mul,
    zRow_zMonomial_mul] using hr

theorem candidateEvaluator_positive_skein_row
    (D : PLLinkDiagram) (hD : 0 < D.nArc) (c : Fin D.nCrossing)
    (hc : crossingSign D c = .pos) (n : ℤ) :
    aMonomial * zRow (Gemini.candidateEvaluator D hD) n -
      aInvMonomial * zRow (Gemini.candidateEvaluator (switchCrossing D c) hD) n =
      zRow (Gemini.candidateEvaluator (smoothCrossing D c)
        (by change 0 < D.nArc + 2; omega)) (n - 1) := by
  exact normalizedEvaluator_positive_skein_row Gemini.candidateEvaluator
    (Gemini.candidateEvaluator_isNormalized Gemini.all_lowerCrossingEvaluatorSkeinIH)
    D hD c hc n








end DirectGLSSW.HOMFLY
