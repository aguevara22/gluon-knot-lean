import SM.Chirotope
import Mathlib.Tactic

namespace SM

noncomputable section
variable {k : ℕ}

/-- The printed gap ratio uses the ordered endpoints of the whole selected list. -/
def lineGapEpsilon (t : Fin (k + 1) → ℝ) (j : Fin k) : SignType :=
  SignType.sign ((t j.succ - t j.castSucc) / (t (Fin.last k) - t 0))

def normalizedLineCoordinate (t : Fin (k + 1) → ℝ) (l : Fin (k + 1)) : ℝ :=
  (t l - t 0) / (t (Fin.last k) - t 0)

theorem selected_endpoint_difference_nonzero (hk : 0 < k)
    (t : Fin (k + 1) → ℝ) (hinj : Function.Injective t) : t (Fin.last k) - t 0 ≠ 0 := by
  apply sub_ne_zero.mpr
  intro he
  have hi := congrArg Fin.val (hinj he)
  change k = 0 at hi
  omega

theorem normalizedLineCoordinate_first (t : Fin (k + 1) → ℝ) :
    normalizedLineCoordinate t 0 = 0 := by simp [normalizedLineCoordinate]

theorem normalizedLineCoordinate_last (t : Fin (k + 1) → ℝ)
    (hd : t (Fin.last k) - t 0 ≠ 0) :
    normalizedLineCoordinate t (Fin.last k) = 1 := by
  exact div_self hd

theorem normalizedLineCoordinate_injective (t : Fin (k + 1) → ℝ)
    (hinj : Function.Injective t) (hd : t (Fin.last k) - t 0 ≠ 0) :
    Function.Injective (normalizedLineCoordinate t) := by
  intro a b he
  apply hinj
  have hc := congrArg (fun x : ℝ => x * (t (Fin.last k) - t 0)) he
  have hsub : t a - t 0 = t b - t 0 := by
    simpa only [normalizedLineCoordinate, div_mul_cancel₀ _ hd] using hc
  linarith

/-- Normalization changes neither the selected points nor their line, even
when the original endpoint difference is negative. -/
theorem normalizedLineCoordinate_representation (p ω : Plane) (t : Fin (k + 1) → ℝ)
    (hd : t (Fin.last k) - t 0 ≠ 0) (l : Fin (k + 1)) :
    p + t l • ω = (p + t 0 • ω) + normalizedLineCoordinate t l •
      ((t (Fin.last k) - t 0) • ω) := by
  rw [smul_smul]
  simp only [normalizedLineCoordinate, div_mul_cancel₀ _ hd]
  ext <;> dsimp <;> ring

theorem normalizedLineCoordinate_gap (t : Fin (k + 1) → ℝ) (j : Fin k) :
    normalizedLineCoordinate t j.succ - normalizedLineCoordinate t j.castSucc =
      (t j.succ - t j.castSucc) / (t (Fin.last k) - t 0) := by
  unfold normalizedLineCoordinate
  rw [← sub_div]
  congr 1
  ring

theorem lineGapEpsilon_positive (t : Fin (k + 1) → ℝ) (j : Fin k) :
    lineGapEpsilon t j = 1 ↔
      normalizedLineCoordinate t j.castSucc < normalizedLineCoordinate t j.succ := by
  unfold lineGapEpsilon
  rw [sign_eq_one_iff, ← normalizedLineCoordinate_gap, sub_pos]

theorem lineGapEpsilon_negative (t : Fin (k + 1) → ℝ) (j : Fin k) :
    lineGapEpsilon t j = -1 ↔
      normalizedLineCoordinate t j.succ < normalizedLineCoordinate t j.castSucc := by
  unfold lineGapEpsilon
  rw [sign_eq_neg_one_iff, ← normalizedLineCoordinate_gap, sub_neg]

end
end SM

#check SM.lineGapEpsilon
#print axioms SM.lineGapEpsilon
#check SM.normalizedLineCoordinate
#print axioms SM.normalizedLineCoordinate
#check SM.selected_endpoint_difference_nonzero
#print axioms SM.selected_endpoint_difference_nonzero
#check SM.normalizedLineCoordinate_first
#print axioms SM.normalizedLineCoordinate_first
#check SM.normalizedLineCoordinate_last
#print axioms SM.normalizedLineCoordinate_last
#check SM.normalizedLineCoordinate_injective
#print axioms SM.normalizedLineCoordinate_injective
#check SM.normalizedLineCoordinate_representation
#print axioms SM.normalizedLineCoordinate_representation
#check SM.normalizedLineCoordinate_gap
#print axioms SM.normalizedLineCoordinate_gap
#check SM.lineGapEpsilon_positive
#print axioms SM.lineGapEpsilon_positive
#check SM.lineGapEpsilon_negative
#print axioms SM.lineGapEpsilon_negative
