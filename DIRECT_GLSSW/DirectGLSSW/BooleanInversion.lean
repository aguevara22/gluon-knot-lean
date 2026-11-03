import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Defs

/-!
# Boolean cancellation in separating-smoothing inversion

Source: `eq:boolean-cancellation` and the final regrouping in `lem:inversion`.
These are statements about arbitrary finite supports. The geometric bijection
from two-stage smoothings to a support and one of its subsets is NOT assumed
to have been proved here.
-/

namespace DirectGLSSW
open scoped BigOperators

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- The coefficient of a fixed final support after all choices of the
first-stage subset have been summed. -/
def refinementCoefficient (U : Finset ι) : R :=
  ∑ S ∈ U.powerset, (-1 : R) ^ (U.card - S.card)

theorem refinementCoefficient_eq (U : Finset ι) :
    refinementCoefficient (R := R) U = if U = ∅ then 1 else 0 := by
  classical
  have h := Finset.sum_pow_mul_eq_add_pow (1 : R) (-1 : R) U
  simp only [one_pow, one_mul, add_neg_cancel] at h
  unfold refinementCoefficient
  rw [h]
  by_cases hU : U = ∅
  · simp [hU]
  · simp [hU, Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hU)]

@[simp] theorem refinementCoefficient_empty :
    refinementCoefficient (R := R) (∅ : Finset ι) = 1 := by
  simp [refinementCoefficient_eq]

theorem refinementCoefficient_nonempty (U : Finset ι) (hU : U.Nonempty) :
    refinementCoefficient (R := R) U = 0 := by
  simp [refinementCoefficient_eq, hU.ne_empty]

/-- Once a two-stage expansion has been correctly grouped by its final
support, every nonempty support cancels, with no bound on its cardinality. -/
theorem grouped_refinement_inversion
    (supports : Finset (Finset ι)) (hEmpty : ∅ ∈ supports)
    (weight : Finset ι → R) :
    (∑ U ∈ supports, refinementCoefficient (R := R) U * weight U) = weight ∅ := by
  classical
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro U _ hU
    simp [refinementCoefficient_eq, hU]
  · exact fun h => False.elim (h hEmpty)

/-- Expanded form used by a future concrete smoothing-refinement proof. -/
theorem grouped_refinement_inversion_expanded
    (supports : Finset (Finset ι)) (hEmpty : ∅ ∈ supports)
    (weight : Finset ι → R) :
    (∑ U ∈ supports, ∑ S ∈ U.powerset,
      (-1 : R) ^ (U.card - S.card) * weight U) = weight ∅ := by
  simpa only [refinementCoefficient, Finset.sum_mul] using
    grouped_refinement_inversion supports hEmpty weight

end DirectGLSSW
