import SM.CoordinateIsolation
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Nonzero affine resultant for irreducible nonassociated controls. The proof
uses primeness in the actual polynomial UFD and the proved degree obstruction;
nonassociation remains a separate obligation for the concrete finite family. -/

namespace SM

open MvPolynomial

noncomputable section

variable {σ : Type*}

theorem affine_polynomial_resultant_ne_zero (i : σ) (a b c d : MvPolynomial σ ℝ)
    (ha : a ≠ 0) (hai : i ∉ a.vars) (hbi : i ∉ b.vars)
    (hF : Irreducible (a * X i + b)) (hG : Irreducible (c * X i + d))
    (hFG : ¬ Associated (a * X i + b) (c * X i + d)) : a * d - b * c ≠ 0 := by
  intro hz
  have he : c * (a * X i + b) = a * (c * X i + d) := by
    linear_combination -hz
  have hdiv : a * X i + b ∣ a * (c * X i + d) := by
    refine ⟨c, ?_⟩
    rw [← he]
    ring
  have hdeg : (a * X i + b).degreeOf i = 1 := polynomial_linear_degree ha hai hbi
  have hnot : ¬ a * X i + b ∣ a := polynomial_not_dvd_of_degree_lt ha
    (by rw [polynomial_degree_zero hai, hdeg]; omega)
  have hp : Prime (a * X i + b) := irreducible_iff_prime.mp hF
  have hFGdiv := (hp.dvd_mul.mp hdiv).resolve_left hnot
  exact hFG (hF.associated_of_dvd hG hFGdiv)

def coordinateResultant (i : σ) (p q : MvPolynomial σ ℝ) : RemainingPolynomial i :=
  coordinateSlope i p * coordinateIntercept i q - coordinateIntercept i p * coordinateSlope i q

theorem coordinateResultant_ne_zero (i : σ) (p q : MvPolynomial σ ℝ)
    (hp : p.degreeOf i ≤ 1) (hq : q.degreeOf i ≤ 1) (hdep : i ∈ p.vars)
    (hirrp : Irreducible p) (hirrq : Irreducible q) (hneq : ¬ Associated p q) :
    coordinateResultant i p q ≠ 0 := by
  have hp' := coordinate_affine_decomposition i p hp
  have hq' := coordinate_affine_decomposition i q hq
  have ha : embedRemaining i (coordinateSlope i p) ≠ 0 := by
    intro hzero
    apply coordinateSlope_ne_zero i p hp hdep
    apply embedRemaining_injective i
    simpa only [map_zero] using hzero
  have hF : Irreducible (embedRemaining i (coordinateSlope i p) * X i +
      embedRemaining i (coordinateIntercept i p)) := hp' ▸ hirrp
  have hG : Irreducible (embedRemaining i (coordinateSlope i q) * X i +
      embedRemaining i (coordinateIntercept i q)) := hq' ▸ hirrq
  have hFG : ¬ Associated
      (embedRemaining i (coordinateSlope i p) * X i + embedRemaining i (coordinateIntercept i p))
      (embedRemaining i (coordinateSlope i q) * X i + embedRemaining i (coordinateIntercept i q)) := by
    rwa [← hp', ← hq']
  have hnonzero := affine_polynomial_resultant_ne_zero i
    (embedRemaining i (coordinateSlope i p)) (embedRemaining i (coordinateIntercept i p))
    (embedRemaining i (coordinateSlope i q)) (embedRemaining i (coordinateIntercept i q))
    ha (embedRemaining_avoids i _) (embedRemaining_avoids i _) hF hG hFG
  intro hz
  apply hnonzero
  have he := congrArg (embedRemaining i) hz
  simpa only [coordinateResultant, map_sub, map_mul, map_zero] using he

end

end SM
