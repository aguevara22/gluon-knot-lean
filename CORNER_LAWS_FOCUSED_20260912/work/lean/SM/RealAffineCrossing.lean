import SM.RealAffineRoots
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Nonzero real affine slopes give genuine simple sign-changing crossings in
the actual real parameter. The derivative and signs are evaluated, not inferred
from a formal degree bound alone. -/

namespace SM

open Polynomial

noncomputable section

theorem realAffinePolynomial_derivative (a b : ℝ) :
    (realAffinePolynomial a b).derivative = C a := by
  simp [realAffinePolynomial]

theorem realAffinePolynomial_hasDerivAt (a b t : ℝ) :
    HasDerivAt (fun s => (realAffinePolynomial a b).eval s) a t := by
  simpa only [realAffinePolynomial_derivative, eval_C] using
    (realAffinePolynomial a b).hasDerivAt t

theorem realAffinePolynomial_simple_at_root (a b r : ℝ) (ha : a ≠ 0)
    (hr : (realAffinePolynomial a b).IsRoot r) :
    (realAffinePolynomial a b).rootMultiplicity r = 1 := by
  rw [(realAffinePolynomial_root_iff a b ha r).mp hr]
  exact realAffinePolynomial_simple_root a b ha

theorem realAffinePolynomial_eval_from_root (a b r t : ℝ)
    (hr : (realAffinePolynomial a b).IsRoot r) :
    (realAffinePolynomial a b).eval t = a * (t - r) := by
  have hr' : a * r + b = 0 := by
    simpa only [IsRoot, realAffinePolynomial_eval] using hr
  rw [realAffinePolynomial_eval]
  calc
    a * t + b = a * (t - r) + (a * r + b) := by ring
    _ = a * (t - r) := by rw [hr', add_zero]

theorem realAffinePolynomial_crossing_product (a b r u v : ℝ) (ha : a ≠ 0)
    (hr : (realAffinePolynomial a b).IsRoot r) (hu : u < r) (hv : r < v) :
    (realAffinePolynomial a b).eval u * (realAffinePolynomial a b).eval v < 0 := by
  rw [realAffinePolynomial_eval_from_root a b r u hr,
    realAffinePolynomial_eval_from_root a b r v hr]
  have hs : 0 < a * a := mul_self_pos.mpr ha
  have ht : (u - r) * (v - r) < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hu) (sub_pos.mpr hv)
  calc
    (a * (u - r)) * (a * (v - r)) = (a * a) * ((u - r) * (v - r)) := by ring
    _ < 0 := mul_neg_of_pos_of_neg hs ht

end

end SM
