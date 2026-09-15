import SM.Farout
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
set_option pp.universes false

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Equality of every actual triple inside J is equality of the complete
restricted arrays; no condition is imposed on entries outside J. -/
theorem restrictTripleArray_eq_of_local (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ t : IncreasingBoundaryTriple n, J.left ≤ t.lower → t.upper ≤ J.right → H₁ t = H₂ t) :
    restrictTripleArray J H₁ = restrictTripleArray J H₂ := by
  funext t
  exact h (J.liftTriple t) (J.globalPosition_bounds t.lower).1 (J.globalPosition_bounds t.upper).2

/-- Inverse coordinates depend only on actual triples inside their own
interval. The one-leaf convention is proved separately before using a closed
full local interval at larger arity. -/
theorem farOnlyCoordinates_local (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ t : IncreasingBoundaryTriple n, J.left ≤ t.lower → t.upper ≤ J.right → H₁ t = H₂ t) :
    farOnlyCoordinates H₁ J = farOnlyCoordinates H₂ J := by
  by_cases hj : J.leaves = 1
  · rw [farOnlyCoordinates_leaf H₁ J hj, farOnlyCoordinates_leaf H₂ J hj]
  · have hJ : 2 ≤ J.leaves := by have := J.leaves_pos; omega
    let K := fullBoundaryInterval (by omega : 3 ≤ J.leaves + 1)
    have he := congrArg (fun H : TripleArray (J.leaves + 1) R => farOnlyCoordinates H)
      (restrictTripleArray_eq_of_local J H₁ H₂ h)
    have h₁ := congrFun (farOnlyCoordinates_restrict J H₁) K
    have h₂ := congrFun (farOnlyCoordinates_restrict J H₂) K
    change farOnlyCoordinates H₁ (J.liftInterval K) = farOnlyCoordinates (restrictTripleArray J H₁) K at h₁
    change farOnlyCoordinates H₂ (J.liftInterval K) = farOnlyCoordinates (restrictTripleArray J H₂) K at h₂
    rw [J.lift_fullInterval hJ] at h₁ h₂
    exact h₁.trans ((congrFun he K).trans h₂.symm)

/-- If one critical triple is the only array entry that can differ, every
interval not containing its full span has unchanged inverse coordinate. This
is the locality step in the single-triple wall response, before wall geometry. -/
theorem farOnlyCoordinates_unchanged_off_critical (H₁ H₂ : TripleArray n R)
    (critical : IncreasingBoundaryTriple n)
    (h : ∀ t : IncreasingBoundaryTriple n, t ≠ critical → H₁ t = H₂ t)
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ critical.lower ∧ critical.upper ≤ J.right)) :
    farOnlyCoordinates H₁ J = farOnlyCoordinates H₂ J := by
  apply farOnlyCoordinates_local J H₁ H₂
  intro t hl hr
  apply h t
  intro ht
  subst t
  exact hJ ⟨hl, hr⟩

end
end SM

namespace FarOnlyLocalityIndependentReview
open SM
noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]
local instance : DecidableEq (IncreasingBoundaryTriple n) := Classical.decEq _

theorem entire_restricted_c_equal (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ t : IncreasingBoundaryTriple n, J.left ≤ t.lower → t.upper ≤ J.right → H₁ t = H₂ t) :
    restrictIntervalArray J (farOnlyCoordinates H₁) = restrictIntervalArray J (farOnlyCoordinates H₂) := by
  rw [farOnlyCoordinates_restrict, farOnlyCoordinates_restrict, restrictTripleArray_eq_of_local J H₁ H₂ h]

theorem every_actual_local_subinterval (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ t : IncreasingBoundaryTriple n, J.left ≤ t.lower → t.upper ≤ J.right → H₁ t = H₂ t)
    (K : BoundaryInterval (J.leaves + 1)) :
    farOnlyCoordinates H₁ (J.liftInterval K) = farOnlyCoordinates H₂ (J.liftInterval K) :=
  congrFun (entire_restricted_c_equal J H₁ H₂ h) K

theorem left_gap_unchanged (H₁ H₂ : TripleArray n R) (critical : IncreasingBoundaryTriple n)
    (h : ∀ t : IncreasingBoundaryTriple n, t ≠ critical → H₁ t = H₂ t) :
    farOnlyCoordinates H₁ critical.leftInterval = farOnlyCoordinates H₂ critical.leftInterval := by
  apply farOnlyCoordinates_unchanged_off_critical H₁ H₂ critical h
  intro hc
  have hb := hc.2
  change critical.upper ≤ critical.middle at hb
  exact (not_le_of_gt critical.middle_upper) hb

theorem right_gap_unchanged (H₁ H₂ : TripleArray n R) (critical : IncreasingBoundaryTriple n)
    (h : ∀ t : IncreasingBoundaryTriple n, t ≠ critical → H₁ t = H₂ t) :
    farOnlyCoordinates H₁ critical.rightInterval = farOnlyCoordinates H₂ critical.rightInterval := by
  apply farOnlyCoordinates_unchanged_off_critical H₁ H₂ critical h
  intro hc
  have hb := hc.1
  change critical.middle ≤ critical.lower at hb
  exact (not_le_of_gt critical.lower_middle) hb

theorem every_proper_critical_child (H₁ H₂ : TripleArray n R) (critical : IncreasingBoundaryTriple n)
    (h : ∀ t : IncreasingBoundaryTriple n, t ≠ critical → H₁ t = H₂ t)
    (π : IntervalComposition (⟨critical.lower, critical.upper,
      lt_trans critical.lower_middle critical.middle_upper⟩ : BoundaryInterval n))
    (hp : 2 ≤ π.parts) (k : Fin π.parts) :
    farOnlyCoordinates H₁ (π.part k) = farOnlyCoordinates H₂ (π.part k) := by
  apply farOnlyCoordinates_unchanged_off_critical H₁ H₂ critical h
  intro hc
  have hs := π.part_leaves_lt hp k
  have hl := hc.1
  have hr := hc.2
  change (π.part k).left.val ≤ critical.lower.val at hl
  change critical.upper.val ≤ (π.part k).right.val at hr
  change (π.part k).right.val - (π.part k).left.val < critical.upper.val - critical.lower.val at hs
  omega

theorem leaf_needs_no_array_agreement (J : BoundaryInterval n) (hj : J.leaves = 1)
    (H₁ H₂ : TripleArray n R) : farOnlyCoordinates H₁ J = farOnlyCoordinates H₂ J := by
  rw [farOnlyCoordinates_leaf H₁ J hj, farOnlyCoordinates_leaf H₂ J hj]

theorem arbitrary_critical_update_off_span (H : TripleArray n R) (critical : IncreasingBoundaryTriple n)
    (value : R) (J : BoundaryInterval n)
    (hj : ¬ (J.left ≤ critical.lower ∧ critical.upper ≤ J.right)) :
    farOnlyCoordinates H J = farOnlyCoordinates (Function.update H critical value) J := by
  classical
  apply farOnlyCoordinates_unchanged_off_critical H (Function.update H critical value) critical _ J hj
  intro t ht
  simp [Function.update_of_ne ht]

theorem entire_restricted_output_equal (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ t : IncreasingBoundaryTriple n, J.left ≤ t.lower → t.upper ≤ J.right → H₁ t = H₂ t) :
    restrictIntervalArray J (farOnlyOutput H₁) = restrictIntervalArray J (farOnlyOutput H₂) := by
  rw [farOnlyOutput_restrict, farOnlyOutput_restrict, restrictTripleArray_eq_of_local J H₁ H₂ h]

end
end FarOnlyLocalityIndependentReview


#check SM.restrictTripleArray_eq_of_local
#print axioms SM.restrictTripleArray_eq_of_local
#check SM.farOnlyCoordinates_local
#print axioms SM.farOnlyCoordinates_local
#check SM.farOnlyCoordinates_unchanged_off_critical
#print axioms SM.farOnlyCoordinates_unchanged_off_critical
#print SM.BoundaryInterval
#print SM.BoundaryInterval.leaves
#print SM.IncreasingBoundaryTriple
#print SM.TripleArray
#print SM.IntervalArray
#print SM.farOnlyCoordinates
#print SM.farOnlyOutput
#print SM.restrictTripleArray
#print SM.restrictIntervalArray
#print SM.BoundaryInterval.liftTriple
#print SM.BoundaryInterval.globalPosition
#print axioms FarOnlyLocalityIndependentReview.entire_restricted_c_equal
#print axioms FarOnlyLocalityIndependentReview.every_actual_local_subinterval
#print axioms FarOnlyLocalityIndependentReview.left_gap_unchanged
#print axioms FarOnlyLocalityIndependentReview.right_gap_unchanged
#print axioms FarOnlyLocalityIndependentReview.every_proper_critical_child
#print axioms FarOnlyLocalityIndependentReview.leaf_needs_no_array_agreement
#print axioms FarOnlyLocalityIndependentReview.arbitrary_critical_update_off_span
#print axioms FarOnlyLocalityIndependentReview.entire_restricted_output_equal
