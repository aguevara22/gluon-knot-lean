import DirectGLSSW.CutRefinement
import DirectGLSSW.CutIncidence
import DirectGLSSW.BooleanInversion
import Mathlib.Data.Fintype.BigOperators

/-!
# Expanding the concrete composition of interval-current maps

Source: `ep:factorization`. Finite distributivity expands the actual outer
Phi map into the sum over an outer cut set and independently chosen inner
cut sets in each outer gap. Weight preservation under refinement is a
separate obligation.
-/

namespace DirectGLSSW
open scoped BigOperators

/-- The summand specified by outer cuts and one inner cut set per outer gap. -/
def nestedCutWeight (D H : TripleArray) (X : IntervalArray) (i j : ℕ)
    (R : Σ S : IntervalCutSet i j,
      ∀ e : CutGap i j S.val, IntervalCutSet e.val.1 e.val.2) : ℚ :=
  gateProduct 0 H i j (cutVertices i j R.1.val) *
    ∏ e : CutGap i j R.1.val,
      cutContribution D 0 X e.val.1 e.val.2 (R.2 e).val

/-- Expand the composed Phi map on its actual finite cut indices. -/
theorem phi_composition_eq_sum (D H : TripleArray) (X : IntervalArray)
    {i j : ℕ} (hij : i < j) :
    phi 0 H (fun a b => phi D 0 X a b) i j =
      ∑ R : (Σ S : IntervalCutSet i j,
        ∀ e : CutGap i j S.val, IntervalCutSet e.val.1 e.val.2),
        nestedCutWeight D H X i j R := by
  classical
  have hinner (a b : ℕ) : phi D 0 X a b =
      ∑ U : IntervalCutSet a b, cutContribution D 0 X a b U.val :=
    (Finset.sum_coe_sort _ _).symm
  rw [Fintype.sum_sigma]
  change (∑ S ∈ (Finset.Ioo i j).powerset,
    cutContribution 0 H (fun a b => phi D 0 X a b) i j S) = _
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro S _
  change gateProduct 0 H i j (cutVertices i j S.val) *
    branchProduct (fun a b => phi D 0 X a b) (cutVertices i j S.val) = _
  rw [branchProduct_eq_prod_cutEdges _ hij (Finset.mem_powerset.mp S.property)]
  rw [← Finset.prod_coe_sort]
  simp_rw [hinner]
  rw [Fintype.prod_sum, Finset.mul_sum]
  rfl

end DirectGLSSW
