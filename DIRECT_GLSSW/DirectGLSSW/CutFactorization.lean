import DirectGLSSW.CutExpansion
import DirectGLSSW.CompositionExpansion
import DirectGLSSW.CutLocalWeights

/-!
# Near-data factorization for the actual finite-cut map

Source: `ep:factorization`. The refinement equivalence, final-neighbor
matching and finite distributivity are all proved on concrete cut objects.
-/

namespace DirectGLSSW
open scoped BigOperators

/-- Restricting a final cut set to the selected outer gaps preserves every
branch factor and every inner near factor with its final immediate neighbors. -/
theorem nestedCutWeight_selected (D H : TripleArray) (X : IntervalArray)
    {i j : ℕ} (hij : i < j)
    (R : Σ T : IntervalCutSet i j, ↥T.val.powerset) :
    nestedCutWeight D H X i j (selectedToCutRefinement R) =
      cutRefinementWeight D H X i j R.1.val R.2.val := by
  classical
  rcases R with ⟨⟨T, hT⟩, ⟨S, hS⟩⟩
  have hTI := Finset.mem_powerset.mp hT
  have hST := Finset.mem_powerset.mp hS
  have hSI := hST.trans hTI
  change gateProduct (fun _ _ _ => 0) H i j (cutVertices i j S) *
      (∏ e : CutGap i j S, cutContribution D (fun _ _ _ => 0) X e.val.1 e.val.2
        (T ∩ Finset.Ioo e.val.1 e.val.2)) =
    cutRefinementWeight D H X i j T S
  rw [gateProduct_zero_near H hij hSI]
  simp only [cutContribution, Finset.prod_mul_distrib]
  rw [Finset.prod_coe_sort (cutEdges i j S) (fun e : ℕ × ℕ =>
      gateProduct D (fun _ _ _ => 0) e.1 e.2
        (cutVertices e.1 e.2 (T ∩ Finset.Ioo e.1 e.2))),
    Finset.prod_coe_sort (cutEdges i j S) (fun e : ℕ × ℕ =>
      branchProduct X (cutVertices e.1 e.2 (T ∩ Finset.Ioo e.1 e.2))),
    local_product_near D hij hSI hST hTI,
    local_product_branch X hij hSI hST hTI]
  unfold cutRefinementWeight
  ring
/-- Regroup the expanded actual Phi map by a final cut set and its selected
outer subset. This is finite distributivity, not an assumed refinement law. -/
theorem phi_eq_sum_refinementWeight (D H : TripleArray) (X : IntervalArray)
    {i j : ℕ} (hij : i < j) :
    phi D H X i j =
      ∑ R : (Σ T : IntervalCutSet i j, ↥T.val.powerset),
        cutRefinementWeight D H X i j R.1.val R.2.val := by
  classical
  calc
    phi D H X i j = ∑ T : IntervalCutSet i j, cutContribution D H X i j T.val :=
      (Finset.sum_coe_sort (Finset.Ioo i j).powerset (cutContribution D H X i j)).symm
    _ = ∑ T : IntervalCutSet i j, ∑ S : ↥T.val.powerset,
        cutRefinementWeight D H X i j T.val S.val := by
      apply Finset.sum_congr rfl
      intro T _
      rw [cutContribution_eq_sum_refinementWeights D H X hij
        (Finset.mem_powerset.mp T.property)]
      exact (Finset.sum_coe_sort T.val.powerset (cutRefinementWeight D H X i j T.val)).symm
    _ = _ := (Fintype.sum_sigma (fun R : (Σ T : IntervalCutSet i j, ↥T.val.powerset) =>
      cutRefinementWeight D H X i j R.1.val R.2.val)).symm

/-- The concrete finite-cut map factors into its near-only and far-only maps.
The proof uses the actual two-stage refinement equivalence and matched weights. -/
theorem phi_factorization (D H : TripleArray) (X : IntervalArray)
    {i j : ℕ} (hij : i < j) :
    phi D H X i j =
      phi (fun _ _ _ => 0) H (fun a b => phi D (fun _ _ _ => 0) X a b) i j := by
  classical
  calc
    phi D H X i j =
        ∑ R : (Σ T : IntervalCutSet i j, ↥T.val.powerset),
          cutRefinementWeight D H X i j R.1.val R.2.val :=
      phi_eq_sum_refinementWeight D H X hij
    _ = ∑ R : (Σ T : IntervalCutSet i j, ↥T.val.powerset),
        nestedCutWeight D H X i j (selectedToCutRefinement R) := by
      apply Finset.sum_congr rfl
      intro R _
      exact (nestedCutWeight_selected D H X hij R).symm
    _ = ∑ R : (Σ S : IntervalCutSet i j,
        ∀ e : CutGap i j S.val, IntervalCutSet e.val.1 e.val.2),
        nestedCutWeight D H X i j R :=
      (cutRefinementEquiv hij).symm.sum_comp (nestedCutWeight D H X i j)
    _ = _ := (phi_composition_eq_sum D H X hij).symm


end DirectGLSSW
