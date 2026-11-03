import DirectGLSSW.CutExpansion

/-!
# Endpoint cut-list single-gate identities

Source context: `ep:endpoint-calculation`, equations `ep:F`,
`ep:collinear-far-identities`, and `ep:three-endpoint-events`.
This module proves finite cut-list algebra under middle-only near data. It
makes no geometric crossing or propagated-current claim.
-/

namespace DirectGLSSW
open scoped BigOperators

/-- Middle-only near data makes the actual gate product a product indexed by
exactly the selected internal cuts. -/
theorem gateProduct_middleNear_eq_prod
    (d : ℕ → ℚ) (H : TripleArray) {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) :
    gateProduct (fun _ k _ => d k) H i j (cutVertices i j S) =
      ∏ k ∈ S, (d k - H i k j) / 2 := by
  rw [gateProduct_eq_prod_cutTriples _ _ hij hS]
  calc
    _ = ∏ k ∈ (cutTriples i j S).image (fun t => t.2.1),
        (d k - H i k j) / 2 :=
      (Finset.prod_image (f := fun k => (d k - H i k j) / 2)
        (fun t ht u hu htu => cutTriples_middle_injective hij hS ht hu htu)).symm
    _ = _ := by rw [cutTriples_middle_image hij hS]

/-- Changing exactly one far gate changes an actual cut contribution by the
changed gate times the product of the other old gates and the unchanged
branch product. -/
theorem cutContribution_middleNear_single_far_gate_change
    (d : ℕ → ℚ) (H0 H1 : TripleArray) (b : IntervalArray)
    {i j : ℕ} (hij : i < j) {S : Finset ℕ}
    (hS : S ⊆ Finset.Ioo i j) {k : ℕ} (δ : ℚ)
    (hother : ∀ l, l ≠ k → H1 i l j = H0 i l j)
    (hchange : H1 i k j - H0 i k j = 2 * δ) :
    cutContribution (fun _ l _ => d l) H1 b i j S -
        cutContribution (fun _ l _ => d l) H0 b i j S =
      if k ∈ S then
        -δ * (∏ l ∈ S.erase k, (d l - H0 i l j) / 2) *
          branchProduct b (cutVertices i j S)
      else 0 := by
  classical
  unfold cutContribution
  rw [gateProduct_middleNear_eq_prod d H1 hij hS,
    gateProduct_middleNear_eq_prod d H0 hij hS]
  let oldGate : ℕ → ℚ := fun l => (d l - H0 i l j) / 2
  let newGate : ℕ → ℚ := fun l => (d l - H1 i l j) / 2
  by_cases hk : k ∈ S
  · have hrest : (∏ l ∈ S.erase k, newGate l) =
        ∏ l ∈ S.erase k, oldGate l := by
      apply Finset.prod_congr rfl
      intro l hl
      have hlk : l ≠ k := fun heq => (Finset.mem_erase.mp hl).1 heq
      simp only [oldGate, newGate]
      rw [hother l hlk]
    have hchange' : (H1 i k j - H0 i k j) / 2 = δ := by
      rw [hchange]
      ring
    have hdiff : newGate k - oldGate k = -δ := by
      dsimp [newGate, oldGate]
      calc
        _ = -((H1 i k j - H0 i k j) / 2) := by ring
        _ = -δ := congrArg Neg.neg hchange'
    simp only [if_pos hk]
    calc
      _ = (newGate k - oldGate k) *
          (∏ l ∈ S.erase k, oldGate l) * branchProduct b (cutVertices i j S) := by
        rw [← Finset.mul_prod_erase S newGate hk,
          ← Finset.mul_prod_erase S oldGate hk, hrest]
        ring
      _ = _ := by
        rw [hdiff]
  · have hsame : (∏ l ∈ S, newGate l) = ∏ l ∈ S, oldGate l := by
      apply Finset.prod_congr rfl
      intro l hl
      have hlk : l ≠ k := fun heq => hk (heq ▸ hl)
      simp only [oldGate, newGate]
      rw [hother l hlk]
    simp only [hk, if_false]
    rw [hsame]
    ring

/-- Summing the single-gate change over all actual internal cut lists gives a
finite sum indexed exactly by supports containing the changed middle cut. -/
theorem phi_middleNear_single_far_gate_change
    (d : ℕ → ℚ) (H0 H1 : TripleArray) (b : IntervalArray)
    {i j : ℕ} (hij : i < j) (k : ℕ) (δ : ℚ)
    (hother : ∀ l, l ≠ k → H1 i l j = H0 i l j)
    (hchange : H1 i k j - H0 i k j = 2 * δ) :
    phi (fun _ l _ => d l) H1 b i j -
        phi (fun _ l _ => d l) H0 b i j =
      -δ * ∑ S ∈ (Finset.Ioo i j).powerset.filter (fun S => k ∈ S),
        (∏ l ∈ S.erase k, (d l - H0 i l j) / 2) *
          branchProduct b (cutVertices i j S) := by
  classical
  unfold phi
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ S ∈ (Finset.Ioo i j).powerset,
        (if k ∈ S then
          -δ * (∏ l ∈ S.erase k, (d l - H0 i l j) / 2) *
            branchProduct b (cutVertices i j S)
         else 0) := by
      apply Finset.sum_congr rfl
      intro S hS
      have hsubset : S ⊆ Finset.Ioo i j := Finset.mem_powerset.mp hS
      simpa using cutContribution_middleNear_single_far_gate_change
        d H0 H1 b hij hsubset δ hother hchange
    _ = ∑ S ∈ (Finset.Ioo i j).powerset.filter (fun S => k ∈ S),
        -δ * (∏ l ∈ S.erase k, (d l - H0 i l j) / 2) *
          branchProduct b (cutVertices i j S) := by
      rw [Finset.sum_filter]
    _ = -δ * ∑ S ∈ (Finset.Ioo i j).powerset.filter (fun S => k ∈ S),
        (∏ l ∈ S.erase k, (d l - H0 i l j) / 2) *
          branchProduct b (cutVertices i j S) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring

end DirectGLSSW
