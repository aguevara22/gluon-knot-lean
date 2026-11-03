import DirectGLSSW.CurrentFidelity
import DirectGLSSW.EndpointSingleGate

/-!
# Direct endpoint ordinary-current jump from the cut-list identity

This module first proves interval locality for an arbitrary fixed near array,
then derives the actual ordinary-current jump at one endpoint pair. It makes
no claim about propagation to larger endpoints or about geometric events.
-/

namespace DirectGLSSW
open scoped BigOperators

/-- For fixed near data, nonunary cut contributions agree when far data and
all shorter branch entries agree throughout the interval. -/
theorem nonUnary_congr_interval_fixed_near (D H₁ H₂ : TripleArray)
    {X₁ X₂ : IntervalArray} {i j : ℕ} (hij : i < j)
    (hH : ∀ a b c, i ≤ a → a < b → b < c → c ≤ j → H₁ a b c = H₂ a b c)
    (hX : ∀ a b, i ≤ a → a < b → b ≤ j → b - a < j - i → X₁ a b = X₂ a b) :
    nonUnary D H₁ X₁ i j = nonUnary D H₂ X₂ i j := by
  classical
  unfold nonUnary
  apply Finset.sum_congr rfl
  intro S hS
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hS
  have hSnon : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  have hSsub : S ⊆ Finset.Ioo i j := Finset.mem_powerset.mp hmem
  rw [cutContribution, cutContribution,
    gateProduct_eq_prod_cutTriples _ _ hij hSsub,
    gateProduct_eq_prod_cutTriples _ _ hij hSsub,
    branchProduct_eq_prod_cutEdges X₁ hij hSsub,
    branchProduct_eq_prod_cutEdges X₂ hij hSsub]
  congr 1
  · apply Finset.prod_congr rfl
    intro t ht
    have hmid := cutTriples_middle_mem hij hSsub ht
    have hbound := Finset.mem_Ioo.mp (hSsub hmid)
    have heq := hH i t.2.1 j (le_refl i) hbound.1 hbound.2 (le_refl j)
    rw [heq]
  · apply Finset.prod_congr rfl
    intro e he
    rcases e with ⟨a, b⟩
    have hb := cutVertices_branch_bounds hij hSsub hSnon
      (by simpa only [cutEdges, List.mem_toFinset] using he)
    exact hX a b hb.1 hb.2.1 hb.2.2.1 hb.2.2.2

/-- The ordinary-current interval induction is local for every fixed near
array, with no zero-near assumption. -/
theorem ordinaryCurrent_congr_interval_fixed_near (D H₁ H₂ : TripleArray)
    {i j : ℕ} (hij : i < j)
    (hH : ∀ a b c, i ≤ a → a < b → b < c → c ≤ j → H₁ a b c = H₂ a b c) :
    ordinaryCurrent D H₁ i j = ordinaryCurrent D H₂ i j := by
  generalize hn : j - i = n
  induction n using Nat.strong_induction_on generalizing i j with
  | h n ih =>
      have hnon : nonUnary D H₁ (ordinaryCurrent D H₁) i j =
          nonUnary D H₂ (ordinaryCurrent D H₂) i j := by
        apply nonUnary_congr_interval_fixed_near D H₁ H₂ hij hH
        intro a b hia hab hbj hlt
        have hHsub : ∀ x y z, a ≤ x → x < y → y < z → z ≤ b → H₁ x y z = H₂ x y z := by
          intro x y z hax hxy hyz hzb
          exact hH x y z (by omega) hxy hyz (by omega)
        exact ih (b - a) (by omega) hab hHsub rfl
      rw [ordinaryCurrent_recurrence D H₁ hij,
        ordinaryCurrent_recurrence D H₂ hij, hnon]

/-- If the only possible changed far triple is the whole parent interval,
ordinary currents agree on every proper subinterval. -/
theorem ordinaryCurrent_proper_interval_agreement (D H₀ H₁ : TripleArray)
    {i j a b : ℕ} (hij : i < j) (hia : i ≤ a) (hab : a < b) (hbj : b ≤ j)
    (hshort : b - a < j - i) {k : ℕ}
    (hother : ∀ x y z, i ≤ x → x < y → y < z → z ≤ j →
      (x ≠ i ∨ y ≠ k ∨ z ≠ j) → H₁ x y z = H₀ x y z) :
    ordinaryCurrent D H₁ a b = ordinaryCurrent D H₀ a b := by
  apply ordinaryCurrent_congr_interval_fixed_near D H₁ H₀ hab
  intro x y z hax hxy hyz hzb
  have hix : i ≤ x := le_trans hia hax
  have hzj : z ≤ j := le_trans hzb hbj
  by_cases htarget : x = i ∧ y = k ∧ z = j
  · rcases htarget with ⟨hxi, hyk, hzj'⟩
    have hai : a = i := by omega
    have hbj' : b = j := by omega
    omega
  · exact (hother x y z hix hxy hyz hzj (by
      by_cases hxi : x = i
      · by_cases hyk : y = k
        · by_cases hzj' : z = j
          · exact False.elim (htarget ⟨hxi, hyk, hzj'⟩)
          · exact Or.inr (Or.inr hzj')
        · exact Or.inr (Or.inl hyk)
      · exact Or.inl hxi))

/-- The actual ordinary current changes by the punctured cut sum at the
specified far-gate event. -/
theorem ordinaryCurrent_middle_single_far_gate_change
    (d : ℕ → ℚ) (H₀ H₁ : TripleArray) {i j : ℕ} (hij : i < j)
    {k : ℕ} (hik : i < k) (hkj : k < j) (δ : ℚ)
    (hother : ∀ a b c, i ≤ a → a < b → b < c → c ≤ j →
      (a ≠ i ∨ b ≠ k ∨ c ≠ j) → H₁ a b c = H₀ a b c)
    (hchange : H₁ i k j - H₀ i k j = 2 * δ) :
    ordinaryCurrent (fun _ l _ => d l) H₁ i j -
        ordinaryCurrent (fun _ l _ => d l) H₀ i j =
      δ * ∑ S ∈ (Finset.Ioo i j).powerset.filter (fun S => k ∈ S),
        (∏ l ∈ S.erase k, (d l - H₀ i l j) / 2) *
          branchProduct (ordinaryCurrent (fun _ l _ => d l) H₀)
            (cutVertices i j S) := by
  have _hkInterior : k ∈ Finset.Ioo i j := Finset.mem_Ioo.mpr ⟨hik, hkj⟩
  let D : TripleArray := fun _ l _ => d l
  let b₀ : IntervalArray := ordinaryCurrent D H₀
  have hproper : ∀ a b, i ≤ a → a < b → b ≤ j → b - a < j - i →
      ordinaryCurrent D H₁ a b = ordinaryCurrent D H₀ a b := by
    intro a b hia hab hbj hshort
    exact ordinaryCurrent_proper_interval_agreement D H₀ H₁ hij hia hab hbj hshort hother
  have hbranch : nonUnary D H₁ (ordinaryCurrent D H₁) i j = nonUnary D H₁ b₀ i j :=
    nonUnary_congr_interval_fixed_near D H₁ H₁ hij (by intro a b c ha hab hbc hc; rfl) (by
      intro a b hia hab hbj hshort
      exact hproper a b hia hab hbj hshort)
  let H₁' : TripleArray := fun a b c =>
    if a = i ∧ b = k ∧ c = j then H₁ a b c else H₀ a b c
  have hHlocal : ∀ a b c, i ≤ a → a < b → b < c → c ≤ j →
      H₁ a b c = H₁' a b c := by
    intro a b c hia hab hbc hcj
    by_cases htarget : a = i ∧ b = k ∧ c = j
    · simp [H₁', htarget]
    · simp [H₁', htarget, hother a b c hia hab hbc hcj (by
        by_cases hai : a = i
        · by_cases hbk : b = k
          · by_cases hcj' : c = j
            · exact False.elim (htarget ⟨hai, hbk, hcj'⟩)
            · exact Or.inr (Or.inr hcj')
          · exact Or.inr (Or.inl hbk)
        · exact Or.inl hai)]
  have hphiLocal : phi D H₁ b₀ i j = phi D H₁' b₀ i j := by
    rw [phi_eq_unary_add, phi_eq_unary_add]
    congr 1
    exact nonUnary_congr_interval_fixed_near D H₁ H₁' hij hHlocal (by
      intro a b hia hab hbj hshort
      rfl)
  have hother' : ∀ l, l ≠ k → H₁' i l j = H₀ i l j := by
    intro l hl
    simp [H₁', hl]
  have hchange' : H₁' i k j - H₀ i k j = 2 * δ := by
    simp [H₁', hik, hkj]
    exact hchange
  have hphiChange :=
    DirectGLSSW.phi_middleNear_single_far_gate_change d H₀ H₁' b₀ hij k δ hother' hchange'
  have hphi : phi D H₁ b₀ i j - phi D H₀ b₀ i j =
      -δ * ∑ S ∈ (Finset.Ioo i j).powerset.filter (fun S => k ∈ S),
        (∏ l ∈ S.erase k, (d l - H₀ i l j) / 2) *
          branchProduct b₀ (cutVertices i j S) := by
    rw [hphiLocal]
    exact hphiChange
  have hphiNonUnary : phi D H₁ b₀ i j - phi D H₀ b₀ i j =
      nonUnary D H₁ b₀ i j - nonUnary D H₀ b₀ i j := by
    rw [phi_eq_unary_add, phi_eq_unary_add]
    ring
  calc
    _ = (source i j - nonUnary D H₁ (ordinaryCurrent D H₁) i j) -
        (source i j - nonUnary D H₀ (ordinaryCurrent D H₀) i j) := by
          rw [ordinaryCurrent_recurrence D H₁ hij,
            ordinaryCurrent_recurrence D H₀ hij]
    _ = -(nonUnary D H₁ b₀ i j - nonUnary D H₀ b₀ i j) := by
          rw [hbranch]
          ring
    _ = δ * ∑ S ∈ (Finset.Ioo i j).powerset.filter (fun S => k ∈ S),
        (∏ l ∈ S.erase k, (d l - H₀ i l j) / 2) *
          branchProduct b₀ (cutVertices i j S) := by
          rw [← hphiNonUnary, hphi]
          ring

end DirectGLSSW
