import DirectGLSSW.NearData

namespace DirectGLSSW
open scoped BigOperators

theorem nonUnary_zero_near_congr_interval (H₁ H₂ : TripleArray)
    {X₁ X₂ : IntervalArray} {i j : ℕ} (hij : i < j)
    (hH : ∀ a b c, i ≤ a → a < b → b < c → c ≤ j → H₁ a b c = H₂ a b c)
    (hX : ∀ a b, i ≤ a → a < b → b ≤ j → b - a < j - i →
      X₁ a b = X₂ a b) :
    nonUnary (fun _ _ _ => 0) H₁ X₁ i j =
      nonUnary (fun _ _ _ => 0) H₂ X₂ i j := by
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
    have hbmem := cutTriples_middle_mem hij hSsub ht
    have hb := Finset.mem_Ioo.mp (hSsub hbmem)
    have heq := hH i t.2.1 j (le_refl i) hb.1 hb.2 (le_refl j)
    simp only [zero_sub]
    rw [heq]
  · apply Finset.prod_congr rfl
    intro e he
    rcases e with ⟨a, b⟩
    have hb := cutVertices_branch_bounds hij hSsub hSnon
      (by simpa only [cutEdges, List.mem_toFinset] using he)
    exact hX a b hb.1 hb.2.1 hb.2.2.1 hb.2.2.2

theorem ordinaryCurrent_zero_near_congr_interval (H₁ H₂ : TripleArray)
    {i j : ℕ} (hij : i < j)
    (hH : ∀ a b c, i ≤ a → a < b → b < c → c ≤ j → H₁ a b c = H₂ a b c) :
    ordinaryCurrent (fun _ _ _ => 0) H₁ i j =
      ordinaryCurrent (fun _ _ _ => 0) H₂ i j := by
  generalize hn : j - i = n
  induction n using Nat.strong_induction_on generalizing i j with
  | h n ih =>
      have hnon : nonUnary (fun _ _ _ => 0) H₁
          (ordinaryCurrent (fun _ _ _ => 0) H₁) i j =
          nonUnary (fun _ _ _ => 0) H₂
          (ordinaryCurrent (fun _ _ _ => 0) H₂) i j := by
        apply nonUnary_zero_near_congr_interval H₁ H₂ hij hH
        intro a b hia hab hbj hlt
        have hHsub : ∀ x y z, a ≤ x → x < y → y < z → z ≤ b → H₁ x y z = H₂ x y z := by
          intro x y z hax hxy hyz hzb
          exact hH x y z (by omega) hxy hyz (by omega)
        exact ih (b - a) (by omega) hab hHsub rfl
      rw [ordinaryCurrent_recurrence (fun _ _ _ => 0) H₁ hij,
        ordinaryCurrent_recurrence (fun _ _ _ => 0) H₂ hij, hnon]

theorem markedAmplitude_zero_near_congr_interval (H₁ H₂ : TripleArray)
    {i j : ℕ} (hij : i < j)
    (hH : ∀ a b c, i ≤ a → a < b → b < c → c ≤ j → H₁ a b c = H₂ a b c) :
    markedAmplitude (fun _ _ _ => 0) H₁ i j =
      markedAmplitude (fun _ _ _ => 0) H₂ i j := by
  unfold markedAmplitude
  rw [phi_eq_unary_add, phi_eq_unary_add]
  congr 1
  · exact ordinaryCurrent_zero_near_congr_interval H₁ H₂ hij hH
  · apply nonUnary_zero_near_congr_interval (fun a b c => -H₁ a b c)
      (fun a b c => -H₂ a b c) hij
    · intro a b c hia hab hbc hcj
      rw [hH a b c hia hab hbc hcj]
    · intro a b hia hab hbj _
      apply ordinaryCurrent_zero_near_congr_interval H₁ H₂ hab
      intro x y z hax hxy hyz hzb
      exact hH x y z (by omega) hxy hyz (by omega)

theorem markedAmplitude_congr_interval (D₁ D₂ H₁ H₂ : TripleArray)
    {i j : ℕ} (hij : i < j)
    (hH : ∀ a b c, i ≤ a → a < b → b < c → c ≤ j → H₁ a b c = H₂ a b c) :
    markedAmplitude D₁ H₁ i j = markedAmplitude D₂ H₂ i j := by
  calc
    markedAmplitude D₁ H₁ i j =
        markedAmplitude (fun _ _ _ => 0) H₁ i j :=
      markedAmplitude_zero_near D₁ H₁ hij
    _ = markedAmplitude (fun _ _ _ => 0) H₂ i j :=
      markedAmplitude_zero_near_congr_interval H₁ H₂ hij hH
    _ = markedAmplitude D₂ H₂ i j :=
      (markedAmplitude_zero_near D₂ H₂ hij).symm

end DirectGLSSW





