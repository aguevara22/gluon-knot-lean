import DirectGLSSW.IntervalCurrent

/-!
# Fidelity of the finite ordinary-current recurrence

Source: `ep:Phi`, `ep:tree-recursion` and the following triangular
uniqueness paragraph. This module preserves the existing guarded
implementation and proves that its guard is always true at a nonunary
branch. All source equations and uniqueness conclusions concern `i < j`.
No conclusion constrains entries on or below the diagonal.

These declarations are provisional until independent statement review.
-/

namespace DirectGLSSW
open scoped BigOperators

private theorem adjacent_lt_of_pairwise {v : List ℕ}
    (hv : v.Pairwise (· < ·)) {a b : ℕ}
    (hab : (a, b) ∈ v.zip v.tail) : a < b := by
  induction v with
  | nil => simp at hab
  | cons x xs ih =>
      cases xs with
      | nil => simp at hab
      | cons y ys =>
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hab
          rcases hab with heq | hab
          · cases heq
            exact (List.pairwise_cons.mp hv).1 b (by simp)
          · exact ih (List.pairwise_cons.mp hv).2 hab

private theorem adjacent_bounds_aux {i j k : ℕ} {l : List ℕ}
    (hik : i ≤ k) (hkj : k < j)
    (hl : ∀ x ∈ l, i < x ∧ x < j)
    (hproper : l ≠ [] ∨ i < k) {a b : ℕ}
    (hab : (a, b) ∈ (k :: l ++ [j]).zip (l ++ [j])) :
    i ≤ a ∧ b ≤ j ∧ b - a < j - i := by
  induction l generalizing k with
  | nil =>
      simp at hab
      obtain ⟨rfl, rfl⟩ := hab
      have hik' : i < a := hproper.resolve_left (by simp)
      omega
  | cons x xs ih =>
      have hx := hl x (by simp)
      simp only [List.cons_append, List.zip_cons_cons, List.mem_cons] at hab
      rcases hab with heq | hab
      · cases heq
        omega
      · exact ih (by omega) hx.2 (fun y hy => hl y (by simp [hy]))
          (Or.inr hx.1) hab

/-- The endpoint-and-subset representation gives a strictly increasing cut list. -/
theorem cutVertices_pairwise {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) :
    (cutVertices i j S).Pairwise (· < ·) := by
  have hint : ∀ x ∈ S.sort (· ≤ ·), i < x ∧ x < j := by
    intro x hx
    exact Finset.mem_Ioo.mp (hS ((Finset.mem_sort (· ≤ ·)).mp hx))
  change (i :: (S.sort (· ≤ ·) ++ [j])).Pairwise (· < ·)
  apply List.pairwise_cons.mpr
  constructor
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact (hint x hx).1
    · exact hij
  · apply List.pairwise_append.mpr
    refine ⟨S.sort_sorted_lt, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    exact (hint x hx).2

/-- Every branch of every nonunary cut has positive, strictly smaller length. -/
theorem cutVertices_branch_bounds {i j a b : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) (hne : S.Nonempty)
    (hab : (a, b) ∈ (cutVertices i j S).zip (cutVertices i j S).tail) :
    i ≤ a ∧ a < b ∧ b ≤ j ∧ b - a < j - i := by
  have hint : ∀ x ∈ S.sort (· ≤ ·), i < x ∧ x < j := by
    intro x hx
    exact Finset.mem_Ioo.mp (hS ((Finset.mem_sort (· ≤ ·)).mp hx))
  have hsne : S.sort (· ≤ ·) ≠ [] := by
    obtain ⟨x, hx⟩ := hne
    intro heq
    have hmem : x ∈ S.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hx
    simp [heq] at hmem
  have hbounds := adjacent_bounds_aux (le_refl i) hij hint (Or.inl hsne)
    (by simpa only [cutVertices, List.tail_cons] using hab)
  exact ⟨hbounds.1, adjacent_lt_of_pairwise (cutVertices_pairwise hij hS) hab,
    hbounds.2.1, hbounds.2.2⟩

/-- A nonunary sum reads only positive intervals shorter than its parent. -/
theorem nonUnary_congr_lt (D H : TripleArray) {X Y : IntervalArray} {i j : ℕ}
    (hij : i < j)
    (hXY : ∀ a b, a < b → b - a < j - i → X a b = Y a b) :
    nonUnary D H X i j = nonUnary D H Y i j := by
  unfold nonUnary
  apply Finset.sum_congr rfl
  intro S hS
  obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hS
  have hnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  have hsubset : S ⊆ Finset.Ioo i j := Finset.mem_powerset.mp hsub
  unfold cutContribution
  congr 1
  unfold branchProduct
  apply congrArg List.prod
  apply List.map_congr_left
  rintro ⟨a, b⟩ hab
  have hb := cutVertices_branch_bounds hij hsubset hnonempty hab
  exact hXY a b hb.2.1 hb.2.2.2

/-- The implementation's decrease guard disappears on every source interval. -/
theorem ordinaryCurrent_recurrence (D H : TripleArray) {i j : ℕ}
    (hij : i < j) :
    ordinaryCurrent D H i j =
      source i j - nonUnary D H (ordinaryCurrent D H) i j := by
  rw [ordinaryCurrent]
  congr 1
  apply nonUnary_congr_lt D H hij
  intro a b _ hlt
  simp only [dif_pos hlt]

/-- The constructed ordinary current solves the exact finite Phi equation. -/
theorem ordinaryCurrent_phi (D H : TripleArray) {i j : ℕ} (hij : i < j) :
    phi D H (ordinaryCurrent D H) i j = source i j := by
  rw [phi_eq_unary_add]
  exact (eq_sub_iff_add_eq).mp (ordinaryCurrent_recurrence D H hij)

/-- Any solution of the source equation agrees with the constructed current
on every strictly upper-triangular entry. Values elsewhere are irrelevant. -/
theorem ordinaryCurrent_unique (D H : TripleArray) (X : IntervalArray)
    (hX : ∀ i j, i < j → phi D H X i j = source i j)
    {i j : ℕ} (hij : i < j) : X i j = ordinaryCurrent D H i j := by
  generalize hn : j - i = n
  induction n using Nat.strong_induction_on generalizing i j with
  | h n ih =>
      have hshort : nonUnary D H X i j =
          nonUnary D H (ordinaryCurrent D H) i j := by
        apply nonUnary_congr_lt D H hij
        intro a b hab hlt
        exact ih (b - a) (by omega) hab rfl
      have hsource : X i j + nonUnary D H X i j = source i j := by
        rw [← phi_eq_unary_add]
        exact hX i j hij
      rw [ordinaryCurrent_recurrence D H hij, ← hshort]
      exact (eq_sub_iff_add_eq).mpr hsource

end DirectGLSSW
