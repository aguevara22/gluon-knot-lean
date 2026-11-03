import DirectGLSSW.CurrentFidelity

/-!
# Disjoint gaps in an increasing cut list

Source: `ep:factorization`.
The finite edges are exactly adjacent pairs of the existing cut list.
These are combinatorial prerequisites; the Phi composition identity is not proved here.
-/

namespace DirectGLSSW

/-- Consecutive vertices in a strictly increasing list have no intervening
list vertex. The weak inequalities include the two endpoints. -/
theorem adjacent_separation {v : List ℕ}
    (hv : v.Pairwise (· < ·)) {a b : ℕ}
    (hab : (a, b) ∈ v.zip v.tail) :
    a ∈ v ∧ b ∈ v ∧ a < b ∧ ∀ x ∈ v, x ≤ a ∨ b ≤ x := by
  induction v with
  | nil => simp at hab
  | cons y ys ih =>
      cases ys with
      | nil => simp at hab
      | cons z zs =>
          have hy := List.pairwise_cons.mp hv
          have hz := List.pairwise_cons.mp hy.2
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hab
          rcases hab with heq | hab
          · cases heq
            refine ⟨by simp, by simp, hy.1 b (by simp), ?_⟩
            intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | rfl | hx
            · exact Or.inl (le_refl _)
            · exact Or.inr (le_refl _)
            · exact Or.inr (Nat.le_of_lt (hz.1 x hx))
          · obtain ⟨ha, hb, hlt, hsep⟩ := ih hy.2 hab
            refine ⟨by simp [ha], by simp [hb], hlt, ?_⟩
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact Or.inl (Nat.le_of_lt (hy.1 a ha))
            · exact hsep x hx

/-- Open gaps of a strictly increasing list contain a point at most once. -/
theorem adjacent_gap_unique {v : List ℕ}
    (hv : v.Pairwise (· < ·)) {e f : ℕ × ℕ} {k : ℕ}
    (he : e ∈ v.zip v.tail) (hf : f ∈ v.zip v.tail)
    (hek : e.1 < k ∧ k < e.2) (hfk : f.1 < k ∧ k < f.2) : e = f := by
  obtain ⟨hea, heb, _, hsepE⟩ := adjacent_separation hv he
  obtain ⟨hfa, hfb, _, hsepF⟩ := adjacent_separation hv hf
  have h₁ := hsepE f.1 hfa
  have h₂ := hsepF e.1 hea
  have h₃ := hsepE f.2 hfb
  have h₄ := hsepF e.2 heb
  apply Prod.ext <;> omega

private theorem exists_adjacent_gap_aux {i j k : ℕ} {l : List ℕ}
    (hik : i < k) (hkj : k < j) (hk : k ∉ l) :
    ∃ e ∈ (i :: l ++ [j]).zip (l ++ [j]), e.1 < k ∧ k < e.2 := by
  induction l generalizing i with
  | nil => exact ⟨(i, j), by simp, hik, hkj⟩
  | cons x xs ih =>
      by_cases hkx : k < x
      · exact ⟨(i, x), by simp, hik, hkx⟩
      · have hxk : x < k := by
          have hne : k ≠ x := fun heq => hk (by simp [heq])
          omega
        obtain ⟨e, he, hek⟩ := ih hxk (fun h => hk (by simp [h]))
        refine ⟨e, ?_, hek⟩
        simp only [List.cons_append, List.zip_cons_cons, List.mem_cons]
        exact Or.inr he

/-- Every internal point outside the selected cuts lies in exactly one
open interval between consecutive vertices of the existing cut list. -/
theorem cutVertices_existsUnique_gap {i j k : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (hk : k ∈ Finset.Ioo i j) (hnot : k ∉ S) :
    ∃! e : ℕ × ℕ,
      e ∈ (cutVertices i j S).zip (cutVertices i j S).tail ∧
      e.1 < k ∧ k < e.2 := by
  have hsort : k ∉ S.sort (· ≤ ·) := by simpa using hnot
  obtain ⟨e, he, hek⟩ := exists_adjacent_gap_aux
    (Finset.mem_Ioo.mp hk).1 (Finset.mem_Ioo.mp hk).2 hsort
  have he' : e ∈ (cutVertices i j S).zip (cutVertices i j S).tail := by
    simpa only [cutVertices, List.tail_cons] using he
  refine ⟨e, ⟨he', hek⟩, ?_⟩
  intro f hf
  exact adjacent_gap_unique (cutVertices_pairwise hij hS) hf.1 he' hf.2 hek

/-- Finite edge support, without changing the source cut representation. -/
def cutEdges (i j : ℕ) (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  ((cutVertices i j S).zip (cutVertices i j S).tail).toFinset

/-- The interval of each consecutive edge lies inside the parent interval
and contains no selected cut. -/
theorem cutEdges_gap_subset {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) {e : ℕ × ℕ}
    (he : e ∈ cutEdges i j S) :
    Finset.Ioo e.1 e.2 ⊆ Finset.Ioo i j \ S := by
  have he' : e ∈ (cutVertices i j S).zip (cutVertices i j S).tail := by
    simpa only [cutEdges, List.mem_toFinset] using he
  obtain ⟨hea, heb, _, hsep⟩ := adjacent_separation (cutVertices_pairwise hij hS) he'
  have hbound : ∀ x ∈ cutVertices i j S, i ≤ x ∧ x ≤ j := by
    intro x hx
    simp only [cutVertices, List.mem_cons, List.mem_append, List.mem_singleton,
      Finset.mem_sort, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | hx) | rfl
    · exact ⟨le_refl _, Nat.le_of_lt hij⟩
    · have hx' := Finset.mem_Ioo.mp (hS hx)
      exact ⟨Nat.le_of_lt hx'.1, Nat.le_of_lt hx'.2⟩
    · exact ⟨Nat.le_of_lt hij, le_refl _⟩
  intro k hk
  have hek := Finset.mem_Ioo.mp hk
  have ha := hbound e.1 hea
  have hb := hbound e.2 heb
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_Ioo.mpr (by omega), ?_⟩
  intro hkS
  have hkv : k ∈ cutVertices i j S := by simp [cutVertices, hkS]
  have hsplit := hsep k hkv
  omega

/-- Distinct edges have disjoint open gap intervals. -/
theorem cutEdges_gaps_pairwiseDisjoint {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) :
    Set.PairwiseDisjoint (cutEdges i j S : Set (ℕ × ℕ))
      (fun e => Finset.Ioo e.1 e.2) := by
  intro e he f hf hef
  apply Finset.disjoint_left.mpr
  intro k hke hkf
  apply hef
  apply adjacent_gap_unique (cutVertices_pairwise hij hS)
    (by simpa only [cutEdges, Finset.mem_coe, List.mem_toFinset] using he)
    (by simpa only [cutEdges, Finset.mem_coe, List.mem_toFinset] using hf)
    (Finset.mem_Ioo.mp hke) (Finset.mem_Ioo.mp hkf)

/-- The disjoint gap intervals exhaust precisely the unselected internal
vertices. Disjointness is `cutEdges_gaps_pairwiseDisjoint`. -/
theorem cutEdges_biUnion_Ioo {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) :
    (cutEdges i j S).biUnion (fun e => Finset.Ioo e.1 e.2) =
      Finset.Ioo i j \ S := by
  ext k
  constructor
  · intro hk
    obtain ⟨e, he, hk⟩ := Finset.mem_biUnion.mp hk
    exact cutEdges_gap_subset hij hS he hk
  · intro hk
    obtain ⟨hint, hnot⟩ := Finset.mem_sdiff.mp hk
    obtain ⟨e, ⟨he, hek⟩, _⟩ := cutVertices_existsUnique_gap hij hS hint hnot
    apply Finset.mem_biUnion.mpr
    exact ⟨e, by simpa only [cutEdges, List.mem_toFinset] using he,
      Finset.mem_Ioo.mpr hek⟩

end DirectGLSSW
