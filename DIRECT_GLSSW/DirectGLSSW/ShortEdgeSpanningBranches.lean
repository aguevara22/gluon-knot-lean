import DirectGLSSW.ShortEdgeWeighted

namespace DirectGLSSW.ShortEdgeWeighted.SpanningBranchesImpl
open scoped BigOperators

theorem parentTable_liftAfter_on_side
    (a x y : ℕ) (ha : 0 < a) (hxy : x < y)
    (hside : y ≤ a ∨ a ≤ x) (t : ℕ → Sign) (U : IntervalArray) :
    parentTable a ha t U (ShortEdgeCutFibers.liftAfter a x)
      (ShortEdgeCutFibers.liftAfter a y) =
      if x = a then ((beta a t - (t y).value) / 2) * U x y else U x y := by
  rcases hside with hy | hx
  · have hxle : x ≤ a := by omega
    have hxa : x ≠ a := by omega
    have hyB : y ≠ a + 1 := by omega
    have hygt : ¬ a + 1 < y := by omega
    simp [parentTable, ShortEdgeCutFibers.liftAfter, collapseAfter,
      ShortEdgeCutFibers.collapseAfter, hxle, hy, hxa, hyB, hygt]
  · by_cases heq : x = a
    · subst x
      have hya : ¬ y ≤ a := by omega
      have hyB : y + 1 ≠ a + 1 := by omega
      have hbig : a + 1 < y + 1 := by omega
      have hc : ¬ y + 1 ≤ a := by omega
      have hyA : y ≠ a := by omega
      simp [parentTable, ShortEdgeCutFibers.liftAfter, collapseAfter,
        ShortEdgeCutFibers.collapseAfter, hya, hyB, hbig, hc, hyA]
    · have hxa : ¬ x ≤ a := by omega
      have hya : ¬ y ≤ a := by omega
      have hxA : x + 1 ≠ a := by omega
      have hxlt : ¬ x + 1 < a := by omega
      have hxle : ¬ x + 1 ≤ a := by omega
      have hyle : ¬ y + 1 ≤ a := by omega
      simp [parentTable, ShortEdgeCutFibers.liftAfter, collapseAfter,
        ShortEdgeCutFibers.collapseAfter, hxa, hya, hxA, hxlt, hxle, hyle, heq]

theorem parentTable_liftAt_on_side
    (a x y : ℕ) (ha : 0 < a) (hxy : x < y)
    (hside : y ≤ a ∨ a ≤ x) (t : ℕ → Sign) (U : IntervalArray) :
    parentTable a ha t U (if x < a then x else x + 1)
      (if y < a then y else y + 1) =
      if y = a then ((alpha a ha t - (t x).value) / 2) * U x y else U x y := by
  rcases hside with hy | hx
  · have hxlt : x < a := by omega
    have hxle : x ≤ a := by omega
    have hxA : x ≠ a := by omega
    by_cases heq : y = a
    · subst y
      simp [parentTable, hxlt, hxA]
    · have hylt : y < a := by omega
      have hyB : y ≠ a + 1 := by omega
      have hygt : ¬ a + 1 < y := by omega
      simp [parentTable, hxlt, hylt, hxA, hyB, heq, collapseAfter,
        ShortEdgeCutFibers.collapseAfter, hxle, hy, hygt]
  · have hxlt : ¬ x < a := by omega
    have hylt : ¬ y < a := by omega
    have hxA : x + 1 ≠ a := by omega
    have hxlt' : ¬ x + 1 < a := by omega
    have hxle : ¬ x + 1 ≤ a := by omega
    have hyle : ¬ y + 1 ≤ a := by omega
    have hyA : y ≠ a := by omega
    simp [parentTable, hxlt, hylt, hxA, hxlt', hxle, hyle, hyA,
      collapseAfter, ShortEdgeCutFibers.collapseAfter]

theorem branchProduct_rescale_edge
    (b₁ b₀ : IntervalArray) (q : ℚ) {i j x y : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j)
    (he : (x,y) ∈ cutEdges i j S) (hxy : b₁ x y = q * b₀ x y)
    (hother : ∀ e ∈ cutEdges i j S, e ≠ (x,y) → b₁ e.1 e.2 = b₀ e.1 e.2) :
    branchProduct b₁ (cutVertices i j S) = q * branchProduct b₀ (cutVertices i j S) := by
  rw [branchProduct_eq_prod_cutEdges b₁ hij hS,
    branchProduct_eq_prod_cutEdges b₀ hij hS]
  rw [← Finset.mul_prod_erase _ (fun e : ℕ × ℕ => b₁ e.1 e.2) he,
    ← Finset.mul_prod_erase _ (fun e : ℕ × ℕ => b₀ e.1 e.2) he]
  have hprod : (∏ e ∈ (cutEdges i j S).erase (x,y), b₁ e.1 e.2) =
      ∏ e ∈ (cutEdges i j S).erase (x,y), b₀ e.1 e.2 := by
    apply Finset.prod_congr rfl
    intro e he'
    exact hother e (Finset.mem_erase.mp he').2 (Finset.mem_erase.mp he').1
  rw [hprod, hxy]
  ring

theorem branchProduct_cutAtA
    (a i j L R : ℕ) (ha : 0 < a) (hij : i < j)
    (t : ℕ → Sign) (U : IntervalArray) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioo i j) (htriple : (L,a,R) ∈ cutTriples i j S) :
    branchProduct (parentTable a ha t U)
      ((cutVertices i j S).map (ShortEdgeCutFibers.liftAfter a)) =
      ((beta a t - (t R).value) / 2) * branchProduct U (cutVertices i j S) := by
  rw [branchProduct_map]
  have hAR := (cutTriples_mem_iff hij hS).mp htriple |>.2
  have hARfacts := (cutEdges_mem_iff hij hS).mp hAR
  apply branchProduct_rescale_edge _ U _ hij hS hAR
  · simpa using parentTable_liftAfter_on_side a a R ha hARfacts.2.2.1
      (Or.inr (le_refl a)) t U
  · rintro ⟨x,y⟩ he hne
    have hfacts := (cutEdges_mem_iff hij hS).mp he
    have hside : y ≤ a ∨ a ≤ x := (hfacts.2.2.2 a hARfacts.1).symm
    rw [parentTable_liftAfter_on_side a x y ha hfacts.2.2.1 hside t U]
    have hxa : x ≠ a := by
      intro hx
      subst x
      have hy : y = R := adjacent_same_first (cutVertices_pairwise hij hS)
        (by simpa [cutEdges] using he) (by simpa [cutEdges] using hAR)
      exact hne (by simp [hy])
    simp [hxa]

theorem branchProduct_cutAtB
    (a i j L R : ℕ) (ha : 0 < a) (hij : i < j)
    (t : ℕ → Sign) (U : IntervalArray) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioo i j) (htriple : (L,a,R) ∈ cutTriples i j S) :
    branchProduct (parentTable a ha t U)
      ((cutVertices i j S).map (fun x => if x < a then x else x + 1)) =
      ((alpha a ha t - (t L).value) / 2) * branchProduct U (cutVertices i j S) := by
  rw [branchProduct_map]
  have hLA := (cutTriples_mem_iff hij hS).mp htriple |>.1
  have hLAfacts := (cutEdges_mem_iff hij hS).mp hLA
  apply branchProduct_rescale_edge _ U _ hij hS hLA
  · simpa using parentTable_liftAt_on_side a L a ha hLAfacts.2.2.1
      (Or.inl (le_refl a)) t U
  · rintro ⟨x,y⟩ he hne
    have hfacts := (cutEdges_mem_iff hij hS).mp he
    have hside : y ≤ a ∨ a ≤ x := (hfacts.2.2.2 a hLAfacts.2.1).symm
    rw [parentTable_liftAt_on_side a x y ha hfacts.2.2.1 hside t U]
    have hya : y ≠ a := by
      intro hy
      subst y
      have hx : x = L := adjacent_same_last (cutVertices_pairwise hij hS)
        (by simpa [cutEdges] using he) (by simpa [cutEdges] using hLA)
      exact hne (by simp [hx])
    simp [hya]

end DirectGLSSW.ShortEdgeWeighted.SpanningBranchesImpl
