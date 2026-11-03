import DirectGLSSW.ShortEdgeWeighted
import DirectGLSSW.ShortEdgeSpanningBranches

namespace DirectGLSSW.ShortEdgeWeighted.SpliceProductsImpl
open DirectGLSSW.ShortEdgeWeighted.SpanningBranchesImpl

private theorem branchProduct_congr {b₁ b₂ : IntervalArray} {v : List ℕ}
    (h : ∀ x y, (x, y) ∈ v.zip v.tail → b₁ x y = b₂ x y) :
    branchProduct b₁ v = branchProduct b₂ v := by
  unfold branchProduct
  congr 1
  apply List.map_congr_left
  rintro ⟨x, y⟩ hxy
  exact h x y hxy

private theorem pairwise_adjacent_less {v : List ℕ}
    (hv : v.Pairwise (· < ·)) {x y : ℕ} (hxy : (x, y) ∈ v.zip v.tail) : x < y := by
  exact ((adjacent_mem_iff hv).mp hxy).2.2.1

theorem branchProduct_splice (b : IntervalArray) (p q : List ℕ) (x : ℕ) :
    branchProduct b (p ++ x :: q) =
      branchProduct b (p ++ [x]) * branchProduct b (x :: q) := by
  induction p with
  | nil => simp [branchProduct]
  | cons z zs ih =>
    cases zs with
    | nil => simp [branchProduct]
    | cons z₂ rest =>
      simp only [List.cons_append]
      change b z z₂ * branchProduct b (z₂ :: (rest ++ x :: q)) =
        (b z z₂ * branchProduct b (z₂ :: (rest ++ [x]))) *
          branchProduct b (x :: q)
      have ih' : branchProduct b (z₂ :: (rest ++ x :: q)) =
          branchProduct b (z₂ :: (rest ++ [x])) * branchProduct b (x :: q) := by
        simpa only [List.cons_append] using ih
      rw [ih']
      ring

theorem gateProduct_splice (D H : TripleArray) (i j : ℕ)
    (p q : List ℕ) (x y : ℕ) :
    gateProduct D H i j (p ++ x :: y :: q) =
      gateProduct D H i j (p ++ [x, y]) *
        gateProduct D H i j (x :: y :: q) := by
  induction p with
  | nil => simp [gateProduct]
  | cons z zs ih =>
    cases zs with
    | nil => simp [gateProduct]
    | cons z₂ rest =>
      cases rest with
      | nil => simp [gateProduct]; ring
      | cons z₃ rest₂ =>
        have ih' : gateProduct D H i j (z₂ :: z₃ :: (rest₂ ++ x :: y :: q)) =
            gateProduct D H i j (z₂ :: z₃ :: (rest₂ ++ [x, y])) *
              gateProduct D H i j (x :: y :: q) := by
          simpa only [List.cons_append] using ih
        change ((D z z₂ z₃ - H i z₂ j) / 2) *
            gateProduct D H i j (z₂ :: z₃ :: (rest₂ ++ x :: y :: q)) =
          (((D z z₂ z₃ - H i z₂ j) / 2) *
            gateProduct D H i j (z₂ :: z₃ :: (rest₂ ++ [x, y]))) *
              gateProduct D H i j (x :: y :: q)
        rw [ih']
        ring

theorem branchProduct_liftAfter_on_side
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) (U : IntervalArray)
    (v : List ℕ) (hv : v.Pairwise (· < ·))
    (hside : ∀ x ∈ v, x ≤ a) :
    branchProduct (parentTable a ha t U)
      (v.map (ShortEdgeCutFibers.liftAfter a)) = branchProduct U v := by
  rw [branchProduct_map]
  apply branchProduct_congr
  intro x y hxy
  have hxy' : x < y := pairwise_adjacent_less hv hxy
  have hyv : y ∈ v := by
    exact List.mem_of_mem_tail (List.of_mem_zip hxy).2
  have hy : y ≤ a := hside y hyv
  have hx : x ≤ a := hside x (List.of_mem_zip hxy).1
  have hxa : x ≠ a := by omega
  rw [parentTable_liftAfter_on_side a x y ha hxy' (Or.inl hy) t U]
  simp [hxa]

theorem branchProduct_liftAt_on_side
    (a : ℕ) (ha : 0 < a) (t : ℕ → Sign) (U : IntervalArray)
    (v : List ℕ) (hv : v.Pairwise (· < ·))
    (hside : ∀ x ∈ v, a ≤ x) :
    branchProduct (parentTable a ha t U)
      (v.map (fun x => if x < a then x else x + 1)) = branchProduct U v := by
  rw [branchProduct_map]
  apply branchProduct_congr
  intro x y hxy
  have hxy' : x < y := pairwise_adjacent_less hv hxy
  have hx : a ≤ x := hside x (List.of_mem_zip hxy).1
  rw [parentTable_liftAt_on_side a x y ha hxy' (Or.inr hx) t U]
  have hyv : y ∈ v := by
    exact List.mem_of_mem_tail (List.of_mem_zip hxy).2
  have hy : a ≤ y := hside y hyv
  have hya : y ≠ a := by omega
  simp [hya]

end DirectGLSSW.ShortEdgeWeighted.SpliceProductsImpl
