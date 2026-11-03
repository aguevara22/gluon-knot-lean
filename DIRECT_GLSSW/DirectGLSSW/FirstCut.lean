import DirectGLSSW.IntervalCurrent
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

namespace DirectGLSSW
open scoped BigOperators

/-- Weighted sum over every internal cut subset. -/
def weightedCutSum (w : ℕ → ℚ) (b : IntervalArray) (i j : ℕ) : ℚ :=
  ∑ S ∈ (Finset.Ioo i j).powerset,
    (∏ l ∈ S, w l) * branchProduct b (cutVertices i j S)

/-- The part of the weighted cut sum with at least one internal cut. -/
def weightedCutSumNonempty (w : ℕ → ℚ) (b : IntervalArray)
    (i j : ℕ) : ℚ :=
  ∑ S ∈ ((Finset.Ioo i j).powerset).erase ∅,
    (∏ l ∈ S, w l) * branchProduct b (cutVertices i j S)

private theorem branchProduct_firstCut (b : IntervalArray) {i k j : ℕ}
    (hik : i < k) (hkj : k < j) {T : Finset ℕ}
    (hT : T ⊆ Finset.Ioo k j) :
    branchProduct b (cutVertices i j (insert k T)) =
      b i k * branchProduct b (cutVertices k j T) := by
  classical
  have hsort : (insert k T).sort (· ≤ ·) = k :: T.sort (· ≤ ·) := by
    apply Finset.sort_insert
    · intro x hx
      exact Nat.le_of_lt (Finset.mem_Ioo.mp (hT hx)).1
    · intro hk
      have h := Finset.mem_Ioo.mp (hT hk)
      omega
  simp [branchProduct, cutVertices, hsort, List.zip_cons_cons]

abbrev NonemptyIntervalCuts (i j : ℕ) :=
  ↥(((Finset.Ioo i j).powerset).erase ∅)

abbrev FirstCutTails (i j : ℕ) :=
  Σ k : ↥(Finset.Ioo i j), ↥((Finset.Ioo k.1 j).powerset)

private def firstCutToPair {i j : ℕ}
    (S : NonemptyIntervalCuts i j) : FirstCutTails i j := by
  classical
  have hne : S.1.Nonempty := by
    have hnot : S.1 ≠ ∅ := (Finset.mem_erase.mp S.2).1
    exact Finset.nonempty_iff_ne_empty.mpr hnot
  let k := S.1.min' hne
  have hkS : k ∈ S.1 := Finset.min'_mem S.1 hne
  have hS : S.1 ⊆ Finset.Ioo i j := Finset.mem_powerset.mp (Finset.mem_erase.mp S.2).2
  have hkI : k ∈ Finset.Ioo i j := hS hkS
  refine ⟨⟨k, hkI⟩, ⟨S.1.erase k, Finset.mem_powerset.mpr ?_⟩⟩
  intro x hx
  have hx' := Finset.mem_erase.mp hx
  have hxI := Finset.mem_Ioo.mp (hS hx'.2)
  have hkle : k ≤ x := Finset.min'_le S.1 x hx'.2
  have hlt : k < x := by omega
  exact Finset.mem_Ioo.mpr ⟨hlt, hxI.2⟩

private def firstCutPairToSet {i j : ℕ}
    (p : FirstCutTails i j) : NonemptyIntervalCuts i j := by
  classical
  rcases p with ⟨k, T⟩
  let S := insert k.1 T.1
  have hT : T.1 ⊆ Finset.Ioo k.1 j := Finset.mem_powerset.mp T.2
  refine ⟨S, Finset.mem_erase.mpr ⟨by simp [S], Finset.mem_powerset.mpr ?_⟩⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact k.2
  · have hxI := Finset.mem_Ioo.mp (hT hx)
    exact Finset.mem_Ioo.mpr ⟨lt_trans (Finset.mem_Ioo.mp k.2).1 hxI.1, hxI.2⟩

private def firstCutEquiv {i j : ℕ} :
    NonemptyIntervalCuts i j ≃ FirstCutTails i j where
  toFun := firstCutToPair
  invFun := firstCutPairToSet
  left_inv := by
    intro S
    apply Subtype.ext
    dsimp only [firstCutPairToSet, firstCutToPair]
    rw [Finset.insert_erase]
    exact Finset.min'_mem S.1 (by
      apply Finset.nonempty_iff_ne_empty.mpr
      exact (Finset.mem_erase.mp S.2).1)
  right_inv := by
    intro p
    rcases p with ⟨k, T⟩
    let U := insert k.1 T.1
    have hT : T.1 ⊆ Finset.Ioo k.1 j := Finset.mem_powerset.mp T.2
    have hne : U.Nonempty := ⟨k.1, Finset.mem_insert_self _ _⟩
    have hmin : U.min' hne = k.1 := by
      apply le_antisymm
      · exact Finset.min'_le U k.1 (Finset.mem_insert_self _ _)
      · apply Finset.le_min' U hne k.1
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact le_rfl
        · exact Nat.le_of_lt (Finset.mem_Ioo.mp (hT hx)).1
    have hnot : k.1 ∉ T.1 := by
      intro hkT
      have hh := Finset.mem_Ioo.mp (hT hkT)
      omega
    apply Sigma.ext (Subtype.ext hmin)
    apply (Subtype.heq_iff_coe_eq ?_).mpr
    · dsimp only [firstCutToPair, firstCutPairToSet]
      change U.erase (U.min' hne) = T.1
      rw [hmin]
      simpa [U, hnot]
    · dsimp only [firstCutToPair, firstCutPairToSet]
      change ∀ A : Finset ℕ,
        A ∈ (Finset.Ioo (U.min' hne) j).powerset ↔
          A ∈ (Finset.Ioo k.1 j).powerset
      intro A
      rw [hmin]

private theorem firstCutTerm (w : ℕ → ℚ) (b : IntervalArray)
    {i k j : ℕ} (hik : i < k) (hkj : k < j) {T : Finset ℕ}
    (hT : T ⊆ Finset.Ioo k j) :
    (∏ l ∈ insert k T, w l) * branchProduct b (cutVertices i j (insert k T)) =
      b i k * w k * ((∏ l ∈ T, w l) * branchProduct b (cutVertices k j T)) := by
  classical
  have hnot : k ∉ T := by
    intro hkT
    have hh := Finset.mem_Ioo.mp (hT hkT)
    omega
  rw [Finset.prod_insert hnot, branchProduct_firstCut b hik hkj hT]
  ring

/-- The nonempty finite cut sum groups by its least internal cut. -/
theorem weightedCutSumNonempty_eq_firstCut (w : ℕ → ℚ) (b : IntervalArray)
    {i j : ℕ} (hij : i < j) :
    weightedCutSumNonempty w b i j =
      ∑ k ∈ Finset.Ioo i j, b i k * w k * weightedCutSum w b k j := by
  classical
  letI : Fintype (NonemptyIntervalCuts i j) := inferInstance
  letI : Fintype (FirstCutTails i j) := inferInstance
  let e := firstCutEquiv (i := i) (j := j)
  let f : NonemptyIntervalCuts i j → ℚ := fun S =>
    (∏ l ∈ S.1, w l) * branchProduct b (cutVertices i j S.1)
  calc
    weightedCutSumNonempty w b i j = ∑ S : NonemptyIntervalCuts i j, f S := by
      change (∑ S ∈ ((Finset.Ioo i j).powerset).erase ∅,
          (∏ l ∈ S, w l) * branchProduct b (cutVertices i j S)) =
        ∑ S : NonemptyIntervalCuts i j,
          (∏ l ∈ S.1, w l) * branchProduct b (cutVertices i j S.1)
      exact (Finset.sum_coe_sort _ _).symm
    _ = ∑ p : FirstCutTails i j, f (e.symm p) := by
      simpa [e] using (e.sum_comp (fun p => f (e.symm p)))
    _ = ∑ k : ↥(Finset.Ioo i j), ∑ T : ↥((Finset.Ioo k.1 j).powerset),
          b i k.1 * w k.1 *
            ((∏ l ∈ T.1, w l) * branchProduct b (cutVertices k.1 j T.1)) := by
      rw [Fintype.sum_sigma]
      apply Fintype.sum_congr
      intro k
      apply Fintype.sum_congr
      intro T
      dsimp [e, firstCutEquiv, firstCutPairToSet, f]
      exact firstCutTerm w b (Finset.mem_Ioo.mp k.2).1
        (Finset.mem_Ioo.mp k.2).2 (Finset.mem_powerset.mp T.2)
    _ = ∑ k ∈ Finset.Ioo i j, b i k * w k * weightedCutSum w b k j := by
      have hinner (k : ↥(Finset.Ioo i j)) :
          (∑ T : ↥((Finset.Ioo k.1 j).powerset),
            (∏ l ∈ T.1, w l) * branchProduct b (cutVertices k.1 j T.1)) =
            weightedCutSum w b k.1 j := by
        calc
          _ = ∑ T ∈ (Finset.Ioo k.1 j).powerset,
                (∏ l ∈ T, w l) * branchProduct b (cutVertices k.1 j T) :=
            Finset.sum_coe_sort _ _
          _ = weightedCutSum w b k.1 j := rfl
      calc
        _ = ∑ k : ↥(Finset.Ioo i j),
              b i k.1 * w k.1 *
                (∑ T : ↥((Finset.Ioo k.1 j).powerset),
                  (∏ l ∈ T.1, w l) * branchProduct b (cutVertices k.1 j T.1)) := by
          apply Fintype.sum_congr
          intro k
          calc
            _ = ∑ T ∈ (Finset.Ioo k.1 j).powerset,
                  b i k.1 * w k.1 *
                    ((∏ l ∈ T, w l) * branchProduct b (cutVertices k.1 j T)) :=
              Finset.sum_coe_sort _ _
            _ = b i k.1 * w k.1 *
                  (∑ T ∈ (Finset.Ioo k.1 j).powerset,
                    (∏ l ∈ T, w l) * branchProduct b (cutVertices k.1 j T)) := by
              rw [Finset.mul_sum]
            _ = b i k.1 * w k.1 *
                  (∑ T : ↥((Finset.Ioo k.1 j).powerset),
                    (∏ l ∈ T.1, w l) * branchProduct b (cutVertices k.1 j T.1)) := by
              rw [← Finset.sum_coe_sort]
        _ = ∑ k : ↥(Finset.Ioo i j),
              b i k.1 * w k.1 * weightedCutSum w b k.1 j := by
          apply Fintype.sum_congr
          intro k
          rw [hinner k]
        _ = ∑ k ∈ Finset.Ioo i j, b i k * w k * weightedCutSum w b k j :=
          Finset.sum_coe_sort (Finset.Ioo i j)
            (fun k => b i k * w k * weightedCutSum w b k j)

/-- The full sum is its empty-cut term plus the least-cut decomposition. -/
theorem weightedCutSum_eq_firstCut (w : ℕ → ℚ) (b : IntervalArray)
    {i j : ℕ} (hij : i < j) :
    weightedCutSum w b i j =
      b i j + ∑ k ∈ Finset.Ioo i j, b i k * w k * weightedCutSum w b k j := by
  classical
  conv_lhs => unfold weightedCutSum
  have hempty : (∅ : Finset ℕ) ∈ (Finset.Ioo i j).powerset := by simp
  rw [← Finset.add_sum_erase _ _ hempty]
  change (∏ l ∈ (∅ : Finset ℕ), w l) * branchProduct b (cutVertices i j ∅) +
      weightedCutSumNonempty w b i j = _
  rw [weightedCutSumNonempty_eq_firstCut w b hij]
  have he : branchProduct b (cutVertices i j ∅) = b i j := by
    simp [branchProduct, cutVertices]
  simp only [Finset.prod_empty, one_mul, he]









end DirectGLSSW
