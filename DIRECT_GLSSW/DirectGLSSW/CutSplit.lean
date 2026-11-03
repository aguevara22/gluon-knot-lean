import DirectGLSSW.CutLocalWeights
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

namespace DirectGLSSW
open scoped BigOperators

private def leftCuts (k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun x => x < k)

private def rightCuts (k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun x => k < x)

private theorem erase_eq_left_union_right {k : ℕ} (S : Finset ℕ) : S.erase k = leftCuts k S ∪ rightCuts k S := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_union, leftCuts, rightCuts,
    Finset.mem_filter]
  constructor
  · rintro ⟨hne, hx⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨hx, hlt⟩
    · exact Or.inr ⟨hx, hgt⟩
  · rintro (⟨hx, hlt⟩ | ⟨hx, hgt⟩)
    · exact ⟨ne_of_lt hlt, hx⟩
    · exact ⟨ne_of_gt hgt, hx⟩

private theorem leftCuts_subset {i k j : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Ioo i j) :
    leftCuts k S ⊆ Finset.Ioo i k := by
  intro x hx
  have hxS := Finset.mem_filter.mp hx |>.1
  have hxi := Finset.mem_Ioo.mp (hS hxS)
  exact Finset.mem_Ioo.mpr ⟨hxi.1, Finset.mem_filter.mp hx |>.2⟩

private theorem rightCuts_subset {i k j : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Ioo i j) :
    rightCuts k S ⊆ Finset.Ioo k j := by
  intro x hx
  have hxS := Finset.mem_filter.mp hx |>.1
  have hxi := Finset.mem_Ioo.mp (hS hxS)
  exact Finset.mem_Ioo.mpr ⟨Finset.mem_filter.mp hx |>.2, hxi.2⟩

private theorem leftCuts_eq_inter {i k j : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Ioo i j) :
    leftCuts k S = S ∩ Finset.Ioo i k := by
  ext x
  simp only [leftCuts, Finset.mem_filter, Finset.mem_inter, Finset.mem_Ioo]
  have hS' := hS
  constructor
  · rintro ⟨hxS, hxk⟩
    have hxi := Finset.mem_Ioo.mp (hS hxS)
    exact ⟨hxS, hxi.1, hxk⟩
  · rintro ⟨hxS, hxi, hxk⟩
    exact ⟨hxS, hxk⟩

private theorem rightCuts_eq_inter {i k j : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Ioo i j) :
    rightCuts k S = S ∩ Finset.Ioo k j := by
  ext x
  simp only [rightCuts, Finset.mem_filter, Finset.mem_inter, Finset.mem_Ioo]
  constructor
  · rintro ⟨hxS, hxk⟩
    have hxi := Finset.mem_Ioo.mp (hS hxS)
    exact ⟨hxS, hxk, hxi.2⟩
  · rintro ⟨hxS, hxk, hxj⟩
    exact ⟨hxS, hxk⟩

private theorem branchProduct_split_at (b : IntervalArray) {i k j : ℕ}
    (hik : i < k) (hkj : k < j) {S : Finset ℕ}
    (hS : S ⊆ Finset.Ioo i j) (hk : k ∈ S) :
    branchProduct b (cutVertices i j S) =
      branchProduct b (cutVertices i k (leftCuts k S)) *
      branchProduct b (cutVertices k j (rightCuts k S)) := by
  classical
  have hs₀ : ({k} : Finset ℕ) ⊆ S := by simpa using hk
  have hij : i < j := lt_trans hik hkj
  have hsingleton : ({k} : Finset ℕ) ⊆ Finset.Ioo i j := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    exact Finset.mem_Ioo.mpr ⟨hik, hkj⟩
  have hlocal := local_product_branch b hij hsingleton hs₀ hS
  have hedges : cutEdges i j {k} = {(i, k), (k, j)} := by
    ext e
    rcases e with ⟨a, c⟩
    simp [cutEdges, cutVertices, List.mem_toFinset, hik.ne, hkj.ne]
  have hleft : S ∩ Finset.Ioo i k = leftCuts k S :=
    (leftCuts_eq_inter hS).symm
  have hright : S ∩ Finset.Ioo k j = rightCuts k S :=
    (rightCuts_eq_inter hS).symm
  rw [hedges] at hlocal
  simp [Finset.prod_insert, hik.ne, hkj.ne] at hlocal
  rw [hleft, hright] at hlocal
  simpa [mul_comm] using hlocal.symm

/-- Splitting the actual finite cut-list sum at a distinguished internal cut.
The weights are arbitrary rationals, so zero weights and empty side subsets are included. -/
theorem weightedCutSum_split_at (w : ℕ → ℚ) (b : IntervalArray)
    {i k j : ℕ} (hik : i < k) (hkj : k < j) :
    (∑ S ∈ ((Finset.Ioo i j).powerset.filter fun S => k ∈ S),
      (∏ x ∈ S.erase k, w x) * branchProduct b (cutVertices i j S)) =
      (∑ L ∈ (Finset.Ioo i k).powerset,
        (∏ x ∈ L, w x) * branchProduct b (cutVertices i k L)) *
      (∑ R ∈ (Finset.Ioo k j).powerset,
        (∏ x ∈ R, w x) * branchProduct b (cutVertices k j R)) := by
  classical
  let P := (Finset.Ioo i j).powerset.filter (fun S => k ∈ S)
  let A := (Finset.Ioo i k).powerset
  let B := (Finset.Ioo k j).powerset
  let T := A ×ˢ B
  change (∑ S ∈ P, (∏ x ∈ S.erase k, w x) * branchProduct b (cutVertices i j S)) =
    (∑ L ∈ A, (∏ x ∈ L, w x) * branchProduct b (cutVertices i k L)) *
      (∑ R ∈ B, (∏ x ∈ R, w x) * branchProduct b (cutVertices k j R))
  have hleftP (S : Finset ℕ) (hS : S ∈ P) : leftCuts k S ∈ A := by
    apply Finset.mem_powerset.mpr
    exact leftCuts_subset (Finset.mem_powerset.mp (Finset.mem_filter.mp hS |>.1))
  have hrightP (S : Finset ℕ) (hS : S ∈ P) : rightCuts k S ∈ B := by
    apply Finset.mem_powerset.mpr
    exact rightCuts_subset (Finset.mem_powerset.mp (Finset.mem_filter.mp hS |>.1))
  have hpairP (p : Finset ℕ × Finset ℕ) (hp : p ∈ T) : p.1 ∈ A ∧ p.2 ∈ B := by
    simpa [T] using hp
  have hinvP (p : Finset ℕ × Finset ℕ) (hp : p ∈ T) : insert k (p.1 ∪ p.2) ∈ P := by
    have hA : p.1 ⊆ Finset.Ioo i k := Finset.mem_powerset.mp (hpairP p hp).1
    have hB : p.2 ⊆ Finset.Ioo k j := Finset.mem_powerset.mp (hpairP p hp).2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powerset.mpr
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_Ioo.mpr ⟨hik, hkj⟩
      · rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_Ioo.mpr (by
            have hxi := Finset.mem_Ioo.mp (hA hx)
            omega)
        · exact Finset.mem_Ioo.mpr (by
            have hxi := Finset.mem_Ioo.mp (hB hx)
            omega)
    · simp
  have hleftInv (S : Finset ℕ) (hS : S ∈ P) : insert k (leftCuts k S ∪ rightCuts k S) = S := by
    ext x
    have hsub : S ⊆ Finset.Ioo i j := Finset.mem_powerset.mp (Finset.mem_filter.mp hS |>.1)
    have hk : k ∈ S := Finset.mem_filter.mp hS |>.2
    by_cases hxk : x = k
    · subst x
      simp [hk]
    · simp only [Finset.mem_insert, Finset.mem_union, leftCuts, rightCuts, Finset.mem_filter]
      constructor
      · rintro (hx | (⟨hx, _⟩ | ⟨hx, _⟩))
        · subst x; exact hk
        · exact hx
        · exact hx
      · intro hx
        by_cases hxlt : x < k
        · exact Or.inr (Or.inl ⟨hx, hxlt⟩)
        · have hxgt : k < x := by
            have hi := Finset.mem_Ioo.mp (hsub hx)
            exact lt_of_le_of_ne (le_of_not_gt hxlt) (Ne.symm hxk)
          exact Or.inr (Or.inr ⟨hx, hxgt⟩)
  have hrightInv (p : Finset ℕ × Finset ℕ) (hp : p ∈ T) :
      (leftCuts k (insert k (p.1 ∪ p.2)), rightCuts k (insert k (p.1 ∪ p.2))) = p := by
    have hA : p.1 ⊆ Finset.Ioo i k := Finset.mem_powerset.mp (hpairP p hp).1
    have hB : p.2 ⊆ Finset.Ioo k j := Finset.mem_powerset.mp (hpairP p hp).2
    apply Prod.ext
    · ext x
      simp only [leftCuts, Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨hx | (hx | hx), hlt⟩
        · subst x; omega
        · exact hx
        · have hi := Finset.mem_Ioo.mp (hB hx)
          omega
      · intro hx
        exact ⟨Or.inr (Or.inl hx), (Finset.mem_Ioo.mp (hA hx)).2⟩
    · ext x
      simp only [rightCuts, Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨hx | (hx | hx), hgt⟩
        · subst x; omega
        · have hi := Finset.mem_Ioo.mp (hA hx)
          omega
        · exact hx
      · intro hx
        exact ⟨Or.inr (Or.inr hx), (Finset.mem_Ioo.mp (hB hx)).1⟩
  have hweights (S : Finset ℕ) (hS : S ∈ P) :
      (∏ x ∈ S.erase k, w x) * branchProduct b (cutVertices i j S) =
        ((∏ x ∈ leftCuts k S, w x) * branchProduct b (cutVertices i k (leftCuts k S))) *
        ((∏ x ∈ rightCuts k S, w x) * branchProduct b (cutVertices k j (rightCuts k S))) := by
    have hsub : S ⊆ Finset.Ioo i j := Finset.mem_powerset.mp (Finset.mem_filter.mp hS |>.1)
    have hk : k ∈ S := Finset.mem_filter.mp hS |>.2
    have hdisj : Disjoint (leftCuts k S) (rightCuts k S) := by
      apply Finset.disjoint_left.mpr
      intro x hxL hxR
      have hlt := Finset.mem_filter.mp hxL |>.2
      have hgt := Finset.mem_filter.mp hxR |>.2
      exact (not_lt_of_ge (le_of_lt hlt)) hgt
    rw [erase_eq_left_union_right (S := S), Finset.prod_union hdisj,
      branchProduct_split_at b hik hkj hsub hk]
    ring
  unfold P A B
  calc
    _ = ∑ p ∈ ((Finset.Ioo i k).powerset ×ˢ (Finset.Ioo k j).powerset),
        ((∏ x ∈ p.1, w x) * branchProduct b (cutVertices i k p.1)) *
          ((∏ x ∈ p.2, w x) * branchProduct b (cutVertices k j p.2)) := by
      refine Finset.sum_bij'
        (fun S _ => (leftCuts k S, rightCuts k S))
        (fun p _ => insert k (p.1 ∪ p.2)) ?_ ?_ ?_ ?_ ?_
      · intro S hS
        exact Finset.mem_product.mpr ⟨hleftP S hS, hrightP S hS⟩
      · intro p hp
        exact hinvP p hp
      · exact hleftInv
      · exact hrightInv
      · intro S hS
        exact hweights S hS
    _ = (∑ L ∈ (Finset.Ioo i k).powerset,
          (∏ x ∈ L, w x) * branchProduct b (cutVertices i k L)) *
        (∑ R ∈ (Finset.Ioo k j).powerset,
          (∏ x ∈ R, w x) * branchProduct b (cutVertices k j R)) := by
      let f : Finset ℕ → ℚ := fun L =>
        (∏ x ∈ L, w x) * branchProduct b (cutVertices i k L)
      let g : Finset ℕ → ℚ := fun R =>
        (∏ x ∈ R, w x) * branchProduct b (cutVertices k j R)
      change (∑ p ∈ (Finset.Ioo i k).powerset ×ˢ (Finset.Ioo k j).powerset,
        f p.1 * g p.2) = (∑ L ∈ (Finset.Ioo i k).powerset, f L) *
          (∑ R ∈ (Finset.Ioo k j).powerset, g R)
      calc
        (∑ p ∈ (Finset.Ioo i k).powerset ×ˢ (Finset.Ioo k j).powerset,
            f p.1 * g p.2) =
            ∑ L ∈ (Finset.Ioo i k).powerset, ∑ R ∈ (Finset.Ioo k j).powerset, f L * g R :=
          Finset.sum_product' (Finset.Ioo i k).powerset (Finset.Ioo k j).powerset (fun L R => f L * g R)
        _ = _ := (Finset.sum_mul_sum _ _ f g).symm









end DirectGLSSW
