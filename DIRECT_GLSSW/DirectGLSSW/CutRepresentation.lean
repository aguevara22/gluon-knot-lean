import DirectGLSSW.CurrentFidelity

/-!
# Exact finite-subset and increasing-cut-list correspondence

Source: `ep:Phi`. The two encodings are equivalent on i < j, and their
weighted Phi sums agree exactly. The original marked-tree expansion and
near-data factorization require additional proofs.
-/

namespace DirectGLSSW
open scoped BigOperators

abbrev IntervalCutSet (i j : ℕ) := ↥((Finset.Ioo i j).powerset)

def IncreasingCuts (i j : ℕ) :=
  {l : List ℕ // (i :: l ++ [j]).Pairwise (· < ·)}

theorem increasingCuts_bounds {i j : ℕ} (l : IncreasingCuts i j)
    {a : ℕ} (ha : a ∈ l.val) : i < a ∧ a < j := by
  have h := List.pairwise_cons.mp l.property
  constructor
  · exact h.1 a (List.mem_append_left _ ha)
  · exact (List.pairwise_append.mp h.2).2.2 a ha j (by simp)

theorem increasingCuts_toFinset_subset {i j : ℕ} (l : IncreasingCuts i j) :
    l.val.toFinset ⊆ Finset.Ioo i j := by
  intro a ha
  exact Finset.mem_Ioo.mpr (increasingCuts_bounds l (List.mem_toFinset.mp ha))

def cutSetToIncreasingCuts {i j : ℕ} (hij : i < j)
    (S : IntervalCutSet i j) : IncreasingCuts i j :=
  ⟨S.val.sort (· ≤ ·), cutVertices_pairwise hij (Finset.mem_powerset.mp S.property)⟩

def increasingCutsToSet {i j : ℕ} (l : IncreasingCuts i j) : IntervalCutSet i j :=
  ⟨l.val.toFinset, Finset.mem_powerset.mpr (increasingCuts_toFinset_subset l)⟩

theorem increasingCutsToSet_cutSetToIncreasingCuts {i j : ℕ} (hij : i < j)
    (S : IntervalCutSet i j) : increasingCutsToSet (cutSetToIncreasingCuts hij S) = S := by
  apply Subtype.ext
  exact Finset.sort_toFinset (· ≤ ·) S.val

theorem cutSetToIncreasingCuts_increasingCutsToSet {i j : ℕ} (hij : i < j)
    (l : IncreasingCuts i j) : cutSetToIncreasingCuts hij (increasingCutsToSet l) = l := by
  apply Subtype.ext
  have hs : l.val.Pairwise (· < ·) :=
    (List.pairwise_append.mp (List.pairwise_cons.mp l.property).2).1
  have hn : l.val.Nodup := hs.imp (fun h => Nat.ne_of_lt h)
  exact (List.toFinset_sort (· ≤ ·) hn).mpr (hs.imp (fun h => Nat.le_of_lt h))

/-- Sorting the internal cut set enumerates exactly the endpoint-fixed increasing words.
The inverse equations are separate opaque theorems, preserving proof-hidden review. -/
def intervalCutEquiv {i j : ℕ} (hij : i < j) :
    IntervalCutSet i j ≃ IncreasingCuts i j where
  toFun := cutSetToIncreasingCuts hij
  invFun := increasingCutsToSet
  left_inv := increasingCutsToSet_cutSetToIncreasingCuts hij
  right_inv := cutSetToIncreasingCuts_increasingCutsToSet hij

noncomputable def phiOnIncreasingCuts (D H : TripleArray) (X : IntervalArray)
    (i j : ℕ) (hij : i < j) : ℚ := by
  letI : Fintype (IncreasingCuts i j) := Fintype.ofEquiv (IntervalCutSet i j) (intervalCutEquiv hij)
  exact ∑ l : IncreasingCuts i j,
    gateProduct D H i j (i :: l.val ++ [j]) * branchProduct X (i :: l.val ++ [j])

theorem phi_eq_increasingCuts (D H : TripleArray) (X : IntervalArray)
    {i j : ℕ} (hij : i < j) :
    phi D H X i j = phiOnIncreasingCuts D H X i j hij := by
  letI : Fintype (IncreasingCuts i j) :=
    Fintype.ofEquiv (IntervalCutSet i j) (intervalCutEquiv hij)
  let f : IncreasingCuts i j → ℚ := fun l =>
    gateProduct D H i j (i :: l.val ++ [j]) * branchProduct X (i :: l.val ++ [j])
  have h := (intervalCutEquiv hij).sum_comp f
  have hg : (∑ S : IntervalCutSet i j, f (intervalCutEquiv hij S)) = phi D H X i j := by
    change (∑ S : ↥((Finset.Ioo i j).powerset), cutContribution D H X i j S.val) =
      ∑ S ∈ (Finset.Ioo i j).powerset, cutContribution D H X i j S
    exact Finset.sum_coe_sort _ _
  exact hg.symm.trans h

/-- The constructed current solves the equation written over actual increasing cut words. -/
theorem ordinaryCurrent_increasingCuts_phi (D H : TripleArray)
    {i j : ℕ} (hij : i < j) :
    phiOnIncreasingCuts D H (ordinaryCurrent D H) i j hij = source i j := by
  rw [← phi_eq_increasingCuts D H (ordinaryCurrent D H) hij]
  exact ordinaryCurrent_phi D H hij

/-- Uniqueness is unchanged when the source uses increasing cut words directly. -/
theorem ordinaryCurrent_unique_increasingCuts (D H : TripleArray) (X : IntervalArray)
    (hX : ∀ i j (hij : i < j), phiOnIncreasingCuts D H X i j hij = source i j)
    {i j : ℕ} (hij : i < j) : X i j = ordinaryCurrent D H i j := by
  apply ordinaryCurrent_unique D H X _ hij
  intro a b hab
  rw [phi_eq_increasingCuts D H X hab]
  exact hX a b hab

end DirectGLSSW
