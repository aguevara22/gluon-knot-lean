import DirectGLSSW.FirstCut
import DirectGLSSW.MixedEdgeCutInverse
import DirectGLSSW.TriangularInverse
import DirectGLSSW.NearData
import DirectGLSSW.EndpointSingleGate
import DirectGLSSW.CurrentFidelity

/-!
# The open marked current as a finite resolvent

This module formalizes the open-current expression in the source's auxiliary
choice `D = -1`.  The matrix is the actual strict-upper interval-current
matrix; its resolvent is the literal finite geometric series.  The marked
amplitude bridge is an auxiliary conditional lemma for the later exposed-edge
geometry argument.
-/

set_option autoImplicit false

namespace DirectGLSSW.OpenMarkedCurrent

open scoped BigOperators

/-- The source's open marked current, with the ordinary current computed at
the auxiliary constant choice `D = -1`. -/
def entry (H : TripleArray) (i j : ℕ) : ℚ :=
  weightedCutSum (fun _ : ℕ => -1)
    (ordinaryCurrent (fun _ _ _ => -1) H) i j

/-- The finite matrix of actual ordinary interval currents, set to zero on and
below the diagonal. -/
def intervalMatrix (H : TripleArray) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun u v => if u.val < v.val then
    ordinaryCurrent (fun _ _ _ => -1) H u.val v.val else 0

/-- The literal finite resolvent `B (I + B)⁻¹` for the interval matrix. -/
def literalResolvent (H : TripleArray) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  intervalMatrix H n * finiteInverse (intervalMatrix H n) n

/-- Unfolding the weighted cut sum gives the actual finite signed-cut
expansion; the empty cut is retained. -/
theorem entry_eq_signedCutExpansion (H : TripleArray) (i j : ℕ) :
    entry H i j =
      ∑ S ∈ (Finset.Ioo i j).powerset,
        (∏ k ∈ S, (-1 : ℚ)) *
          branchProduct (ordinaryCurrent (fun _ _ _ => -1) H)
            (cutVertices i j S) := by
  rfl

/-- Adjacent intervals retain their empty-cut value `1`. -/
theorem entry_adjacent_eq_one (H : TripleArray) (i : ℕ) :
    entry H i (i + 1) = 1 := by
  have hIoo : Finset.Ioo i (i + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro k hk
    simp only [Finset.mem_Ioo] at hk
    omega
  simp [entry, weightedCutSum, hIoo, branchProduct, cutVertices,
    ordinaryCurrent_adjacent]

private theorem intervalMatrix_strictUpper (H : TripleArray) (n : ℕ) :
    StrictUpper (intervalMatrix H n) := by
  intro u v hvu
  simp [intervalMatrix, Nat.not_lt.mpr hvu]

private theorem weightedCutSum_congr_of_branch_eq_local (w : ℕ → ℚ)
    {b₁ b₂ : IntervalArray} {i j : ℕ} (hij : i < j)
    (hbranches : ∀ a b, i ≤ a → a < b → b ≤ j → b₁ a b = b₂ a b) :
    weightedCutSum w b₁ i j = weightedCutSum w b₂ i j := by
  classical
  unfold weightedCutSum
  apply Finset.sum_congr rfl
  intro S hS
  have hSsub : S ⊆ Finset.Ioo i j := Finset.mem_powerset.mp hS
  have hbranch : branchProduct b₁ (cutVertices i j S) =
      branchProduct b₂ (cutVertices i j S) := by
    by_cases hSne : S.Nonempty
    · unfold branchProduct
      congr 1
      apply List.map_congr_left
      rintro ⟨a, b⟩ hab
      have hb := cutVertices_branch_bounds hij hSsub hSne hab
      exact hbranches a b hb.1 hb.2.1 hb.2.2.1
    · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
      subst S
      simp [branchProduct, cutVertices, hbranches i j le_rfl hij le_rfl]
  rw [hbranch]

/-- The actual open marked current is the corresponding entry of the literal
finite resolvent `B (I+B)⁻¹`. -/
theorem entry_eq_literalResolvent {n : ℕ} (H : TripleArray)
    (u v : Fin n) (huv : u < v) :
    entry H u.val v.val = literalResolvent H n u v := by
  let B : Matrix (Fin n) (Fin n) ℚ := intervalMatrix H n
  let F : Matrix (Fin n) (Fin n) ℚ := finiteInverse B n
  have hB : StrictUpper B := by
    exact intervalMatrix_strictUpper H n
  have hF := strictUpper_finiteInverse B hB
  have hId := congrFun (congrFun hF.2 u) v
  have huvVal : u.val ≠ v.val := by omega
  have huNe : u ≠ v := fun heq => huvVal (congrArg Fin.val heq)
  have hEntry : F u v + (B * F) u v = 0 := by
    simpa [F, Matrix.add_mul, Matrix.one_mul, Matrix.one_apply, huNe] using hId
  have hResolvent : (B * F) u v = - F u v := by
    calc
      (B * F) u v = (B * F) u v + F u v - F u v := by ring
      _ = 0 - F u v := by rw [add_comm, hEntry]
      _ = -F u v := by ring
  have hCutSum :
      weightedCutSum (fun _ : ℕ => -1) (finiteMatrixIntervalArray B)
          u.val v.val =
        weightedCutSum (fun _ : ℕ => -1)
          (ordinaryCurrent (fun _ _ _ => -1) H) u.val v.val := by
    apply weightedCutSum_congr_of_branch_eq_local (fun _ : ℕ => -1) huv
    intro a b hua hab hbv
    have ha : a < n := by omega
    have hb : b < n := by omega
    simp [finiteMatrixIntervalArray, B, intervalMatrix, ha, hb, hab]
  have hFinite := finiteInverse_entry_eq_negative_weightedCutSum
    B hB u v huv
  have hFinite' : F u v = -entry H u.val v.val := by
    calc
      F u v = -weightedCutSum (fun _ : ℕ => -1)
          (finiteMatrixIntervalArray B) u.val v.val := hFinite
      _ = -weightedCutSum (fun _ : ℕ => -1)
          (ordinaryCurrent (fun _ _ _ => -1) H) u.val v.val :=
        congrArg Neg.neg hCutSum
      _ = -entry H u.val v.val := by rfl
  calc
    entry H u.val v.val = -F u v := by rw [hFinite']; ring
    _ = (B * F) u v := hResolvent.symm
    _ = literalResolvent H n u v := by rfl

/-- With all top far signs equal to `-1`, the auxiliary marked amplitude is
the open current.  This is an internal bridge for the exposed-edge argument;
it is not a final theorem with a geometric premise. -/
theorem entry_eq_markedAmplitude_of_topFarSigns
    (D H : TripleArray) {i j : ℕ} (hij : i < j)
    (hfar : ∀ k ∈ Finset.Ioo i j, H i k j = -1) :
    entry H i j = markedAmplitude D H i j := by
  have hmarked :
      markedAmplitude (fun _ _ _ => -1) H i j = entry H i j := by
    unfold markedAmplitude phi entry weightedCutSum
    apply Finset.sum_congr rfl
    intro S hS
    unfold cutContribution
    rw [gateProduct_middleNear_eq_prod
      (fun _ : ℕ => -1) (fun a b c => -H a b c) hij
      (Finset.mem_powerset.mp hS)]
    have hprod :
        (∏ k ∈ S, ((-1 : ℚ) - (-H i k j)) / 2) =
          ∏ k ∈ S, (-1 : ℚ) := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [hfar k (Finset.mem_powerset.mp hS hk)]
      norm_num
    rw [hprod]
  calc
    entry H i j = markedAmplitude (fun _ _ _ => -1) H i j := hmarked.symm
    _ = markedAmplitude D H i j :=
    (markedAmplitude_near_independent
        (fun _ _ _ => -1) D H hij)

end DirectGLSSW.OpenMarkedCurrent








