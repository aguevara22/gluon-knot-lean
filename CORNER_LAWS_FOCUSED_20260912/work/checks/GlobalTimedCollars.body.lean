namespace SM

open Set

noncomputable section

theorem uniformMeshLocalTime_mem_unit_iff (N : ℕ) (hN : 0 < N)
    (k : Fin N) (t : unitInterval) :
    uniformMeshLocalTime N k t ∈ Icc (0 : ℝ) 1 ↔ t ∈ uniformMeshCell N hN k := by
  constructor
  · intro ht
    have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    dsimp [uniformMeshLocalTime] at ht
    constructor
    · change (k.val : ℝ) / (N : ℝ) ≤ (t : ℝ)
      exact (div_le_iff₀ hNR).mpr (by nlinarith [ht.1])
    · change (t : ℝ) ≤ (uniformMeshPoint N hN k.succ : ℝ)
      simp only [uniformMeshPoint, Fin.val_succ, Nat.cast_add, Nat.cast_one]
      exact (le_div_iff₀ hNR).mpr (by nlinarith [ht.2])
  · exact uniformMeshLocalTime_mem_unit N hN k t

namespace CurveCubeSubdivision.CubeCoordinateApproximation

variable {n : ℕ} [NeZero n] {γ : unitInterval → LabelledTuple n} {δ : ℝ}
  {d : CurveCubeSubdivision γ δ} {W : d.InternalWaypoint × ScalarCoordinate n → ℝ}
  (A : d.CubeCoordinateApproximation W)

theorem generic_endpoint_collar :
    ∃ ε > 0, ∀ t : unitInterval,
      ((t : ℝ) < ε ∨ 1 - ε < (t : ℝ)) → Generic (A.path t) := by
  have hm : 0 < 2 * n := by have := NeZero.pos n; omega
  have hNR : (0 : ℝ) < d.count := Nat.cast_pos.mpr d.count_pos
  refine ⟨1 / (d.count : ℝ), one_div_pos.mpr hNR, ?_⟩
  intro t ht
  obtain ⟨k, hk⟩ := exists_uniformMeshCell _ (Nat.mul_pos d.count_pos hm) t
  have hc := fine_uniformMeshCell_subset_coarse d.count_pos hm k hk
  have hlo : (k.divNat.val : ℝ) / (d.count : ℝ) ≤ (t : ℝ) := hc.1
  have hup : (t : ℝ) ≤ ((k.divNat.val : ℝ) + 1) / (d.count : ℝ) := by
    have hu : (t : ℝ) ≤ (uniformMeshPoint d.count d.count_pos k.divNat.succ : ℝ) := hc.2
    simpa only [uniformMeshPoint, Fin.val_succ, Nat.cast_add, Nat.cast_one] using hu
  apply A.generic_collar_cells k _ t hk
  rcases ht with hfirst | hlast
  · have hqR : (k.divNat.val : ℝ) < 1 :=
      (div_lt_div_iff_of_pos_right hNR).mp (hlo.trans_lt hfirst)
    have hqN : k.divNat.val < 1 := by exact_mod_cast hqR
    exact Or.inl (by omega)
  · have hmul := mul_lt_mul_of_pos_left hlast hNR
    have hupper := (le_div_iff₀ hNR).mp hup
    have hcancel : (d.count : ℝ) * (1 / (d.count : ℝ)) = 1 :=
      mul_one_div_cancel (ne_of_gt hNR)
    have hqR : (d.count : ℝ) < (k.divNat.val : ℝ) + 2 := by nlinarith
    have hqN : d.count < k.divNat.val + 2 := by exact_mod_cast hqR
    have := k.divNat.isLt
    exact Or.inr (by omega)

theorem nongeneric_central_time (hn : 3 ≤ n)
    (hJ : ∀ j, JointLegConditions (d.centralLeg hn j) W)
    (k : Fin (d.count * (2 * n))) (t : unitInterval)
    (ht : t ∈ uniformMeshCell _ (Nat.mul_pos d.count_pos (by omega)) k)
    (hng : ¬ Generic (A.path t)) :
    ∃ hc : 0 < k.divNat.val ∧ k.divNat.val + 1 < d.count,
      uniformMeshLocalTime _ k t ∈ Ioo (0 : ℝ) 1 ∧
      uniformMeshLocalTime _ k t ∈
        centralControlRootSet (d.centralLeg hn (⟨k.divNat, hc⟩, k.modNat)) W := by
  have hnotend : ¬ (k.divNat.val = 0 ∨ k.divNat.val + 1 = d.count) :=
    fun he => hng (A.generic_collar_cells k he t ht)
  have hc : 0 < k.divNat.val ∧ k.divNat.val + 1 < d.count := by
    have := k.divNat.isLt
    omega
  let leg := d.centralLeg hn (⟨k.divNat, hc⟩, k.modNat)
  have hng' : ¬ Generic (tupleOfScalarCoordinates (leg.assignment W
      (uniformMeshLocalTime _ k t))) := by
    rw [← A.central_branch hn k hc t ht]
    exact hng
  have hr := central_nongeneric_subset_roots hn leg W hng'
  have hzero : uniformMeshLocalTime _ k t ≠ 0 := by
    intro hz
    rw [hz] at hr
    exact central_root_zero_excluded leg W (hJ _) hr
  have hone : uniformMeshLocalTime _ k t ≠ 1 := by
    intro ho
    rw [ho] at hr
    exact central_root_one_excluded leg W (hJ _) hr
  have hclosed := uniformMeshLocalTime_mem_unit _ (Nat.mul_pos d.count_pos (by omega)) k t ht
  exact ⟨hc, ⟨lt_of_le_of_ne hclosed.1 hzero.symm, lt_of_le_of_ne hclosed.2 hone⟩, hr⟩

end CurveCubeSubdivision.CubeCoordinateApproximation

end

end SM
