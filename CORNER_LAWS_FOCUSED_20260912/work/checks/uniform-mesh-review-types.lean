import Mathlib.Topology.UnitInterval
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-! Development prototype for a strict source-time subdivision. It remains
outside the theorem-library inventory until kernel and independent review. -/

namespace SM

open Set

noncomputable section

def uniformMeshPoint (N : ℕ) (hN : 0 < N) (j : Fin (N + 1)) : unitInterval :=
  ⟨(j.val : ℝ) / (N : ℝ), div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    (div_le_one (Nat.cast_pos.mpr hN)).mpr (by exact_mod_cast Nat.le_of_lt_succ j.isLt)⟩

theorem uniformMeshPoint_first (N : ℕ) (hN : 0 < N) :
    uniformMeshPoint N hN ⟨0, by omega⟩ = 0 := by
  apply Subtype.ext
  simp [uniformMeshPoint]

theorem uniformMeshPoint_last (N : ℕ) (hN : 0 < N) :
    uniformMeshPoint N hN ⟨N, by omega⟩ = 1 := by
  apply Subtype.ext
  simp [uniformMeshPoint, ne_of_gt (Nat.cast_pos.mpr hN : (0 : ℝ) < N)]

theorem uniformMeshPoint_strictMono (N : ℕ) (hN : 0 < N) :
    StrictMono (uniformMeshPoint N hN) := by
  intro a b hab
  change (a.val : ℝ) / (N : ℝ) < (b.val : ℝ) / (N : ℝ)
  apply (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hN)).mpr
  exact_mod_cast hab

theorem uniformMeshPoint_step (N : ℕ) (hN : 0 < N) (j : Fin N) :
    (uniformMeshPoint N hN j.succ : ℝ) -
      (uniformMeshPoint N hN j.castSucc : ℝ) = 1 / (N : ℝ) := by
  simp only [uniformMeshPoint, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

theorem exists_fine_uniformMesh (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 3 ≤ N ∧ 1 / (N : ℝ) < ε := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
  have hbound : 1 / ε < ((m + 3 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hmul : 1 < ((m + 3 : ℕ) : ℝ) * ε := (div_lt_iff₀ hε).mp hbound
  refine ⟨m + 3, by omega, ?_⟩
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < ((m + 3 : ℕ) : ℝ))).mpr
  nlinarith

theorem uniformMeshPoint_cell_subset_ball (N : ℕ) (hN : 0 < N)
    (j : Fin N) (ε : ℝ) (hε : 1 / (N : ℝ) < ε) :
    Icc (uniformMeshPoint N hN j.castSucc) (uniformMeshPoint N hN j.succ) ⊆
      Metric.ball (uniformMeshPoint N hN j.castSucc) ε := by
  intro t ht
  change dist (t : ℝ) (uniformMeshPoint N hN j.castSucc : ℝ) < ε
  have hnonneg : 0 ≤ (t : ℝ) - (uniformMeshPoint N hN j.castSucc : ℝ) :=
    sub_nonneg.mpr ht.1
  rw [Real.dist_eq, abs_of_nonneg hnonneg]
  have hstep := uniformMeshPoint_step N hN j
  have hupper : (t : ℝ) ≤ (uniformMeshPoint N hN j.succ : ℝ) := ht.2
  linarith

theorem uniformMeshPoint_cell_subset_right_ball (N : ℕ) (hN : 0 < N)
    (j : Fin N) (ε : ℝ) (hε : 1 / (N : ℝ) < ε) :
    Icc (uniformMeshPoint N hN j.castSucc) (uniformMeshPoint N hN j.succ) ⊆
      Metric.ball (uniformMeshPoint N hN j.succ) ε := by
  intro t ht
  change dist (t : ℝ) (uniformMeshPoint N hN j.succ : ℝ) < ε
  have hnonpos : (t : ℝ) - (uniformMeshPoint N hN j.succ : ℝ) ≤ 0 :=
    sub_nonpos.mpr ht.2
  rw [Real.dist_eq, abs_of_nonpos hnonpos]
  have hstep := uniformMeshPoint_step N hN j
  have hlower : (uniformMeshPoint N hN j.castSucc : ℝ) ≤ (t : ℝ) := ht.1
  linarith

theorem exists_uniformMesh_subordinate_with_endpoints {ι : Type*}
    (C : ι → Set unitInterval) (hopen : ∀ i, IsOpen (C i))
    (hcover : univ ⊆ ⋃ i, C i) (first last : ι)
    (hfirst : (0 : unitInterval) ∈ C first) (hlast : (1 : unitInterval) ∈ C last) :
    ∃ N : ℕ, ∃ hN : 0 < N, 3 ≤ N ∧ ∀ j : Fin N, ∃ i : ι,
      Icc (uniformMeshPoint N hN j.castSucc) (uniformMeshPoint N hN j.succ) ⊆ C i ∧
      (j.val = 0 → i = first) ∧ (j.val + 1 = N → i = last) := by
  obtain ⟨δ, hδ, hballs⟩ := lebesgue_number_lemma_of_metric isCompact_univ hopen hcover
  obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.isOpen_iff.mp (hopen first) 0 hfirst
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.isOpen_iff.mp (hopen last) 1 hlast
  obtain ⟨N, hN3, hfine⟩ := exists_fine_uniformMesh (min δ (min ε₀ ε₁))
    (lt_min hδ (lt_min hε₀ hε₁))
  have hN : 0 < N := by omega
  have hfδ : 1 / (N : ℝ) < δ := lt_of_lt_of_le hfine (min_le_left _ _)
  have hf₀ : 1 / (N : ℝ) < ε₀ :=
    lt_of_lt_of_le hfine ((min_le_right _ _).trans (min_le_left _ _))
  have hf₁ : 1 / (N : ℝ) < ε₁ :=
    lt_of_lt_of_le hfine ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨N, hN, hN3, ?_⟩
  intro j
  by_cases hj₀ : j.val = 0
  · refine ⟨first, ?_, fun _ => rfl, ?_⟩
    · have he : uniformMeshPoint N hN j.castSucc = 0 := by
        have hj : j.castSucc = (⟨0, by omega⟩ : Fin (N + 1)) := Fin.ext hj₀
        rw [hj, uniformMeshPoint_first]
      intro t ht
      apply hball₀
      have hm := uniformMeshPoint_cell_subset_ball N hN j ε₀ hf₀ ht
      rwa [he] at hm
    · intro hj₁
      exfalso
      omega
  · by_cases hj₁ : j.val + 1 = N
    · refine ⟨last, ?_, fun hz => (hj₀ hz).elim, fun _ => rfl⟩
      have he : uniformMeshPoint N hN j.succ = 1 := by
        have hj : j.succ = (⟨N, by omega⟩ : Fin (N + 1)) := Fin.ext hj₁
        rw [hj, uniformMeshPoint_last]
      intro t ht
      apply hball₁
      have hm := uniformMeshPoint_cell_subset_right_ball N hN j ε₁ hf₁ ht
      rwa [he] at hm
    · obtain ⟨i, hi⟩ := hballs (uniformMeshPoint N hN j.castSucc) trivial
      exact ⟨i, (uniformMeshPoint_cell_subset_ball N hN j δ hfδ).trans hi,
        fun hz => (hj₀ hz).elim, fun hz => (hj₁ hz).elim⟩

end

end SM


set_option pp.universes false
#print SM.uniformMeshPoint
#check SM.uniformMeshPoint
#print axioms SM.uniformMeshPoint
#check SM.uniformMeshPoint_first
#print axioms SM.uniformMeshPoint_first
#check SM.uniformMeshPoint_last
#print axioms SM.uniformMeshPoint_last
#check SM.uniformMeshPoint_strictMono
#print axioms SM.uniformMeshPoint_strictMono
#check SM.uniformMeshPoint_step
#print axioms SM.uniformMeshPoint_step
#check SM.exists_fine_uniformMesh
#print axioms SM.exists_fine_uniformMesh
#check SM.uniformMeshPoint_cell_subset_ball
#print axioms SM.uniformMeshPoint_cell_subset_ball
#check SM.uniformMeshPoint_cell_subset_right_ball
#print axioms SM.uniformMeshPoint_cell_subset_right_ball
#check SM.exists_uniformMesh_subordinate_with_endpoints
#print axioms SM.exists_uniformMesh_subordinate_with_endpoints

open Set

-- The source curve and open image cover supply the interval cover by preimage.
example {X : Type*} [TopologicalSpace X] {ι : Type*}
    (gamma : unitInterval → X) (hgamma : Continuous gamma)
    (C : ι → Set X) (hopen : ∀ i, IsOpen (C i))
    (hcover : range gamma ⊆ ⋃ i, C i) (first last : ι)
    (hfirst : gamma 0 ∈ C first) (hlast : gamma 1 ∈ C last) :
    ∃ N : ℕ, ∃ hN : 0 < N, 3 ≤ N ∧
      StrictMono (SM.uniformMeshPoint N hN) ∧
      SM.uniformMeshPoint N hN ⟨0, by omega⟩ = 0 ∧
      SM.uniformMeshPoint N hN ⟨N, by omega⟩ = 1 ∧
      ∀ j : Fin N, ∃ i : ι,
        gamma '' Icc (SM.uniformMeshPoint N hN j.castSucc)
          (SM.uniformMeshPoint N hN j.succ) ⊆ C i ∧
        (j.val = 0 → i = first) ∧ (j.val + 1 = N → i = last) := by
  have hc : univ ⊆ ⋃ i, gamma ⁻¹' C i := by
    intro t _
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨t, rfl⟩)
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨N, hN, hN3, hs⟩ := SM.exists_uniformMesh_subordinate_with_endpoints
    (fun i => gamma ⁻¹' C i) (fun i => (hopen i).preimage hgamma) hc
    first last hfirst hlast
  refine ⟨N, hN, hN3, SM.uniformMeshPoint_strictMono N hN,
    SM.uniformMeshPoint_first N hN, SM.uniformMeshPoint_last N hN, ?_⟩
  intro j
  obtain ⟨i, hi, hf, hl⟩ := hs j
  refine ⟨i, ?_, hf, hl⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hi ht

-- Even the smallest required subdivision has a genuine internal cell.
example : SM.uniformMeshPoint 3 (by decide) ⟨1, by decide⟩ <
    SM.uniformMeshPoint 3 (by decide) ⟨2, by decide⟩ := by
  exact SM.uniformMeshPoint_strictMono 3 (by decide) (by decide)
