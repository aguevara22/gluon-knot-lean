import UniversalCycleSecants

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain CarrierFamilyDensity Set

/-- Literal coordinate restriction, not an arbitrary geometric pullback.
The new line is held fixed while choosing the old coordinates in an open slice. -/
theorem dense_old_coordinates {n : ℕ} (A : Set (Fin n → CarrierLine)) (hA : Dense A) :
    Dense {L : Fin (n+1) → CarrierLine | (fun i => L i.castSucc) ∈ A} := by
  classical
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨L, hL⟩ := hUne
  let put : (Fin n → CarrierLine) → (Fin (n+1) → CarrierLine) :=
    fun M i => if h : i.val < n then M ⟨i.val,h⟩ else L i
  have hc : Continuous put := by
    apply continuous_pi
    intro i
    dsimp [put]
    split_ifs <;> fun_prop
  have he : put (fun i => L i.castSucc) = L := by
    funext i
    dsimp [put]
    split_ifs with h
    · congr 1
    · rfl
  have hpre : IsOpen (put ⁻¹' U) := hU.preimage hc
  have hprene : (put ⁻¹' U).Nonempty := by
    refine ⟨fun i => L i.castSucc, ?_⟩
    change put (fun i => L i.castSucc) ∈ U
    rw [he]
    exact hL
  obtain ⟨M, hMU, hMA⟩ := hA.inter_open_nonempty _ hpre hprene
  refine ⟨put M, hMU, ?_⟩
  have hm : (fun i : Fin n => put M i.castSucc) = M := by
    funext i
    simp only [put, Fin.coe_castSucc, dif_pos i.isLt]
  change (fun i : Fin n => put M i.castSucc) ∈ A
  rw [hm]
  exact hMA

theorem open_old_coordinates {n : ℕ} (A : Set (Fin n → CarrierLine)) (hA : IsOpen A) :
    IsOpen {L : Fin (n+1) → CarrierLine | (fun i => L i.castSucc) ∈ A} :=
  hA.preimage (by fun_prop)

/-- All cyclic secants, daughter G1 numerators, and universal augmented-family
conditions are simultaneously proper while old vertices AND the auxiliary line vary. -/
theorem augmented_joint_dense_open {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hAux : GeometricSmoothingWeights.auxiliaryGenericity q hq) :
    Dense {L : Fin (n+1) → CarrierLine |
      daughterSecantExclusions q hq (fun i => L i.castSucc) ∧
      allNonalternatingSupportDaughterNumeratorsNonzero q hq.g2 (fun i => L i.castSucc) ∧
      UniversalLocus L ∧ PairTransverse L ∧ allCycleSecantExclusions L} ∧
    IsOpen {L : Fin (n+1) → CarrierLine |
      daughterSecantExclusions q hq (fun i => L i.castSucc) ∧
      allNonalternatingSupportDaughterNumeratorsNonzero q hq.g2 (fun i => L i.castSucc) ∧
      UniversalLocus L ∧ PairTransverse L ∧ allCycleSecantExclusions L} := by
  have hS := daughterSecantExclusions_dense_open q hq hAux
  have hD := all_nonalternating_support_daughter_numerator_locus_dense_open q hq.g2
    hq.size_ge_three hq.g1
  have hU := universal_all_cycles_dense_open (n+1)
  have hsD := dense_old_coordinates _ hS.1
  have hsO := open_old_coordinates _ hS.2
  have hdD := dense_old_coordinates _ hD.1
  have hdO := open_old_coordinates _ hD.2
  exact ⟨hsD.inter_of_isOpen_left (hdD.inter_of_isOpen_left hU.1 hdO) hsO,
    hsO.inter (hdO.inter hU.2)⟩

end DirectGLSSW.CyclicCarrierClearing



