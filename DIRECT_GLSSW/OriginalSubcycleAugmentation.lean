import ChildOriginalCarriers

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain

/-- A new supporting line for a detached original-carrier child is selected
using the SAME original-parent augmented inventory. No child coefficient or
second retained artificial carrier is required. -/
theorem canonical_augmented_of_original_subcycle {m N : ℕ}
    (Q : Fin N → PlanarPoint ℝ) (d : Fin m → PlanarPoint ℝ) (hd : CyclicGeneric d)
    (f : Fin m → Fin N) (hf : Function.Injective f)
    (hi : ∀ i, lineValue (polygonCarrierCoordinates Q (f i)) (d i) = 0 ∧
      lineValue (polygonCarrierCoordinates Q (f i)) (d (cyclicSuccessor i)) = 0)
    (K : CarrierLine) (hU : UniversalLocus (canonicalAugmentedCarrier Q K))
    (hT : PairTransverse (canonicalAugmentedCarrier Q K))
    (hC : allCycleSecantExclusions (canonicalAugmentedCarrier Q K)) :
    UniversalLocus (canonicalAugmentedCarrier d K) ∧
      PairTransverse (canonicalAugmentedCarrier d K) ∧
      allCycleSecantExclusions (canonicalAugmentedCarrier d K) := by
  let F : Fin (m+1) → Fin (N+1) := fun i =>
    if h : i.val < m then (f ⟨i.val,h⟩).castSucc else Fin.last N
  have hF : Function.Injective F := by
    intro i j he
    by_cases hi : i.val < m <;> by_cases hj : j.val < m
    · simp only [F,dif_pos hi,dif_pos hj] at he
      have hh := hf ((Fin.castSucc_injective N) he)
      exact Fin.ext (congrArg (fun t : Fin m => t.val) hh)
    · simp only [F,dif_pos hi,dif_neg hj] at he
      have hh := congrArg Fin.val he
      have hl := (f ⟨i.val,hi⟩).isLt
      simp only [Fin.coe_castSucc,Fin.val_last] at hh
      omega
    · simp only [F,dif_neg hi,dif_pos hj] at he
      have hh := congrArg Fin.val he
      have hl := (f ⟨j.val,hj⟩).isLt
      simp only [Fin.coe_castSucc,Fin.val_last] at hh
      omega
    · apply Fin.ext
      have := i.isLt
      have := j.isLt
      omega
  let L := canonicalAugmentedCarrier Q K ∘ F
  have hlast : L (Fin.last m) = K := by simp [L,F,canonicalAugmentedCarrier]
  have hinc : ∀ i : Fin m, lineValue (L i.castSucc) (d i) = 0 ∧
      lineValue (L i.castSucc) (d (cyclicSuccessor i)) = 0 := by
    intro i
    simpa only [L,Function.comp_def,F,Fin.coe_castSucc,dif_pos i.isLt,
      canonicalAugmentedCarrier,dif_pos (f i).isLt] using hi i
  exact canonical_augmented_of_supplied d hd K L hlast
    (universalLocus_comap _ hU F hF) (pairTransverse_comap _ hT F hF)
    (allCycleSecantExclusions_comap _ hC F hF) hinc

end DirectGLSSW.CyclicCarrierClearing

