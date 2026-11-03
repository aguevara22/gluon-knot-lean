import PolynomialPuncture

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain CarrierScaleTransport

theorem line_eq_smul_normalized_support (K : CarrierLine)
    (a U D : PlanarPoint ℝ) (scale ε : ℝ) (hε : ε ≠ 0)
    (hv : scale • D-U ≠ 0) (hK : K.1 ≠ 0)
    (hA : lineValue K (a+ε • U) = 0)
    (hB : lineValue K (a+(ε*scale) • D) = 0) :
    ∃ t : ℝ, t ≠ 0 ∧ K = t •
      (scale • D-U,-planarDet (scale • D-U) (a+ε • U)) := by
  have he : (a+(ε*scale) • D)-(a+ε • U) = ε • (scale • D-U) := by
    ext <;> simp [smul_eq_mul] <;> ring
  have hn : (a+(ε*scale) • D)-(a+ε • U) ≠ 0 := by
    rw [he]
    exact smul_ne_zero hε hv
  obtain ⟨s,hs,hline⟩ := exists_nonzero_scale_of_incident K
    (a+ε • U) (a+(ε*scale) • D) hn hK hA hB
  have hc : ((a+(ε*scale) • D)-(a+ε • U),
      -planarDet ((a+(ε*scale) • D)-(a+ε • U)) (a+ε • U)) =
      ε • (scale • D-U,-planarDet (scale • D-U) (a+ε • U)) := by
    rw [he]
    apply Prod.ext
    · rfl
    · simp [planarDet,smul_eq_mul]
      ring
  refine ⟨s*ε,mul_ne_zero hs hε,?_⟩
  rw [hline,hc,smul_smul]

theorem augmented_inventory_of_last_smul {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (K : CarrierLine) (s : ℝ) (hs : s ≠ 0)
    (hU : UniversalLocus (canonicalAugmentedCarrier q (s • K)))
    (hT : PairTransverse (canonicalAugmentedCarrier q (s • K)))
    (hC : allCycleSecantExclusions (canonicalAugmentedCarrier q (s • K))) :
    UniversalLocus (canonicalAugmentedCarrier q K) ∧
      PairTransverse (canonicalAugmentedCarrier q K) ∧
      allCycleSecantExclusions (canonicalAugmentedCarrier q K) := by
  let w : Fin (n+1) → ℝ := fun i => if i.val < n then 1 else s
  have hw : ∀ i, w i ≠ 0 := by intro i; dsimp [w]; split <;> simp_all
  have he : canonicalAugmentedCarrier q (s • K) =
      fun i => w i • canonicalAugmentedCarrier q K i := by
    funext i
    by_cases hi : i.val < n <;> simp [canonicalAugmentedCarrier,w,hi]
  rw [he] at hU hT hC
  exact ⟨universalLocus_of_smul _ w hU,pairTransverse_of_smul _ w hT,
    allCycleSecantExclusions_of_smul _ w hw hT hC⟩

end DirectGLSSW.CyclicCarrierClearing


