import RecursiveTruncationPhysicalCarriers

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain

/-- Canonical incidence of any future point is equivalent to incidence on the
literal original supplied carrier, not merely on the current endpoints. -/
theorem original_carrier_incidence_iff {N m : ℕ}
    (Q : Fin N → PlanarPoint ℝ) (d : Fin m → PlanarPoint ℝ)
    (hd : CyclicGeneric d) (f : Fin m → Fin N) (hf : Function.Injective f)
    (hT : PairTransverse (polygonCarrierCoordinates Q))
    (hi : ∀ i, lineValue (polygonCarrierCoordinates Q (f i)) (d i)=0 ∧
      lineValue (polygonCarrierCoordinates Q (f i)) (d (cyclicSuccessor i))=0) :
    ∀ i x, lineValue (polygonCarrierCoordinates Q (f i)) x=0 ↔
      lineValue (polygonCarrierCoordinates d i) x=0 := by
  obtain ⟨s,hs,he⟩ := CarrierScaleTransport.exists_supplied_scales d hd
    (polygonCarrierCoordinates Q ∘ f) (pairTransverse_comap _ hT f hf) hi
  intro i x
  have hline := congrFun he i
  change polygonCarrierCoordinates Q (f i) = s i • polygonCarrierCoordinates d i at hline
  rw [hline,CarrierScaleTransport.lineValue_smul,mul_eq_zero]
  simp only [hs i,false_or]

end DirectGLSSW.CyclicCarrierClearing

