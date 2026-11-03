import OriginalRecursiveWindows

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain

/-- Literal incidence composes through a generic intermediate polygon. Thus a
restarted detached child retains original carrier provenance at every depth. -/
theorem original_subcycle_incidence_trans {N m k : ℕ}
    (Q : Fin N → PlanarPoint ℝ) (d : Fin m → PlanarPoint ℝ)
    (hd : CyclicGeneric d) (e : Fin k → PlanarPoint ℝ)
    (f : Fin m → Fin N) (hf : Function.Injective f)
    (g : Fin k → Fin m) (hg : Function.Injective g)
    (hT : PairTransverse (polygonCarrierCoordinates Q))
    (hi : ∀ i, lineValue (polygonCarrierCoordinates Q (f i)) (d i) = 0 ∧
      lineValue (polygonCarrierCoordinates Q (f i)) (d (cyclicSuccessor i)) = 0)
    (hj : ∀ j, lineValue (polygonCarrierCoordinates d (g j)) (e j) = 0 ∧
      lineValue (polygonCarrierCoordinates d (g j)) (e (cyclicSuccessor j)) = 0) :
    Function.Injective (f ∘ g) ∧
      ∀ j, lineValue (polygonCarrierCoordinates Q ((f ∘ g) j)) (e j) = 0 ∧
        lineValue (polygonCarrierCoordinates Q ((f ∘ g) j)) (e (cyclicSuccessor j)) = 0 := by
  obtain ⟨s,_,hs⟩ := CarrierScaleTransport.exists_supplied_scales d hd
    (polygonCarrierCoordinates Q ∘ f) (pairTransverse_comap _ hT f hf) hi
  refine ⟨hf.comp hg,?_⟩
  intro j
  have he := congrFun hs (g j)
  change polygonCarrierCoordinates Q (f (g j)) = s (g j) • polygonCarrierCoordinates d (g j) at he
  change lineValue (polygonCarrierCoordinates Q (f (g j))) (e j) = 0 ∧
    lineValue (polygonCarrierCoordinates Q (f (g j))) (e (cyclicSuccessor j)) = 0
  rw [he,CarrierScaleTransport.lineValue_smul,CarrierScaleTransport.lineValue_smul,
    (hj j).1,(hj j).2,mul_zero]
  exact ⟨rfl,rfl⟩

end DirectGLSSW.CyclicCarrierClearing

