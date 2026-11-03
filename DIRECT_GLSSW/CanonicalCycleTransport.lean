import UniversalCycleSecants
import CarrierScaleTransport

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain CarrierScaleTransport

theorem allCycleSecantExclusions_comap {N M : ℕ} (L : Fin M → CarrierLine)
    (hL : allCycleSecantExclusions L) (g : Fin N → Fin M)
    (hg : Function.Injective g) : allCycleSecantExclusions (L ∘ g) := by
  intro m hm f hf hq
  have hmM : m ≤ M := by simpa using Fintype.card_le_of_injective (g ∘ f) (hg.comp hf)
  exact hL m hmM (g ∘ f) (hg.comp hf) hq

theorem allCycleSecantExclusions_of_smul {N : ℕ} (L : Fin N → CarrierLine)
    (s : Fin N → ℝ) (hs : ∀ i, s i ≠ 0)
    (hT : PairTransverse (fun i => s i • L i))
    (hC : allCycleSecantExclusions (fun i => s i • L i)) :
    allCycleSecantExclusions L := by
  have hTL : PairTransverse L := pairTransverse_of_smul L s hT
  intro m hm f hf hex
  obtain ⟨q,hq⟩ := hex
  have hn (i : Fin m) : f ((cyclicSuccessorPerm m)⁻¹ i) ≠ f i := by
    exact fun h => AuxiliaryCarrierPairs.cyclicSuccessorPerm_symm_ne_self hq.size_ge_three i (hf h)
  have hd : ∀ i, lineDenominator (L (f ((cyclicSuccessorPerm m)⁻¹ i))) (L (f i)) ≠ 0 :=
    fun i => hTL _ _ (hn i)
  have hds : ∀ i, lineDenominator (s (f ((cyclicSuccessorPerm m)⁻¹ i)) • L (f ((cyclicSuccessorPerm m)⁻¹ i)))
      (s (f i) • L (f i)) ≠ 0 := fun i => hT _ _ (hn i)
  have he : reconstructPolygon ((fun i => s i • L i) ∘ f) = reconstructPolygon (L ∘ f) := by
    funext i
    exact lineIntersection_smul _ _ _ _ (hs _) (hs _) (hd i)
  have hc := (cycleSecantExclusions_iff f (fun i => s i • L i) hds).mp
    (hC m hm f hf ⟨q,hq⟩)
  rw [he] at hc
  exact (cycleSecantExclusions_iff f L hd).mpr hc

theorem canonical_all_cycles_of_supplied {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (L : Fin n → CarrierLine) (hT : PairTransverse L)
    (hC : allCycleSecantExclusions L)
    (hinc : ∀ i, lineValue (L i) (q i) = 0 ∧ lineValue (L i) (q (cyclicSuccessor i)) = 0) :
    allCycleSecantExclusions (polygonCarrierCoordinates q) := by
  obtain ⟨s,hs,he⟩ := exists_supplied_scales q hq L hT hinc
  rw [he] at hT hC
  exact allCycleSecantExclusions_of_smul _ s hs hT hC

end DirectGLSSW.CyclicCarrierClearing



