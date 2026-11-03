import CanonicalInventoryCharacterizations
import ActualAuxiliaryCarrier

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain AuxiliaryCarrierPairs DaughterFirstReturn
open GeometricSmoothingWeights LocalDaughterTransport LocalCrossingTransport ActualCarrierTransport

theorem properPairs_cyclic {m N : ℕ} (hm : 3 ≤ m) (f : Fin m → Fin N)
    (hf : Function.Injective f) (i j k : Fin m) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ProperPairs (f ((cyclicSuccessorPerm m)⁻¹ i),f i)
      (f ((cyclicSuccessorPerm m)⁻¹ j),f j)
      (f ((cyclicSuccessorPerm m)⁻¹ k),f k) := by
  have hn (u : Fin m) : f ((cyclicSuccessorPerm m)⁻¹ u) ≠ f u :=
    fun h => cyclicSuccessorPerm_symm_ne_self hm u (hf h)
  have hp := cyclicCarrierPair_injective hm f hf
  refine ⟨hn i,hn j,hn k,?_,?_,?_,?_⟩
  · exact fun h => hij (hp h)
  · exact fun h => hjk (hp h)
  · exact fun h => hik (hp h)
  · exact cyclicCarrierPair_no_three_common hm f hf i j k hij hjk hik

/-- Every actual separating daughter is generic because its literal cyclic
carrier pairs are proper and the original canonical family is universal.
No daughter genericity or pullback density is a premise. -/
theorem auxiliaryGenericity_of_canonical_universal {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hU : UniversalLocus (polygonCarrierCoordinates q)) : auxiliaryGenericity q hq := by
  apply auxiliaryGenericity_of_retained q hq
  intro S hS root hroot
  have hm := DaughterTurns.daughterVertexCount_ge_three q hq.g2 S hq.size_ge_three hq.g1 root hroot
  have hf := daughterCarrier_injective q hq.g2 S hq.size_ge_three hS root
  refine ⟨hm,?_,DaughterClosedContainment.daughter_no_triple q S hq hS root hroot⟩
  intro i j k hij hjk hik
  have hP := properPairs_cyclic hm (daughterCarrier q hq.g2 S root) hf k j i
    hjk.symm hij.symm hik.symm
  have hnum := hU _ _ _ hP
  intro hz
  apply hnum
  exact (actual_daughter_triple_numerator_zero_iff q hq S root hroot k j i).mpr hz

end DirectGLSSW.CyclicCarrierClearing


