import DirectGLSSW.PolygonNonalternation
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace DirectGLSSW.SourceNonalternatingSeparation
open PermutationOrbits PolygonNonalternation
attribute [local instance] Classical.propDecidable

/-- Pairwise nonalternation of the actual crossing visits is equivalent to
maximal actual continuation count together with split eligibility at every
prefix, regardless of the order of the selected smoothings. -/
theorem nonalternating_iff_count_and_no_rejoin {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) :
    polygonNonalternating q hq.g2 S ↔
      componentCount (smoothingDartPermutation q hq.g2 S) = S.card + 1 ∧
      ∀ T : Finset (PolygonCrossing q), T ⊆ S →
        ∀ c : PolygonCrossing q, c ∈ S → c ∉ T →
          (smoothingDartPermutation q hq.g2 T).SameCycle
            (Sum.inr (c,false)) (Sum.inr (c,true)) := by
  classical
  constructor
  · intro hS
    refine ⟨(polygonNonalternating_iff_dart_count q hq.g2 hq.size_ge_three S).mp hS, ?_⟩
    intro T hT c hc hcT
    have hi : insert c T ⊆ S := Finset.insert_subset hc hT
    exact dart_sameCycle_before_insert q hq.g2 T c hcT
      (polygonNonalternating_mono q hq.g2 hS hi)
  · rintro ⟨hcount,_⟩
    exact (polygonNonalternating_iff_dart_count q hq.g2 hq.size_ge_three S).mpr hcount

/-- Every permitted next actual smoothing increases the full count by one. -/
theorem every_prefix_splits {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (hS : polygonNonalternating q hq.g2 S)
    (T : Finset (PolygonCrossing q)) (hT : T ⊆ S)
    (c : PolygonCrossing q) (hc : c ∈ S) (hcT : c ∉ T) :
    componentCount (smoothingDartPermutation q hq.g2 (insert c T)) =
      componentCount (smoothingDartPermutation q hq.g2 T) + 1 := by
  classical
  exact dart_componentCount_insert q hq.g2 hq.size_ge_three T c hcT
    (polygonNonalternating_mono q hq.g2 hS (Finset.insert_subset hc hT))

/-- Across any two prefixes, the actual continuation partition only refines. -/
theorem every_prefix_refines {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (hS : polygonNonalternating q hq.g2 S)
    (T U : Finset (PolygonCrossing q)) (hTU : T ⊆ U) (hUS : U ⊆ S)
    (x y : PolygonEvent q)
    (hxy : (smoothingDartPermutation q hq.g2 U).SameCycle x y) :
    (smoothingDartPermutation q hq.g2 T).SameCycle x y :=
  dart_refines_of_subset q hq.g2 T U hTU
    (polygonNonalternating_mono q hq.g2 hS hUS) hxy

/-- The carrier is the actual oriented event successor with exactly the
selected crossing visits exchanged; vertex anchors remain fixed. -/
theorem actual_continuation_formula {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    smoothingDartPermutation q hq.g2 S x =
      smoothingPairingMap q S (polygonEventSuccessor q hq.g2 x) := rfl

/-- Consecutive actual dart segments meet at their literal plane endpoints. -/
theorem actual_continuation_endpoints {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    polygonEventPoint q (smoothingDartPermutation q hq.g2 S x) =
      polygonEventPoint q (polygonEventSuccessor q hq.g2 x) :=
  smoothingDartPermutation_endpoint q hq.g2 S x

end DirectGLSSW.SourceNonalternatingSeparation





