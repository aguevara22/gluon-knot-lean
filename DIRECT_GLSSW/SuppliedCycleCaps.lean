import UniversalCycleSecants
import AllEdgeCapRealization

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain AuxiliaryCarrierPairs
open EdgeAffineNormalization ExtendedReturnArcGeometry InteriorEdgeEvents

theorem actual_secants_of_supplied_cycle {m N : ℕ}
    (q : Fin m → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (L : Fin N → CarrierLine) (hT : PairTransverse L) (hC : allCycleSecantExclusions L)
    (f : Fin m → Fin N) (hf : Function.Injective f)
    (hinc : ∀ i, lineValue (L (f i)) (q i) = 0 ∧
      lineValue (L (f i)) (q (cyclicSuccessor i)) = 0) :
    (∀ l : Fin 4 → Fin m, Function.Injective l →
      OriginalOuterProperness.outerNumerator (q ∘ l) ≠ 0) ∧
    (∀ l : Fin 6 → Fin m, Function.Injective l →
      OriginalSecantProperness.secantNumerator (q ∘ l) ≠ 0) := by
  have hd (i : Fin m) : lineDenominator
      (L (f ((cyclicSuccessorPerm m)⁻¹ i))) (L (f i)) ≠ 0 :=
    hT _ _ (fun h => cyclicSuccessorPerm_symm_ne_self hq.size_ge_three i (hf h))
  have he : reconstructPolygon (L ∘ f) = q := by
    funext i
    have hi : cyclicSuccessor ((cyclicSuccessorPerm m)⁻¹ i) = i := by
      simpa only [cyclicSuccessorPerm_apply] using (cyclicSuccessorPerm m).apply_symm_apply i
    symm
    apply lineIntersection_unique _ _ _ (hd i)
    · simpa only [hi] using (hinc ((cyclicSuccessorPerm m)⁻¹ i)).2
    · exact (hinc i).1
  have hs := (cycleSecantExclusions_iff f L hd).mp (allCycleSecantExclusions_apply L hC q hq f hf)
  simpa only [he] using hs

/-- Applies to any actual original, truncated, or nested component once its
literal injective carrier list and incidence have been established. -/
theorem cap_realization_of_supplied_cycle {m N : ℕ}
    (q : Fin m → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (L : Fin N → CarrierLine) (hT : PairTransverse L) (hC : allCycleSecantExclusions L)
    (f : Fin m → Fin N) (hf : Function.Injective f)
    (hinc : ∀ i, lineValue (L (f i)) (q i) = 0 ∧
      lineValue (L (f i)) (q (cyclicSuccessor i)) = 0)
    (e : Fin m) :
    let P := normalizedPolygon q e ∘ cyclicVertexEquiv e
    ∃ ε : ℝ, 0 < ε ∧ ε < geometricRadius hq.size_ge_three P ∧
      Set.InjOn (CapCriticalEventGeometry.criticalRoot (extendedArc hq.size_ge_three P ε))
        ↑(CapCriticalTimes.criticalPairs (extendedArc hq.size_ge_three P ε) m) ∧
      ∀ t : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
        ∀ a b : Fin m, a.val < b.val →
          CyclicGeneric (GlobalCapEntry.lineCapCore
            (CapCrossingEvent.horizontalMove (extendedArc hq.size_ge_three P ε) (t+s)) a b) := by
  have hs := actual_secants_of_supplied_cycle q hq L hT hC f hf hinc
  exact AllEdgeCapRealization.every_edge_realization q hq hs.2 hs.1 e

end DirectGLSSW.CyclicCarrierClearing


