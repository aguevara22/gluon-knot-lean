import ConfigurationSmoothingNeighborhood
import ExposedCutInverse
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PhysicalSourceInitialization
open Filter Topology GeometricSmoothingWeights ExposedOpenPrimitive

theorem eventually_auxiliary_primitive (hRI : GLSSWRootIndependence) {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (hAux : auxiliaryGenericity q hq) :
    ∀ᶠ r in 𝓝 q, ∃ hr : CyclicGeneric r, ∃ hAr : auxiliaryGenericity r hr,
      separatingSmoothingSum r hr hAr=separatingSmoothingSum q hq hAux := by
  obtain ⟨η,hη,hall⟩ := ConfigurationSmoothingNeighborhood.exists_smoothingSums_neighborhood hRI q hq hAux
  have hclose : ∀ᶠ r in 𝓝 q, CrossingIncidenceNeighborhood.CoordClose η r q := by
    apply Filter.eventually_all.mpr
    intro i
    have h1 : ContinuousAt (fun r : Fin n → PlanarPoint ℝ => |(r i).1-(q i).1|) q := ((continuous_apply i).fst.continuousAt.sub continuousAt_const).abs
    have h2 : ContinuousAt (fun r : Fin n → PlanarPoint ℝ => |(r i).2-(q i).2|) q := ((continuous_apply i).snd.continuousAt.sub continuousAt_const).abs
    exact (h1.eventually (isOpen_Iio.mem_nhds (by simpa using hη))).and
      (h2.eventually (isOpen_Iio.mem_nhds (by simpa using hη)))
  filter_upwards [hclose] with r hr
  obtain ⟨hr,hAr,hν,_⟩ := hall r hr
  exact ⟨hr,hAr,hν⟩

theorem eventually_uniform_left {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hl : ∀ i, 0 < planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i))) :
    ∀ᶠ r in 𝓝 q, ∀ i, 0 < planarDet (cyclicTangent r i) (cyclicTangent r (cyclicSuccessor i)) := by
  apply Filter.eventually_all.mpr
  intro i
  have hc : ContinuousAt (fun r : Fin n → PlanarPoint ℝ => planarDet (cyclicTangent r i)
    (cyclicTangent r (cyclicSuccessor i))) q := by unfold cyclicTangent planarDet; fun_prop
  exact hc.eventually (isOpen_Ioi.mem_nhds (hl i))

theorem eventually_leftExposed {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (e : Fin n) (he : LeftExposed q e) : ∀ᶠ r in 𝓝 q, LeftExposed r e := by
  apply Filter.eventually_all.mpr
  intro i
  by_cases hi : i=e
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hi))
  by_cases hs : i=cyclicSuccessor e
  · exact Filter.Eventually.of_forall (fun _ _ h => False.elim (h hs))
  have hc : ContinuousAt (fun r : Fin n → PlanarPoint ℝ => planarDet (cyclicTangent r e) (r i-r e)) q := by
    unfold cyclicTangent planarDet; fun_prop
  exact (hc.eventually (isOpen_Ioi.mem_nhds (he i hi hs))).mono (fun _ h _ _ => h)
end DirectGLSSW.PhysicalSourceInitialization
