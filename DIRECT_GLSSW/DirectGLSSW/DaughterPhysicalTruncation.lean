import DirectGLSSW.TruncationPointListAdapter
import DirectGLSSW.TruncationFixedScale
import DirectGLSSW.TruncationRescaling

set_option autoImplicit false

namespace DirectGLSSW.DaughterPhysicalTruncation

open TruncationDirection TruncationFixedScale TruncationPointListAdapter

theorem exists_physical_truncation_amplitude (hRI : GLSSWRootIndependence)
    {m : ℕ} (d : Fin (m + 1) → PlanarPoint ℝ) (hd : CyclicGeneric d)
    (p : Fin (m + 1)) (hp : cyclicSuccessor p = 0)
    (A P N : PlanarPoint ℝ) (α β scale : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hscale : 0 < scale)
    (hA : d 0 = A) (hP : d p = A + α • (P - A))
    (hN : d (cyclicSuccessor 0) = A + β • (N - A))
    (hturn : 0 < planarDet (A - P) (N - A))
    (havoid : ∀ j : Fin (m + 1), j ≠ 0 →
      planarDet (scale • (N - A) - (P - A)) (d j - A) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ {k : ℕ} (r : Fin k → PlanarPoint ℝ),
        List.ofFn r = (A + ε • (P - A)) ::
          (A + (ε * scale) • (N - A)) :: (List.ofFn d).tail →
        ∃ hr : CyclicGeneric r, polygonAmplitude r hr = -polygonAmplitude d hd := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have hsd : 0 < scale * α / β := div_pos (mul_pos hscale hα) hβ
  have hdturn : 0 < planarDet (d 0 - d p) (d (cyclicSuccessor 0) - d 0) := by
    rw [hA, hP, hN]
    exact TruncationRescaling.daughter_turn_positive A P N α β hα hβ hturn
  have hdavoid (j : Fin (m + 1)) (hj : j ≠ 0) :
      planarDet ((scale * α / β) • (d (cyclicSuccessor 0) - d 0) -
        (d p - d 0)) (d j - d 0) ≠ 0 := by
    rw [hA, hP, hN]
    exact TruncationRescaling.daughter_direction_det_ne_zero
      A P N (d j) α β scale hα0 hβ0 (havoid j hj)
  obtain ⟨δ, hδ, hg⟩ := exists_fixedScale_leftCorner_truncation_amplitude
    hRI d hd 0 p hp hdturn (scale * α / β) hsd hdavoid
  refine ⟨α * δ, mul_pos hα hδ, ?_⟩
  intro ε hε hεδ k r hrlist
  have hη : 0 < ε / α := div_pos hε hα
  have hηδ : ε / α < δ := (div_lt_iff₀ hα).mpr (by simpa [mul_comm] using hεδ)
  obtain ⟨_, _, ht, hamp⟩ := hg (ε / α) hη hηδ
  let t := truncateCyclicCorner d 0 p (scale * α / β) (ε / α)
  have htlist : List.ofFn t = (A + ε • (P - A)) ::
      (A + (ε * scale) • (N - A)) :: (List.ofFn d).tail := by
    rw [pointList_truncate_zero]
    rw [hA, hP, hN,
      TruncationRescaling.previous_point_rescaling A P α ε hα0,
      TruncationRescaling.next_point_rescaling A N α β scale ε hα0 hβ0]
  have heq : List.ofFn t = List.ofFn r := htlist.trans hrlist.symm
  let hr : CyclicGeneric r := cyclicGeneric_of_pointList_eq t r ht heq
  refine ⟨hr, ?_⟩
  rw [← polygonAmplitude_eq_of_pointList_eq t r ht hr heq]
  exact hamp

theorem exists_physical_truncation_amplitude_at_zero (hRI : GLSSWRootIndependence)
    {m : ℕ} (d : Fin m → PlanarPoint ℝ) (hd : CyclicGeneric d)
    (z p : Fin m) (hz : z.val = 0) (hp : cyclicSuccessor p = z)
    (A P N : PlanarPoint ℝ) (α β scale : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hscale : 0 < scale)
    (hA : d z = A) (hP : d p = A + α • (P - A))
    (hN : d (cyclicSuccessor z) = A + β • (N - A))
    (hturn : 0 < planarDet (A - P) (N - A))
    (havoid : ∀ j : Fin m, j ≠ z →
      planarDet (scale • (N - A) - (P - A)) (d j - A) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ {k : ℕ} (r : Fin k → PlanarPoint ℝ),
        List.ofFn r = (A + ε • (P - A)) ::
          (A + (ε * scale) • (N - A)) :: (List.ofFn d).tail →
        ∃ hr : CyclicGeneric r, polygonAmplitude r hr = -polygonAmplitude d hd := by
  cases m with
  | zero => exact Fin.elim0 z
  | succ m =>
      have hz0 : z = 0 := Fin.ext hz
      cases hz0
      exact exists_physical_truncation_amplitude hRI d hd p hp
        A P N α β scale hα hβ hscale hA hP hN hturn havoid

end DirectGLSSW.DaughterPhysicalTruncation
