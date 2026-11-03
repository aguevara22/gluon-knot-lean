import ExtendedReturnEndpointMatrix
import ExtendedReturnEndpointTurns
import DirectGLSSW.ConcreteCapMatrix

set_option autoImplicit false

namespace DirectGLSSW.ExtendedReturnCapInverse
open ExtendedReturnArcGeometry OrderedCapEvents CapCriticalEventGeometry CapCriticalTimes
open GlobalCapAlgebra

/-- Only critical-root injectivity remains auxiliary in the geometric matrix application. -/
theorem inverse_zero_of_equal_event_signs (hRI : GLSSWRootIndependence)
    {n : ℕ} (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (hU : (P (zeroIndex hn)).2 = 0) (hV : (P (lastIndex hn)).2 = 0)
    (ε : ℝ) (hε : 0 < ε) (hbound : ε < geometricRadius hn P)
    (hroots : Set.InjOn (criticalRoot (extendedArc hn P ε))
      ↑(criticalPairs (extendedArc hn P ε) n))
    (c d : EventIndex (extendedArc hn P ε) n) (hne : c ≠ d)
    (hs : eventSign (extendedArc hn P ε) n c = eventSign (extendedArc hn P ε) n d) :
    finiteInverse (eventMatrix (extendedArc hn P ε) n)
      (actualTimes (extendedArc hn P ε) n).card c d = 0 := by
  have hG1 : cyclicNoncollinear (extendedWord hn P ε) :=
    affineWord_G1 P _ hP.g1 ε (le_of_lt hε) (lt_of_lt_of_le hbound (min_le_left _ _))
  apply ConcreteCapMatrix.actual_equal_sign_inverse_zero hRI (extendedArc hn P ε) n
    _ _ _ _ hroots _ c d hne hs
  · rw [extendedArc_zero, hU]
  · intro a ha han
    rw [extendedArc, arcFromWord_positive _ _ a ha han]
    exact extendedWord_off_line hn P hP.g1 hU hV ε hε _
  · intro a b ha han hb hbn hab heq
    rw [extendedArc, arcFromWord_positive _ _ a ha han,
      arcFromWord_positive _ _ b hb hbn] at heq
    have hidx := cyclicNoncollinear_injective hn _ hG1 heq
    have hv := congrArg Fin.val hidx
    simp only [Fin.val_mk] at hv
    omega
  · exact arcFromWord_positive_G1 _ _ hG1
  · intro t _
    exact extendedArc_localCaps hn P hP hU hV ε hε hbound t

/-- Opposite geometric turns give actual endpoint data with direct entry A(P) and inverse entry zero. -/
theorem exists_endpoint_matrix_and_inverse (hRI : GLSSWRootIndependence)
    {n : ℕ} (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (hU : (P (zeroIndex hn)).2 = 0) (hV : (P (lastIndex hn)).2 = 0)
    (hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1)
    (hturn : planarDet (cyclicTangent P (lastIndex hn)) (cyclicTangent P (zeroIndex hn)) *
      planarDet (cyclicTangent P (penultimateIndex hn)) (cyclicTangent P (lastIndex hn)) < 0)
    (ε : ℝ) (hε : 0 < ε) (hbound : ε < geometricRadius hn P)
    (hroots : Set.InjOn (criticalRoot (extendedArc hn P ε))
      ↑(criticalPairs (extendedArc hn P ε) n)) :
    ∃ cU cV : EventIndex (extendedArc hn P ε) n,
      eventTime (extendedArc hn P ε) n cU = 0 ∧
      eventTime (extendedArc hn P ε) n cV = (P (lastIndex hn)).1 - (P (zeroIndex hn)).1 ∧
      cU < cV ∧ eventMatrix (extendedArc hn P ε) n cU cV = polygonAmplitude P hP ∧
      finiteInverse (eventMatrix (extendedArc hn P ε) n)
        (actualTimes (extendedArc hn P ε) n).card cU cV = 0 := by
  obtain ⟨cU, cV, hTU, hTV, hPU, hPV, hlt, hs⟩ :=
    ExtendedReturnEndpointTurns.endpoint_events_equal_sign hn P hP.g1 hU hV hleft hturn ε hε
  refine ⟨cU, cV, hTU, hTV, hlt, ?_, ?_⟩
  · exact ExtendedReturnEndpointMatrix.endpoint_entry_eq_amplitude
      hRI hn P hP hU hV hleft ε cU cV hTU hTV hPU hPV
  · exact inverse_zero_of_equal_event_signs hRI hn P hP hU hV ε hε hbound hroots
      cU cV (ne_of_lt hlt) hs

end DirectGLSSW.ExtendedReturnCapInverse



