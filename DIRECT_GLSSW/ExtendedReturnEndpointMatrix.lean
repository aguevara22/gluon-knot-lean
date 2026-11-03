import DirectGLSSW.ExtendedReturnClippedWord
import ExtendedReturnEndpointEvents
import DirectGLSSW.CapEventInterpretation

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace DirectGLSSW.ExtendedReturnEndpointMatrix
open ExtendedReturnArcGeometry ExtendedReturnClippedWord OrderedCapEvents
open CrossingCapPairing CapEventInterpretation

/-- Actual endpoint event data identifies the direct cap-matrix entry with A(P). -/
theorem endpoint_entry_eq_amplitude (hRI : GLSSWRootIndependence)
    {n : ℕ} (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (hU : (P (zeroIndex hn)).2 = 0) (hV : (P (lastIndex hn)).2 = 0)
    (hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1) (ε : ℝ)
    (cU cV : EventIndex (extendedArc hn P ε) n)
    (hTU : eventTime (extendedArc hn P ε) n cU = 0)
    (hTV : eventTime (extendedArc hn P ε) n cV =
      (P (lastIndex hn)).1 - (P (zeroIndex hn)).1)
    (hPU : eventPair (extendedArc hn P ε) n cU = (1,2))
    (hPV : eventPair (extendedArc hn P ε) n cV = (n-1,n)) :
    eventMatrix (extendedArc hn P ε) n cU cV = polygonAmplitude P hP := by
  have hPUfst : (eventPair (extendedArc hn P ε) n cU).1 = 1 := congrArg Prod.fst hPU
  have hPVfst : (eventPair (extendedArc hn P ε) n cV).1 = n-1 := congrArg Prod.fst hPV
  have hzero : ((extendedArc hn P ε) 0).2 = 0 := by rw [extendedArc_zero, hU]
  have hcd : cU < cV := by
    apply (eventTime_strictMono (extendedArc hn P ε) n).lt_iff_lt.mp
    rw [hTU, hTV]
    exact sub_pos.mpr hleft
  have horder : (eventPair (extendedArc hn P ε) n cU).1 <
      (eventPair (extendedArc hn P ε) n cV).1 := by
    rw [hPUfst, hPVfst]
    omega
  have hgeneric_at (k l : ℕ) (c d : ℝ)
      (hk : k = 1) (hl : l = n-1) (hc : c = 0)
      (hd : d = (P (lastIndex hn)).1 - (P (zeroIndex hn)).1) :
      CyclicGeneric (crossingClippedCapWord (extendedArc hn P ε) c d k l) := by
    subst k l c d
    exact whole_cap_generic hn P hP hU hV ε
  have hcap : CyclicGeneric (crossingClippedCapWord (extendedArc hn P ε)
      (eventTime (extendedArc hn P ε) n cU) (eventTime (extendedArc hn P ε) n cV)
      (eventPair (extendedArc hn P ε) n cU).1
      (eventPair (extendedArc hn P ε) n cV).1) := by
    exact hgeneric_at _ _ _ _ hPUfst hPVfst hTU hTV
  rw [eventMatrix_eq_cap_amplitude hRI _ n hzero cU cV hcd horder hcap]
  have hamplitude_at (k l : ℕ) (c d : ℝ)
      (hgeneric : CyclicGeneric (crossingClippedCapWord (extendedArc hn P ε) c d k l))
      (hk : k = 1) (hl : l = n-1) (hc : c = 0)
      (hd : d = (P (lastIndex hn)).1 - (P (zeroIndex hn)).1) :
      polygonAmplitude (crossingClippedCapWord (extendedArc hn P ε) c d k l) hgeneric =
        polygonAmplitude P hP := by
    subst k l c d
    exact whole_cap_amplitude hRI hn P hP hU hV ε
  exact hamplitude_at _ _ _ _ hcap hPUfst hPVfst hTU hTV

/-- G1 supplies the endpoint pair identities from their actual event times. -/
theorem endpoint_entry_eq_amplitude_of_times (hRI : GLSSWRootIndependence)
    {n : ℕ} (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (hU : (P (zeroIndex hn)).2 = 0) (hV : (P (lastIndex hn)).2 = 0)
    (hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1) (ε : ℝ)
    (cU cV : EventIndex (extendedArc hn P ε) n)
    (hTU : eventTime (extendedArc hn P ε) n cU = 0)
    (hTV : eventTime (extendedArc hn P ε) n cV =
      (P (lastIndex hn)).1 - (P (zeroIndex hn)).1) :
    eventMatrix (extendedArc hn P ε) n cU cV = polygonAmplitude P hP := by
  have hu := eventPair_spec (extendedArc hn P ε) n cU
  have hv := eventPair_spec (extendedArc hn P ε) n cV
  have hPU := (ExtendedReturnEndpointEvents.endpoint_actual_root_unique
    hn P hP.g1 hU hV ε _ hu.1).1 (hu.2.trans hTU)
  have hPV := (ExtendedReturnEndpointEvents.endpoint_actual_root_unique
    hn P hP.g1 hU hV ε _ hv.1).2 (hv.2.trans hTV)
  exact endpoint_entry_eq_amplitude hRI hn P hP hU hV hleft ε cU cV hTU hTV hPU hPV

/-- The original polygon supplies actual ordered endpoint indices with entry A(P). -/
theorem exists_endpoint_entry_eq_amplitude (hRI : GLSSWRootIndependence)
    {n : ℕ} (hn : 3 ≤ n) (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (hU : (P (zeroIndex hn)).2 = 0) (hV : (P (lastIndex hn)).2 = 0)
    (hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1) (ε : ℝ) (hε : 0 < ε) :
    ∃ cU cV : EventIndex (extendedArc hn P ε) n,
      eventTime (extendedArc hn P ε) n cU = 0 ∧
      eventTime (extendedArc hn P ε) n cV = (P (lastIndex hn)).1 - (P (zeroIndex hn)).1 ∧
      cU < cV ∧ eventMatrix (extendedArc hn P ε) n cU cV = polygonAmplitude P hP := by
  obtain ⟨cU, cV, hTU, hTV, hPU, hPV, hlt, _, _⟩ :=
    ExtendedReturnEndpointEvents.endpoint_events hn P hP.g1 hU hV hleft ε hε
  exact ⟨cU, cV, hTU, hTV, hlt,
    endpoint_entry_eq_amplitude hRI hn P hP hU hV hleft ε cU cV hTU hTV hPU hPV⟩

end DirectGLSSW.ExtendedReturnEndpointMatrix




