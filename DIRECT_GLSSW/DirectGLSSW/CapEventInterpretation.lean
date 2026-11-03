import DirectGLSSW.OrderedCapEvents
import DirectGLSSW.CrossingCapPairing

set_option autoImplicit false

namespace DirectGLSSW.CapEventInterpretation
open DirectGLSSW OrderedCapEvents CrossingCapPairing

theorem event_end_height_ne_zero (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (c : EventIndex q n) : (q (eventPair q n c).2).2 ≠ 0 := by
  have hneg := (eventPair_bounds q n c).2.2.2.1
  intro hz
  rw [hz, div_zero] at hneg
  exact (lt_irrefl 0) hneg

noncomputable def eventDirection (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (c : EventIndex q n) : Sign :=
  nonzeroScalarSign (q (eventPair q n c).2).2 (event_end_height_ne_zero q n c)

theorem eventSign_eq_directionValue (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (c : EventIndex q n) : eventSign q n c = (eventDirection q n c).value := by
  exact scalarSignValue_eq_nonzeroScalarSign _ (event_end_height_ne_zero q n c)

theorem eventPairing_reverse_arc_zero (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (c d : EventIndex q n) (horder : (eventPair q n d).1 ≤ (eventPair q n c).1) :
    eventPairing q n c d = 0 := by
  have hc := eventPair_bounds q n c
  have hd := eventPair_bounds q n d
  exact actual_pairing_eq_zero_of_reverse_order q n
    (eventPair q n c).1 (eventPair q n d).1 (eventTime q n c) (eventTime q n d)
    hc.1 hc.2.1 hd.1 hd.2.1 horder

theorem eventPairing_eq_cap_amplitude (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (hzero : (q 0).2 = 0)
    (c d : EventIndex q n) (hcd : c < d)
    (horder : (eventPair q n c).1 < (eventPair q n d).1)
    (hcap : CyclicGeneric (crossingClippedCapWord q (eventTime q n c) (eventTime q n d)
      (eventPair q n c).1 (eventPair q n d).1)) :
    eventPairing q n c d = polygonAmplitude
      (crossingClippedCapWord q (eventTime q n c) (eventTime q n d)
        (eventPair q n c).1 (eventPair q n d).1) hcap := by
  have hc := eventPair_bounds q n c
  have hd := eventPair_bounds q n d
  exact actual_pairing_eq_clipped_cap_amplitude hRI q n
    (eventPair q n c).1 (eventPair q n d).1 (eventTime q n c) (eventTime q n d)
    hzero hc.1 hc.2.1 hd.1 hd.2.1 (eventTime_strictMono q n hcd) horder hcap

theorem eventMatrix_eq_cap_amplitude (hRI : GLSSWRootIndependence)
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (hzero : (q 0).2 = 0)
    (c d : EventIndex q n) (hcd : c < d)
    (horder : (eventPair q n c).1 < (eventPair q n d).1)
    (hcap : CyclicGeneric (crossingClippedCapWord q (eventTime q n c) (eventTime q n d)
      (eventPair q n c).1 (eventPair q n d).1)) :
    eventMatrix q n c d = polygonAmplitude
      (crossingClippedCapWord q (eventTime q n c) (eventTime q n d)
        (eventPair q n c).1 (eventPair q n d).1) hcap := by
  rw [eventMatrix, if_pos hcd]
  exact eventPairing_eq_cap_amplitude hRI q n hzero c d hcd horder hcap








end DirectGLSSW.CapEventInterpretation
