import DaughterWordLocality
import DirectGLSSW.LocalCoordinates

set_option autoImplicit false
namespace DirectGLSSW.RefinementFamilyLocality
open PermutationOrbits ActualLocalSupports DaughterFirstReturn GeometricSmoothingWeights
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
variable (S : Finset (PolygonCrossing q))

/-- Incoming old-component label attached to an outgoing event. -/
def outgoingOldLabel (y : PolygonEvent q) :
    Component (smoothingIncomingPermutation q hq.g2 S) :=
  componentOf (smoothingIncomingPermutation q hq.g2 S) (smoothingPairing q S y)

theorem successor_label (y : PolygonEvent q) :
    componentOf (smoothingIncomingPermutation q hq.g2 S)
      (polygonEventSuccessor q hq.g2 y) = outgoingOldLabel q hq S y := by
  have h := componentOf_apply (smoothingIncomingPermutation q hq.g2 S)
    (smoothingPairing q S y)
  change componentOf (smoothingIncomingPermutation q hq.g2 S)
    (polygonEventSuccessor q hq.g2 (smoothingPairing q S (smoothingPairing q S y))) = _ at h
  have hp : smoothingPairing q S (smoothingPairing q S y) = y :=
    smoothingPairingMap_involutive q S y
  rw [hp] at h
  exact h

theorem pairing_families_eq_on_label
    (f g : LocalSupports q (smoothingIncomingPermutation q hq.g2 S) S)
    (A : Component (smoothingIncomingPermutation q hq.g2 S)) (hfg : f A = g A)
    (x : PolygonEvent q) (hx : componentOf (smoothingIncomingPermutation q hq.g2 S) x = A) :
    smoothingPairing q (unionLocal q (smoothingIncomingPermutation q hq.g2 S) S f) x =
    smoothingPairing q (unionLocal q (smoothingIncomingPermutation q hq.g2 S) S g) x := by
  rw [LocalCoordinates.smoothingPairing_unionLocal_eq_localImage_on_fibre q _ S f A ⟨x,hx⟩,
    LocalCoordinates.smoothingPairing_unionLocal_eq_localImage_on_fibre q _ S g A ⟨x,hx⟩,
    hfg]

theorem outgoing_families_eq_on_label
    (f g : LocalSupports q (smoothingIncomingPermutation q hq.g2 S) S)
    (A : Component (smoothingIncomingPermutation q hq.g2 S)) (hfg : f A = g A)
    (y : PolygonEvent q) (hy : outgoingOldLabel q hq S y = A) :
    smoothingDartPermutation q hq.g2
      (S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S f) y =
    smoothingDartPermutation q hq.g2
      (S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S g) y := by
  have hf := disjoint_of_eligible q _ S _ (unionLocal_eligible q _ S f)
  have hg := disjoint_of_eligible q _ S _ (unionLocal_eligible q _ S g)
  simp only [smoothingDartPermutation_apply, smoothingPairing_union q _ _ hf,
    smoothingPairing_union q _ _ hg, Equiv.Perm.mul_apply]
  apply congrArg (smoothingPairing q S)
  exact pairing_families_eq_on_label q hq S f g A hfg _ ((successor_label q hq S y).trans hy)

theorem refined_outgoing_preserves_label
    (f : LocalSupports q (smoothingIncomingPermutation q hq.g2 S) S)
    (y : PolygonEvent q) :
    outgoingOldLabel q hq S
      (smoothingDartPermutation q hq.g2
        (S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S f) y) =
    outgoingOldLabel q hq S y := by
  have hf := disjoint_of_eligible q _ S _ (unionLocal_eligible q _ S f)
  unfold outgoingOldLabel
  rw [smoothingDartPermutation_apply, smoothingPairing_union q _ _ hf]
  simp only [Equiv.Perm.mul_apply]
  rw [show ∀ x, smoothingPairing q S (smoothingPairing q S x) = x from
    smoothingPairingMap_involutive q S]
  change componentOf (smoothingIncomingPermutation q hq.g2 S)
    (smoothingPairing q (unionLocal q (smoothingIncomingPermutation q hq.g2 S) S f)
      (polygonEventSuccessor q hq.g2 y)) = _
  rw [show componentOf (smoothingIncomingPermutation q hq.g2 S)
    (smoothingPairing q (unionLocal q (smoothingIncomingPermutation q hq.g2 S) S f)
      (polygonEventSuccessor q hq.g2 y)) =
    componentOf (smoothingIncomingPermutation q hq.g2 S) (polygonEventSuccessor q hq.g2 y) from
      pairing_preserves_oldLabel q _ S _ (unionLocal_eligible q _ S f) _]
  exact successor_label q hq S y

theorem retained_families_iff_on_label
    (f g : LocalSupports q (smoothingIncomingPermutation q hq.g2 S) S)
    (A : Component (smoothingIncomingPermutation q hq.g2 S)) (hfg : f A = g A)
    (y : PolygonEvent q) (hy : outgoingOldLabel q hq S y = A) :
    retainedCorner q (S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S f) y ↔
    retainedCorner q (S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S g) y := by
  cases y with
  | inl e => exact Iff.rfl
  | inr v =>
    by_cases hv : v.1 ∈ S
    · simp [retainedCorner, hv]
    · have hfix : smoothingPairing q S (Sum.inr v) = Sum.inr v :=
        (smoothingPairing_visit_fixed_iff q S v).mpr hv
      have hlabel : componentOf (smoothingIncomingPermutation q hq.g2 S) (Sum.inr v) = A := by
        simpa only [outgoingOldLabel, hfix] using hy
      have hp := pairing_families_eq_on_label q hq S f g A hfg (Sum.inr v) hlabel
      have hmem : v.1 ∈ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S f ↔
          v.1 ∈ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S g := by
        have hi : smoothingPairing q (unionLocal q (smoothingIncomingPermutation q hq.g2 S) S f) (Sum.inr v) = Sum.inr v ↔
            smoothingPairing q (unionLocal q (smoothingIncomingPermutation q hq.g2 S) S g) (Sum.inr v) = Sum.inr v := by rw [hp]
        exact not_iff_not.mp ((smoothingPairing_visit_fixed_iff q _ v).symm.trans
          (hi.trans (smoothingPairing_visit_fixed_iff q _ v)))
      simpa only [retainedCorner, Finset.mem_union, hv, false_or] using hmem

/-- Only the local support in the old component containing the root matters. -/
theorem daughterPointList_eq_of_family_eq
    (f g : LocalSupports q (smoothingIncomingPermutation q hq.g2 S) S)
    (A : Component (smoothingIncomingPermutation q hq.g2 S)) (hfg : f A = g A)
    (root : PolygonEvent q) (hroot : outgoingOldLabel q hq S root = A) :
    daughterPointList q hq.g2
      (S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S f) root =
    daughterPointList q hq.g2
      (S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S g) root := by
  apply DaughterWordLocality.daughterPointList_eq_on_region q hq _ _ root
    (fun y => outgoingOldLabel q hq S y = A) hroot
  · intro y hy
    exact (refined_outgoing_preserves_label q hq S g y).trans hy
  · exact outgoing_families_eq_on_label q hq S f g A hfg
  · exact retained_families_iff_on_label q hq S f g A hfg

theorem outgoingOldLabel_eq_iff (x y : PolygonEvent q) :
    outgoingOldLabel q hq S x = outgoingOldLabel q hq S y ↔
    componentOf (smoothingDartPermutation q hq.g2 S) x =
      componentOf (smoothingDartPermutation q hq.g2 S) y := by
  have hmap (z : PolygonEvent q) :
      smoothingComponentEquiv q hq.g2 S (outgoingOldLabel q hq S z) =
        componentOf (smoothingDartPermutation q hq.g2 S) z := by
    change componentOf (smoothingDartPermutation q hq.g2 S)
      (smoothingPairing q S (smoothingPairing q S z)) = _
    rw [show smoothingPairing q S (smoothingPairing q S z) = z from
      smoothingPairingMap_involutive q S z]
  constructor
  · intro h
    have hm := congrArg (smoothingComponentEquiv q hq.g2 S) h
    simpa only [hmap] using hm
  · intro h
    apply (smoothingComponentEquiv q hq.g2 S).injective
    simpa only [hmap] using h

/-- Actual selected component amplitudes depend only on that old component's
second-stage support. The agreement and invariance hypotheses of the generic
locality lemma are derived, not assumptions. -/
theorem componentAmplitude_eq_of_family_eq
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq)
    (f g : LocalSupports q (smoothingIncomingPermutation q hq.g2 S) S)
    (hf : PolygonNonalternation.polygonNonalternating q hq.g2
      (S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S f))
    (hg : PolygonNonalternation.polygonNonalternating q hq.g2
      (S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S g))
    (A : Component (smoothingIncomingPermutation q hq.g2 S)) (hfg : f A = g A)
    (root : PolygonEvent q) (hroot : outgoingOldLabel q hq S root = A) :
    componentAmplitude q hq
      (S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S f) hAux hf
      (componentOf (smoothingDartPermutation q hq.g2
        (S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S f)) root) =
    componentAmplitude q hq
      (S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S g) hAux hg
      (componentOf (smoothingDartPermutation q hq.g2
        (S ∪ unionLocal q (smoothingIncomingPermutation q hq.g2 S) S g)) root) := by
  apply DaughterWordLocality.componentAmplitude_eq_on_region q hq _ _ root hRI hAux hg hf
    (fun y => outgoingOldLabel q hq S y = A) hroot
  · intro y hy
    exact (refined_outgoing_preserves_label q hq S g y).trans hy
  · exact outgoing_families_eq_on_label q hq S f g A hfg
  · exact retained_families_iff_on_label q hq S f g A hfg










end
end DirectGLSSW.RefinementFamilyLocality
