import DirectGLSSW.OrderedEventSuccessor
import DirectGLSSW.SmoothingPairing
import DirectGLSSW.PermutationOrbits

/-!
# Incoming-event and outgoing-dart smoothing permutations

Source motivation: frozen note lines 131–139; exact scope transcribed in
STATEMENTS.md before proof authoring. These are concrete successor-gluing
permutations and their full orbit quotients. Geometric component realization,
nonalternation, and general split/join counts are not asserted here.
-/

set_option autoImplicit false

namespace DirectGLSSW

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] [LinearOrder K] {n : ℕ}

/-- An incoming event takes the outgoing branch of its paired event, then
advances by the original oriented event successor. -/
noncomputable def smoothingIncomingPermutation (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q)) :
    Equiv.Perm (PolygonEvent q) :=
  polygonEventSuccessor q hq * smoothingPairing q S

/-- A dart retains the original event-to-successor segment; the next dart
starts at the event paired with its original terminal event. -/
noncomputable def smoothingDartPermutation (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q)) :
    Equiv.Perm (PolygonEvent q) :=
  smoothingPairing q S * polygonEventSuccessor q hq

theorem smoothingIncomingPermutation_apply (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (x : PolygonEvent q) :
    smoothingIncomingPermutation q hq S x =
      polygonEventSuccessor q hq (smoothingPairing q S x) := rfl

theorem smoothingDartPermutation_apply (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (x : PolygonEvent q) :
    smoothingDartPermutation q hq S x =
      smoothingPairing q S (polygonEventSuccessor q hq x) := rfl

/-- The two labelling conventions are explicitly conjugate. -/
theorem smoothingDartPermutation_conjugate (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q)) :
    smoothingDartPermutation q hq S =
      smoothingPairing q S * smoothingIncomingPermutation q hq S *
        (smoothingPairing q S)⁻¹ := by
  simp [smoothingIncomingPermutation, smoothingDartPermutation, mul_assoc]

/-- The pairing transports successor orientation, not just component counts. -/
theorem smoothingPermutation_intertwine (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (x : PolygonEvent q) :
    smoothingDartPermutation q hq S (smoothingPairing q S x) =
      smoothingPairing q S (smoothingIncomingPermutation q hq S x) := rfl

/-- Full orbit equivalence, including any singleton orbits, induced by pairing. -/
noncomputable def smoothingComponentEquiv (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q)) :
    PermutationOrbits.Component (smoothingIncomingPermutation q hq S) ≃
      PermutationOrbits.Component (smoothingDartPermutation q hq S) :=
  PermutationOrbits.productOrderEquiv (polygonEventSuccessor q hq) (smoothingPairing q S)

/-- Incoming labels and dart labels are paired, rather than literally equal. -/
theorem smoothingComponentEquiv_componentOf (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (x : PolygonEvent q) :
    smoothingComponentEquiv q hq S
        (PermutationOrbits.componentOf (smoothingIncomingPermutation q hq S) x) =
      PermutationOrbits.componentOf (smoothingDartPermutation q hq S)
        (smoothingPairing q S x) := rfl

theorem smoothingComponentCounts_equal (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q)) :
    PermutationOrbits.componentCount (smoothingIncomingPermutation q hq S) =
      PermutationOrbits.componentCount (smoothingDartPermutation q hq S) :=
  PermutationOrbits.componentCount_product_order
    (polygonEventSuccessor q hq) (smoothingPairing q S)

/-- The next dart's initial plane point is the previous dart's terminal point.
This equality alone does not assert a geometric-component equivalence. -/
theorem smoothingDartPermutation_endpoint (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q))
    (x : PolygonEvent q) :
    polygonEventPoint q (smoothingDartPermutation q hq S x) =
      polygonEventPoint q (polygonEventSuccessor q hq x) :=
  smoothingPairing_point q S (polygonEventSuccessor q hq x)

theorem smoothingIncomingPermutation_empty (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) :
    smoothingIncomingPermutation q hq ∅ = polygonEventSuccessor q hq := by
  simp [smoothingIncomingPermutation, smoothingPairing_empty]

theorem smoothingDartPermutation_empty (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) :
    smoothingDartPermutation q hq ∅ = polygonEventSuccessor q hq := by
  simp [smoothingDartPermutation, smoothingPairing_empty]

/-- With no selected cut there is exactly one component on the polygon domain.
The anchor witness supplies nonemptiness; IsCycleOn alone would not suffice. -/
theorem smoothingIncomingComponentCount_empty (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (hn : 3 ≤ n) :
    PermutationOrbits.componentCount (smoothingIncomingPermutation q hq ∅) = 1 := by
  letI : Nonempty (PolygonEvent q) := ⟨Sum.inl ⟨0, by omega⟩⟩
  rw [smoothingIncomingPermutation_empty]
  exact PermutationOrbits.componentCount_eq_one _ (polygonEventSuccessor_isCycleOn q hq)

theorem smoothingDartComponentCount_empty (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (hn : 3 ≤ n) :
    PermutationOrbits.componentCount (smoothingDartPermutation q hq ∅) = 1 := by
  rw [← smoothingComponentCounts_equal]
  exact smoothingIncomingComponentCount_empty q hq hn

/-- Disjoint global supports compose on the right in incoming-event convention. -/
theorem smoothingIncomingPermutation_union (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S T : Finset (PolygonCrossing q))
    (hST : Disjoint S T) :
    smoothingIncomingPermutation q hq (S ∪ T) =
      smoothingIncomingPermutation q hq S * smoothingPairing q T := by
  simp only [smoothingIncomingPermutation, smoothingPairing_union q S T hST, mul_assoc]

/-- Disjoint global supports compose on the left in outgoing-dart convention.
No local eligibility, separation, or refinement property is assumed or proved. -/
theorem smoothingDartPermutation_union (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S T : Finset (PolygonCrossing q))
    (hST : Disjoint S T) :
    smoothingDartPermutation q hq (S ∪ T) =
      smoothingPairing q T * smoothingDartPermutation q hq S := by
  simp only [smoothingDartPermutation, smoothingPairing_union q S T hST]
  rw [smoothingPairing_commute q S T, mul_assoc]

end DirectGLSSW
