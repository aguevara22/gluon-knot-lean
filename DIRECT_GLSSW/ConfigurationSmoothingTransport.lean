import ConfigurationEventOrder
import DirectGLSSW.OrbitNormalization
import DirectGLSSW.OrbitWordPrerequisite
import DirectGLSSW.DaughterPointListFilter
import DirectGLSSW.PolygonNonalternation

set_option autoImplicit false
namespace DirectGLSSW.ConfigurationSmoothingTransport
open CrossingRationalParameters CrossingIncidenceNeighborhood LabelledCrossingContinuity
open ConfigurationEventOrder DaughterFirstReturn PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P Q : Configuration n)
variable (h : ∀ e f, edgeIntersection Q e f ↔ edgeIntersection P e f)

def mappedSupport (S : Finset (PolygonCrossing P)) : Finset (PolygonCrossing Q) :=
  S.map (labelEquiv P Q h).toEmbedding

theorem mappedSupport_mem (S : Finset (PolygonCrossing P)) (c : PolygonCrossing P) :
    labelEquiv P Q h c ∈ mappedSupport P Q h S ↔ c ∈ S := by
  classical
  simp [mappedSupport]

theorem eventEquiv_pairing (S : Finset (PolygonCrossing P)) (x : PolygonEvent P) :
    eventEquiv P Q h (smoothingPairing P S x) =
      smoothingPairing Q (mappedSupport P Q h S) (eventEquiv P Q h x) := by
  classical
  cases x with
  | inl a => rfl
  | inr v =>
    rcases v with ⟨c,b⟩
    change eventEquiv P Q h (if c ∈ S then Sum.inr (c,!b) else Sum.inr (c,b)) =
      if labelEquiv P Q h c ∈ mappedSupport P Q h S then
        Sum.inr (labelEquiv P Q h c,!b) else Sum.inr (labelEquiv P Q h c,b)
    simp only [mappedSupport_mem]
    by_cases hc : c ∈ S <;> simp only [hc,if_true,if_false] <;> rfl

theorem eventEquiv_retained (S : Finset (PolygonCrossing P)) (x : PolygonEvent P) :
    retainedCorner Q (mappedSupport P Q h S) (eventEquiv P Q h x) ↔ retainedCorner P S x := by
  cases x with
  | inl a => rfl
  | inr v => exact mappedSupport_mem P Q h S v.1

/-- This intermediate input is precisely the actual label-preserving order
isomorphism; the final neighborhood theorem derives it from original G1–G2. -/
def OrderCompatible (hP : cyclicNoTripleIntersections P) (hQ : cyclicNoTripleIntersections Q) : Prop :=
  letI := polygonEventOrder P hP
  letI := polygonEventOrder Q hQ
  ∃ F : PolygonEvent P ≃o PolygonEvent Q, F.toEquiv = eventEquiv P Q h

variable (hP : CyclicGeneric P) (hQ : CyclicGeneric Q)
variable (horder : OrderCompatible P Q h hP.g2 hQ.g2)

include horder in
theorem eventEquiv_successor (x : PolygonEvent P) :
    eventEquiv P Q h (polygonEventSuccessor P hP.g2 x) =
      polygonEventSuccessor Q hQ.g2 (eventEquiv P Q h x) := by
  letI := polygonEventOrder P hP.g2
  letI := polygonEventOrder Q hQ.g2
  obtain ⟨F,hF⟩ := horder
  have hnat := (orderedCyclicSuccessor_naturality (PolygonEvent P) F x).symm
  change F.toEquiv (polygonEventSuccessor P hP.g2 x) =
    polygonEventSuccessor Q hQ.g2 (F.toEquiv x) at hnat
  simpa only [hF] using hnat

include horder in
theorem eventEquiv_dart (S : Finset (PolygonCrossing P)) (x : PolygonEvent P) :
    eventEquiv P Q h (smoothingDartPermutation P hP.g2 S x) =
      smoothingDartPermutation Q hQ.g2 (mappedSupport P Q h S) (eventEquiv P Q h x) := by
  rw [smoothingDartPermutation_apply,smoothingDartPermutation_apply,
    eventEquiv_pairing,eventEquiv_successor P Q h hP hQ horder]

def componentEquiv (S : Finset (PolygonCrossing P)) :
    Component (smoothingDartPermutation P hP.g2 S) ≃
      Component (smoothingDartPermutation Q hQ.g2 (mappedSupport P Q h S)) :=
  componentEquivOfIntertwining (eventEquiv P Q h) _ _ (eventEquiv_dart P Q h hP hQ horder S)

theorem componentEquiv_componentOf (S : Finset (PolygonCrossing P)) (x : PolygonEvent P) :
    componentEquiv P Q h hP hQ horder S (componentOf (smoothingDartPermutation P hP.g2 S) x) =
      componentOf (smoothingDartPermutation Q hQ.g2 (mappedSupport P Q h S)) (eventEquiv P Q h x) := rfl

include horder in
theorem nonalternating_iff (S : Finset (PolygonCrossing P)) :
    PolygonNonalternation.polygonNonalternating P hP.g2 S ↔
      PolygonNonalternation.polygonNonalternating Q hQ.g2 (mappedSupport P Q h S) := by
  rw [PolygonNonalternation.polygonNonalternating_iff_dart_count P hP.g2 hP.size_ge_three,
    PolygonNonalternation.polygonNonalternating_iff_dart_count Q hQ.g2 hQ.size_ge_three]
  have hc := Fintype.card_congr (componentEquiv P Q h hP hQ horder S)
  change componentCount _ = componentCount _ at hc
  rw [hc]
  simp [mappedSupport]

/- Proof adapted, with attribution, from the frozen staged normalization module's
public generic orbitWord_map_equiv. Only canonical orbit APIs are imported here. -/
/-- Rooted orbit words commute with an actual permutation intertwining. -/
theorem orbitWord_map_equiv {α β : Type*} [Fintype α] [Fintype β]
    (E : α ≃ β) (p : Equiv.Perm α) (s : Equiv.Perm β)
    (he : ∀ x, E (p x) = s (E x)) (root : α) :
    PermutationOrbits.orbitWord s (E root) =
      (PermutationOrbits.orbitWord p root).map E := by
  classical
  let N := Fintype.card (PermutationOrbits.Fibre p
    (PermutationOrbits.componentOf p root))
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨⟨root,rfl⟩⟩
  let f : Fin N → β := fun i => E (PermutationOrbits.orbitEnumeration p root i).val
  have hf : Function.Injective f :=
    E.injective.comp (Subtype.val_injective.comp
      (PermutationOrbits.orbitEnumeration p root).injective)
  have hstep : ∀ i, s (f i) = f (cyclicSuccessor i) := by
    intro i
    have henum := congrArg Subtype.val
      (PermutationOrbits.orbitEnumeration_successor p root i)
    exact (he _).symm.trans (congrArg E henum.symm)
  have hroot : f ⟨0,hN⟩ = E root := by simp [f]
  have hword := orbitWord_eq_of_injective_cyclicSuccessor s hN f hf hstep
  rw [hroot] at hword
  simpa [f, PermutationOrbits.orbitWord, List.map_ofFn] using hword


/-- The original retained orbit label word, independent of nearby coordinates. -/
def retainedLabelWord (S : Finset (PolygonCrossing P)) (root : PolygonEvent P) : List (PolygonEvent P) :=
  (orbitWord (smoothingDartPermutation P hP.g2 S) root).filter
    (fun x => decide (retainedCorner P S x))

/- Actual daughters use the fixed original retained label word with nearby actual
point coordinates. No daughter genericity or nonalternation hypothesis is needed. -/
include horder in
theorem daughterPointList_eq_mappedWord (S : Finset (PolygonCrossing P)) (root : PolygonEvent P) :
    daughterPointList Q hQ.g2 (mappedSupport P Q h S) (eventEquiv P Q h root) =
      (retainedLabelWord P hP S root).map (fun x => polygonEventPoint Q (eventEquiv P Q h x)) := by
  classical
  have hw := orbitWord_map_equiv (eventEquiv P Q h)
    (smoothingDartPermutation P hP.g2 S) (smoothingDartPermutation Q hQ.g2 (mappedSupport P Q h S))
    (eventEquiv_dart P Q h hP hQ horder S) root
  have hret : (fun x => decide (retainedCorner Q (mappedSupport P Q h S) (eventEquiv P Q h x))) =
      (fun x => decide (retainedCorner P S x)) := by
    funext x
    simp only [eventEquiv_retained]
  rw [DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map,hw,
    ← DaughterPointListFilter.map_filter_comp (eventEquiv P Q h)
      (fun x => decide (retainedCorner Q (mappedSupport P Q h S) x)),hret,List.map_map]
  rfl














end
end DirectGLSSW.ConfigurationSmoothingTransport
