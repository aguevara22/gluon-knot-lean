import DirectGLSSW.EdgeAffineNormalization
import DirectGLSSW.SmoothingPermutations
import DirectGLSSW.OrbitNormalization
import DirectGLSSW.OrbitWordPrerequisite
import DirectGLSSW.DaughterPointListFilter
import DirectGLSSW.PolygonNonalternation
import DirectGLSSW.TruncationPointListAdapter
import DirectGLSSW.DaughterRootAmplitude
import DirectGLSSW.GeometricSmoothingSumTransport

set_option autoImplicit false

namespace DirectGLSSW.EdgeAffineNormalization

variable {n : ℕ} (u v : PlanarPoint ℝ) (huv : u ≠ v)
  (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)

/-- The normalization keeps the two distinct visits of each crossing. -/
def visitEquiv : CrossingVisit q ≃ CrossingVisit (fun i => normalize u v (q i)) :=
  Equiv.prodCongr (crossingEquiv u v huv q) (Equiv.refl Bool)

/-- Original vertex labels are unchanged; actual crossing visits are transported. -/
def eventEquiv : PolygonEvent q ≃ PolygonEvent (fun i => normalize u v (q i)) :=
  Equiv.sumCongr (Equiv.refl (Fin n)) (visitEquiv u v huv q)

theorem eventEquiv_edge (x : PolygonEvent q) :
    polygonEventEdge (fun i => normalize u v (q i)) (eventEquiv u v huv q x) =
      polygonEventEdge q x := by
  cases x with
  | inl e => rfl
  | inr w => rcases w with ⟨c,b⟩; cases b <;> rfl

include hq in
theorem eventEquiv_parameter (x : PolygonEvent q) :
    polygonEventParameter (fun i => normalize u v (q i)) (eventEquiv u v huv q x) =
      polygonEventParameter q x := by
  cases x with
  | inl e => rfl
  | inr w =>
    rcases w with ⟨c,b⟩
    cases b
    · exact (normalize_crossingParameters u v huv q hq c).1
    · exact (normalize_crossingParameters u v huv q hq c).2

include hq in
theorem eventEquiv_point (x : PolygonEvent q) :
    polygonEventPoint (fun i => normalize u v (q i)) (eventEquiv u v huv q x) =
      normalize u v (polygonEventPoint q x) := by
  cases x with
  | inl e => rfl
  | inr w => exact normalize_crossingPoint u v huv q hq w.1

/-- The affine change of coordinates preserves the actual traversal order. -/
noncomputable def eventOrderIso :
    letI := polygonEventOrder q hq.g2
    letI := polygonEventOrder (fun i => normalize u v (q i))
      (normalize_generic u v huv q hq).g2
    PolygonEvent q ≃o PolygonEvent (fun i => normalize u v (q i)) := by
  letI := polygonEventOrder q hq.g2
  letI := polygonEventOrder (fun i => normalize u v (q i))
    (normalize_generic u v huv q hq).g2
  refine { toEquiv := eventEquiv u v huv q, map_rel_iff' := ?_ }
  intro x y
  rw [← not_lt, ← not_lt]
  apply not_congr
  rw [polygonEvent_lt_iff, polygonEvent_lt_iff]
  simp only [eventEquiv_edge, eventEquiv_parameter u v huv q hq]

theorem eventEquiv_successor (x : PolygonEvent q) :
    eventEquiv u v huv q (polygonEventSuccessor q hq.g2 x) =
      polygonEventSuccessor (fun i => normalize u v (q i))
        (normalize_generic u v huv q hq).g2 (eventEquiv u v huv q x) := by
  letI := polygonEventOrder q hq.g2
  letI := polygonEventOrder (fun i => normalize u v (q i))
    (normalize_generic u v huv q hq).g2
  exact (orderedCyclicSuccessor_naturality (PolygonEvent q)
    (eventOrderIso u v huv q hq) x).symm

noncomputable def normalizedSupport (S : Finset (PolygonCrossing q)) :
    Finset (PolygonCrossing (fun i => normalize u v (q i))) :=
  S.map (crossingEquiv u v huv q).toEmbedding

theorem normalizedSupport_mem (S : Finset (PolygonCrossing q)) (c : PolygonCrossing q) :
    crossingEquiv u v huv q c ∈ normalizedSupport u v huv q S ↔ c ∈ S := by
  classical
  simp [normalizedSupport]

theorem eventEquiv_pairing (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    eventEquiv u v huv q (smoothingPairing q S x) =
      smoothingPairing (fun i => normalize u v (q i)) (normalizedSupport u v huv q S)
        (eventEquiv u v huv q x) := by
  classical
  cases x with
  | inl e => rfl
  | inr w =>
    rcases w with ⟨c,b⟩
    change eventEquiv u v huv q
        (if c ∈ S then Sum.inr (c, !b) else Sum.inr (c,b)) =
      if crossingEquiv u v huv q c ∈ normalizedSupport u v huv q S then
        Sum.inr (crossingEquiv u v huv q c, !b)
      else Sum.inr (crossingEquiv u v huv q c,b)
    simp only [normalizedSupport_mem]
    by_cases hc : c ∈ S <;> simp only [hc, if_true, if_false] <;> rfl

/-- Exact conjugacy of outgoing-dart smoothing, with no genericity premise on daughters. -/
theorem eventEquiv_dart (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    eventEquiv u v huv q (smoothingDartPermutation q hq.g2 S x) =
      smoothingDartPermutation (fun i => normalize u v (q i))
        (normalize_generic u v huv q hq).g2 (normalizedSupport u v huv q S)
        (eventEquiv u v huv q x) := by
  rw [smoothingDartPermutation_apply, smoothingDartPermutation_apply,
    eventEquiv_pairing, eventEquiv_successor u v huv q hq]

noncomputable def normalizedComponentEquiv (S : Finset (PolygonCrossing q)) :
    PermutationOrbits.Component (smoothingDartPermutation q hq.g2 S) ≃
      PermutationOrbits.Component (smoothingDartPermutation
        (fun i => normalize u v (q i)) (normalize_generic u v huv q hq).g2
        (normalizedSupport u v huv q S)) :=
  PermutationOrbits.componentEquivOfIntertwining (eventEquiv u v huv q) _ _
    (eventEquiv_dart u v huv q hq S)

theorem normalizedComponentEquiv_componentOf (S : Finset (PolygonCrossing q))
    (x : PolygonEvent q) :
    normalizedComponentEquiv u v huv q hq S
        (PermutationOrbits.componentOf (smoothingDartPermutation q hq.g2 S) x) =
      PermutationOrbits.componentOf (smoothingDartPermutation
        (fun i => normalize u v (q i)) (normalize_generic u v huv q hq).g2
        (normalizedSupport u v huv q S)) (eventEquiv u v huv q x) := rfl

theorem normalization_componentCount (S : Finset (PolygonCrossing q)) :
    PermutationOrbits.componentCount (smoothingDartPermutation q hq.g2 S) =
      PermutationOrbits.componentCount (smoothingDartPermutation
        (fun i => normalize u v (q i)) (normalize_generic u v huv q hq).g2
        (normalizedSupport u v huv q S)) :=
  Fintype.card_congr (normalizedComponentEquiv u v huv q hq S)

theorem normalization_nonalternating_iff (S : Finset (PolygonCrossing q)) :
    PolygonNonalternation.polygonNonalternating q hq.g2 S ↔
      PolygonNonalternation.polygonNonalternating
        (fun i => normalize u v (q i)) (normalize_generic u v huv q hq).g2
        (normalizedSupport u v huv q S) := by
  rw [PolygonNonalternation.polygonNonalternating_iff_dart_count q hq.g2 hq.size_ge_three,
    PolygonNonalternation.polygonNonalternating_iff_dart_count
      (fun i => normalize u v (q i)) (normalize_generic u v huv q hq).g2 hq.size_ge_three,
    normalization_componentCount u v huv q hq]
  simp [normalizedSupport]

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

theorem eventEquiv_retained (S : Finset (PolygonCrossing q)) (x : PolygonEvent q) :
    DaughterFirstReturn.retainedCorner (fun i => normalize u v (q i))
        (normalizedSupport u v huv q S) (eventEquiv u v huv q x) ↔
      DaughterFirstReturn.retainedCorner q S x := by
  cases x with
  | inl e => rfl
  | inr w => exact normalizedSupport_mem u v huv q S w.1

/-- Every daughter point list is the affine image of the original rooted list.
This includes arbitrary supports and roots, without assuming daughter G1. -/
theorem normalization_daughterPointList (S : Finset (PolygonCrossing q))
    (root : PolygonEvent q) :
    DaughterFirstReturn.daughterPointList (fun i => normalize u v (q i))
        (normalize_generic u v huv q hq).g2 (normalizedSupport u v huv q S)
        (eventEquiv u v huv q root) =
      (DaughterFirstReturn.daughterPointList q hq.g2 S root).map (normalize u v) := by
  classical
  let Q := fun i => normalize u v (q i)
  let E := eventEquiv u v huv q
  let T := normalizedSupport u v huv q S
  let p := smoothingDartPermutation q hq.g2 S
  let s := smoothingDartPermutation Q (normalize_generic u v huv q hq).g2 T
  have hword : PermutationOrbits.orbitWord s (E root) =
      (PermutationOrbits.orbitWord p root).map E :=
    orbitWord_map_equiv E p s (eventEquiv_dart u v huv q hq S) root
  have hret : (fun x => decide (DaughterFirstReturn.retainedCorner Q T (E x))) =
      (fun x => decide (DaughterFirstReturn.retainedCorner q S x)) := by
    funext x
    simp only [Q, T, E, eventEquiv_retained]
  rw [DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map,
    DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map]
  change ((PermutationOrbits.orbitWord s (E root)).filter
      (fun x => decide (DaughterFirstReturn.retainedCorner Q T x))).map
        (polygonEventPoint Q) = _
  rw [hword, ← DaughterPointListFilter.map_filter_comp E
    (fun x => decide (DaughterFirstReturn.retainedCorner Q T x)), hret,
    List.map_map, List.map_map]
  apply List.map_congr_left
  intro x _
  exact eventEquiv_point u v huv q hq x

theorem normalization_daughterGeneric (S : Finset (PolygonCrossing q))
    (root : PolygonEvent q)
    (hD : CyclicGeneric (DaughterFirstReturn.daughterVertex q hq.g2 S root)) :
    CyclicGeneric (DaughterFirstReturn.daughterVertex (fun i => normalize u v (q i))
      (normalize_generic u v huv q hq).g2 (normalizedSupport u v huv q S)
      (eventEquiv u v huv q root)) := by
  apply TruncationPointListAdapter.cyclicGeneric_of_pointList_eq
    (fun i => normalize u v (DaughterFirstReturn.daughterVertex q hq.g2 S root i))
  · exact normalize_generic u v huv _ hD
  · simpa only [DaughterFirstReturn.daughterPointList, List.map_ofFn] using
      (normalization_daughterPointList u v huv q hq S root).symm

theorem normalization_daughterAmplitude (S : Finset (PolygonCrossing q))
    (root : PolygonEvent q)
    (hD : CyclicGeneric (DaughterFirstReturn.daughterVertex q hq.g2 S root)) :
    polygonAmplitude (DaughterFirstReturn.daughterVertex q hq.g2 S root) hD =
      polygonAmplitude (DaughterFirstReturn.daughterVertex (fun i => normalize u v (q i))
        (normalize_generic u v huv q hq).g2 (normalizedSupport u v huv q S)
        (eventEquiv u v huv q root))
        (normalization_daughterGeneric u v huv q hq S root hD) := by
  apply (normalize_amplitude u v huv _ hD).trans
  apply TruncationPointListAdapter.polygonAmplitude_eq_of_pointList_eq
  simpa only [DaughterFirstReturn.daughterPointList, List.map_ofFn] using
    (normalization_daughterPointList u v huv q hq S root).symm

theorem normalization_auxiliaryGenericity
    (hAux : GeometricSmoothingWeights.auxiliaryGenericity q hq) :
    GeometricSmoothingWeights.auxiliaryGenericity (fun i => normalize u v (q i))
      (normalize_generic u v huv q hq) := by
  intro T hT y
  obtain ⟨S,rfl⟩ := (crossingEquiv u v huv q).finsetCongr.surjective T
  obtain ⟨x,rfl⟩ := (eventEquiv u v huv q).surjective y
  apply normalization_daughterGeneric u v huv q hq S x
  exact hAux S ((normalization_nonalternating_iff u v huv q hq S).mpr hT) x

open GeometricSmoothingWeights PermutationOrbits in
theorem normalization_componentAmplitude
    (hRI : GLSSWRootIndependence)
    (hAux : auxiliaryGenericity q hq)
    (S : Finset (PolygonCrossing q))
    (hS : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (c : Component (smoothingDartPermutation q hq.g2 S)) :
    componentAmplitude q hq S hAux hS c =
      componentAmplitude (fun i => normalize u v (q i)) (normalize_generic u v huv q hq)
        (normalizedSupport u v huv q S) (normalization_auxiliaryGenericity u v huv q hq hAux)
        ((normalization_nonalternating_iff u v huv q hq S).mp hS)
        (normalizedComponentEquiv u v huv q hq S c) := by
  let Q := fun i => normalize u v (q i)
  let hQ := normalize_generic u v huv q hq
  let T := normalizedSupport u v huv q S
  let E := eventEquiv u v huv q
  let C := normalizedComponentEquiv u v huv q hq S
  let x := componentRoot q hq S c
  let y := componentRoot Q hQ T (C c)
  have hx : CyclicGeneric (DaughterFirstReturn.daughterVertex q hq.g2 S x) :=
    hAux S hS x
  have hxy : (smoothingDartPermutation Q hQ.g2 T).SameCycle (E x) y := by
    apply (componentOf_eq_iff _ _ _).mp
    calc
      componentOf (smoothingDartPermutation Q hQ.g2 T) (E x) =
          C (componentOf (smoothingDartPermutation q hq.g2 S) x) := rfl
      _ = C c := by rw [componentRoot_sameComponent]
      _ = componentOf (smoothingDartPermutation Q hQ.g2 T) y :=
        (componentRoot_sameComponent Q hQ T (C c)).symm
  exact (normalization_daughterAmplitude u v huv q hq S x hx).trans
    (DaughterRootAmplitude.daughterPolygonAmplitude_eq_of_sameCycle hRI Q hQ.g2 T
      (E x) y hxy (normalization_daughterGeneric u v huv q hq S x hx))

open GeometricSmoothingWeights PermutationOrbits in
theorem normalization_componentAmplitudeProduct
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq)
    (S : Finset (PolygonCrossing q))
    (hS : PolygonNonalternation.polygonNonalternating q hq.g2 S) :
    componentAmplitudeProduct q hq S hAux hS =
      componentAmplitudeProduct (fun i => normalize u v (q i))
        (normalize_generic u v huv q hq) (normalizedSupport u v huv q S)
        (normalization_auxiliaryGenericity u v huv q hq hAux)
        ((normalization_nonalternating_iff u v huv q hq S).mp hS) := by
  unfold componentAmplitudeProduct
  apply Fintype.prod_equiv (normalizedComponentEquiv u v huv q hq S)
  intro c
  exact normalization_componentAmplitude u v huv q hq hRI hAux S hS c

open GeometricSmoothingWeights GeometricSmoothingSumTransport in
/-- The full separating primitive is unchanged by positive affine normalization.
The only root-change premise is the explicitly authorized root independence;
the original auxiliary daughter-genericity hypothesis is transported, not strengthened. -/
theorem normalization_separatingSmoothingSum
    (hRI : GLSSWRootIndependence) (hAux : auxiliaryGenericity q hq) :
    separatingSmoothingSum q hq hAux =
      separatingSmoothingSum (fun i => normalize u v (q i))
        (normalize_generic u v huv q hq)
        (normalization_auxiliaryGenericity u v huv q hq hAux) := by
  let Q := fun i => normalize u v (q i)
  let hQ := normalize_generic u v huv q hq
  let E := separatingSupportEquiv q hq Q hQ (crossingEquiv u v huv q)
    (normalization_nonalternating_iff u v huv q hq)
  unfold separatingSmoothingSum
  apply Fintype.sum_equiv E
  intro S
  have hcard : (E S).val.card = S.val.card := Finset.card_map _
  rw [hcard]
  congr 1
  exact normalization_componentAmplitudeProduct u v huv q hq hRI hAux S.val S.property

end DirectGLSSW.EdgeAffineNormalization

























