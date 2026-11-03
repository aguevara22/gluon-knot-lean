import DirectGLSSW.MixedEdgeRetainedSuccessor
import DirectGLSSW.OrbitWordPrerequisite

set_option autoImplicit false

namespace DirectGLSSW.MixedEdgeRetainedWord

open Equiv DaughterFirstReturn MixedEdgeRetainedSuccessor PermutationOrbits

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

abbrev RetainedEvent (q : Fin n → PlanarPoint K)
    (S : Finset (PolygonCrossing q)) := {x : PolygonEvent q // retainedCorner q S x}

noncomputable instance retainedEventFintype
    (q : Fin n → PlanarPoint K) (S : Finset (PolygonCrossing q)) :
    Fintype (RetainedEvent q S) := by
  classical
  unfold RetainedEvent
  infer_instance

noncomputable def retainedPairing (q : Fin n → PlanarPoint K)
    (S : Finset (PolygonCrossing q)) : Equiv.Perm (RetainedEvent q S) :=
  (smoothingPairing q S).subtypePerm
    (fun x => (pairing_preserves_retained q S x).symm)

noncomputable def retainedOriginalSuccessor (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q)) :
    Equiv.Perm (RetainedEvent q S) := by
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq
  exact orderedCyclicSuccessor (RetainedEvent q S)

noncomputable def retainedDartPermutation (q : Fin n → PlanarPoint K)
    (hq : cyclicNoTripleIntersections q) (S : Finset (PolygonCrossing q)) :
    Equiv.Perm (RetainedEvent q S) :=
  retainedPairing q S * retainedOriginalSuccessor q hq S

theorem originalCornerNext_eq_retainedOriginalSuccessor
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (x : PolygonEvent q)
    (hx : retainedCorner q S x) :
    originalCornerNext q hq S x hx =
      (retainedOriginalSuccessor q hq S ⟨x, hx⟩).val := by
  classical
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq
  let E := polygonEventEnumeration q hq
  let P : Fin (Fintype.card (PolygonEvent q)) → Prop :=
    fun i => retainedCorner q S (E i)
  let R := {i : Fin (Fintype.card (PolygonEvent q)) // P i}
  let idx : R := ⟨E.symm x, by simpa [P] using hx⟩
  let e : RetainedEvent q S ≃o R := {
    toFun := fun y => ⟨E.symm y.val, by simpa [P] using y.property⟩
    invFun := fun y => ⟨E y.val, by simpa [P] using y.property⟩
    left_inv := by
      intro y
      apply Subtype.ext
      exact E.apply_symm_apply y.val
    right_inv := by
      intro y
      apply Subtype.ext
      exact E.symm_apply_apply y.val
    map_rel_iff' := by
      intro a b
      change E.symm a.val ≤ E.symm b.val ↔ a.val ≤ b.val
      exact E.symm.map_rel_iff
  }
  have he : e ⟨x, hx⟩ = idx := by
    apply Subtype.ext
    rfl
  have hnat := orderedCyclicSuccessor_naturality (RetainedEvent q S) e
    (⟨x, hx⟩ : RetainedEvent q S)
  have h := congrArg (fun y : R => E y.val) hnat
  rw [he] at h
  simpa [originalCornerNext, retainedOriginalSuccessor, E, R, idx, e] using h

theorem retainedDartPermutation_apply
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (x : RetainedEvent q S) :
    (retainedDartPermutation q hq S x).val =
      smoothingPairing q S (originalCornerNext q hq S x.val x.property) := by
  rw [retainedDartPermutation, Equiv.Perm.mul_apply]
  simp [retainedPairing, originalCornerNext_eq_retainedOriginalSuccessor]

theorem daughterPointList_eq_retainedOrbitWord
    (q : Fin n → PlanarPoint K) (hq : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
    (hroot : retainedCorner q S root) :
    daughterPointList q hq S root =
      (orbitWord (retainedDartPermutation q hq S) ⟨root, hroot⟩).map
        (fun x : RetainedEvent q S => polygonEventPoint q x.val) := by
  classical
  let N := Fintype.card (CornerCoord q hq S root)
  have hN : 0 < N := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨⟨0, orbitCard_pos q hq S root⟩,
      by simpa [orbitEventAt] using hroot⟩⟩
  let f : Fin N → RetainedEvent q S := fun i =>
    ⟨orbitEventAt q hq S root (cornerEnumeration q hq S root i).val,
      (cornerEnumeration q hq S root i).property⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hevent : orbitEventAt q hq S root (cornerEnumeration q hq S root i).val =
        orbitEventAt q hq S root (cornerEnumeration q hq S root j).val := by
      exact congrArg (fun z : RetainedEvent q S => z.val) hij
    have hfibre :
        (orbitEnumeration (DartPerm q hq S) root (cornerEnumeration q hq S root i).val) =
          (orbitEnumeration (DartPerm q hq S) root (cornerEnumeration q hq S root j).val) := by
      apply Subtype.ext
      exact hevent
    have hindex := (orbitEnumeration (DartPerm q hq S) root).injective hfibre
    exact (cornerEnumeration q hq S root).injective (Subtype.ext hindex)
  have hf0 : f ⟨0, hN⟩ = ⟨root, hroot⟩ := by
    apply Subtype.ext
    change orbitEventAt q hq S root
      (cornerEnumeration q hq S root ⟨0, hN⟩).val = root
    rw [cornerEnumeration_zero_eq_rootcoord q hq S root hroot hN]
    simp [orbitEventAt]
  have hstep : ∀ i, retainedDartPermutation q hq S (f i) =
      f (cyclicSuccessor i) := by
    intro i
    let c := cornerEnumeration q hq S root i
    apply Subtype.ext
    rw [retainedDartPermutation_apply]
    change smoothingPairing q S
        (originalCornerNext q hq S (orbitEventAt q hq S root c.val) c.property) =
      orbitEventAt q hq S root (cornerEnumeration q hq S root (cyclicSuccessor i)).val
    rw [cornerEnumeration_successor]
    exact (cornerSuccessor_eq_pairing_originalCornerNext q hq S root c).symm
  have hword := orbitWord_eq_of_injective_cyclicSuccessor
    (p := retainedDartPermutation q hq S) (N := N) hN f hf hstep
  rw [← hf0, hword]
  simp [daughterPointList, daughterVertex, f, N]
  funext i
  rfl

end DirectGLSSW.MixedEdgeRetainedWord









