import DaughterLocalSupportTransport

set_option autoImplicit false
namespace DirectGLSSW.DaughterUnionNonalternation
open DaughterFirstReturn DaughterG2Inheritance DaughterPairingLift DaughterLocalSupportTransport
open PolygonNonalternation PermutationOrbits ActualLocalSupports LocalCoordinates ChordNonalternation
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

/-- One local support and empty supports in all other actual components. -/
theorem unionLocal_update_empty {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (p : Equiv.Perm (PolygonEvent P)) (S : Finset (PolygonCrossing P))
    (A : Component p) (L : Finset (LocalCrossing P p S A)) :
    unionLocal P p S (Function.update (fun B : Component p => (∅ : Finset (LocalCrossing P p S B))) A L) = L.image Subtype.val := by
  classical
  ext c
  change c ∈ Finset.univ.biUnion _ ↔ c ∈ L.image Subtype.val
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨B,hB⟩
    by_cases hBA : B = A
    · subst B
      simpa using hB
    · simpa [Function.update_of_ne hBA] using hB
  · intro hc
    exact ⟨A,by simpa using hc⟩

theorem local_nonalternating_update_empty {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (p : Equiv.Perm (PolygonEvent P)) (S : Finset (PolygonCrossing P))
    (roots : ComponentRoots p) (A : Component p) (L : Finset (LocalCrossing P p S A)) :
    (∀ B, Nonalternating (localEndpoint P p S B (roots B))
      ((Function.update (fun B : Component p => (∅ : Finset (LocalCrossing P p S B))) A L) B)) ↔
    Nonalternating (localEndpoint P p S A (roots A)) L := by
  constructor
  · intro h
    simpa using h A
  · intro h B
    by_cases hBA : B = A
    · subst B
      simpa using h
    · simp [Function.update_of_ne hBA]

/-- Exact one-component separating-support correspondence, assembled with the
accepted actual incoming two-stage refinement theorem. -/
theorem polygonNonalternating_union_liftedSupport_iff {n : ℕ}
    (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
    (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
    (root : PolygonEvent P) (hroot : retainedCorner P S root)
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root))) :
    polygonNonalternating P hP.g2 (S ∪ liftedSupport P hP S hS root hroot T) ↔
      polygonNonalternating (daughterVertex P hP.g2 S root)
        (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T := by
  classical
  let p := smoothingIncomingPermutation P hP.g2 S
  let A := componentOf p (smoothingPairing P S root)
  let L := incomingSupport P hP S hS root hroot T
  let family : LocalSupports P p S := Function.update (fun B : Component p => (∅ : Finset (LocalCrossing P p S B))) A L
  let roots : ComponentRoots p := fun B => Classical.choice (inferInstance : Nonempty (Fibre p B))
  have hUnion : unionLocal P p S family = liftedSupport P hP S hS root hroot T :=
    (unionLocal_update_empty P p S A L).trans (incomingSupport_parent_image P hP S hS root hroot T)
  have hglobal := TwoStageRefinement.polygonNonalternating_unionLocal_iff
    P hP.g2 hP.size_ge_three S hS roots family
  rw [hUnion] at hglobal
  have hlocal : TwoStageRefinement.LocalNonalternating P hP.g2 S roots family ↔
      Nonalternating (localEndpoint P p S A (roots A)) L :=
    local_nonalternating_update_empty P p S roots A L
  exact (hglobal.trans hlocal).trans
    (daughter_nonalternating_iff_incomingLocal_at_root P hP S hS root hroot (roots A) T).symm




end
end DirectGLSSW.DaughterUnionNonalternation
