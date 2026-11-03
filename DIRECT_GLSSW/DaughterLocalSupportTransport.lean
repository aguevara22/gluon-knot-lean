import DaughterDartNonalternation
import DartIncomingLocalSupports
import DaughterPairingLift
import DirectGLSSW.TwoStageRefinement

set_option autoImplicit false
namespace DirectGLSSW.DaughterLocalSupportTransport
open DaughterFirstReturn DaughterG2Inheritance DaughterLocalCrossingEquiv DaughterParentCrossing
open DaughterDartNonalternation DartIncomingLocalSupports DaughterPairingLift
open PolygonNonalternation PermutationOrbits ActualLocalSupports LocalCoordinates ChordNonalternation
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

abbrev IncomingLocal := LocalCrossing P (smoothingIncomingPermutation P hP.g2 S) S
  (componentOf (smoothingIncomingPermutation P hP.g2 S) (smoothingPairing P S root))

def incomingCrossingEquiv : PolygonCrossing (daughterVertex P hP.g2 S root) ≃
    IncomingLocal P hP S root :=
  (localCrossingEquiv P hP S hS root hroot).trans (dartIncomingLocalEquiv P hP.g2 S root)

theorem incomingCrossingEquiv_val (c : PolygonCrossing (daughterVertex P hP.g2 S root)) :
    (incomingCrossingEquiv P hP S hS root hroot c).val = parentCrossing P hP S hS root hroot c := rfl

def incomingSupport (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root))) :
    Finset (IncomingLocal P hP S root) := T.map (incomingCrossingEquiv P hP S hS root hroot).toEmbedding

theorem incomingSupport_card (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root))) :
    (incomingSupport P hP S hS root hroot T).card = T.card := Finset.card_map _

theorem incomingSupport_parent_image (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root))) :
    (incomingSupport P hP S hS root hroot T).image Subtype.val =
      liftedSupport P hP S hS root hroot T := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨d,hd,hdc⟩ := Finset.mem_image.mp hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hd
    exact Finset.mem_map.mpr ⟨a,ha,hdc⟩
  · intro hc
    obtain ⟨a,ha,hac⟩ := Finset.mem_map.mp hc
    exact Finset.mem_image.mpr ⟨incomingCrossingEquiv P hP S hS root hroot a,
      Finset.mem_map.mpr ⟨a,ha,rfl⟩,hac⟩

theorem daughter_nonalternating_iff_incomingLocal
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root))) :
    polygonNonalternating (daughterVertex P hP.g2 S root)
      (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T ↔
    Nonalternating (localEndpoint P (smoothingIncomingPermutation P hP.g2 S) S
      (componentOf (smoothingIncomingPermutation P hP.g2 S) (smoothingPairing P S root))
      ⟨smoothingPairing P S root,rfl⟩) (incomingSupport P hP S hS root hroot T) := by
  have h := (daughter_nonalternating_iff_dartLocal P hP S hS root hroot T).trans
    (local_nonalternating_dart_iff_incoming P hP.g2 S root
      (T.map (localCrossingEquiv P hP S hS root hroot).toEmbedding))
  simpa only [Finset.map_map] using h

/-- Exact support bijection on the actual incoming component used by TwoStageRefinement. -/
def localSupportEquiv :
    {T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)) //
      polygonNonalternating (daughterVertex P hP.g2 S root)
        (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T} ≃
    {L : Finset (IncomingLocal P hP S root) //
      Nonalternating (localEndpoint P (smoothingIncomingPermutation P hP.g2 S) S
        (componentOf (smoothingIncomingPermutation P hP.g2 S) (smoothingPairing P S root))
        ⟨smoothingPairing P S root,rfl⟩) L} :=
  (incomingCrossingEquiv P hP S hS root hroot).finsetCongr.subtypeEquiv
    (daughter_nonalternating_iff_incomingLocal P hP S hS root hroot)

theorem localSupportEquiv_apply
    (T : {T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root)) //
      polygonNonalternating (daughterVertex P hP.g2 S root)
        (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T}) :
    (localSupportEquiv P hP S hS root hroot T).val = incomingSupport P hP S hS root hroot T.val := rfl

theorem local_nonalternating_root_iff {m : ℕ} (Q : Fin m → PlanarPoint ℝ)
    (p : Equiv.Perm (PolygonEvent Q)) (U : Finset (PolygonCrossing Q))
    (A : Component p) (x y : Fibre p A) (L : Finset (LocalCrossing Q p U A)) :
    Nonalternating (localEndpoint Q p U A x) L ↔ Nonalternating (localEndpoint Q p U A y) L := by
  classical
  let family : LocalSupports Q p U := Function.update (fun _ => ∅) A L
  simpa [family] using local_nonalternating_root_independent Q p U family A x y

theorem daughter_nonalternating_iff_incomingLocal_at_root
    (xA : Fibre (smoothingIncomingPermutation P hP.g2 S)
      (componentOf (smoothingIncomingPermutation P hP.g2 S) (smoothingPairing P S root)))
    (T : Finset (PolygonCrossing (daughterVertex P hP.g2 S root))) :
    polygonNonalternating (daughterVertex P hP.g2 S root)
      (daughter_cyclicNoTripleIntersections P hP.g2 S hP.size_ge_three hS root) T ↔
    Nonalternating (localEndpoint P (smoothingIncomingPermutation P hP.g2 S) S
      (componentOf (smoothingIncomingPermutation P hP.g2 S) (smoothingPairing P S root)) xA)
      (incomingSupport P hP S hS root hroot T) :=
  (daughter_nonalternating_iff_incomingLocal P hP S hS root hroot T).trans
    (local_nonalternating_root_iff P (smoothingIncomingPermutation P hP.g2 S) S _
      ⟨smoothingPairing P S root,rfl⟩ xA (incomingSupport P hP S hS root hroot T))












end
end DirectGLSSW.DaughterLocalSupportTransport
