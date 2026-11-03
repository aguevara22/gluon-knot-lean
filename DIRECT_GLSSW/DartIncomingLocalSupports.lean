import RootedOrbitRankTransport
import NonalternatingEndpointTransport
import DirectGLSSW.DaughterFirstReturn

set_option autoImplicit false
namespace DirectGLSSW.DartIncomingLocalSupports
open DaughterFirstReturn PermutationOrbits ActualLocalSupports LocalCoordinates
open ChordNonalternation FiniteCycleOrder NonalternatingEndpointTransport
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : ℕ} (P : Fin n → PlanarPoint K) (hG2 : cyclicNoTripleIntersections P)
variable (S : Finset (PolygonCrossing P)) (root : PolygonEvent P)

theorem dart_to_incoming_intertwine (x : PolygonEvent P) :
    smoothingPairing P S (smoothingDartPermutation P hG2 S x) =
      smoothingIncomingPermutation P hG2 S (smoothingPairing P S x) := by
  simp only [smoothingDartPermutation_apply,smoothingIncomingPermutation_apply,
    smoothingPairing_apply]
  rw [smoothingPairingMap_involutive P S _,smoothingPairingMap_involutive P S _]

theorem paired_component_iff (x : PolygonEvent P) :
    componentOf (smoothingIncomingPermutation P hG2 S) (smoothingPairing P S x) =
        componentOf (smoothingIncomingPermutation P hG2 S) (smoothingPairing P S root) ↔
      componentOf (smoothingDartPermutation P hG2 S) x =
        componentOf (smoothingDartPermutation P hG2 S) root := by
  rw [componentOf_eq_iff,componentOf_eq_iff]
  exact (sameCycle_iff_of_intertwining (smoothingPairing P S)
    (smoothingDartPermutation P hG2 S) (smoothingIncomingPermutation P hG2 S)
    (dart_to_incoming_intertwine P hG2 S) x root).symm

theorem unselected_component_iff (c : PolygonCrossing P) (hc : c ∉ S) (b : Bool) :
    componentOf (smoothingIncomingPermutation P hG2 S) (Sum.inr (c,b)) =
        componentOf (smoothingIncomingPermutation P hG2 S) (smoothingPairing P S root) ↔
      componentOf (smoothingDartPermutation P hG2 S) (Sum.inr (c,b)) =
        componentOf (smoothingDartPermutation P hG2 S) root := by
  have hfix := pairing_fixes_noncorner P S (Sum.inr (c,b)) hc
  simpa only [hfix] using paired_component_iff P hG2 S root (Sum.inr (c,b))

/-- Actual old local crossings are unchanged; the incoming component is rooted
at the paired retained event, which need not equal the original dart root. -/
def dartIncomingLocalEquiv :
    LocalCrossing P (smoothingDartPermutation P hG2 S) S
      (componentOf (smoothingDartPermutation P hG2 S) root) ≃
    LocalCrossing P (smoothingIncomingPermutation P hG2 S) S
      (componentOf (smoothingIncomingPermutation P hG2 S) (smoothingPairing P S root)) where
  toFun c := ⟨c.val,c.property.1,
    (unselected_component_iff P hG2 S root c.val c.property.1 false).mpr c.property.2.1,
    (unselected_component_iff P hG2 S root c.val c.property.1 true).mpr c.property.2.2⟩
  invFun c := ⟨c.val,c.property.1,
    (unselected_component_iff P hG2 S root c.val c.property.1 false).mp c.property.2.1,
    (unselected_component_iff P hG2 S root c.val c.property.1 true).mp c.property.2.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem dartIncomingLocalEquiv_val (c : LocalCrossing P (smoothingDartPermutation P hG2 S) S
    (componentOf (smoothingDartPermutation P hG2 S) root)) :
    (dartIncomingLocalEquiv P hG2 S root c).val = c.val := rfl

theorem localEndpoint_incoming_val
    (c : LocalCrossing P (smoothingDartPermutation P hG2 S) S
      (componentOf (smoothingDartPermutation P hG2 S) root)) (b : Bool) :
    (localEndpoint P (smoothingIncomingPermutation P hG2 S) S
      (componentOf (smoothingIncomingPermutation P hG2 S) (smoothingPairing P S root))
      ⟨smoothingPairing P S root,rfl⟩ (dartIncomingLocalEquiv P hG2 S root c,b)).val =
    (localEndpoint P (smoothingDartPermutation P hG2 S) S
      (componentOf (smoothingDartPermutation P hG2 S) root) ⟨root,rfl⟩ (c,b)).val := by
  let x := localVisitLift P (smoothingDartPermutation P hG2 S) S
    (componentOf (smoothingDartPermutation P hG2 S) root) c b
  have h := RootedOrbitRankTransport.orbitRank_map_val (smoothingPairing P S)
    (smoothingDartPermutation P hG2 S) (smoothingIncomingPermutation P hG2 S)
    (dart_to_incoming_intertwine P hG2 S) root x
  have hf : RootedOrbitRankTransport.fibreEquiv (smoothingPairing P S)
      (smoothingDartPermutation P hG2 S) (smoothingIncomingPermutation P hG2 S)
      (dart_to_incoming_intertwine P hG2 S) root x =
      localVisitLift P (smoothingIncomingPermutation P hG2 S) S
        (componentOf (smoothingIncomingPermutation P hG2 S) (smoothingPairing P S root))
        (dartIncomingLocalEquiv P hG2 S root c) b := by
    apply Subtype.ext
    cases b <;> exact pairing_fixes_noncorner P S _ c.property.1
  rw [hf] at h
  simpa [localEndpoint,rootedEnumeration,x] using h

theorem local_nonalternating_dart_iff_incoming
    (L : Finset (LocalCrossing P (smoothingDartPermutation P hG2 S) S
      (componentOf (smoothingDartPermutation P hG2 S) root))) :
    Nonalternating (localEndpoint P (smoothingDartPermutation P hG2 S) S
      (componentOf (smoothingDartPermutation P hG2 S) root) ⟨root,rfl⟩) L ↔
    Nonalternating (localEndpoint P (smoothingIncomingPermutation P hG2 S) S
      (componentOf (smoothingIncomingPermutation P hG2 S) (smoothingPairing P S root))
      ⟨smoothingPairing P S root,rfl⟩)
      (L.map (dartIncomingLocalEquiv P hG2 S root).toEmbedding) := by
  rw [nonalternating_map]
  constructor <;> intro h c hc d hd hcd <;>
    simpa only [Equiv.toEmbedding_apply,strictCyclicBetween,Fin.lt_def,localEndpoint_incoming_val] using h c hc d hd hcd








end
end DirectGLSSW.DartIncomingLocalSupports
