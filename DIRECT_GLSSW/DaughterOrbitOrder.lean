import DaughterOrbitCoordinates

set_option autoImplicit false
namespace DirectGLSSW.DaughterOrbitOrder
open DaughterFirstReturn DaughterOrbitCoordinates DaughterEventCoverage PolygonNonalternation
open PermutationOrbits
noncomputable section

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (root : PolygonEvent P)

def eventRank (y : PolygonEvent P)
    (hy : componentOf (smoothingDartPermutation P hP.g2 S) y =
      componentOf (smoothingDartPermutation P hP.g2 S) root) : OrbitCoord P hP.g2 S root :=
  (orbitEnumeration (DartPerm P hP.g2 S) root).symm ⟨y,hy⟩

theorem orbitEventAt_eventRank (y : PolygonEvent P)
    (hy : componentOf (smoothingDartPermutation P hP.g2 S) y =
      componentOf (smoothingDartPermutation P hP.g2 S) root) :
    orbitEventAt P hP.g2 S root (eventRank P hP S root y hy) = y :=
  congrArg Subtype.val ((orbitEnumeration (DartPerm P hP.g2 S) root).apply_symm_apply ⟨y,hy⟩)

variable (hS : polygonNonalternating P hP.g2 S) (hroot : retainedCorner P S root)
include hS hroot

/-- The actual rank is at or after its retained start and before every later
retained start, so this includes the precise nonwrapping next-corner bound. -/
theorem eventRank_bounds (y : PolygonEvent P)
    (hy : componentOf (smoothingDartPermutation P hP.g2 S) y =
      componentOf (smoothingDartPermutation P hP.g2 S) root)
    (i : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (he : polygonEventEdge P y = daughterCarrier P hP.g2 S root i) :
    (cornerEnumeration P hP.g2 S root i).val.val ≤ (eventRank P hP S root y hy).val ∧
      ∀ j, i < j → (eventRank P hP S root y hy).val <
        (cornerEnumeration P hP.g2 S root j).val.val := by
  apply orbitCoordinate_bounds P hP S hS root hroot (eventRank P hP S root y hy) i
  rwa [orbitEventAt_eventRank]

theorem eventRank_lt_of_carrier_lt (y z : PolygonEvent P)
    (hy : componentOf (smoothingDartPermutation P hP.g2 S) y =
      componentOf (smoothingDartPermutation P hP.g2 S) root)
    (hz : componentOf (smoothingDartPermutation P hP.g2 S) z =
      componentOf (smoothingDartPermutation P hP.g2 S) root)
    (i j : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (hey : polygonEventEdge P y = daughterCarrier P hP.g2 S root i)
    (hez : polygonEventEdge P z = daughterCarrier P hP.g2 S root j)
    (hij : i < j) : eventRank P hP S root y hy < eventRank P hP S root z hz := by
  apply orbitCoordinate_lt_of_carrier_lt P hP S hS root hroot _ _ i j _ _ hij
  · rwa [orbitEventAt_eventRank]
  · rwa [orbitEventAt_eventRank]

theorem eventRank_lt_iff_parameter_lt (y z : PolygonEvent P)
    (hy : componentOf (smoothingDartPermutation P hP.g2 S) y =
      componentOf (smoothingDartPermutation P hP.g2 S) root)
    (hz : componentOf (smoothingDartPermutation P hP.g2 S) z =
      componentOf (smoothingDartPermutation P hP.g2 S) root)
    (i : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (hey : polygonEventEdge P y = daughterCarrier P hP.g2 S root i)
    (hez : polygonEventEdge P z = daughterCarrier P hP.g2 S root i) :
    eventRank P hP S root y hy < eventRank P hP S root z hz ↔
      polygonEventParameter P y < polygonEventParameter P z := by
  have hey' : polygonEventEdge P (orbitEventAt P hP.g2 S root (eventRank P hP S root y hy)) =
      daughterCarrier P hP.g2 S root i := by rwa [orbitEventAt_eventRank]
  have hez' : polygonEventEdge P (orbitEventAt P hP.g2 S root (eventRank P hP S root z hz)) =
      daughterCarrier P hP.g2 S root i := by rwa [orbitEventAt_eventRank]
  simpa only [orbitEventAt_eventRank] using orbitCoordinate_lt_iff_parameter_lt
    P hP S hS root hroot (eventRank P hP S root y hy) (eventRank P hP S root z hz) i hey' hez'

theorem retained_event_eq_start (y : PolygonEvent P)
    (hy : componentOf (smoothingDartPermutation P hP.g2 S) y =
      componentOf (smoothingDartPermutation P hP.g2 S) root)
    (i : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (he : polygonEventEdge P y = daughterCarrier P hP.g2 S root i)
    (hret : retainedCorner P S y) :
    y = orbitEventAt P hP.g2 S root (cornerEnumeration P hP.g2 S root i).val := by
  let r := eventRank P hP S root y hy
  have hry : orbitEventAt P hP.g2 S root r = y := orbitEventAt_eventRank P hP S root y hy
  have he' : polygonEventEdge P (orbitEventAt P hP.g2 S root r) =
      daughterCarrier P hP.g2 S root i := hry ▸ he
  obtain ⟨k,hk,_,hiter⟩ := orbitCoordinate_prefix P hP S hS root hroot r i he'
  have hkzero : k = 0 := by
    by_contra h
    have hkpos : 0 < k := Nat.pos_of_ne_zero h
    have hno := (cornerSuccessor_is_firstReturn P hP.g2 S hP.size_ge_three root hroot
      (cornerEnumeration P hP.g2 S root i)).2.2.2.2.2 k hkpos hk
    apply hno
    rw [← hiter,hry]
    exact hret
  rw [← hry,hiter,hkzero,pow_zero,Equiv.Perm.one_apply]

theorem nonretained_event_on_carrier_inside (y : PolygonEvent P)
    (hy : componentOf (smoothingDartPermutation P hP.g2 S) y =
      componentOf (smoothingDartPermutation P hP.g2 S) root)
    (i : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (he : polygonEventEdge P y = daughterCarrier P hP.g2 S root i)
    (hnret : ¬ retainedCorner P S y) :
    edgeInterior (daughterVertex P hP.g2 S root) i (polygonEventPoint P y) := by
  obtain ⟨j,hej,hinside⟩ := nonretained_event_in_daughter_edge P hP S root hroot y hnret hy
  have hji := daughterCarrier_injective P hP.g2 S hP.size_ge_three hS root (hej.symm.trans he)
  simpa only [hji] using hinside








end
end DirectGLSSW.DaughterOrbitOrder
