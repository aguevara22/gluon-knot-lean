import DaughterGapNoSkip
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.DaughterClosedContainment
open DaughterFirstReturn EventSegmentGeometry
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
    (hroot : retainedCorner q S root)
include hroot

/-- An original event in a sharp side interior, on that side's original
carrier, belongs to the actual selected dart component. -/
theorem daughter_side_event_membership
    (i : Fin (Fintype.card (CornerCoord q hq.g2 S root))) (x : PolygonEvent q)
    (he : polygonEventEdge q x = polygonEventEdge q
      (orbitEventAt q hq.g2 S root (cornerEnumeration q hq.g2 S root i).val))
    (hx : edgeInterior (daughterVertex q hq.g2 S root) i (polygonEventPoint q x)) :
    PermutationOrbits.componentOf (DartPerm q hq.g2 S) x =
      PermutationOrbits.componentOf (DartPerm q hq.g2 S) root := by
  let c := cornerEnumeration q hq.g2 S root i
  let start := orbitEventAt q hq.g2 S root c.val
  let d := cornerGap q hq.g2 S root c.val (cornerSuccessor q hq.g2 S root c).val
  let z := lastDartStart q hq.g2 S root c
  let e := polygonEventEdge q start
  let u := polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three z
  obtain ⟨hd,hnext,_,hpoint,_,_⟩ := cornerSuccessor_is_firstReturn q hq.g2 S hq.size_ge_three root hroot c
  have hm : d-1<d := by omega
  have hpref := orbitPrefix_edge_parameter q hq.g2 S hq.size_ge_three root hroot c (d-1) hm
  have hzedge : polygonEventEdge q z = e := hpref.1
  have hsu : polygonEventParameter q start < u := hpref.2.trans_lt
    (polygonEventSuccessor_positive_elementary_step q hq.g2 hq.size_ge_three z).1
  have hs : daughterVertex q hq.g2 S root i =
      affinePoint (q e) (q (cyclicSuccessor e)) (polygonEventParameter q start) :=
    polygonEventPoint_eq_affine q start
  have ht : daughterVertex q hq.g2 S root (cyclicSuccessor i) =
      affinePoint (q e) (q (cyclicSuccessor e)) u := by
    change polygonEventPoint q (orbitEventAt q hq.g2 S root
      (cornerEnumeration q hq.g2 S root (cyclicSuccessor i)).val) = _
    rw [cornerEnumeration_successor,←hnext,hpoint]
    simpa only [hzedge] using
      (polygonEventSuccessor_positive_elementary_step q hq.g2 hq.size_ge_three z).2.2.2.1
  have hpx : polygonEventPoint q x =
      affinePoint (q e) (q (cyclicSuccessor e)) (polygonEventParameter q x) := by
    simpa only [he] using polygonEventPoint_eq_affine q x
  obtain ⟨r,hr0,hr1,hr⟩ := hx
  have hab : q e ≠ q (cyclicSuccessor e) := by
    intro hh
    exact (cyclicSuccessor_ne_self (by have := hq.size_ge_three; omega) e)
      ((cyclicNoncollinear_injective hq.size_ge_three q hq.g1 hh).symm)
  have hv : polygonEventParameter q x =
      polygonEventParameter q start + (u-polygonEventParameter q start)*r := by
    apply affinePoint_injective (q e) (q (cyclicSuccessor e)) hab
    rw [←hpx,hr,hs,ht]
    ext <;> simp [affinePoint] <;> ring
  have hlo : polygonEventParameter q start ≤ polygonEventParameter q x := by rw [hv]; nlinarith
  have hhi : polygonEventParameter q x < u := by rw [hv]; nlinarith
  obtain ⟨k,_,hk⟩ := gap_event_of_parameter q hq S root hroot c x he hlo hhi
  rw [hk,PermutationOrbits.componentOf_pow_apply]
  exact (PermutationOrbits.orbitEnumeration (DartPerm q hq.g2 S) root c.val).property
end DirectGLSSW.DaughterClosedContainment
