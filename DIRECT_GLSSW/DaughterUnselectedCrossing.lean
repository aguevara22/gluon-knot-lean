import DaughterGapInterior
import RetainedGapPartition
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DaughterClosedContainment
open DaughterFirstReturn PermutationOrbits
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
    (hroot : retainedCorner q S root)
include hroot

theorem nonretained_event_in_daughter_side (x : PolygonEvent q)
    (hx : componentOf (DartPerm q hq.g2 S) x = componentOf (DartPerm q hq.g2 S) root)
    (hnot : ¬retainedCorner q S x) :
    ∃ i : Fin (Fintype.card (CornerCoord q hq.g2 S root)),
      edgeInterior (daughterVertex q hq.g2 S root) i (polygonEventPoint q x) ∧
      daughterCarrier q hq.g2 S root i = polygonEventEdge q x := by
  obtain ⟨i,k,hk0,hk,hx'⟩ := nonretained_event_in_cornerGap q hq.g2 S root hroot x hx hnot
  refine ⟨i,?_,?_⟩
  · rw [hx']
    exact gap_event_in_daughter_interior q hq S root hroot i k hk0 hk
  · rw [hx']
    exact (orbitPrefix_edge_parameter q hq.g2 S hq.size_ge_three root hroot
      (cornerEnumeration q hq.g2 S root i) k hk).1.symm

/-- Both actual unselected crossing visits in this dart component give a
physical crossing of the sharp retained polygon, with the same plane point. -/
theorem unselected_crossing_in_daughter (c : PolygonCrossing q) (hc : c ∉ S)
    (hvis : ∀ b : Bool, componentOf (DartPerm q hq.g2 S) (Sum.inr (c,b)) =
      componentOf (DartPerm q hq.g2 S) root)
    (hD : CyclicGeneric (daughterVertex q hq.g2 S root)) :
    ∃ d : PolygonCrossing (daughterVertex q hq.g2 S root),
      crossingPoint (daughterVertex q hq.g2 S root) d = crossingPoint q c := by
  obtain ⟨i,hi,hei⟩ := nonretained_event_in_daughter_side q hq S root hroot
    (Sum.inr (c,false)) (hvis false) hc
  obtain ⟨j,hj,hej⟩ := nonretained_event_in_daughter_side q hq S root hroot
    (Sum.inr (c,true)) (hvis true) hc
  change edgeInterior (daughterVertex q hq.g2 S root) i (crossingPoint q c) at hi
  change edgeInterior (daughterVertex q hq.g2 S root) j (crossingPoint q c) at hj
  have hij : i≠j := by
    intro heq
    have he := hei.symm.trans ((congrArg (daughterCarrier q hq.g2 S root) heq).trans hej)
    exact (ne_of_lt c.property.1) he
  rcases lt_or_gt_of_ne hij with hij | hji
  · let d : PolygonCrossing (daughterVertex q hq.g2 S root) := ⟨(i,j),hij,crossingPoint q c,hi,hj⟩
    exact ⟨d,(crossingPoint_eq_of_mem hD.size_ge_three _ hD.g1 d _ hi hj).symm⟩
  · let d : PolygonCrossing (daughterVertex q hq.g2 S root) := ⟨(j,i),hji,crossingPoint q c,hj,hi⟩
    exact ⟨d,(crossingPoint_eq_of_mem hD.size_ge_three _ hD.g1 d _ hj hi).symm⟩
end DirectGLSSW.DaughterClosedContainment
