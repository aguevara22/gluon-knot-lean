import DaughterClosedContainment
import ActiveArcOpenSideGeometry
import ActiveArcPhysicalWords

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

noncomputable section

namespace DirectGLSSW.OneSegmentContract

open DirectGLSSW DaughterFirstReturn
open ActiveArc RetainedWords PhysicalSegments OpenCarrier Nonalternation

/-- Every side of an actual polygon daughter is a positive closed subsegment
of its labelled original edge, and no two daughter sides have that label. -/
theorem polygon_component_one_segment {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (root : PolygonEvent q) (hroot : retainedCorner q S root) :
    (∀ i : Fin (Fintype.card (CornerCoord q hq.g2 S root)),
      ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
        daughterVertex q hq.g2 S root i =
          affinePoint (q (daughterCarrier q hq.g2 S root i))
            (q (cyclicSuccessor (daughterCarrier q hq.g2 S root i))) s ∧
        daughterVertex q hq.g2 S root (cyclicSuccessor i) =
          affinePoint (q (daughterCarrier q hq.g2 S root i))
            (q (cyclicSuccessor (daughterCarrier q hq.g2 S root i))) t) ∧
    (∀ e : Fin n, ∀ i j : Fin (Fintype.card (CornerCoord q hq.g2 S root)),
      daughterCarrier q hq.g2 S root i = e →
      daughterCarrier q hq.g2 S root j = e → i = j) := by
  constructor
  · intro i
    exact DaughterClosedContainment.daughterSide_endpoint_parameters
      q hq.g2 S hq.size_ge_three root hroot i
  · intro e i j hi hj
    have hinj := daughterCarrier_injective q hq.g2 S hq.size_ge_three hNA root
    exact hinj (hi.trans hj.symm)

/-- Every dart component of a separating support has a retained root and
satisfies the polygon one-segment contract. -/
theorem polygon_all_components_one_segment {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)
    (x : PolygonEvent q) :
    ∃ root : PolygonEvent q,
      (DartPerm q hq.g2 S).SameCycle x root ∧
      retainedCorner q S root ∧
      (∀ i : Fin (Fintype.card (CornerCoord q hq.g2 S root)),
        ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
          daughterVertex q hq.g2 S root i =
            affinePoint (q (daughterCarrier q hq.g2 S root i))
              (q (cyclicSuccessor (daughterCarrier q hq.g2 S root i))) s ∧
          daughterVertex q hq.g2 S root (cyclicSuccessor i) =
            affinePoint (q (daughterCarrier q hq.g2 S root i))
              (q (cyclicSuccessor (daughterCarrier q hq.g2 S root i))) t) ∧
      (∀ e : Fin n, ∀ i j : Fin (Fintype.card (CornerCoord q hq.g2 S root)),
        daughterCarrier q hq.g2 S root i = e →
        daughterCarrier q hq.g2 S root j = e → i = j) := by
  obtain ⟨root, hcycle, hroot⟩ :=
    everyDartOrbit_hasCorner q hq.g2 S hq.size_ge_three x
  exact ⟨root, hcycle, hroot,
    polygon_component_one_segment q hq S hNA root hroot⟩

/-- Every retained physical side of any actual open-arc smoothing component,
except the terminal endpoint seam, lies in one original edge. Its edge label
occurs at most once in that component. -/
theorem retained_component_one_segment {n : ℕ}
    (q : Fin (n + 2) → PlanarPoint ℝ) (hR : Regular q)
    (S : Finset (Crossing q)) (hS : Nonalternating q hR S) :
    (∀ root : Event q,
      ∀ i : Fin (Fintype.card (Corner q hR S root)),
      (hnot : cornerEvent q hR S root i ≠ terminal q) →
      ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
        vertex q hR S root i =
          affinePoint (q (outgoingEdge q S (cornerEvent q hR S root i) hnot).castSucc)
            (q (outgoingEdge q S (cornerEvent q hR S root i) hnot).succ) a ∧
        vertex q hR S root (cyclicSuccessor i) =
          affinePoint (q (outgoingEdge q S (cornerEvent q hR S root i) hnot).castSucc)
            (q (outgoingEdge q S (cornerEvent q hR S root i) hnot).succ) b) ∧
    (∀ root : Event q,
      ∀ i j : Fin (Fintype.card (Corner q hR S root)),
      ∀ (hi : cornerEvent q hR S root i ≠ terminal q)
        (hj : cornerEvent q hR S root j ≠ terminal q),
      outgoingEdge q S (cornerEvent q hR S root i) hi =
        outgoingEdge q S (cornerEvent q hR S root j) hj → i = j) := by
  constructor
  · intro root i hnot
    let c := enumeration q hR S root i
    have hx : eventAt q hR S root c.val ≠ terminal q := by
      simpa [c, cornerEvent] using hnot
    obtain ⟨a,b,ha,hab,hb,hpoint,hnext,_⟩ :=
      retained_side_physical q hR S root c hx
    have hcyc := enumeration_cyclic q hR S root i
    have hev : eventAt q hR S root (nextCorner q hR S root c).val =
        cornerEvent q hR S root (cyclicSuccessor i) := by
      rw [← hcyc]
      rfl
    rw [hev] at hnext
    refine ⟨a,b,ha,hab,hb,?_,hnext⟩
    simpa [vertex, cornerEvent, c] using hpoint
  · intro root i j hi hj he
    have htag : edgeTag q (pairing q S (cornerEvent q hR S root i)) =
        edgeTag q (pairing q S (cornerEvent q hR S root j)) := by
      have hv := congrArg Fin.val he
      simpa [outgoingEdge, physicalEdge, cornerEvent] using hv
    exact OpenCarrier.retainedCarrier_injective q hR S hS root htag

/-- The distinguished open retained word lists exactly its physical sides;
the final-to-first terminal seam is not included. -/
theorem open_component_one_segment {n : ℕ}
    (q : Fin (n + 2) → PlanarPoint ℝ) (hR : Regular q)
    (S : Finset (Crossing q)) (hS : Nonalternating q hR S) :
    (∀ i : Fin (openCount q hR S - 1),
      ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
        vertex q hR S (start q) ⟨i.val, by
          have hi := i.isLt
          change i.val < openCount q hR S
          omega⟩ =
          affinePoint (q (openSideCarrier q hR S i).castSucc)
            (q (openSideCarrier q hR S i).succ) a ∧
        vertex q hR S (start q) ⟨i.val + 1, by
          have hi := i.isLt
          change i.val + 1 < openCount q hR S
          omega⟩ =
          affinePoint (q (openSideCarrier q hR S i).castSucc)
            (q (openSideCarrier q hR S i).succ) b) ∧
    (∀ e : Fin (n + 1), ∀ i j : Fin (openCount q hR S - 1),
      openSideCarrier q hR S i = e → openSideCarrier q hR S j = e → i = j) := by
  constructor
  · intro i
    exact OpenCarrier.openSideCarrier_physical q hR S i
  · intro e i j hi hj
    apply OpenCarrier.openSideCarrier_injective q hR S hS
    exact hi.trans hj.symm

end DirectGLSSW.OneSegmentContract

