import CrossingOrientationLocality
import LocalSupportConjugacy
import PolygonRebaseDiagramIso
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.PositivePolygonLocality
open PermutationOrbits PolygonDrawingBridge PolygonDrawing LocalCrossingTransport Filter Topology
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q r : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) (hr : CyclicGeneric r)
    (E : PolygonCrossing q ≃ PolygonCrossing r)
    (hl : ∀ c, (E c).val = c.val)
    (ho : ∀ x y : PolygonEvent q, (polygonEventOrder q hq.g2).lt x y ↔
      (polygonEventOrder r hr.g2).lt (polygonEventMapEquiv E x) (polygonEventMapEquiv E y))

def arcMap : Fin (positivePolygonEventDiagram q hq).nArc ≃ Fin (positivePolygonEventDiagram r hr).nArc :=
  (eventFin q).symm.trans ((polygonEventMapEquiv E).trans (eventFin r))
def crossingMap : Fin (positivePolygonEventDiagram q hq).nCrossing ≃ Fin (positivePolygonEventDiagram r hr).nCrossing :=
  (crossingFin q).symm.trans (E.trans (crossingFin r))

include hl ho in
theorem event_successor (x : PolygonEvent q) :
    polygonEventMapEquiv E (polygonEventSuccessor q hq.g2 x) =
      polygonEventSuccessor r hr.g2 (polygonEventMapEquiv E x) := by
  have h := LocalSupportConjugacy.smoothingDartPermutation_map q r hq hr E hl ho ∅ x
  simpa only [Finset.map_empty, smoothingDartPermutation_empty] using h

theorem arcMap_event (x : PolygonEvent q) : arcMap q r hq hr E (eventFin q x) = eventFin r (polygonEventMapEquiv E x) := by
  exact congrArg (fun y => eventFin r (polygonEventMapEquiv E y)) ((eventFin q).symm_apply_apply x)

theorem crossingMap_crossing (c : PolygonCrossing q) : crossingMap q r hq hr E (crossingFin q c) = crossingFin r (E c) := by
  exact congrArg (fun y => crossingFin r (E y)) ((crossingFin q).symm_apply_apply c)

include hl ho in
theorem arcMap_continuation (a) :
    arcMap q r hq hr E ((positivePolygonEventDiagram q hq).continuation a) =
      (positivePolygonEventDiagram r hr).continuation (arcMap q r hq hr E a) := by
  obtain ⟨x,rfl⟩ := (eventFin q).surjective a
  change arcMap q r hq hr E ((polygonEventDiagram q hq).continuation _) = (polygonEventDiagram r hr).continuation _
  rw [polygonEventDiagram_continuation,arcMap_event,arcMap_event,polygonEventDiagram_continuation,event_successor q r hq hr E hl ho]

theorem arcMap_outgoing (c : PolygonCrossing q) (i : Fin 2) :
    arcMap q r hq hr E ((positivePolygonEventDiagram q hq).outgoing (crossingFin q c) i) =
      (positivePolygonEventDiagram r hr).outgoing (crossingFin r (E c)) i := by
  simp only [positivePolygonEventDiagram,positiveDiagram,polygonEventDiagram,outgoingIndex,Equiv.symm_apply_apply]
  change arcMap q r hq hr E (eventFin q (visit q c i)) = eventFin r (visit r (E c) i)
  rw [arcMap_event]
  rfl

include hl ho in
def diagramIso
    (hp : ∀ c : PolygonCrossing q, (0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2)) ↔
      (0 < planarDet (cyclicTangent r (E c).val.1) (cyclicTangent r (E c).val.2))) :
    SignedDiagramIso (positivePolygonEventDiagram q hq) (positivePolygonEventDiagram r hr) where
  arcEquiv := arcMap q r hq hr E
  crossingEquiv := crossingMap q r hq hr E
  continuation_map := arcMap_continuation q r hq hr E hl ho
  incoming_map := by
    intro c i
    obtain ⟨c,rfl⟩ := (crossingFin q).surjective c
    rw [crossingMap_crossing]
    apply (positivePolygonEventDiagram r hr).continuation.injective
    rw [← arcMap_continuation q r hq hr E hl ho,
      (positivePolygonEventDiagram q hq).continuation_crossing,
      (positivePolygonEventDiagram r hr).continuation_crossing]
    exact arcMap_outgoing q r hq hr E c i
  outgoing_map := by
    intro c i
    obtain ⟨c,rfl⟩ := (crossingFin q).surjective c
    rw [crossingMap_crossing]
    exact arcMap_outgoing q r hq hr E c i
  through_map := by intro c; rfl
  overBranch_map := by
    intro c
    obtain ⟨c,rfl⟩ := (crossingFin q).surjective c
    rw [crossingMap_crossing,positivePolygonEventDiagram_overBranch,positivePolygonEventDiagram_overBranch]
    exact if_congr (hp c) rfl rfl
  crossingSign_map := by
    intro c
    rw [positivePolygonEventDiagram_crossingSign,positivePolygonEventDiagram_crossingSign]

theorem eventually_positivePolygon_signedIso {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∀ᶠ r in 𝓝 q, ∃ hr : CyclicGeneric r,
      Nonempty (SignedDiagramIso (positivePolygonEventDiagram q hq) (positivePolygonEventDiagram r hr)) := by
  filter_upwards [CrossingOrientationLocality.eventually_configuration_oriented_event_order q hq] with r h
  obtain ⟨hr,E,hl,ho,hp⟩ := h
  exact ⟨hr,⟨diagramIso q r hq hr E hl ho hp⟩⟩
end DirectGLSSW.HOMFLY.PositivePolygonLocality
