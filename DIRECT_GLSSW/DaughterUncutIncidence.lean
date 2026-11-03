import DaughterUnionNonalternation
import SpectatorDaughterWords
import UncutDaughterEdge

set_option autoImplicit false
namespace DirectGLSSW.DaughterUncutIncidence
open PrimitiveEdgeGrouping DaughterFirstReturn DaughterParentCrossing DaughterEventLift
  DaughterPairingLift DaughterG2Inheritance PolygonNonalternation PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (e : Fin n) (U : OffEdgeSupport P hP e)

abbrev edgeDaughter := daughterVertex P hP.g2 U.val (Sum.inl e)
abbrev edgeDaughterG2 : cyclicNoTripleIntersections (edgeDaughter P hP e U) :=
  daughter_cyclicNoTripleIntersections P hP.g2 U.val hP.size_ge_three U.property.1 (Sum.inl e)

theorem edgeDaughter_size_pos : 0 < Fintype.card (CornerCoord P hP.g2 U.val (Sum.inl e)) := by
  have h := DaughterTurns.daughterVertexCount_ge_three P hP.g2 U.val hP.size_ge_three hP.g1
    (Sum.inl e) (by trivial)
  omega

def daughterChosenEdge : Fin (Fintype.card (CornerCoord P hP.g2 U.val (Sum.inl e))) :=
  ⟨0,edgeDaughter_size_pos P hP e U⟩

@[simp] theorem daughterChosenEdge_val : (daughterChosenEdge P hP e U).val = 0 := rfl

theorem chosenEdge_start_event :
    orbitEventAt P hP.g2 U.val (Sum.inl e)
      (cornerEnumeration P hP.g2 U.val (Sum.inl e) (daughterChosenEdge P hP e U)).val = Sum.inl e :=
  eventLift_zero P hP U.val U.property.1 (Sum.inl e) (by trivial) (edgeDaughter_size_pos P hP e U)

theorem daughterChosenEdge_carrier :
    daughterCarrier P hP.g2 U.val (Sum.inl e) (daughterChosenEdge P hP e U) = e := by
  unfold daughterCarrier
  rw [chosenEdge_start_event]
  rfl

theorem whole_edge_vertices :
    edgeDaughter P hP e U (daughterChosenEdge P hP e U) = P e ∧
    edgeDaughter P hP e U (cyclicSuccessor (daughterChosenEdge P hP e U)) = P (cyclicSuccessor e) :=
  UncutDaughterEdge.uncut_anchor_vertices P hP.g2 hP.size_ge_three U.val (Sum.inl e)
    (by trivial) e U.property.2 (daughterChosenEdge P hP e U) (chosenEdge_start_event P hP e U)

theorem whole_edge_tangent :
    cyclicTangent (edgeDaughter P hP e U) (daughterChosenEdge P hP e U) = cyclicTangent P e :=
  UncutDaughterEdge.uncut_anchor_tangent P hP.g2 hP.size_ge_three U.val (Sum.inl e)
    (by trivial) e U.property.2 (daughterChosenEdge P hP e U) (chosenEdge_start_event P hP e U)

theorem incident_parent_iff (c : PolygonCrossing (edgeDaughter P hP e U)) :
    Incident P e (parentCrossing P hP U.val U.property.1 (Sum.inl e) (by trivial) c) ↔
    Incident (edgeDaughter P hP e U) (daughterChosenEdge P hP e U) c :=
  parentCrossing_incident_iff P hP U.val U.property.1 (Sum.inl e) (by trivial)
    (daughterChosenEdge P hP e U) e (daughterChosenEdge_carrier P hP e U) c

def parentEdgeEmbedding : EdgeChord (edgeDaughter P hP e U) (daughterChosenEdge P hP e U) ↪
    PolygonCrossing P where
  toFun c := parentCrossing P hP U.val U.property.1 (Sum.inl e) (by trivial) c.val
  inj' := fun _ _ h => Subtype.ext
    (parentCrossing_injective P hP U.val U.property.1 (Sum.inl e) (by trivial) h)

theorem parentEdgeEmbedding_incident
    (c : EdgeChord (edgeDaughter P hP e U) (daughterChosenEdge P hP e U)) :
    Incident P e (parentEdgeEmbedding P hP e U c) :=
  (incident_parent_iff P hP e U c.val).mpr c.property

theorem exists_preimage_of_completion (T : EdgeCompletion P hP e U)
    (c : PolygonCrossing P) (hc : c ∈ T.val) :
    ∃ d : EdgeChord (edgeDaughter P hP e U) (daughterChosenEdge P hP e U),
      parentEdgeEmbedding P hP e U d = c := by
  have hcU : c ∉ U.val := fun h => U.property.2 c h (T.property.1 c hc)
  obtain ⟨hf,ht⟩ := SpectatorDaughterWords.completion_dart_visits_in_edge_component P hP e U T c hc
  let c' : ActualLocalSupports.LocalCrossing P (smoothingDartPermutation P hP.g2 U.val) U.val
      (componentOf (smoothingDartPermutation P hP.g2 U.val) (Sum.inl e)) := ⟨c,hcU,hf,ht⟩
  obtain ⟨d,hd⟩ := (DaughterLocalCrossingEquiv.localCrossingEquiv P hP U.val U.property.1
    (Sum.inl e) (by trivial)).surjective c'
  have he : parentCrossing P hP U.val U.property.1 (Sum.inl e) (by trivial) d = c :=
    congrArg Subtype.val hd
  have hi : Incident (edgeDaughter P hP e U) (daughterChosenEdge P hP e U) d :=
    (incident_parent_iff P hP e U d).mp (he.symm ▸ T.property.1 c hc)
  exact ⟨⟨d,hi⟩,he⟩

theorem map_parentEdgeEmbedding_eq_liftedSupport
    (T : Finset (EdgeChord (edgeDaughter P hP e U) (daughterChosenEdge P hP e U))) :
    T.map (parentEdgeEmbedding P hP e U) =
      liftedSupport P hP U.val U.property.1 (Sum.inl e) (by trivial) (T.image Subtype.val) := by
  ext c
  simp only [Finset.mem_map,liftedSupport,Finset.mem_image]
  constructor
  · rintro ⟨d,hd,rfl⟩
    exact ⟨d.val,⟨d,hd,rfl⟩,rfl⟩
  · rintro ⟨d,⟨a,ha,rfl⟩,he⟩
    exact ⟨a,ha,he⟩













end
end DirectGLSSW.DaughterUncutIncidence
