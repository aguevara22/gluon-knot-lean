import DaughterNoRetainedInterior

set_option autoImplicit false
namespace DirectGLSSW.DaughterCrossingAvoidance
open DaughterFirstReturn DaughterParentCrossing DaughterNoRetainedInterior PolygonNonalternation
noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)

theorem parentCrossing_not_mem (c : PolygonCrossing (daughterVertex P hP.g2 S root)) :
    parentCrossing P hP S hS root hroot c ∉ S := by
  let p := parentCrossing P hP S hS root hroot c
  let e := daughterCarrier P hP.g2 S root c.val.1
  have hi : PrimitiveEdgeGrouping.Incident P e p :=
    (parentCrossing_incident_iff P hP S hS root hroot c.val.1 e rfl c).mpr (Or.inl rfl)
  let v := edgeVisit P e ⟨p,hi⟩
  let y : PolygonEvent P := Sum.inr v
  intro hc
  have hy : retainedCorner P S y := hc
  have hye : polygonEventEdge P y = e := (edgeVisitSide_spec P e ⟨p,hi⟩).1
  apply no_retained_event_in_daughter_edge P hP S root hroot c.val.1 y hy hye
  change edgeInterior (daughterVertex P hP.g2 S root) c.val.1 (crossingPoint P p)
  rw [parentCrossing_point]
  exact crossingPoint_mem_left _ c

def crossingEmbeddingOutsideSupport : PolygonCrossing (daughterVertex P hP.g2 S root) ↪
    {c : PolygonCrossing P // c ∉ S} where
  toFun c := ⟨parentCrossing P hP S hS root hroot c,parentCrossing_not_mem P hP S hS root hroot c⟩
  inj' := fun _ _ h => parentCrossing_injective P hP S hS root hroot (congrArg Subtype.val h)



end
end DirectGLSSW.DaughterCrossingAvoidance
