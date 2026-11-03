import ActiveArcNonalternation
import ActiveArcCutRetainedWords
import DirectGLSSW.PolygonNonalternation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Nonalternation
open DirectGLSSW PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)

abbrev Support := {S : Finset (Crossing q) // Nonalternating q hR S}
instance supportFintype : Fintype (Support q hR) := by unfold Support;infer_instance

/-- The unique endpoint orbit is open; the remaining actual orbits number exactly |S|. -/
theorem closed_component_count (S : Support q hR) :
    (Finset.univ.erase (openComponent q hR.noTriple S.val)).card=S.val.card := by
  classical
  rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ]
  have hc := (nonalternating_iff_componentCount q hR S.val).mp S.property
  change Fintype.card (Component (incoming q hR.noTriple S.val))=S.val.card+1 at hc
  omega

end DirectGLSSW.ActiveArc.Nonalternation

namespace DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW ExposedOpenPrimitive PrimitiveEdgeGrouping PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2))
variable (hq : CyclicGeneric q) (he : LeftExposed q e)

theorem nonalternating_iff_parent (S : Finset (ActiveArc.Crossing (cutArc q e))) :
    Nonalternation.Nonalternating (cutArc q e) (cutArc_regular q e hq) S ↔
      PolygonNonalternation.polygonNonalternating q hq.g2 (mappedSupport q e hq he S) := by
  rw [Nonalternation.nonalternating_iff_componentCount,
    PolygonNonalternation.polygonNonalternating_iff_dart_count q hq.g2 hq.size_ge_three]
  rw [componentCount_eq_of_intertwining (dartEventEquiv q e hq he S)
    (ActiveArc.incoming (cutArc q e) (cutArc_regular q e hq).noTriple S)
    (smoothingDartPermutation q hq.g2 (mappedSupport q e hq he S))
    (dartEventEquiv_intertwine q e hq he S)]
  simp [mappedSupport]

/-- Literal physical separating supports are exactly the actual exposed off-edge supports. -/
def supportEquiv : Nonalternation.Support (cutArc q e) (cutArc_regular q e hq) ≃ OffEdgeSupport q hq e :=
  (exposedCrossingEquiv q e hq he).finsetCongr.subtypeEquiv (fun S => by
    constructor
    · intro hS
      exact ⟨(nonalternating_iff_parent q e hq he S).mp hS,
        fun c _ => leftExposed_no_incident_crossing q hq e he c⟩
    · intro hS
      exact (nonalternating_iff_parent q e hq he S).mpr hS.1)

theorem supportEquiv_val (S : Nonalternation.Support (cutArc q e) (cutArc_regular q e hq)) :
    (supportEquiv q e hq he S).val=mappedSupport q e hq he S.val := rfl

theorem supportEquiv_card (S : Nonalternation.Support (cutArc q e) (cutArc_regular q e hq)) :
    (supportEquiv q e hq he S).val.card=S.val.card := by
  rw [supportEquiv_val]
  exact Finset.card_map _

end DirectGLSSW.ActiveArc.ExposedChart
