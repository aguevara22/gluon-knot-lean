import LowestRowContract.Contract
import HOMFLYOrbitEmbedding

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ComponentRestrictionComparison
open DirectGLSSW HOMFLY PermutationOrbits

variable {D : PLLinkDiagram} {C : diagramComponent D}
variable (R : LowestRowContract.ComponentRestriction D C)

def arcEmbedding (a : Fin R.diagram.nArc) : Fin D.nArc := (R.arcEquiv a).val

theorem arcEmbedding_injective : Function.Injective (arcEmbedding R) := by
  intro a b h
  apply R.arcEquiv.injective
  exact Subtype.ext h

theorem arcEmbedding_continuation (a : Fin R.diagram.nArc) :
    arcEmbedding R (R.diagram.continuation a) = D.continuation (arcEmbedding R a) :=
  R.continuation_eq a

noncomputable def rootedFibreEquiv (r : Fin R.diagram.nArc) :
    Fibre R.diagram.continuation (componentOf R.diagram.continuation r) ≃
      Fibre D.continuation (componentOf D.continuation (arcEmbedding R r)) :=
  orbitFibreEquivOfEmbedding R.diagram.continuation D.continuation
    (arcEmbedding R) (arcEmbedding_injective R) (arcEmbedding_continuation R) r

@[simp] theorem rootedFibreEquiv_val (r : Fin R.diagram.nArc)
    (x : Fibre R.diagram.continuation (componentOf R.diagram.continuation r)) :
    (rootedFibreEquiv R r x).val = arcEmbedding R x.val := by
  exact orbitFibreEquivOfEmbedding_val R.diagram.continuation D.continuation
    (arcEmbedding R) (arcEmbedding_injective R) (arcEmbedding_continuation R) r x

theorem rootedOrbitPosition_transport (r : Fin R.diagram.nArc)
    (x : Fibre R.diagram.continuation (componentOf R.diagram.continuation r)) :
    ((orbitEnumeration D.continuation (arcEmbedding R r)).symm
      (rootedFibreEquiv R r x)).val =
    ((orbitEnumeration R.diagram.continuation r).symm x).val := by
  exact orbitPosition_embedding R.diagram.continuation D.continuation
    (arcEmbedding R) (arcEmbedding_injective R) (arcEmbedding_continuation R) r x

theorem rootedOrbitOrder_transport (r : Fin R.diagram.nArc)
    (x y : Fibre R.diagram.continuation (componentOf R.diagram.continuation r)) :
    (((orbitEnumeration D.continuation (arcEmbedding R r)).symm
        (rootedFibreEquiv R r x)).val <
      ((orbitEnumeration D.continuation (arcEmbedding R r)).symm
        (rootedFibreEquiv R r y)).val) ↔
    (((orbitEnumeration R.diagram.continuation r).symm x).val <
      ((orbitEnumeration R.diagram.continuation r).symm y).val) := by
  rw [rootedOrbitPosition_transport R r x, rootedOrbitPosition_transport R r y]

/-- The actual incoming port of a restricted crossing is transported to the
corresponding incoming port of the ambient diagram. -/
theorem rootedFibreEquiv_incoming_val (r : Fin R.diagram.nArc)
    (c : Fin R.diagram.nCrossing) (i : Fin 2)
    (hc : componentOf R.diagram.continuation (R.diagram.incoming c i) =
      componentOf R.diagram.continuation r) :
    (rootedFibreEquiv R r ⟨R.diagram.incoming c i, hc⟩).val =
      D.incoming (R.crossingEquiv c).val i := by
  rw [rootedFibreEquiv_val]
  exact R.incoming_eq c i

theorem rootedOrbitPosition_incoming_transport (r : Fin R.diagram.nArc)
    (c : Fin R.diagram.nCrossing) (i : Fin 2)
    (hc : componentOf R.diagram.continuation (R.diagram.incoming c i) =
      componentOf R.diagram.continuation r) :
    ((orbitEnumeration D.continuation (arcEmbedding R r)).symm
      (rootedFibreEquiv R r ⟨R.diagram.incoming c i, hc⟩)).val =
    ((orbitEnumeration R.diagram.continuation r).symm
      ⟨R.diagram.incoming c i, hc⟩).val :=
  rootedOrbitPosition_transport R r ⟨R.diagram.incoming c i, hc⟩

end DirectGLSSW.HOMFLY.ComponentRestrictionComparison
