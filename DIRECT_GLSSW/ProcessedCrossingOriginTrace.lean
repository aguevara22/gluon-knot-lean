import ProcessedCrossingOriginStep
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable
namespace MarkedParentTrace

def crossingOrigin {s t : MarkedParentState} (h : MarkedParentTrace s t) :
    Fin t.1.nCrossing ↪ Fin s.1.nCrossing :=
  match h with
  | .nil _ => Function.Embedding.refl _
  | .cons step tail => tail.crossingOrigin.trans step.crossingOrigin

theorem crossingOrigin_incoming {s t : MarkedParentState} (h : MarkedParentTrace s t) :
    ∀ (d : Fin t.1.nCrossing) (i : Fin 2),
      h.arcOrigin (t.1.incoming d i) = some (s.1.incoming (h.crossingOrigin d) i) := by
  induction h with
  | nil s => intro d i; rfl
  | cons step tail ih =>
    intro d i
    change (tail.arcOrigin (_)).bind step.arcOrigin = _
    rw [ih,Option.some_bind,step.crossingOrigin_incoming]
    rfl

theorem crossingOrigin_outgoing {s t : MarkedParentState} (h : MarkedParentTrace s t) :
    ∀ (d : Fin t.1.nCrossing) (i : Fin 2),
      h.arcOrigin (t.1.outgoing d i) = some (s.1.outgoing (h.crossingOrigin d) i) := by
  induction h with
  | nil s => intro d i; rfl
  | cons step tail ih =>
    intro d i
    change (tail.arcOrigin (_)).bind step.arcOrigin = _
    rw [ih,Option.some_bind,step.crossingOrigin_outgoing]
    rfl

theorem crossingOrigin_point {s t : MarkedParentState} (h : MarkedParentTrace s t) :
    ∀ d : Fin t.1.nCrossing,
      t.1.vertexPoint (t.1.crossingVertex d) =
        s.1.vertexPoint (s.1.crossingVertex (h.crossingOrigin d)) := by
  induction h with
  | nil s => intro d; rfl
  | cons step tail ih =>
    intro d
    exact (ih d).trans (step.crossingOrigin_point (tail.crossingOrigin d))

theorem crossingOrigin_through {s t : MarkedParentState} (h : MarkedParentTrace s t) :
    ∀ d : Fin t.1.nCrossing, t.1.through d = s.1.through (h.crossingOrigin d) := by
  induction h with
  | nil s => intro d; rfl
  | cons step tail ih =>
    intro d
    exact (ih d).trans (step.crossingOrigin_through (tail.crossingOrigin d))

end MarkedParentTrace
end DirectGLSSW.HOMFLY
