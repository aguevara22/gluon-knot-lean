import ActiveArcParentReducedPairing

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

/-- Actual physical point values on the reduced orbit keep the tiny initial
edge as a literal q[0] prefix. Deletion to the incoming orbit is separate. -/
theorem reduced_parent_pointWord :
    letI := eventOrder q hR.noTriple
    letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
    (orbitWord (orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T) *
      complementRetainedPairing q hR c hc hcut S T) (complementRetainedStart q hR c hc hcut S T)).map
        (fun x => eventPoint q x.val)=
      q ⟨0,by omega⟩ ::
        (orbitWord (orderedCyclicSuccessor (ParentRetained q c hcut T) *
          physicalRetainedPairing (parent q c hcut) T) (parentRetainedStart q c hcut T)).map
            (fun x => eventPoint (parent q c hcut) x.val) := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
  rw [reduced_parent_orbitWord,List.map_cons,List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  exact parentEventMap_point q hR c hc hcut x.val

end DirectGLSSW.ActiveArc.CompatibleWords
