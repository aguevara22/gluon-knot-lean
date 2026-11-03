import HOMFLYCutUnaffectedOrder

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY
open PermutationOrbits

/-- A traversal's own base arc identifies its component's exact orbit
coordinates; no arbitrary-rank invariance is assumed. -/
theorem visitPosition_orbitEnumeration {D : PLLinkDiagram} (T : BasedTraversal D)
    (root : Fin D.nArc)
    (hroot : (T.baseArc (componentOf D.continuation root)).val = root)
    (j : Fin (Fintype.card (Fibre D.continuation (componentOf D.continuation root)))) :
    visitPosition T (orbitEnumeration D.continuation root j).val = j.val := by
  have he := (orbitEnumeration D.continuation root j).property
  rw [visitPosition_eq_orbitPosition_of_baseArc T _ root
    (by rw [he]; exact hroot) he]
  exact congrArg Fin.val ((orbitEnumeration D.continuation root).symm_apply_apply j)

theorem visitRank_orbitEnumeration {D : PLLinkDiagram} (T : BasedTraversal D)
    (root : Fin D.nArc)
    (hroot : (T.baseArc (componentOf D.continuation root)).val = root)
    (j : Fin (Fintype.card (Fibre D.continuation (componentOf D.continuation root)))) :
    visitRank T (orbitEnumeration D.continuation root j).val =
      (T.componentIndex (componentOf D.continuation root), j.val) := by
  unfold visitRank
  rw [(orbitEnumeration D.continuation root j).property,
    visitPosition_orbitEnumeration T root hroot j]

/-- Incoming ports at distinct retained crossings cannot coincide with one
of the two deleted ports. -/
theorem incoming_ne_of_crossing_ne (D : PLLinkDiagram) (c d : Fin D.nCrossing)
    (hdc : d ≠ c) (i j : Fin 2) : D.incoming d i ≠ D.incoming c j := by
  intro h
  apply hdc
  apply D.crossingVertex_injective
  calc
    D.crossingVertex d = D.arcTarget (D.incoming d i) := (D.incoming_target d i).symm
    _ = D.arcTarget (D.incoming c j) := congrArg D.arcTarget h
    _ = D.crossingVertex c := D.incoming_target c j

end DirectGLSSW.HOMFLY




