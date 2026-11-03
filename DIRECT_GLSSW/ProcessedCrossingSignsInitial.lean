import ProcessedCrossingSigns
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract

theorem MarkedParentTrace.detached_crossings_positive_of_initial
    (D : PLLinkDiagram) (T : BasedTraversal D)
    (hconn : ∀ x y : Fin D.nArc, D.continuation.SameCycle x y)
    (hpos : ∀ d : Fin D.nCrossing, crossingSign D d = Sign.pos)
    (t : MarkedParentState)
    (h : MarkedParentTrace ⟨D,T,ProcessedParentMarks.initial D T hconn⟩ t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _) (firstVisitedBranch t.2.1 c) (Sum.inl true))) :
    ∀ d : Fin R.diagram.nCrossing, crossingSign R.diagram d = Sign.pos := by
  apply h.detached_crossings_positive _ c hc R
  intro d
  exact Or.inl (hpos d)
end DirectGLSSW.HOMFLY
