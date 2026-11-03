import CrossingHolePerimeter
import FixedRectangleSideExact

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

-- SOURCE PREPARATION ONLY. These are inputs to the literal retained-neighbour
-- construction in CONTRACT.md; no successful compile is claimed.
theorem secantVisitHalfCell_bounds {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i h : Fin 2) :
    secantVisitLeft T c i ≤ (secantVisitHalfCell T c i h).1 ∧
    (secantVisitHalfCell T c i h).1 < (secantVisitHalfCell T c i h).2 ∧
    (secantVisitHalfCell T c i h).2 ≤ secantVisitRight T c i := by
  have hs := secantVisit_endpoints_straddle T c i
  fin_cases h <;> simp [secantVisitHalfCell] <;> constructor
  · exact hs.1
  · exact hs.2.le
  · exact hs.1.le
  · exact hs.2

theorem secantVisitHalfCell_adjacent {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i h : Fin 2)
    (hi : componentOf D.continuation (D.incoming c i)=C) :
    secantAxisAdjacent T C (secantVisitHalfCell T c i h).1
      (secantVisitHalfCell T c i h).2 := by
  fin_cases h
  · simpa [secantVisitHalfCell] using secantVisit_left_half_adjacent T C c i hi
  · simpa [secantVisitHalfCell] using secantVisit_right_half_adjacent T C c i hi

/-- A literal half-cell cannot be contained in any other actual same-component
visit window. This is the overlap-identification step used to exclude every
other star from the outside neighbour; isolation is derived, not assumed. -/
theorem secantVisitHalfCell_contained_unique {D : PLLinkDiagram} (T : BasedTraversal D)
    (c d : Fin D.nCrossing) (i j h : Fin 2)
    (hC : componentOf D.continuation (D.incoming c i)=
      componentOf D.continuation (D.incoming d j))
    (hlo : secantVisitLeft T d j ≤ (secantVisitHalfCell T c i h).1)
    (hhi : (secantVisitHalfCell T c i h).2 ≤ secantVisitRight T d j) :
    (c,i)=(d,j) := by
  by_contra hne
  have hb := secantVisitHalfCell_bounds T c i h
  rcases distinctVisitWindows_separated T c d i j hne hC with hg | hg <;>
    linarith [hb.1,hb.2.1,hb.2.2]

/-- The signed-visit order forces the actual common-cutoff window gap; this
also bounds the one-cell exterior collar after using adjacent width≤1/4. -/
theorem orderedVisitWindows_gap {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i j : Fin 2) (hij : i≠j)
    (hC : componentOf D.continuation (D.incoming c i)=
      componentOf D.continuation (D.incoming c j))
    (horder : crossingVisitTime T c i < crossingVisitTime T c j) :
    secantVisitRight T c i + 1/2 < secantVisitLeft T c j := by
  have hn : (c,i)≠(c,j) := by intro he;exact hij (congrArg Prod.snd he)
  have hs := secantVisit_endpoints_straddle T c i
  have ht := secantVisit_endpoints_straddle T c j
  rcases distinctVisitWindows_separated T c c i j hn hC with hg | hg
  · exact hg
  · linarith [hs.1,ht.2]

end
end DirectGLSSW.HOMFLY.PrincipalTurning




