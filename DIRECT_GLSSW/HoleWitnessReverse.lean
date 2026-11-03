import HoleWitnessCompleteness

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem crossingHoleOutsideSide_touches {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j)
    (a b u v : ℝ)
    (ha : secantAxisAdjacent T C a (secantVisitLeft T c i))
    (hb : secantAxisAdjacent T C (secantVisitRight T c i) b)
    (hu : secantAxisAdjacent T C u (secantVisitLeft T c j))
    (hv : secantAxisAdjacent T C (secantVisitRight T c j) v)
    (h k : Fin 2) (s : Fin 4) (hext : crossingHoleGridExterior h k s) :
    rectangleTouchesCrossingHole T C c i j
      (crossingHoleOutsideSide T C c i j hij hi hj horder a b u v ha hb hu hv h k s) := by
  have hcell := crossingHoleGridCell_mem T C c i j hi hj h k
  fin_cases s
  · have hk : k=0 := by simpa [crossingHoleGridExterior] using hext
    subst k
    change ∃ w, secantAxisAdjacent T C (secantVisitLeft T c j) w ∧
      (secantVisitHalfCell T c i h,(secantVisitLeft T c j,w)) ∈ secantCrossingHoleCells T C c i j
    refine ⟨crossingVisitTime T c j,secantVisit_left_half_adjacent T C c j hj,?_⟩
    simpa [crossingHoleGridCell,secantVisitHalfCell] using hcell
  · have hh : h=1 := by simpa [crossingHoleGridExterior] using hext
    subst h
    change ∃ w, secantAxisAdjacent T C w (secantVisitRight T c i) ∧
      ((w,secantVisitRight T c i),secantVisitHalfCell T c j k) ∈ secantCrossingHoleCells T C c i j
    refine ⟨crossingVisitTime T c i,secantVisit_right_half_adjacent T C c i hi,?_⟩
    simpa [crossingHoleGridCell,secantVisitHalfCell] using hcell
  · have hk : k=1 := by simpa [crossingHoleGridExterior] using hext
    subst k
    change ∃ w, secantAxisAdjacent T C w (secantVisitRight T c j) ∧
      (secantVisitHalfCell T c i h,(w,secantVisitRight T c j)) ∈ secantCrossingHoleCells T C c i j
    refine ⟨crossingVisitTime T c j,secantVisit_right_half_adjacent T C c j hj,?_⟩
    simpa [crossingHoleGridCell,secantVisitHalfCell] using hcell
  · have hh : h=0 := by simpa [crossingHoleGridExterior] using hext
    subst h
    change ∃ w, secantAxisAdjacent T C (secantVisitLeft T c i) w ∧
      ((secantVisitLeft T c i,w),secantVisitHalfCell T c j k) ∈ secantCrossingHoleCells T C c i j
    refine ⟨crossingVisitTime T c i,secantVisit_left_half_adjacent T C c i hi,?_⟩
    simpa [crossingHoleGridCell,secantVisitHalfCell] using hcell

end
end DirectGLSSW.HOMFLY.PrincipalTurning

