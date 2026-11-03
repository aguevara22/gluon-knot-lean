import HoleExteriorRetained

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Actual one-cell outside neighbours; exterior selector determines which
of the two hole half-cells touches this side. -/
def crossingHoleOutsideCell {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i j h k : Fin 2) (a b u v : ℝ) (s : Fin 4) :
    (ℝ × ℝ) × (ℝ × ℝ) :=
  if s=0 then (secantVisitHalfCell T c i h,(u,secantVisitLeft T c j))
  else if s=1 then ((secantVisitRight T c i,b),secantVisitHalfCell T c j k)
  else if s=2 then (secantVisitHalfCell T c i h,(secantVisitRight T c j,v))
  else ((a,secantVisitLeft T c i),secantVisitHalfCell T c j k)

def crossingHoleOutsideSideIndex (s : Fin 4) : Fin 4 :=
  if s=0 then 2 else if s=1 then 3 else if s=2 then 0 else 1

noncomputable def crossingHoleOutsideSide {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j)
    (a b u v : ℝ)
    (ha : secantAxisAdjacent T C a (secantVisitLeft T c i))
    (hb : secantAxisAdjacent T C (secantVisitRight T c i) b)
    (hu : secantAxisAdjacent T C u (secantVisitLeft T c j))
    (hv : secantAxisAdjacent T C (secantVisitRight T c j) v)
    (h k : Fin 2) (s : Fin 4) : RetainedRectangleSide T C :=
  (⟨crossingHoleOutsideCell T c i j h k a b u v s,by
    have hr := holeExterior_neighbours_retained T C c i j h k hij hi hj horder a b u v ha hb hu hv
    fin_cases s
    · simpa [crossingHoleOutsideCell] using hr.1
    · simpa [crossingHoleOutsideCell] using hr.2.1
    · simpa [crossingHoleOutsideCell] using hr.2.2.1
    · simpa [crossingHoleOutsideCell] using hr.2.2.2⟩,
    crossingHoleOutsideSideIndex s)

/-- Literal endpoint equality gives the clockwise retained-side orientation,
with no sign convention inferred merely from a picture. -/
theorem crossingHoleOutsideSide_reverses_endpoints {D : PLLinkDiagram} (T : BasedTraversal D)
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
    rectangleSideStart (crossingHoleOutsideSide T C c i j hij hi hj horder a b u v ha hb hu hv h k s) =
      parameterRectangleSideFinish (crossingHoleGridCell T c i j h k) s ∧
    rectangleSideFinish (crossingHoleOutsideSide T C c i j hij hi hj horder a b u v ha hb hu hv h k s) =
      parameterRectangleSideStart (crossingHoleGridCell T c i j h k) s := by
  fin_cases h <;> fin_cases k <;> fin_cases s <;>
    simp [crossingHoleGridExterior] at hext <;>
    simp [crossingHoleOutsideSide,crossingHoleOutsideCell,crossingHoleOutsideSideIndex,
      rectangleSideStart,rectangleSideFinish,parameterRectangleSideStart,parameterRectangleSideFinish,
      crossingHoleGridCell,secantVisitHalfCell]

/-- These actual clockwise neighbours are fixed in the existing retained
side involution because the reverse directed side belongs to a removed hole. -/
theorem crossingHoleOutsideSide_fixed {D : PLLinkDiagram} (T : BasedTraversal D)
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
    rectangleSideReverse (crossingHoleOutsideSide T C c i j hij hi hj horder a b u v ha hb hu hv h k s) =
      crossingHoleOutsideSide T C c i j hij hi hj horder a b u v ha hb hu hv h k s := by
  apply rectangleSide_exterior_or_removed_implies_fixed
  right
  have hx := secantVisitHalfCell_adjacent T C c i h hi
  have hy := secantVisitHalfCell_adjacent T C c j k hj
  have hnot := secantCrossingHoleCell_not_retained T C c i j hij hi hj horder
    (crossingHoleGridCell T c i j h k) (crossingHoleGridCell_mem T C c i j hi hj h k)
  have hreason := (secantCellPair_not_retained_iff T C _ _ _ _ hx hy).mp hnot
  fin_cases s
  · have hk : k=0 := by simpa [crossingHoleGridExterior] using hext
    subst k
    refine ⟨crossingVisitTime T c j,secantVisit_left_half_adjacent T C c j hj,?_⟩
    simpa [crossingHoleOutsideSide,crossingHoleOutsideCell,crossingHoleOutsideSideIndex,
      rectangleRemovedNeighbour,secantVisitHalfCell] using hreason
  · have hh : h=1 := by simpa [crossingHoleGridExterior] using hext
    subst h
    refine ⟨crossingVisitTime T c i,secantVisit_right_half_adjacent T C c i hi,?_⟩
    simpa [crossingHoleOutsideSide,crossingHoleOutsideCell,crossingHoleOutsideSideIndex,
      rectangleRemovedNeighbour,secantVisitHalfCell] using hreason
  · have hk : k=1 := by simpa [crossingHoleGridExterior] using hext
    subst k
    refine ⟨crossingVisitTime T c j,secantVisit_right_half_adjacent T C c j hj,?_⟩
    simpa [crossingHoleOutsideSide,crossingHoleOutsideCell,crossingHoleOutsideSideIndex,
      rectangleRemovedNeighbour,secantVisitHalfCell] using hreason
  · have hh : h=0 := by simpa [crossingHoleGridExterior] using hext
    subst h
    refine ⟨crossingVisitTime T c i,secantVisit_left_half_adjacent T C c i hi,?_⟩
    simpa [crossingHoleOutsideSide,crossingHoleOutsideCell,crossingHoleOutsideSideIndex,
      rectangleRemovedNeighbour,secantVisitHalfCell] using hreason

end
end DirectGLSSW.HOMFLY.PrincipalTurning


