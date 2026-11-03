import ExactCrossingHoleCells

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

def secantVisitHalfCell {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) (k : Fin 2) : ℝ × ℝ :=
  if k=0 then (secantVisitLeft T c i,crossingVisitTime T c i)
  else (crossingVisitTime T c i,secantVisitRight T c i)

def crossingHoleGridCell {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i j : Fin 2) (h k : Fin 2) : (ℝ × ℝ) × (ℝ × ℝ) :=
  (secantVisitHalfCell T c i h,secantVisitHalfCell T c j k)

theorem crossingHoleGridCell_mem {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C) (h k : Fin 2) :
    crossingHoleGridCell T c i j h k ∈ secantCrossingHoleCells T C c i j := by
  rw [secantCrossingHoleCells_eq_four T C c i j hi hj]
  fin_cases h <;> fin_cases k <;> simp [crossingHoleGridCell,secantVisitHalfCell,secantVisitHalfCells]

def parameterRectangleSideStart (r : (ℝ × ℝ) × (ℝ × ℝ)) (s : Fin 4) : ℝ × ℝ :=
  if s=0 then (r.1.1,r.2.1) else if s=1 then (r.1.2,r.2.1)
  else if s=2 then (r.1.2,r.2.2) else (r.1.1,r.2.2)

def parameterRectangleSideFinish (r : (ℝ × ℝ) × (ℝ × ℝ)) (s : Fin 4) : ℝ × ℝ :=
  if s=0 then (r.1.2,r.2.1) else if s=1 then (r.1.2,r.2.2)
  else if s=2 then (r.1.1,r.2.2) else (r.1.1,r.2.1)

/-- Literal exterior cell sides of the actual two-by-two hole. Internal
sides can meet the secant zero, so no cancellation of them is assumed. -/
def crossingHoleGridExterior (h k : Fin 2) (s : Fin 4) : Prop :=
  (s=0 ∧ k=0) ∨ (s=1 ∧ h=1) ∨ (s=2 ∧ k=1) ∨ (s=3 ∧ h=0)

def crossingHoleGridBoundarySum {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2) : ℝ :=
  ∑ h : Fin 2, ∑ k : Fin 2, ∑ s : Fin 4,
    if crossingHoleGridExterior h k s then
      Complex.arg (basedUniformSecant T C
        (parameterRectangleSideFinish (crossingHoleGridCell T c i j h k) s).1
        (parameterRectangleSideFinish (crossingHoleGridCell T c i j h k) s).2 /
        basedUniformSecant T C
        (parameterRectangleSideStart (crossingHoleGridCell T c i j h k) s).1
        (parameterRectangleSideStart (crossingHoleGridCell T c i j h k) s).2)
    else 0

def crossingHolePerimeterTurn {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2) : ℝ :=
  let Z := basedUniformSecant T C
  let L := secantVisitLeft T c i
  let V := crossingVisitTime T c i
  let R := secantVisitRight T c i
  let l := secantVisitLeft T c j
  let v := crossingVisitTime T c j
  let r := secantVisitRight T c j
  Complex.arg (Z V l / Z L l)+Complex.arg (Z R l / Z V l)+
    Complex.arg (Z R v / Z R l)+Complex.arg (Z R r / Z R v)+
    Complex.arg (Z V r / Z R r)+Complex.arg (Z L r / Z V r)+
    Complex.arg (Z L v / Z L r)+Complex.arg (Z L l / Z L v)

/-- Exhausts the sixteen literal cell sides and leaves exactly eight
exterior increments, with the counterclockwise box orientation. -/
theorem crossingHoleGridBoundarySum_eq_perimeter {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2) :
    crossingHoleGridBoundarySum T C c i j = crossingHolePerimeterTurn T C c i j := by
  simp [crossingHoleGridBoundarySum,Fin.sum_univ_two,Fin.sum_univ_four,
    crossingHoleGridExterior,crossingHoleGridCell,secantVisitHalfCell,
    parameterRectangleSideStart,parameterRectangleSideFinish,crossingHolePerimeterTurn]
  ring

theorem crossingHolePerimeterTurn_eq_starEight {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hi : componentOf D.continuation (D.incoming c i)=C) :
    crossingHolePerimeterTurn T C c i j =
      starEightTurn (basedOrderedCrossingPullback T c i j) (secantMeshEpsilon D) := by
  simp [crossingHolePerimeterTurn,starEightTurn,basedOrderedCrossingPullback,
    basedUniformSecant,secantVisitLeft,secantVisitRight,hi,crossingStarCoordinateInverse]

/-- Actual first/second visit order, including branch1 then0. This is the
CCW hole perimeter; transfer to the retained-chain clockwise side sum is
an explicit remaining global incidence/orientation obligation. -/
theorem firstVisited_crossingHoleGridBoundary_balance {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : componentOf D.continuation (D.incoming c (firstVisitedBranch T c)) =
      componentOf D.continuation (D.incoming c (otherBranch (firstVisitedBranch T c)))) :
    crossingHoleGridBoundarySum T (componentOf D.continuation (D.incoming c (firstVisitedBranch T c)))
      c (firstVisitedBranch T c) (otherBranch (firstVisitedBranch T c)) =
      if 0 < complexDet (crossingVector D c (firstVisitedBranch T c))
        (crossingVector D c (otherBranch (firstVisitedBranch T c)))
      then -(2*Real.pi) else 2*Real.pi := by
  rw [crossingHoleGridBoundarySum_eq_perimeter,crossingHolePerimeterTurn_eq_starEight T _ c _ _ rfl]
  exact firstVisitedBranch_common_boundary_balance T c hself

end
end DirectGLSSW.HOMFLY.PrincipalTurning




