import HoleClockwiseIncidence
import ActualRectangleBoundaryChain

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem crossingHole_branch_ne_other (i : Fin 2) : i ≠ otherBranch i := by
  fin_cases i <;> simp

theorem crossingHoleOutsideSide_increment {D : PLLinkDiagram} (T : BasedTraversal D)
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
    rectangleSideIncrement (crossingHoleOutsideSide T C c i j hij hi hj horder a b u v ha hb hu hv h k s) =
      -Complex.arg (basedUniformSecant T C
        (parameterRectangleSideFinish (crossingHoleGridCell T c i j h k) s).1
        (parameterRectangleSideFinish (crossingHoleGridCell T c i j h k) s).2 /
        basedUniformSecant T C
        (parameterRectangleSideStart (crossingHoleGridCell T c i j h k) s).1
        (parameterRectangleSideStart (crossingHoleGridCell T c i j h k) s).2) := by
  let e := crossingHoleOutsideSide T C c i j hij hi hj horder a b u v ha hb hu hv h k s
  have he := crossingHoleOutsideSide_reverses_endpoints T C c i j hij hi hj horder a b u v ha hb hu hv h k s hext
  have hr := segment_arg_reverse
    (basedUniformSecant T C (rectangleSideStart e).1 (rectangleSideStart e).2)
    (basedUniformSecant T C (rectangleSideFinish e).1 (rectangleSideFinish e).2)
    (rectangleSide_avoids_zero e)
  change rectangleSideIncrement e = _
  change rectangleSideStart e = _ ∧ rectangleSideFinish e = _ at he
  unfold rectangleSideIncrement
  rw [he.1,he.2] at hr ⊢
  linarith

noncomputable def crossingHoleClockwiseSideSum {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j)
    (a b u v : ℝ)
    (ha : secantAxisAdjacent T C a (secantVisitLeft T c i))
    (hb : secantAxisAdjacent T C (secantVisitRight T c i) b)
    (hu : secantAxisAdjacent T C u (secantVisitLeft T c j))
    (hv : secantAxisAdjacent T C (secantVisitRight T c j) v) : ℝ :=
  ∑ h : Fin 2, ∑ k : Fin 2, ∑ s : Fin 4, if crossingHoleGridExterior h k s then
    rectangleSideIncrement (crossingHoleOutsideSide T C c i j hij hi hj horder a b u v ha hb hu hv h k s)
    else 0

/-- A sum of actual fixed retained-side increments, with the clockwise
orientation opposite the previously checked hole perimeter. -/
theorem crossingHoleClockwiseSideSum_eq_negative {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j)
    (a b u v : ℝ)
    (ha : secantAxisAdjacent T C a (secantVisitLeft T c i))
    (hb : secantAxisAdjacent T C (secantVisitRight T c i) b)
    (hu : secantAxisAdjacent T C u (secantVisitLeft T c j))
    (hv : secantAxisAdjacent T C (secantVisitRight T c j) v) :
    crossingHoleClockwiseSideSum T C c i j hij hi hj horder a b u v ha hb hu hv =
      -crossingHoleGridBoundarySum T C c i j := by
  simp only [crossingHoleClockwiseSideSum,crossingHoleGridBoundarySum,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro s _
  by_cases hext : crossingHoleGridExterior h k s
  · simp only [if_pos hext]
    exact crossingHoleOutsideSide_increment T C c i j hij hi hj horder a b u v ha hb hu hv h k s hext
  · simp [hext]

/-- All geometric adjacency data are constructed from D. Both actual visit
orders are supported. This is a local fixed-side sum; its multiplicity-free
regrouping within the entire retained boundary remains a separate gate. -/
theorem firstVisited_clockwise_hole_boundary_exists {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing)
    (hself : componentOf D.continuation (D.incoming c (firstVisitedBranch T c)) =
      componentOf D.continuation (D.incoming c (otherBranch (firstVisitedBranch T c)))) :
    let C := componentOf D.continuation (D.incoming c (firstVisitedBranch T c))
    let i := firstVisitedBranch T c
    let j := otherBranch i
    ∃ a b u v : ℝ,
      ∃ ha : secantAxisAdjacent T C a (secantVisitLeft T c i),
      ∃ hb : secantAxisAdjacent T C (secantVisitRight T c i) b,
      ∃ hu : secantAxisAdjacent T C u (secantVisitLeft T c j),
      ∃ hv : secantAxisAdjacent T C (secantVisitRight T c j) v,
        crossingHoleClockwiseSideSum T C c i j (crossingHole_branch_ne_other i) rfl hself.symm
          (by have hg := firstVisitedBranch_time_gap T c hself; linarith) a b u v ha hb hu hv =
          if 0<complexDet (crossingVector D c i) (crossingVector D c j)
          then 2*Real.pi else -(2*Real.pi) := by
  dsimp only
  obtain ⟨a,b,u,v,ha,hb,hu,hv,_⟩ := crossingHole_retainedNeighbours_exist T _ c _ _
    (crossingHole_branch_ne_other (firstVisitedBranch T c)) rfl hself.symm
    (by have hg := firstVisitedBranch_time_gap T c hself; linarith)
  refine ⟨a,b,u,v,ha,hb,hu,hv,?_⟩
  rw [crossingHoleClockwiseSideSum_eq_negative,firstVisited_crossingHoleGridBoundary_balance T c hself]
  split_ifs <;> ring

end
end DirectGLSSW.HOMFLY.PrincipalTurning





