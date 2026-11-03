import HoleClockwiseIncidence

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem secantAxisAdjacent_successor_unique {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b c : ℝ)
    (h : secantAxisAdjacent T C a b) (h' : secantAxisAdjacent T C a c) : b=c := by
  rcases lt_trichotomy b c with hlt | heq | hlt
  · exact False.elim (h'.2.2.2 b h.2.1 h.2.2.1 hlt)
  · exact heq
  · exact False.elim (h.2.2.2 c h'.2.1 h'.2.2.1 hlt)

theorem secantAxisAdjacent_predecessor_unique {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b c : ℝ)
    (h : secantAxisAdjacent T C a c) (h' : secantAxisAdjacent T C b c) : a=b := by
  rcases lt_trichotomy a b with hlt | heq | hlt
  · exact False.elim (h.2.2.2 b h'.1 hlt h'.2.2.1)
  · exact heq
  · exact False.elim (h'.2.2.2 a h.1 hlt h.2.2.1)

/-- A retained neighbour of an actual hole cannot lie across an internal half-cell seam. -/
theorem crossingHole_retained_above_exterior {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j)
    (a b u v w : ℝ)
    (hq : ((a,b),(u,v)) ∈ secantCrossingHoleCells T C c i j)
    (hn : secantAxisAdjacent T C v w)
    (hr : ((a,b),(v,w)) ∈ secantRetainedRectangles T C) : v=secantVisitRight T c j := by
  have hmem := (secantCrossingHoleCells_membership T C c i j hi hj a b u v).mp hq
  rcases hmem.2 with ⟨he1,he2⟩ | ⟨he1,he2⟩
  · have hseam : v=crossingVisitTime T c j := he2
    have hw := secantAxisAdjacent_successor_unique T C (crossingVisitTime T c j) w (secantVisitRight T c j)
      (by simpa only [hseam] using hn) (secantVisit_right_half_adjacent T C c j hj)
    have hin : ((a,b),(crossingVisitTime T c j,secantVisitRight T c j)) ∈ secantCrossingHoleCells T C c i j :=
      (secantCrossingHoleCells_membership T C c i j hi hj _ _ _ _).mpr ⟨hmem.1,Or.inr ⟨rfl,rfl⟩⟩
    have hnot := secantCrossingHoleCell_not_retained T C c i j hij hi hj horder _ hin
    exact False.elim (hnot (by simpa only [hseam,hw] using hr))
  · exact he2

/-- A retained neighbour of an actual hole cannot lie across an internal half-cell seam. -/
theorem crossingHole_retained_below_exterior {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j)
    (a b u v w : ℝ)
    (hq : ((a,b),(u,v)) ∈ secantCrossingHoleCells T C c i j)
    (hn : secantAxisAdjacent T C w u)
    (hr : ((a,b),(w,u)) ∈ secantRetainedRectangles T C) : u=secantVisitLeft T c j := by
  have hmem := (secantCrossingHoleCells_membership T C c i j hi hj a b u v).mp hq
  rcases hmem.2 with ⟨he1,he2⟩ | ⟨he1,he2⟩
  · exact he1
  · have hseam : u=crossingVisitTime T c j := he1
    have hw := secantAxisAdjacent_predecessor_unique T C w (secantVisitLeft T c j) (crossingVisitTime T c j)
      (by simpa only [hseam] using hn) (secantVisit_left_half_adjacent T C c j hj)
    have hin : ((a,b),(secantVisitLeft T c j,crossingVisitTime T c j)) ∈ secantCrossingHoleCells T C c i j :=
      (secantCrossingHoleCells_membership T C c i j hi hj _ _ _ _).mpr ⟨hmem.1,Or.inl ⟨rfl,rfl⟩⟩
    have hnot := secantCrossingHoleCell_not_retained T C c i j hij hi hj horder _ hin
    exact False.elim (hnot (by simpa only [hseam,hw] using hr))

/-- A retained neighbour of an actual hole cannot lie across an internal half-cell seam. -/
theorem crossingHole_retained_right_exterior {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j)
    (a b u v w : ℝ)
    (hq : ((a,b),(u,v)) ∈ secantCrossingHoleCells T C c i j)
    (hn : secantAxisAdjacent T C b w)
    (hr : ((b,w),(u,v)) ∈ secantRetainedRectangles T C) : b=secantVisitRight T c i := by
  have hmem := (secantCrossingHoleCells_membership T C c i j hi hj a b u v).mp hq
  rcases hmem.1 with ⟨he1,he2⟩ | ⟨he1,he2⟩
  · have hseam : b=crossingVisitTime T c i := he2
    have hw := secantAxisAdjacent_successor_unique T C (crossingVisitTime T c i) w (secantVisitRight T c i)
      (by simpa only [hseam] using hn) (secantVisit_right_half_adjacent T C c i hi)
    have hin : ((crossingVisitTime T c i,secantVisitRight T c i),(u,v)) ∈ secantCrossingHoleCells T C c i j :=
      (secantCrossingHoleCells_membership T C c i j hi hj _ _ _ _).mpr ⟨Or.inr ⟨rfl,rfl⟩,hmem.2⟩
    have hnot := secantCrossingHoleCell_not_retained T C c i j hij hi hj horder _ hin
    exact False.elim (hnot (by simpa only [hseam,hw] using hr))
  · exact he2

/-- A retained neighbour of an actual hole cannot lie across an internal half-cell seam. -/
theorem crossingHole_retained_left_exterior {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j)
    (a b u v w : ℝ)
    (hq : ((a,b),(u,v)) ∈ secantCrossingHoleCells T C c i j)
    (hn : secantAxisAdjacent T C w a)
    (hr : ((w,a),(u,v)) ∈ secantRetainedRectangles T C) : a=secantVisitLeft T c i := by
  have hmem := (secantCrossingHoleCells_membership T C c i j hi hj a b u v).mp hq
  rcases hmem.1 with ⟨he1,he2⟩ | ⟨he1,he2⟩
  · exact he1
  · have hseam : a=crossingVisitTime T c i := he1
    have hw := secantAxisAdjacent_predecessor_unique T C w (secantVisitLeft T c i) (crossingVisitTime T c i)
      (by simpa only [hseam] using hn) (secantVisit_left_half_adjacent T C c i hi)
    have hin : ((secantVisitLeft T c i,crossingVisitTime T c i),(u,v)) ∈ secantCrossingHoleCells T C c i j :=
      (secantCrossingHoleCells_membership T C c i j hi hj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hmem.2⟩
    have hnot := secantCrossingHoleCell_not_retained T C c i j hij hi hj horder _ hin
    exact False.elim (hnot (by simpa only [hseam,hw] using hr))

end
end DirectGLSSW.HOMFLY.PrincipalTurning






