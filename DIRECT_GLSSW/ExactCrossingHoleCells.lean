import VisitWindowCells

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

def secantVisitHalfCells {D : PLLinkDiagram} (T : BasedTraversal D) (c : Fin D.nCrossing) (i : Fin 2) :
    Finset (ℝ × ℝ) :=
  {(secantVisitLeft T c i,crossingVisitTime T c i),(crossingVisitTime T c i,secantVisitRight T c i)}

def secantCrossingHoleCells {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2) :
    Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ((secantAxisCells T C).product (secantAxisCells T C)).filter (fun r =>
    secantVisitLeft T c i≤r.1.1 ∧ r.1.2≤secantVisitRight T c i ∧
    secantVisitLeft T c j≤r.2.1 ∧ r.2.2≤secantVisitRight T c j)

theorem secantCrossingHoleCells_membership {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C) (a b u v : ℝ) :
    ((a,b),(u,v)) ∈ secantCrossingHoleCells T C c i j ↔
      ((a=secantVisitLeft T c i ∧ b=crossingVisitTime T c i) ∨
       (a=crossingVisitTime T c i ∧ b=secantVisitRight T c i)) ∧
      ((u=secantVisitLeft T c j ∧ v=crossingVisitTime T c j) ∨
       (u=crossingVisitTime T c j ∧ v=secantVisitRight T c j)) := by
  constructor
  · intro hr
    have h := Finset.mem_filter.mp hr
    have hc := Finset.mem_product.mp h.1
    have h1 : secantAxisAdjacent T C a b := (Finset.mem_filter.mp hc.1).2
    have h2 : secantAxisAdjacent T C u v := (Finset.mem_filter.mp hc.2).2
    exact ⟨(secantAxis_cell_in_visitWindow_iff T C c i hi a b).mp ⟨h1,h.2.1,h.2.2.1⟩,
      (secantAxis_cell_in_visitWindow_iff T C c j hj u v).mp ⟨h2,h.2.2.2.1,h.2.2.2.2⟩⟩
  · rintro ⟨hfirst,hsecond⟩
    have h1 := (secantAxis_cell_in_visitWindow_iff T C c i hi a b).mpr hfirst
    have h2 := (secantAxis_cell_in_visitWindow_iff T C c j hj u v).mpr hsecond
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,h1.2.1,h1.2.2,h2.2.1,h2.2.2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1.1.1,h1.1.2.1⟩,h1.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2.1.1,h2.1.2.1⟩,h2.1⟩

theorem secantCrossingHoleCells_eq_four {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C) :
    secantCrossingHoleCells T C c i j = (secantVisitHalfCells T c i).product (secantVisitHalfCells T c j) := by
  ext ⟨⟨a,b⟩,⟨u,v⟩⟩
  rw [secantCrossingHoleCells_membership T C c i j hi hj]
  simp [secantVisitHalfCells,Prod.mk.injEq]

theorem secantVisitHalfCells_card (D : PLLinkDiagram) (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) : (secantVisitHalfCells T c i).card=2 := by
  have hs := secantVisit_endpoints_straddle T c i
  have hn : (secantVisitLeft T c i,crossingVisitTime T c i) ≠
      (crossingVisitTime T c i,secantVisitRight T c i) := by
    intro h
    have h' := congrArg Prod.fst h
    exact ne_of_lt hs.1 h'
  simp [secantVisitHalfCells,hn]

theorem secantCrossingHoleCells_card_four {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C) :
    (secantCrossingHoleCells T C c i j).card=4 := by
  rw [secantCrossingHoleCells_eq_four T C c i j hi hj,Finset.product_eq_sprod,Finset.card_product,
    secantVisitHalfCells_card D T c i,secantVisitHalfCells_card D T c j]

theorem secantCrossingHoleCell_not_retained {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i<crossingVisitTime T c j)
    (r : (ℝ × ℝ) × (ℝ × ℝ)) (hr : r ∈ secantCrossingHoleCells T C c i j) :
    r ∉ secantRetainedRectangles T C := by
  have hbound := (Finset.mem_filter.mp hr).2
  intro hretained
  apply (Finset.mem_filter.mp hretained).2.2.2
  exact ⟨c,i,j,hij,hi,hj,horder,hbound.1,hbound.2.1,hbound.2.2.1,hbound.2.2.2⟩

end
end DirectGLSSW.HOMFLY.PrincipalTurning





