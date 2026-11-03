import HoleNeighbourGeometry

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

-- SOURCE PREPARATION ONLY: no compiled object yet.
private theorem finTwo_ne_ne_eq (i j k : Fin 2) (hij : i≠j) (hik : i≠k) : j=k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

/-- The two unchanged half-cell coordinates identify the actual crossing
star; a strict step outside any one side then contradicts its literal bounds. -/
theorem holeExterior_not_insideStar {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j h k : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (a b u v : ℝ) (ha : a<secantVisitLeft T c i) (hb : secantVisitRight T c i<b)
    (hu : u<secantVisitLeft T c j) (hv : secantVisitRight T c j<v) :
    ¬ secantRectangleInsideStar T C (secantVisitHalfCell T c i h).1
      (secantVisitHalfCell T c i h).2 u (secantVisitLeft T c j) ∧
    ¬ secantRectangleInsideStar T C (secantVisitRight T c i) b
      (secantVisitHalfCell T c j k).1 (secantVisitHalfCell T c j k).2 ∧
    ¬ secantRectangleInsideStar T C (secantVisitHalfCell T c i h).1
      (secantVisitHalfCell T c i h).2 (secantVisitRight T c j) v ∧
    ¬ secantRectangleInsideStar T C a (secantVisitLeft T c i)
      (secantVisitHalfCell T c j k).1 (secantVisitHalfCell T c j k).2 := by
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨d,p,q,hpq,hp,hq,_,hlo,hhi,hbot,_⟩
    have he := secantVisitHalfCell_contained_unique T c d i p h (hi.trans hp.symm) hlo hhi
    have hd : c=d := congrArg Prod.fst he
    have hpi : i=p := congrArg Prod.snd he
    subst d; subst p
    have heq : j=q := finTwo_ne_ne_eq i j q hij hpq
    subst q
    linarith
  · rintro ⟨d,p,q,hpq,hp,hq,_,_,hright,hlo,hhi⟩
    have he := secantVisitHalfCell_contained_unique T c d j q k (hj.trans hq.symm) hlo hhi
    have hd : c=d := congrArg Prod.fst he
    have hqj : j=q := congrArg Prod.snd he
    subst d; subst q
    have heq : i=p := finTwo_ne_ne_eq j i p (Ne.symm hij) (Ne.symm hpq)
    subst p
    linarith
  · rintro ⟨d,p,q,hpq,hp,hq,_,hlo,hhi,_,htop⟩
    have he := secantVisitHalfCell_contained_unique T c d i p h (hi.trans hp.symm) hlo hhi
    have hd : c=d := congrArg Prod.fst he
    have hpi : i=p := congrArg Prod.snd he
    subst d; subst p
    have heq : j=q := finTwo_ne_ne_eq i j q hij hpq
    subst q
    linarith
  · rintro ⟨d,p,q,hpq,hp,hq,_,hleft,_,hlo,hhi⟩
    have he := secantVisitHalfCell_contained_unique T c d j q k (hj.trans hq.symm) hlo hhi
    have hd : c=d := congrArg Prod.fst he
    have hqj : j=q := congrArg Prod.snd he
    subst d; subst q
    have heq : i=p := finTwo_ne_ne_eq j i p (Ne.symm hij) (Ne.symm hpq)
    subst p
    linarith

private theorem axisAdjacent_mem_cells {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b : ℝ) (h : secantAxisAdjacent T C a b) :
    (a,b) ∈ secantAxisCells T C :=
  Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h.1,h.2.1⟩,h⟩

/-- Every one-cell outside neighbour of the literal hole is retained. The
adjacency data are actual finite cut adjacency, discharged by the existence
consumer below; no zero-free/retainedness certificate is a premise. -/
theorem holeExterior_neighbours_retained {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j h k : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j)
    (a b u v : ℝ)
    (ha : secantAxisAdjacent T C a (secantVisitLeft T c i))
    (hb : secantAxisAdjacent T C (secantVisitRight T c i) b)
    (hu : secantAxisAdjacent T C u (secantVisitLeft T c j))
    (hv : secantAxisAdjacent T C (secantVisitRight T c j) v) :
    (secantVisitHalfCell T c i h,(u,secantVisitLeft T c j)) ∈ secantRetainedRectangles T C ∧
    ((secantVisitRight T c i,b),secantVisitHalfCell T c j k) ∈ secantRetainedRectangles T C ∧
    (secantVisitHalfCell T c i h,(secantVisitRight T c j,v)) ∈ secantRetainedRectangles T C ∧
    ((a,secantVisitLeft T c i),secantVisitHalfCell T c j k) ∈ secantRetainedRectangles T C := by
  have hx := secantVisitHalfCell_adjacent T C c i h hi
  have hy := secantVisitHalfCell_adjacent T C c j k hj
  have hxb := secantVisitHalfCell_bounds T c i h
  have hyb := secantVisitHalfCell_bounds T c j k
  have hgap := orderedVisitWindows_gap T c i j hij (hi.trans hj.symm) horder
  have huw := secantAxisAdjacent_width T C u _ hu
  have hbw := secantAxisAdjacent_width T C _ b hb
  have hε := secantMeshEpsilon_positive D
  have hm := secantMesh_visit_window_inside_margin T c i (-secantMeshEpsilon D)
    ⟨le_rfl,by linarith⟩
  have hmargin : 1/4 < secantVisitLeft T c i := by
    simpa only [secantVisitLeft] using hm.1
  have hn := holeExterior_not_insideStar T C c i j h k hij hi hj a b u v
    ha.2.2.1 hb.2.2.1 hu.2.2.1 hv.2.2.1
  have hxm := axisAdjacent_mem_cells T C _ _ hx
  have hym := axisAdjacent_mem_cells T C _ _ hy
  have ham := axisAdjacent_mem_cells T C _ _ ha
  have hbm := axisAdjacent_mem_cells T C _ _ hb
  have hum := axisAdjacent_mem_cells T C _ _ hu
  have hvm := axisAdjacent_mem_cells T C _ _ hv
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxm,hum⟩,?_,?_,hn.1⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hbm,hym⟩,?_,?_,hn.2.1⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxm,hvm⟩,?_,?_,hn.2.2.1⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ham,hym⟩,?_,?_,hn.2.2.2⟩⟩
  all_goals first
    | (intro hc; linarith [hc.1,ha.2.2.1,hb.2.2.1,hxb.1,hxb.2.1,hxb.2.2])
    | linarith [hxb.1,hxb.2.1,hxb.2.2,hyb.1,hyb.2.1,hyb.2.2,hu.2.2.1,hv.2.2.1]


/-- Actual finite outside cells exist on all four sides and all eight indexed
outside half-side neighbours are retained. This discharges the coordinate
adjacency premises above from D and the actual common cutoff. -/
theorem crossingHole_retainedNeighbours_exist {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j) :
    ∃ a b u v : ℝ,
      secantAxisAdjacent T C a (secantVisitLeft T c i) ∧
      secantAxisAdjacent T C (secantVisitRight T c i) b ∧
      secantAxisAdjacent T C u (secantVisitLeft T c j) ∧
      secantAxisAdjacent T C (secantVisitRight T c j) v ∧
      ∀ h k : Fin 2,
        (secantVisitHalfCell T c i h,(u,secantVisitLeft T c j)) ∈ secantRetainedRectangles T C ∧
        ((secantVisitRight T c i,b),secantVisitHalfCell T c j k) ∈ secantRetainedRectangles T C ∧
        (secantVisitHalfCell T c i h,(secantVisitRight T c j,v)) ∈ secantRetainedRectangles T C ∧
        ((a,secantVisitLeft T c i),secantVisitHalfCell T c j k) ∈ secantRetainedRectangles T C := by
  have hε := secantMeshEpsilon_positive D
  have hmL := secantMesh_visit_window_inside_margin T c i (-secantMeshEpsilon D)
    ⟨le_rfl,by linarith⟩
  have hmR := secantMesh_visit_window_inside_margin T c i (2*secantMeshEpsilon D)
    ⟨by linarith,le_rfl⟩
  have hnL := secantMesh_visit_window_inside_margin T c j (-secantMeshEpsilon D)
    ⟨le_rfl,by linarith⟩
  have hnR := secantMesh_visit_window_inside_margin T c j (2*secantMeshEpsilon D)
    ⟨by linarith,le_rfl⟩
  have hl : 0<secantVisitLeft T c i := by dsimp only [secantVisitLeft];linarith [hmL.1]
  have hll : 0<secantVisitLeft T c j := by dsimp only [secantVisitLeft];linarith [hnL.1]
  have hr : secantVisitRight T c i < (componentArcLength D (T.baseArc C).val : ℝ) := by
    have hh := hmR.2
    rw [hi] at hh
    dsimp only [secantVisitRight]
    linarith
  have hrr : secantVisitRight T c j < (componentArcLength D (T.baseArc C).val : ℝ) := by
    have hh := hnR.2
    rw [hj] at hh
    dsimp only [secantVisitRight]
    linarith
  have hmi := secantVisit_endpoints_mem_axis T C c i hi
  have hmj := secantVisit_endpoints_mem_axis T C c j hj
  obtain ⟨a,ha⟩ := secantAxis_predecessor_exists T C _ hmi.1 hl
  obtain ⟨b,hb⟩ := secantAxis_successor_exists T C _ hmi.2 hr
  obtain ⟨u,hu⟩ := secantAxis_predecessor_exists T C _ hmj.1 hll
  obtain ⟨v,hv⟩ := secantAxis_successor_exists T C _ hmj.2 hrr
  exact ⟨a,b,u,v,ha,hb,hu,hv,fun h k =>
    holeExterior_neighbours_retained T C c i j h k hij hi hj horder a b u v ha hb hu hv⟩

end
end DirectGLSSW.HOMFLY.PrincipalTurning




