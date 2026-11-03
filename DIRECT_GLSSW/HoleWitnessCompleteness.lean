import HoleStarNeighbourConverse

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Literal adjacency to a cell in this actual crossing hole. -/
def rectangleTouchesCrossingHole {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (e : RetainedRectangleSide T C) : Prop :=
  if e.2=0 then ∃ w, secantAxisAdjacent T C w e.1.val.2.1 ∧
    ((e.1.val.1.1,e.1.val.1.2),(w,e.1.val.2.1)) ∈ secantCrossingHoleCells T C c i j
  else if e.2=1 then ∃ w, secantAxisAdjacent T C e.1.val.1.2 w ∧
    ((e.1.val.1.2,w),(e.1.val.2.1,e.1.val.2.2)) ∈ secantCrossingHoleCells T C c i j
  else if e.2=2 then ∃ w, secantAxisAdjacent T C e.1.val.2.2 w ∧
    ((e.1.val.1.1,e.1.val.1.2),(e.1.val.2.2,w)) ∈ secantCrossingHoleCells T C c i j
  else ∃ w, secantAxisAdjacent T C w e.1.val.1.1 ∧
    ((w,e.1.val.1.1),(e.1.val.2.1,e.1.val.2.2)) ∈ secantCrossingHoleCells T C c i j

/-- Every actual retained side touching this hole is one of its eight
constructed exterior witnesses. No fixedness or isolation certificate. -/
theorem rectangleTouchesCrossingHole_witness {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j)
    (a b u v : ℝ)
    (ha : secantAxisAdjacent T C a (secantVisitLeft T c i))
    (hb : secantAxisAdjacent T C (secantVisitRight T c i) b)
    (hu : secantAxisAdjacent T C u (secantVisitLeft T c j))
    (hv : secantAxisAdjacent T C (secantVisitRight T c j) v)
    (e : RetainedRectangleSide T C)
    (ht : rectangleTouchesCrossingHole T C c i j e) :
    ∃ h k : Fin 2, ∃ s : Fin 4, crossingHoleGridExterior h k s ∧
      e=crossingHoleOutsideSide T C c i j hij hi hj horder a b u v ha hb hu hv h k s := by
  have hc := retainedRectangle_axis_cells e.1
  rcases e with ⟨r,s⟩
  fin_cases s
  · simp only [rectangleTouchesCrossingHole,if_pos rfl] at ht
    obtain ⟨w,hw,hq⟩ := ht
    have hmem := (secantCrossingHoleCells_membership T C c i j hi hj r.val.1.1 r.val.1.2 w r.val.2.1).mp hq
    have hseam := crossingHole_retained_above_exterior T C c i j hij hi hj horder r.val.1.1 r.val.1.2 w r.val.2.1 r.val.2.2 hq hc.2 r.property
    have hend := secantAxisAdjacent_successor_unique T C (secantVisitRight T c j) r.val.2.2 v
      (by simpa only [hseam] using hc.2) hv
    rcases hmem.1 with ⟨he1,he2⟩ | ⟨he1,he2⟩
    · refine ⟨0,1,2,by simp [crossingHoleGridExterior],?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change r.val = crossingHoleOutsideCell T c i j 0 1 a b u v 2
        apply Prod.ext <;> apply Prod.ext <;>
          simp [crossingHoleOutsideCell,secantVisitHalfCell,he1,he2,hseam,hend]
      · rfl
    · refine ⟨1,1,2,by simp [crossingHoleGridExterior],?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change r.val = crossingHoleOutsideCell T c i j 1 1 a b u v 2
        apply Prod.ext <;> apply Prod.ext <;>
          simp [crossingHoleOutsideCell,secantVisitHalfCell,he1,he2,hseam,hend]
      · rfl
  · simp only [rectangleTouchesCrossingHole,show (1 : Fin 4)≠0 by decide,if_false,if_pos rfl] at ht
    obtain ⟨w,hw,hq⟩ := ht
    have hmem := (secantCrossingHoleCells_membership T C c i j hi hj r.val.1.2 w r.val.2.1 r.val.2.2).mp hq
    have hseam := crossingHole_retained_left_exterior T C c i j hij hi hj horder r.val.1.2 w r.val.2.1 r.val.2.2 r.val.1.1 hq hc.1 r.property
    have hend := secantAxisAdjacent_predecessor_unique T C r.val.1.1 a (secantVisitLeft T c i)
      (by simpa only [hseam] using hc.1) ha
    rcases hmem.2 with ⟨he1,he2⟩ | ⟨he1,he2⟩
    · refine ⟨0,0,3,by simp [crossingHoleGridExterior],?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change r.val = crossingHoleOutsideCell T c i j 0 0 a b u v 3
        apply Prod.ext <;> apply Prod.ext <;>
          simp [crossingHoleOutsideCell,secantVisitHalfCell,he1,he2,hseam,hend]
      · rfl
    · refine ⟨0,1,3,by simp [crossingHoleGridExterior],?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change r.val = crossingHoleOutsideCell T c i j 0 1 a b u v 3
        apply Prod.ext <;> apply Prod.ext <;>
          simp [crossingHoleOutsideCell,secantVisitHalfCell,he1,he2,hseam,hend]
      · rfl
  · simp only [rectangleTouchesCrossingHole,show (2 : Fin 4)≠0 by decide,if_false,show (2 : Fin 4)≠1 by decide,if_false,if_pos rfl] at ht
    obtain ⟨w,hw,hq⟩ := ht
    have hmem := (secantCrossingHoleCells_membership T C c i j hi hj r.val.1.1 r.val.1.2 r.val.2.2 w).mp hq
    have hseam := crossingHole_retained_below_exterior T C c i j hij hi hj horder r.val.1.1 r.val.1.2 r.val.2.2 w r.val.2.1 hq hc.2 r.property
    have hend := secantAxisAdjacent_predecessor_unique T C r.val.2.1 u (secantVisitLeft T c j)
      (by simpa only [hseam] using hc.2) hu
    rcases hmem.1 with ⟨he1,he2⟩ | ⟨he1,he2⟩
    · refine ⟨0,0,0,by simp [crossingHoleGridExterior],?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change r.val = crossingHoleOutsideCell T c i j 0 0 a b u v 0
        apply Prod.ext <;> apply Prod.ext <;>
          simp [crossingHoleOutsideCell,secantVisitHalfCell,he1,he2,hseam,hend]
      · rfl
    · refine ⟨1,0,0,by simp [crossingHoleGridExterior],?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change r.val = crossingHoleOutsideCell T c i j 1 0 a b u v 0
        apply Prod.ext <;> apply Prod.ext <;>
          simp [crossingHoleOutsideCell,secantVisitHalfCell,he1,he2,hseam,hend]
      · rfl
  · simp only [rectangleTouchesCrossingHole,show (3 : Fin 4)≠0 by decide,if_false,show (3 : Fin 4)≠1 by decide,if_false,show (3 : Fin 4)≠2 by decide,if_false] at ht
    obtain ⟨w,hw,hq⟩ := ht
    have hmem := (secantCrossingHoleCells_membership T C c i j hi hj w r.val.1.1 r.val.2.1 r.val.2.2).mp hq
    have hseam := crossingHole_retained_right_exterior T C c i j hij hi hj horder w r.val.1.1 r.val.2.1 r.val.2.2 r.val.1.2 hq hc.1 r.property
    have hend := secantAxisAdjacent_successor_unique T C (secantVisitRight T c i) r.val.1.2 b
      (by simpa only [hseam] using hc.1) hb
    rcases hmem.2 with ⟨he1,he2⟩ | ⟨he1,he2⟩
    · refine ⟨1,0,1,by simp [crossingHoleGridExterior],?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change r.val = crossingHoleOutsideCell T c i j 1 0 a b u v 1
        apply Prod.ext <;> apply Prod.ext <;>
          simp [crossingHoleOutsideCell,secantVisitHalfCell,he1,he2,hseam,hend]
      · rfl
    · refine ⟨1,1,1,by simp [crossingHoleGridExterior],?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change r.val = crossingHoleOutsideCell T c i j 1 1 a b u v 1
        apply Prod.ext <;> apply Prod.ext <;>
          simp [crossingHoleOutsideCell,secantVisitHalfCell,he1,he2,hseam,hend]
      · rfl

end
end DirectGLSSW.HOMFLY.PrincipalTurning

