import HoleSideInjectivity

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem secantVisitHalfCell_eq_identifies_visit {D : PLLinkDiagram} (T : BasedTraversal D)
    (c d : Fin D.nCrossing) (i j h k : Fin 2)
    (hC : componentOf D.continuation (D.incoming c i)=
      componentOf D.continuation (D.incoming d j))
    (he : secantVisitHalfCell T c i h = secantVisitHalfCell T d j k) :
    (c,i)=(d,j) := by
  have hb := secantVisitHalfCell_bounds T d j k
  apply secantVisitHalfCell_contained_unique T c d i j h hC
  · rw [he]; exact hb.1
  · rw [he]; exact hb.2.2

/-- Distinct actual crossing holes have disjoint literal clockwise-side
witnesses. The unchanged coordinate identifies a visit, hence its crossing. -/
theorem crossingHoleOutsideSide_eq_identifies_crossing {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c d : Fin D.nCrossing) (i j l m : Fin 2)
    (hij : i≠j) (hlm : l≠m)
    (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (hl : componentOf D.continuation (D.incoming d l)=C)
    (hm : componentOf D.continuation (D.incoming d m)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j)
    (horder' : crossingVisitTime T d l < crossingVisitTime T d m)
    (a b u v a' b' u' v' : ℝ)
    (ha : secantAxisAdjacent T C a (secantVisitLeft T c i))
    (hb : secantAxisAdjacent T C (secantVisitRight T c i) b)
    (hu : secantAxisAdjacent T C u (secantVisitLeft T c j))
    (hv : secantAxisAdjacent T C (secantVisitRight T c j) v)
    (ha' : secantAxisAdjacent T C a' (secantVisitLeft T d l))
    (hb' : secantAxisAdjacent T C (secantVisitRight T d l) b')
    (hu' : secantAxisAdjacent T C u' (secantVisitLeft T d m))
    (hv' : secantAxisAdjacent T C (secantVisitRight T d m) v')
    (h k h' k' : Fin 2) (s s' : Fin 4)
    (he : crossingHoleOutsideSide T C c i j hij hi hj horder a b u v ha hb hu hv h k s =
      crossingHoleOutsideSide T C d l m hlm hl hm horder' a' b' u' v' ha' hb' hu' hv' h' k' s') :
    c=d := by
  have hs : s=s' := crossingHoleOutsideSideIndex_injective (congrArg Prod.snd he)
  subst s'
  have hc := congrArg (fun e : RetainedRectangleSide T C => e.1.val) he
  change crossingHoleOutsideCell T c i j h k a b u v s =
    crossingHoleOutsideCell T d l m h' k' a' b' u' v' s at hc
  fin_cases s
  · have hhalf : secantVisitHalfCell T c i h = secantVisitHalfCell T d l h' := by
      simpa [crossingHoleOutsideCell] using congrArg Prod.fst hc
    exact congrArg Prod.fst (secantVisitHalfCell_eq_identifies_visit T c d i l h h' (hi.trans hl.symm) hhalf)
  · have hhalf : secantVisitHalfCell T c j k = secantVisitHalfCell T d m k' := by
      simpa [crossingHoleOutsideCell] using congrArg Prod.snd hc
    exact congrArg Prod.fst (secantVisitHalfCell_eq_identifies_visit T c d j m k k' (hj.trans hm.symm) hhalf)
  · have hhalf : secantVisitHalfCell T c i h = secantVisitHalfCell T d l h' := by
      simpa [crossingHoleOutsideCell] using congrArg Prod.fst hc
    exact congrArg Prod.fst (secantVisitHalfCell_eq_identifies_visit T c d i l h h' (hi.trans hl.symm) hhalf)
  · have hhalf : secantVisitHalfCell T c j k = secantVisitHalfCell T d m k' := by
      simpa [crossingHoleOutsideCell] using congrArg Prod.snd hc
    exact congrArg Prod.fst (secantVisitHalfCell_eq_identifies_visit T c d j m k k' (hj.trans hm.symm) hhalf)
end
end DirectGLSSW.HOMFLY.PrincipalTurning


