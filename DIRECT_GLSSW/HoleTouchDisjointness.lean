import HoleWitnessCompleteness
import HoleSideDisjointness

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem rectangleTouchesCrossingHole_unique_crossing {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c d : Fin D.nCrossing) (i j l m : Fin 2)
    (hij : i≠j) (hlm : l≠m)
    (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (hl : componentOf D.continuation (D.incoming d l)=C)
    (hm : componentOf D.continuation (D.incoming d m)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j)
    (horder' : crossingVisitTime T d l < crossingVisitTime T d m)
    (e : RetainedRectangleSide T C)
    (ht : rectangleTouchesCrossingHole T C c i j e)
    (ht' : rectangleTouchesCrossingHole T C d l m e) : c=d := by
  obtain ⟨a,b,u,v,ha,hb,hu,hv,_⟩ := crossingHole_retainedNeighbours_exist T C c i j hij hi hj horder
  obtain ⟨a',b',u',v',ha',hb',hu',hv',_⟩ := crossingHole_retainedNeighbours_exist T C d l m hlm hl hm horder'
  obtain ⟨h,k,s,hext,he⟩ := rectangleTouchesCrossingHole_witness T C c i j hij hi hj horder
    a b u v ha hb hu hv e ht
  obtain ⟨h',k',s',hext',he'⟩ := rectangleTouchesCrossingHole_witness T C d l m hlm hl hm horder'
    a' b' u' v' ha' hb' hu' hv' e ht'
  exact crossingHoleOutsideSide_eq_identifies_crossing T C c d i j l m hij hlm hi hj hl hm horder horder'
    a b u v a' b' u' v' ha hb hu hv ha' hb' hu' hv' h k h' k' s s' (he.symm.trans he')

end
end DirectGLSSW.HOMFLY.PrincipalTurning

