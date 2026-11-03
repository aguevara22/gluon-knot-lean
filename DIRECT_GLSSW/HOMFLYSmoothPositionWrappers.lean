import HOMFLYSmoothingVisitTransport
import HOMFLYCutNormalization
set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
open Equiv PermutationOrbits

theorem smoothConnector_orbitPosition (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (i : Fin 2) (x : Fin D.nArc)
    (hc : componentOf (cutContinuation D c) x =
      componentOf (cutContinuation D c) (D.incoming c i))
    (hx : x ≠ D.incoming c i)
    (hs : componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl x)) =
      componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inr i))) :
    ((orbitEnumeration (smoothCrossing D c).continuation
      (smoothArcEquiv D (Sum.inr i))).symm ⟨smoothArcEquiv D (Sum.inl x), hs⟩).val =
    ((orbitEnumeration (cutContinuation D c) (D.incoming c i)).symm ⟨x,hc⟩).val := by
  exact smoothConnector_actual_orbitPosition D c hself i ⟨x,hc⟩ hx

theorem smoothUnaffected_orbitPosition (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (root x : Fin D.nArc)
    (ha : ¬ D.continuation.SameCycle root (D.incoming c 0))
    (hc : componentOf D.continuation x = componentOf D.continuation root)
    (hs : componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl x)) =
      componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl root))) :
    ((orbitEnumeration (smoothCrossing D c).continuation
      (smoothArcEquiv D (Sum.inl root))).symm ⟨smoothArcEquiv D (Sum.inl x),hs⟩).val =
    ((orbitEnumeration D.continuation root).symm ⟨x,hc⟩).val := by
  exact smoothUnaffected_actual_orbitPosition D c hself root ha ⟨x,hc⟩

end DirectGLSSW.HOMFLY


