import DirectGLSSW.HOMFLY.HOMFYSmoothingOldArcInteriors
import Mathlib.Tactic.FinCases

namespace DirectGLSSW.HOMFLY

def smoothCodeArcPoint (D : PLLinkDiagram) (c : Fin D.nCrossing) (ε : ℝ)
    (e : SmoothArcCode D) (s : ℝ) : PlanarPoint ℝ :=
  DirectGLSSW.affinePoint
    (smoothVertexPointGeometryCode D c ε (smoothArcSourceCode D c e))
    (smoothVertexPointGeometryCode D c ε (smoothArcTargetCode D c e)) s

theorem smoothOldArcCode_interiors_disjoint (D : PLLinkDiagram)
    (c : Fin D.nCrossing) (ε : ℝ) (hε : 0 < ε)
    (hεr : ε < crossingCutoffRadius D c) (e f : Fin D.nArc) (hef : e ≠ f)
    (s t : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    smoothCodeArcPoint D c ε (Sum.inl e) s ≠ smoothCodeArcPoint D c ε (Sum.inl f) t := by
  intro h
  obtain ⟨s', hs'0, hs'1, hs'⟩ :=
    smoothOldArcInterior_lies_oldInterior D c ε e s hε hεr hs0 hs1
  obtain ⟨t', ht'0, ht'1, ht'⟩ :=
    smoothOldArcInterior_lies_oldInterior D c ε f t hε hεr ht0 ht1
  apply D.arc_interiors_disjoint e f hef s' t' hs'0 hs'1 ht'0 ht'1
  calc
    DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource e))
        (D.vertexPoint (D.arcTarget e)) s' = smoothCodeArcPoint D c ε (Sum.inl e) s := hs'.symm
    _ = smoothCodeArcPoint D c ε (Sum.inl f) t := h
    _ = DirectGLSSW.affinePoint (D.vertexPoint (D.arcSource f))
        (D.vertexPoint (D.arcTarget f)) t' := ht'

end DirectGLSSW.HOMFLY
