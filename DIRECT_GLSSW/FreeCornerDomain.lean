import UniversalCarrierCornerDomain
import UniversalCarrierStateTransport
import PhysicalTraversalClosure
import FreeCursorNormalized
import GenericCursorWithoutCrossing
import ActiveArcCornerCurrentLimit
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CornerProjector
open Cursor Split Primitive RetainedWords OpenCarrier AuxiliaryCarrierChart UniversalCarrierDomain

theorem suffix_all_support_core_of_supplied {b : ℕ}
    (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (L : Fin (1+b+1) ⊕ Unit → CarrierLine) (hL : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (1+b+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨1+b+1,by omega⟩)=0) :
    ∀ U : Support (suffix q) (regular_suffix q hR), ShortEdgeSignStability.CoreHGeneric
      (rootedPolygonWord (OpenVertex _ _ U) (openLast _ _ U.val)) (openCount (suffix q) (regular_suffix q hR) U.val-1) := by
  have H := corner_word_core_of_supplied q (show 1+b=1+b from rfl) (by omega : 0<1)
    hR L hL hT hinc hterminal
  simpa only [dropWord_eq_literal_suffix] using H

theorem suffix_projector_far_of_supplied {b : ℕ}
    (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (L : Fin (1+b+1) ⊕ Unit → CarrierLine) (hL : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (1+b+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨1+b+1,by omega⟩)=0) :
    ∀ U : Support (suffix q) (regular_suffix q hR), ∀ k j, 1<k → k<j →
      j≤openCount (suffix q) (regular_suffix q hR) U.val →
      polygonHDet (fun i => if i=0 then q 0 else
        rootedPolygonWord (OpenVertex _ _ U) (openLast _ _ U.val) (i-1)) 1 k j≠0 := by
  have H := corner_far_of_supplied q (show 1+b=1+b from rfl) (by omega : 0<1)
    hR L hL hT hinc hterminal
  simp only [dropWord_eq_literal_suffix] at H
  exact fun U k j hk hkj hj => H U (q 0) k j hk hkj hj
end DirectGLSSW.ActiveArc.CornerProjector
