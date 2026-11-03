import CyclicCarrierRealization
import ActiveArcCutGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain ActiveArc.ExposedChart

/-- Physical cut-arc carriers plus its terminal carrier are exactly the
original polygon carriers: the terminal label is the deleted closing edge. -/
def cutCarrierLabel {n : ℕ} (e : Fin (n+2)) : Fin (n+1) ⊕ Unit → Fin (n+2) :=
  Sum.elim (edgeLabel e) (fun _ => e)

theorem cutCarrierLabel_injective {n : ℕ} (e : Fin (n+2)) :
    Function.Injective (cutCarrierLabel e) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (edgeLabel_injective e h)
    | inr y => exact False.elim (edgeLabel_ne_deleted e x h)
  | inr x =>
    cases y with
    | inl y => exact False.elim (edgeLabel_ne_deleted e y h.symm)
    | inr y => congr

/-- No new genericity or density premise on the opened arc: restriction of the
already constructed original carrier family supplies both physical and terminal lines. -/
theorem cutArc_universal_supplied {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (e : Fin (n+2)) (L : Fin (n+2) → CarrierLine)
    (hU : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ i, lineValue (L i) (q i) = 0 ∧
      lineValue (L i) (q (cyclicSuccessor i)) = 0) :
    UniversalLocus (L ∘ cutCarrierLabel e) ∧ PairTransverse (L ∘ cutCarrierLabel e) ∧
      (∀ f : Fin (n+1),
        lineValue ((L ∘ cutCarrierLabel e) (Sum.inl f)) ((cutArc q e) f.castSucc) = 0 ∧
        lineValue ((L ∘ cutCarrierLabel e) (Sum.inl f)) ((cutArc q e) f.succ) = 0) ∧
      lineValue ((L ∘ cutCarrierLabel e) (Sum.inr ()))
        ((cutArc q e) ⟨n+1, by omega⟩) = 0 := by
  refine ⟨universalLocus_comap L hU _ (cutCarrierLabel_injective e),
    pairTransverse_comap L hT _ (cutCarrierLabel_injective e), ?_, ?_⟩
  · intro f
    change lineValue (L (edgeLabel e f)) (q (cyclicVertexEquiv e f.castSucc)) = 0 ∧
      lineValue (L (edgeLabel e f)) (q (cyclicVertexEquiv e f.succ)) = 0
    rw [edgeLabel_successor]
    exact hinc (edgeLabel e f)
  · simpa only [Function.comp_def, cutCarrierLabel, Sum.elim_inr, cutArc_last] using (hinc e).1

end DirectGLSSW.CyclicCarrierClearing


