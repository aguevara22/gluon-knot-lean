import ActiveArcPhysicalJointAuxiliary
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW AuxiliaryCarrierChart Topology

/-- Literal deletion of edge zero from the physical carrier assignment;
the original terminal coordinate line is retained. -/
def suffixCarrierProjection {n : ℕ}
    (L : Fin (n+2) ⊕ Unit → CarrierLine) : Fin (n+1) ⊕ Unit → CarrierLine :=
  fun i => L (i.map Fin.succ id)

private def suffixCarrierSplit {n : ℕ} :
    (Fin (n+2) ⊕ Unit → CarrierLine) ≃ₜ
      CarrierLine × (Fin (n+1) ⊕ Unit → CarrierLine) where
  toFun L := (L (Sum.inl 0), suffixCarrierProjection L)
  invFun P := Sum.elim (Fin.cases P.1 (fun i => P.2 (Sum.inl i))) (fun u => P.2 (Sum.inr u))
  left_inv L := by
    funext i
    rcases i with i|u
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · rfl
  right_inv P := by
    apply Prod.ext
    · rfl
    · funext i
      cases i <;> rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_apply _
    · exact continuous_pi (fun i => continuous_apply _)
  continuous_invFun := by
    apply continuous_pi
    intro i
    cases i with
    | inl i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact continuous_fst
      · change Continuous (fun P : CarrierLine × (Fin (n+1) ⊕ Unit → CarrierLine) => P.2 (Sum.inl j))
        exact (continuous_apply _).comp continuous_snd
    | inr u => exact (continuous_apply _).comp continuous_snd

theorem suffixCarrierProjection_continuous {n : ℕ} :
    Continuous (suffixCarrierProjection (n:=n)) :=
  continuous_pi (fun i => continuous_apply _)

theorem suffixCarrierProjection_isOpenMap {n : ℕ} :
    IsOpenMap (suffixCarrierProjection (n:=n)) :=
  isOpenMap_snd.comp suffixCarrierSplit.isOpenMap

/-- A concrete suffix carrier domain remains dense and open when imposed on
the original carriers. No geometric determinant is assumed. -/
theorem suffix_event_parent_carrier_dense_open {a b : ℕ}
    (qs : Fin (a+b+2) → PlanarPoint ℝ) (hs : Regular qs)
    (d : Crossing qs) (hd : Cursor.FirstCrossing qs d) (hcut : d.val.2.val=a) :
    Dense {L : Fin (a+b+2) ⊕ Unit → CarrierLine |
      eventCarrierLocus qs hs d (suffixCarrierProjection L) ∧
        parentFarLocus qs hs d hcut (suffixCarrierProjection L)} ∧
    IsOpen {L : Fin (a+b+2) ⊕ Unit → CarrierLine |
      eventCarrierLocus qs hs d (suffixCarrierProjection L) ∧
        parentFarLocus qs hs d hcut (suffixCarrierProjection L)} := by
  have hh := event_parent_carrier_dense_open qs hs d hd hcut
  exact ⟨hh.1.preimage suffixCarrierProjection_isOpenMap,
    hh.2.preimage suffixCarrierProjection_continuous⟩

end DirectGLSSW.ActiveArc.OpenCarrier
