import ActiveArcEventDenominatorNeighborhood
import ActiveArcParentDenominatorNeighborhood
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc Cursor RetainedWords Primitive Split AuxiliaryCarrierChart Filter Topology
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)

include hc in
/-- Both finite determinant families are simultaneously dense and open on
one and the same original physical-carrier/terminal-coordinate assignment. -/
theorem event_parent_carrier_dense_open :
    Dense {L | eventCarrierLocus q hR c L ∧ parentFarLocus q hR c hcut L} ∧
    IsOpen {L | eventCarrierLocus q hR c L ∧ parentFarLocus q hR c hcut L} := by
  have he := event_carrier_family_dense_open q hR c hc
  have hp := parent_far_family_dense_open q hR c hcut
  exact ⟨he.1.inter_of_isOpen_left hp.1 he.2,he.2.inter hp.2⟩

include hc in
/-- The joint dense family meets every original carrier neighborhood while
both actual finite families' denominators remain nonzero. -/
theorem exists_nearby_joint_carriers (hG1 : cyclicNoncollinear q)
    (V : Set (Fin (a+b+1) ⊕ Unit → CarrierLine)) (hV : V ∈ 𝓝 (parentChartLines q)) :
    ∃ L ∈ V, (eventCarrierLocus q hR c L ∧ parentFarLocus q hR c hcut L) ∧
      (∀ U : Support q hR, ∀ i : Fin (openCount q hR U.val),
        lineDenominator (L (eventCarrierPair q hR c U i).1)
          (L (eventCarrierPair q hR c U i).2)≠0) ∧
      ∀ T : Support (parent q c hcut) (regular_parent q hR c hcut),
      ∀ i : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val),
        lineDenominator (L (parentCarrierChain q hR c hcut T i.castSucc))
          (L (parentCarrierChain q hR c hcut T i.succ))≠0 := by
  have he := eventually_event_pair_denominators q hR c hc hG1
  have hp := eventually_parent_chain_denominators q hR c hcut hG1
  have hJoint := Filter.Eventually.and hV (he.and hp)
  obtain ⟨W,hWsub,hWopen,hWbase⟩ := mem_nhds_iff.mp hJoint
  obtain ⟨L,hLF,hLW⟩ := (event_parent_carrier_dense_open q hR c hc hcut).1.exists_mem_open
    hWopen ⟨parentChartLines q,hWbase⟩
  exact ⟨L,(hWsub hLW).1,hLF,(hWsub hLW).2⟩

include hc in
/-- One genuine reconstructed arc realizes both dense families, with all
physical incidences and denominators needed by their actual-word transfers. -/
theorem exists_reconstructed_joint_chart (hG1 : cyclicNoncollinear q)
    (V : Set (Fin (a+b+2) → PlanarPoint ℝ)) (hV : V ∈ 𝓝 q) :
    ∃ L : Fin (a+b+1) ⊕ Unit → CarrierLine,
      (OpenChartNondegenerate q L ∧ reconstructOpen q L∈V ∧
      Regular (reconstructOpen q L) ∧ cyclicNoncollinear (reconstructOpen q L) ∧
      (∀ e : Fin (a+b+1),
        lineValue (L (Sum.inl e)) (reconstructOpen q L e.castSucc)=0 ∧
        lineValue (L (Sum.inl e)) (reconstructOpen q L e.succ)=0) ∧
      lineValue (initialLine q) (reconstructOpen q L 0)=0 ∧
      lineValue (L (Sum.inr ())) (reconstructOpen q L ⟨a+b+1,by omega⟩)=0) ∧
      (eventCarrierLocus q hR c L ∧ parentFarLocus q hR c hcut L) ∧
      (∀ U : Support q hR, ∀ i : Fin (openCount q hR U.val),
        lineDenominator (L (eventCarrierPair q hR c U i).1)
          (L (eventCarrierPair q hR c U i).2)≠0) ∧
      ∀ T : Support (parent q c hcut) (regular_parent q hR c hcut),
      ∀ i : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val),
        lineDenominator (L (parentCarrierChain q hR c hcut T i.castSucc))
          (L (parentCarrierChain q hR c hcut T i.succ))≠0 := by
  have hnear := eventually_reconstructOpen_regular_G1 q hR hG1 V hV
  change ∀ᶠ L in 𝓝 (parentChartLines q), _ at hnear
  exact exists_nearby_joint_carriers q hR c hc hcut hG1 _ hnear
end DirectGLSSW.ActiveArc.OpenCarrier
