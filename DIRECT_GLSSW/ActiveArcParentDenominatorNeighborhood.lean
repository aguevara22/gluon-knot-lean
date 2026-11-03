import ActiveArcParentFarFamily
import ActiveArcOpenRegularChart

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc RetainedWords Split AuxiliaryCarrierChart Filter Topology
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hcut : c.val.2.val=a)

/-- All adjacent line pairs in the fixed actual parent-support family stay transverse. -/
theorem eventually_parent_chain_denominators (hG1 : cyclicNoncollinear q) :
    ∀ᶠ L in 𝓝 (parentChartLines q),
      ∀ T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut),
      ∀ i : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val),
        lineDenominator (L (parentCarrierChain q hR c hcut T i.castSucc))
          (L (parentCarrierChain q hR c hcut T i.succ))≠0 := by
  classical
  apply Filter.eventually_all.mpr
  intro T
  apply Filter.eventually_all.mpr
  intro i
  have hc : Continuous (fun L : Fin (a+b+1) ⊕ Unit → CarrierLine =>
      lineDenominator (L (parentCarrierChain q hR c hcut T i.castSucc))
        (L (parentCarrierChain q hR c hcut T i.succ))) := by
    unfold lineDenominator planarDet
    fun_prop
  exact hc.continuousAt.eventually_ne (parent_vertex_intersection q hR c hcut T hG1 i).1

/-- The dense actual far-numerator locus meets any neighborhood while preserving
all fixed-family intersection denominators. No far nonvanishing is assumed. -/
theorem exists_nearby_parent_far_and_denominators (hG1 : cyclicNoncollinear q)
    (V : Set (Fin (a+b+1) ⊕ Unit → CarrierLine)) (hV : V ∈ 𝓝 (parentChartLines q)) :
    ∃ L ∈ V, parentFarLocus q hR c hcut L ∧
      ∀ T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut),
      ∀ i : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val),
        lineDenominator (L (parentCarrierChain q hR c hcut T i.castSucc))
          (L (parentCarrierChain q hR c hcut T i.succ))≠0 := by
  have hD := eventually_parent_chain_denominators q hR c hcut hG1
  have hJoint := Filter.Eventually.and hV hD
  obtain ⟨W,hWsub,hWopen,hWbase⟩ := mem_nhds_iff.mp hJoint
  obtain ⟨L,hLF,hLW⟩ := (parent_far_family_dense_open q hR c hcut).1.exists_mem_open
    hWopen ⟨parentChartLines q,hWbase⟩
  exact ⟨L,(hWsub hLW).1,hLF,(hWsub hLW).2⟩



end DirectGLSSW.ActiveArc.OpenCarrier
