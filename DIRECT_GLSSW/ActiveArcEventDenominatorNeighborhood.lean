import ActiveArcEventCarrierFamily
import ActiveArcOpenRegularChart
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc Cursor RetainedWords Primitive AuxiliaryCarrierChart Filter Topology
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)

include hc in
/-- All actual event-word carrier pairs stay transverse near the source chart. -/
theorem eventually_event_pair_denominators (hG1 : cyclicNoncollinear q) :
    ∀ᶠ L in 𝓝 (parentChartLines (a:=n) (b:=0) q),
      ∀ U : Support q hR, ∀ i : Fin (openCount q hR U.val),
        lineDenominator (L (eventCarrierPair q hR c U i).1)
          (L (eventCarrierPair q hR c U i).2)≠0 := by
  classical
  apply Filter.eventually_all.mpr
  intro U
  apply Filter.eventually_all.mpr
  intro i
  have hcont : Continuous (fun L : Fin (n+1) ⊕ Unit → CarrierLine =>
      lineDenominator (L (eventCarrierPair q hR c U i).1)
        (L (eventCarrierPair q hR c U i).2)) := by
    unfold lineDenominator planarDet
    fun_prop
  exact hcont.continuousAt.eventually_ne (eventCarrierPair_intersection q hR c U hc hG1 i).1

include hc in
/-- The proved dense event locus meets every chart neighborhood while all
actual pair denominators remain nonzero. -/
theorem exists_nearby_event_locus_and_denominators (hG1 : cyclicNoncollinear q)
    (V : Set (Fin (n+1) ⊕ Unit → CarrierLine))
    (hV : V ∈ 𝓝 (parentChartLines (a:=n) (b:=0) q)) :
    ∃ L ∈ V, eventCarrierLocus q hR c L ∧
      ∀ U : Support q hR, ∀ i : Fin (openCount q hR U.val),
        lineDenominator (L (eventCarrierPair q hR c U i).1)
          (L (eventCarrierPair q hR c U i).2)≠0 := by
  have hD := eventually_event_pair_denominators q hR c hc hG1
  have hJoint := Filter.Eventually.and hV hD
  obtain ⟨W,hWsub,hWopen,hWbase⟩ := mem_nhds_iff.mp hJoint
  obtain ⟨L,hLF,hLW⟩ := (event_carrier_family_dense_open q hR c hc).1.exists_mem_open
    hWopen ⟨parentChartLines (a:=n) (b:=0) q,hWbase⟩
  exact ⟨L,(hWsub hLW).1,hLF,(hWsub hLW).2⟩
end DirectGLSSW.ActiveArc.OpenCarrier
