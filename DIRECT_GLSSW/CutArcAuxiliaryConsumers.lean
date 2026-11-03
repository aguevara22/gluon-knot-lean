import CyclicCarrierCharacterizations
import AllEdgeCapRealization
import UniversalCarrierStateTransport
import UniversalCarrierEventDomain
import UniversalCarrierParentCore
import UniversalCarrierCornerDomain

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain ActiveArc ActiveArc.ExposedChart
open ActiveArc.Cursor ActiveArc.Split ActiveArc.Primitive ActiveArc.RetainedWords ActiveArc.OpenCarrier

 theorem cutArc_event_nonvanishing {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin (n+2)) (L : Fin (n+2) → CarrierLine)
    (hU : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ i, lineValue (L i) (q i) = 0 ∧ lineValue (L i) (q (cyclicSuccessor i)) = 0)
    (c : Crossing (cutArc q e)) (hc : FirstCrossing (cutArc q e) c) :
    ∀ S : Support (cutArc q e) (cutArc_regular q e hq), c ∉ S.val →
      EventCarrierNonvanishing (cutArc q e) (cutArc_regular q e hq) c S := by
  obtain ⟨hu,ht,hi,hz⟩ := cutArc_universal_supplied q e L hU hT hinc
  exact event_domain_of_supplied (cutArc q e) (cutArc_regular q e hq) c hc
    (L ∘ cutCarrierLabel e) hu ht hi hz

 theorem cutArc_parent_far_and_core {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e : Fin (a+b+2)) (L : Fin (a+b+2) → CarrierLine)
    (hU : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ i, lineValue (L i) (q i) = 0 ∧ lineValue (L i) (q (cyclicSuccessor i)) = 0)
    (c : Crossing (cutArc q e)) (hcut : c.val.2.val = a) :
    parentFarLocus (cutArc q e) (cutArc_regular q e hq) c hcut (parentChartLines (cutArc q e)) ∧
      ∀ S : Support (parent (cutArc q e) c hcut)
        (regular_parent (cutArc q e) (cutArc_regular q e hq) c hcut),
      ShortEdgeSignStability.CoreHGeneric
        (rootedPolygonWord (OpenVertex _ _ S) (openLast _ _ S.val))
        (openCount (parent (cutArc q e) c hcut)
          (regular_parent (cutArc q e) (cutArc_regular q e hq) c hcut) S.val-1) := by
  obtain ⟨hu,ht,hi,hz⟩ := cutArc_universal_supplied q e L hU hT hinc
  have hg : CyclicGeneric (cutArc q e) := InteriorEdgeEvents.opened_generic q hq e
  exact ⟨canonical_parent_far_of_supplied (cutArc q e) (cutArc_regular q e hq) hg.g1 c hcut
    (L ∘ cutCarrierLabel e) hu ht hi hz,
    parent_all_support_core_of_supplied (cutArc q e) (cutArc_regular q e hq) c hcut
      (L ∘ cutCarrierLabel e) hu ht hi hz⟩

/-- Literal recursive cut-parent restriction of the one original family. -/
 theorem cutArc_parent_supplied {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (e : Fin (a+b+2)) (L : Fin (a+b+2) → CarrierLine)
    (hU : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ i, lineValue (L i) (q i) = 0 ∧ lineValue (L i) (q (cyclicSuccessor i)) = 0)
    (c : Crossing (cutArc q e)) (hcut : c.val.2.val = a) :
    let M := (L ∘ cutCarrierLabel e) ∘ suffixCarrierMap (a := a) (b := b)
    UniversalLocus M ∧ PairTransverse M ∧
      (∀ i : Fin (b+1),
        lineValue (M (Sum.inl i)) (parent (cutArc q e) c hcut i.castSucc) = 0 ∧
        lineValue (M (Sum.inl i)) (parent (cutArc q e) c hcut i.succ) = 0) ∧
      lineValue (M (Sum.inr ())) (parent (cutArc q e) c hcut ⟨b+1,by omega⟩) = 0 := by
  obtain ⟨hu,ht,hi,hz⟩ := cutArc_universal_supplied q e L hU hT hinc
  exact universal_supplied_parent (cutArc q e) c hcut (L ∘ cutCarrierLabel e) hu ht hi hz

end DirectGLSSW.CyclicCarrierClearing



