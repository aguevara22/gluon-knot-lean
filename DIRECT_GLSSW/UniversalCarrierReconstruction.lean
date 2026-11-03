import UniversalCarrierTransverse
import ActiveArcOpenRegularChart
import ActiveArcClosedAuxiliaryNeighborhood
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.UniversalCarrierDomain
open AuxiliaryCarrierChart ActiveArc ActiveArc.OpenCarrier ActiveArc.Primitive ActiveArc.ConfigurationLocality Filter Topology

/-- ONE nearby actual original arc carries a supplied universal family.
The family is constructed, not a supplied genericity or density hypothesis. -/
theorem exists_nearby_universal_supplied {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hQ : Regular q)
    (hG : cyclicNoncollinear q) (hAux : ClosedAuxiliary q hQ)
    (V : Set (Fin (n+2) → PlanarPoint ℝ)) (hV : V∈𝓝 q) :
    ∃ r∈V, ∃ hR : Regular r, ClosedAuxiliary r hR ∧ cyclicNoncollinear r ∧
      ∃ L : Fin (n+1) ⊕ Unit → CarrierLine,
        UniversalLocus L ∧ PairTransverse L ∧
        (∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (r e.castSucc)=0 ∧
          lineValue (L (Sum.inl e)) (r e.succ)=0) ∧
        lineValue (L (Sum.inr ())) (r ⟨n+1,by omega⟩)=0 := by
  let W := V ∩ {r | ∃ hR : Regular r, ClosedAuxiliary r hR}
  have hW : W∈𝓝 q := inter_mem hV (eventually_closedAuxiliary q hQ hG hAux)
  have hgeo := eventually_reconstructOpen_regular_G1 q hQ hG W hW
  obtain ⟨O,hOsub,hOopen,hObase⟩ := mem_nhds_iff.mp hgeo
  obtain ⟨L,hL,hLO⟩ := (universal_transverse_dense_open (α:=Fin (n+1) ⊕ Unit)).1.exists_mem_open
    hOopen ⟨openChartLines q,hObase⟩
  rcases hOsub hLO with ⟨_,hrW,_,hrG,hinc,_,hterminal⟩
  rcases hrW with ⟨hrV,hR,hrA⟩
  exact ⟨reconstructOpen q L,hrV,hR,hrA,hrG,L,hL.1,hL.2,hinc,hterminal⟩
end DirectGLSSW.UniversalCarrierDomain

