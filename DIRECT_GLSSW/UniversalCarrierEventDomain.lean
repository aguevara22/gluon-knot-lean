import UniversalCarrierConsumers
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
noncomputable section
namespace DirectGLSSW.UniversalCarrierDomain
open AuxiliaryCarrierChart ActiveArc ActiveArc.Cursor ActiveArc.RetainedWords
open ActiveArc.Primitive ActiveArc.OpenCarrier

/-- The one supplied generic family supplies the actual event-word hF for
EVERY unselected support at ANY actual first event on the current state. -/
theorem event_domain_of_supplied {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c)
    (L : Fin (n+1) ⊕ Unit → CarrierLine)
    (hL : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (n+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨n+1,by omega⟩)=0) :
    ∀ U : Support q hR, c∉U.val → EventCarrierNonvanishing q hR c U := by
  intro U hu
  let p := eventCarrierPair q hR c U
  have hcard := (eventCarrierPair_data q hR c hc U hu).1
  have hd (v : Fin (openCount q hR U.val)) :
      lineDenominator (L (p v).1) (L (p v).2)≠0 := by
    apply hT
    intro he
    have hh := hcard v
    change ({(p v).1,(p v).2} : Finset (Fin (n+1) ⊕ Unit)).card=2 at hh
    simp only [he,Finset.pair_eq_singleton,Finset.card_singleton] at hh
    omega
  have hx (v : Fin (openCount q hR U.val)) :=
    event_pair_supplied_intersection q hR c U L hinc hterminal hc v (hd v)
  intro i j k hij hjk hkN hexc hz
  have hiN : i < openCount q hR U.val := by omega
  have hjN : j < openCount q hR U.val := by omega
  have hkN' : k < openCount q hR U.val := by omega
  have hjSide : j < openCount q hR U.val-1 := by omega
  let I : Fin (openCount q hR U.val) := ⟨i,hiN⟩
  let J : Fin (openCount q hR U.val) := ⟨j,hjN⟩
  let K : Fin (openCount q hR U.val) := ⟨k,hkN'⟩
  have hexc' : I.val≠0 ∨ K.val≠J.val+1 ∨ eventCarrierChain q hR U J≠Sum.inl c.val.2 := by
    rcases hexc with hh|hh|hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
    · right;right
      intro he
      apply hh
      simpa only [J,eventCarrierChain,dif_pos hjSide,Sum.inl.injEq] using he
  have hn := universal_event_locus q hR c hc L hL U hu I J K hij hjk hexc'
  apply hn
  change carrierTripleNumerator (L (p I).1) (L (p I).2)
    (L (p J).1) (L (p J).2) (L (p K).1) (L (p K).2)=0
  apply (carrierTripleNumerator_zero_iff _ _ _ _ _ _ (hd I) (hd J) (hd K)).2
  rw [hx I,hx J,hx K]
  change planarDet (eventOpenWord q hR U c j-eventOpenWord q hR U c i)
    (eventOpenWord q hR U c k-eventOpenWord q hR U c i)=0
  unfold polygonHDet at hz
  unfold planarDet at hz ⊢
  simp only [Prod.fst_sub,Prod.snd_sub] at hz ⊢
  nlinarith
end DirectGLSSW.UniversalCarrierDomain

