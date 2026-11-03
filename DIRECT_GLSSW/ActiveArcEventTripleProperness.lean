import ActiveArcEventPairData
import CarrierTriplePairProperness

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW Cursor RetainedWords Primitive AuxiliaryCarrierChart CarrierTriplePairProperness
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q) (c : Crossing q)
variable (U : Support q hR)

/-- The literal carrier determinant numerator for three actual event-word positions. -/
def eventTripleNumerator (i j k : Fin (openCount q hR U.val))
    (L : Fin (n+1) ⊕ Unit → CarrierLine) : ℝ :=
  let p := eventCarrierPair q hR c U
  carrierTripleNumerator (L (p i).1) (L (p i).2) (L (p j).1) (L (p j).2)
    (L (p k).1) (L (p k).2)

/-- Every nonexceptional actual-label triple has a proved nonzero numerator
witness. No independent pair assumptions are left to the consumer. -/
theorem eventTripleNumerator_nonzero_witness (hc : FirstCrossing q c) (hu : c∉U.val)
    (i j k : Fin (openCount q hR U.val)) (hij : i.val < j.val) (hjk : j.val < k.val)
    (hexc : i.val≠0 ∨ k.val≠j.val+1 ∨ eventCarrierChain q hR U j≠Sum.inl c.val.2) :
    ∃ L : Fin (n+1) ⊕ Unit → CarrierLine, eventTripleNumerator q hR c U i j k L≠0 := by
  let p := eventCarrierPair q hR c U
  let P := fun i => ({(p i).1,(p i).2} : Finset (Fin (n+1) ⊕ Unit))
  obtain ⟨hcard,hinj,hcommon⟩ := eventCarrierPair_data q hR c hc U hu
  have hne (v : Fin (openCount q hR U.val)) : (p v).1≠(p v).2 := by
    intro hh
    have hv := hcard v
    change (P v).card=2 at hv
    simp only [P,hh,Finset.pair_eq_singleton,Finset.card_singleton] at hv
    omega
  have hpq : P i≠P j := fun h => (ne_of_lt hij) (congrArg Fin.val (hinj h))
  have hqr : P j≠P k := fun h => (ne_of_lt hjk) (congrArg Fin.val (hinj h))
  have hpr : P i≠P k := fun h => (ne_of_lt (lt_trans hij hjk)) (congrArg Fin.val (hinj h))
  have hno : ¬∃ x, x∈P i ∧ x∈P j ∧ x∈P k := by
    intro hx
    obtain ⟨hi,hk,hr⟩ := (hcommon i j k hij hjk).mp hx
    rcases hexc with hh|hh|hh
    · exact hh hi
    · exact hh hk
    · exact hh hr
  exact triple_pairs_numerator_nonzero_witness (p i).1 (p i).2 (p j).1 (p j).2 (p k).1 (p k).2
    (hne i) (hne j) (hne k) hpq hqr hpr hno

theorem eventTripleNumerator_nonzero_dense (hc : FirstCrossing q c) (hu : c∉U.val)
    (i j k : Fin (openCount q hR U.val)) (hij : i.val < j.val) (hjk : j.val < k.val)
    (hexc : i.val≠0 ∨ k.val≠j.val+1 ∨ eventCarrierChain q hR U j≠Sum.inl c.val.2) :
    Dense {L | eventTripleNumerator q hR c U i j k L≠0} := by
  obtain ⟨L,hL⟩ := eventTripleNumerator_nonzero_witness q hR c U hc hu i j k hij hjk hexc
  exact CarrierDensity.dense_assignmentNumerator_ne_zero _ _ _ _ _ _ L hL

/-- At source geometry the numerator vanishes exactly at the literal event
word's determinant zero; all three denominator conditions are produced. -/
theorem eventTripleNumerator_zero_iff (hc : FirstCrossing q c) (hG1 : cyclicNoncollinear q)
    (i j k : Fin (openCount q hR U.val)) :
    eventTripleNumerator q hR c U i j k (parentChartLines (a:=n) (b:=0) q)=0 ↔
      polygonHDet (eventOpenWord q hR U c) i.val j.val k.val=0 := by
  have hi := eventCarrierPair_intersection q hR c U hc hG1 i
  have hj := eventCarrierPair_intersection q hR c U hc hG1 j
  have hk := eventCarrierPair_intersection q hR c U hc hG1 k
  unfold eventTripleNumerator
  rw [carrierTripleNumerator_zero_iff _ _ _ _ _ _ hi.1 hj.1 hk.1,hi.2,hj.2,hk.2]
  have he : polygonHDet (eventOpenWord q hR U c) i.val j.val k.val=
      -planarDet (eventOpenWord q hR U c j.val-eventOpenWord q hR U c i.val)
        (eventOpenWord q hR U c k.val-eventOpenWord q hR U c i.val) := by
    simp only [polygonHDet,planarDet,Prod.fst_sub,Prod.snd_sub]
    ring
  rw [he,neg_eq_zero]

end DirectGLSSW.ActiveArc.OpenCarrier
