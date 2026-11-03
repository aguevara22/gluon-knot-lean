import UniversalCarrierChains
import ActiveArcEventCarrierFamily
import ActiveArcParentFarFamily
import ActiveArcParentSuppliedLines
import ActiveArcEventSuppliedLines
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
noncomputable section
namespace DirectGLSSW.UniversalCarrierDomain
open AuxiliaryCarrierChart ActiveArc ActiveArc.Cursor ActiveArc.Split
open ActiveArc.RetainedWords ActiveArc.Primitive ActiveArc.OpenCarrier

/-- Every actual parent support receives its far domain from the SAME global
carrier locus. No first-event or support enumeration is assumed. -/
theorem universal_parent_far {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)
    (hR : Regular q) (c : Crossing q) (hcut : c.val.2.val=a)
    (L : Fin (a+b+1) ⊕ Unit → CarrierLine) (hL : UniversalLocus L) :
    parentFarLocus q hR c hcut L := by
  intro T i j hi hij
  exact universal_chain_far L hL (parentCarrierChain q hR c hcut T)
    (parentCarrierChain_injective q hR c hcut T)
    (openFirst (parent q c hcut) (regular_parent q hR c hcut) T.val) i j rfl hi hij

/-- Every nonexceptional first-event numerator is one of the global proper
triples. The actual event-pair combinatorics proves every exclusion. -/
theorem universal_event_locus {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hR : Regular q) (c : Crossing q) (hc : FirstCrossing q c)
    (L : Fin (n+1) ⊕ Unit → CarrierLine) (hL : UniversalLocus L) :
    eventCarrierLocus q hR c L := by
  intro U hu i j k hij hjk hexc
  let p := eventCarrierPair q hR c U
  let P := fun v => ({(p v).1,(p v).2} : Finset (Fin (n+1) ⊕ Unit))
  obtain ⟨hcard,hinj,hcommon⟩ := eventCarrierPair_data q hR c hc U hu
  have hne (v) : (p v).1≠(p v).2 := by
    intro hh
    have hv := hcard v
    change (P v).card=2 at hv
    simp only [P,hh,Finset.pair_eq_singleton,Finset.card_singleton] at hv
    omega
  apply hL
  refine ⟨hne i,hne j,hne k,
    fun he => (ne_of_lt hij) (congrArg Fin.val (hinj he)),
    fun he => (ne_of_lt hjk) (congrArg Fin.val (hinj he)),
    fun he => (ne_of_lt (lt_trans hij hjk)) (congrArg Fin.val (hinj he)),?_⟩
  intro hx
  obtain ⟨hi,hk,hr⟩ := (hcommon i j k hij hjk).mp hx
  rcases hexc with hh|hh|hh
  · exact hh hi
  · exact hh hk
  · exact hh hr

/-- An arbitrary supplied transversal family proves the canonical parent hL
needed by transport. Incidence, rather than a canonical-line equality, is used. -/
theorem canonical_parent_far_of_supplied {a b : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q) (hG : cyclicNoncollinear q)
    (c : Crossing q) (hcut : c.val.2.val=a)
    (L : Fin (a+b+1) ⊕ Unit → CarrierLine)
    (hL : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (a+b+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨a+b+1,by omega⟩)=0) :
    parentFarLocus q hR c hcut (parentChartLines q) := by
  intro T i j hi hij hz
  let P := parent q c hcut
  let hP := regular_parent q hR c hcut
  let z := openFirst P hP T.val
  let f := parentCarrierChain q hR c hcut T
  have hd (v : Fin (openCount P hP T.val)) : lineDenominator (L (f v.castSucc)) (L (f v.succ))≠0 := by
    apply hT
    intro he
    have hh := congrArg Fin.val (parentCarrierChain_injective q hR c hcut T he)
    simp only [Fin.coe_castSucc,Fin.val_succ] at hh
    omega
  have hx (v : Fin (openCount P hP T.val)) :=
    parent_vertex_supplied_line_intersection q hR c hcut T L hinc hterminal v (hd v)
  have hp : OpenVertex P hP T z=ActiveArc.crossingPoint q c :=
    (open_vertex_first P hP T.val).trans (parent_zero q c hcut)
  have hn := universal_parent_far q hR c hcut L hL T i j hi hij
  apply hn
  change carrierTripleNumerator (L (f z.castSucc)) (L (f z.succ))
    (L (f i.castSucc)) (L (f i.succ)) (L (f j.castSucc)) (L (f j.succ))=0
  apply (carrierTripleNumerator_zero_iff _ _ _ _ _ _ (hd z) (hd i) (hd j)).2
  rw [hx z,hx i,hx j,hp]
  exact (parent_far_numerator_zero_iff q hR c hcut hG T i j).mp hz
end DirectGLSSW.UniversalCarrierDomain



