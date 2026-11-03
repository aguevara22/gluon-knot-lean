import PhysicalAllSuffixLocus
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc Cursor RetainedWords Primitive Split AuxiliaryCarrierChart
open ConfigurationLocality ConfigurationTransport ConfigurationParent Filter Topology
attribute [local instance] Classical.propDecidable

/-- One actual matched configuration, with every first event in this cut-size
chart on the actual target arc satisfying the finite event/cap conditions. -/
def MatchedAllFirstEvents {a b : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hQ : Regular q)
    (r : Fin (a+b+2) → PlanarPoint ℝ) : Prop :=
  ∃ hR : Regular r, ∃ E : Crossing q ≃ Crossing r,
    ∃ hlabels : ∀ d, (E d).val=d.val,
    (∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
      (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y)) ∧
    cyclicNoncollinear r ∧
    ∀ (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a),
      FirstCrossing r (E c) ∧
      (∀ S : Support r hR, E c∉S.val → EventCarrierNonvanishing r hR (E c) S) ∧
      parentFarLocus r hR (E c) (mapped_cut q r E hlabels c hcut) (parentChartLines r)

/-- ONE nearby ORIGINAL arc realizes the actual event/cap domains on EVERY
literal corner suffix simultaneously. No density, order, transport, numerator,
or current identity is a caller premise. -/
theorem exists_nearby_all_suffix_domains {N : ℕ}
    (q : Fin (N+2) → PlanarPoint ℝ) (hQ : Regular q)
    (hG1 : cyclicNoncollinear q) (hAux : ClosedAuxiliary q hQ)
    (V : Set (Fin (N+2) → PlanarPoint ℝ)) (hV : V∈𝓝 q) :
    ∃ r∈V, (∃ hR : Regular r, ClosedAuxiliary r hR) ∧ cyclicNoncollinear r ∧
      ∀ t : SuffixShape N,
        MatchedAllFirstEvents (suffixWord q t) (suffixRegular q hQ t) (suffixWord r t) := by
  let P := fun (t : SuffixShape N) (r : Fin (N+2) → PlanarPoint ℝ) =>
    ∃ hS : Regular (suffixWord r t), ∃ E : Crossing (suffixWord q t) ≃ Crossing (suffixWord r t),
      (∀ d, (E d).val=d.val) ∧
      (∀ x y : Event (suffixWord q t),
        (eventOrder (suffixWord q t) (suffixRegular q hQ t).noTriple).lt x y ↔
        (eventOrder (suffixWord r t) hS.noTriple).lt
          (eventMapEquiv (suffixWord q t) (suffixWord r t) E x)
          (eventMapEquiv (suffixWord q t) (suffixWord r t) E y))
  have hP : ∀ᶠ r in 𝓝 q, ∀ t, P t r := by
    apply eventually_all.mpr
    intro t
    have hg := dropWord_G1 q t.property hG1
    have hh := eventually_configuration_event_order (suffixWord q t) (suffixRegular q hQ t) hg
    exact (dropWord_continuous t.property).continuousAt.tendsto.eventually hh
  have hA : {r | ∃ hR : Regular r, ClosedAuxiliary r hR}∈𝓝 q :=
    eventually_closedAuxiliary q hQ hG1 hAux
  let W := V ∩ {r | ∃ hR : Regular r, ClosedAuxiliary r hR} ∩ {r | ∀ t, P t r}
  have hW : W∈𝓝 q := inter_mem (inter_mem hV hA) hP
  have hgeo := eventually_reconstructOpen_regular_G1 q hQ hG1 W hW
  have hden : ∀ᶠ L in 𝓝 (openChartLines q), ∀ i : SuffixEventIndex q,
      (∀ U : Support (suffixWord q i.1) (suffixRegular q hQ i.1),
        ∀ j : Fin (openCount (suffixWord q i.1) (suffixRegular q hQ i.1) U.val),
        lineDenominator
          (dropCarriers i.1.property L (eventCarrierPair (suffixWord q i.1) (suffixRegular q hQ i.1) i.2.val U j).1)
          (dropCarriers i.1.property L (eventCarrierPair (suffixWord q i.1) (suffixRegular q hQ i.1) i.2.val U j).2)≠0) ∧
      (∀ T : Support (parent (suffixWord q i.1) i.2.val i.2.property.2)
          (regular_parent (suffixWord q i.1) (suffixRegular q hQ i.1) i.2.val i.2.property.2),
        ∀ j : Fin (openCount (parent (suffixWord q i.1) i.2.val i.2.property.2)
          (regular_parent (suffixWord q i.1) (suffixRegular q hQ i.1) i.2.val i.2.property.2) T.val),
        lineDenominator
          (dropCarriers i.1.property L (parentCarrierChain (suffixWord q i.1) (suffixRegular q hQ i.1)
            i.2.val i.2.property.2 T j.castSucc))
          (dropCarriers i.1.property L (parentCarrierChain (suffixWord q i.1) (suffixRegular q hQ i.1)
            i.2.val i.2.property.2 T j.succ))≠0) := by
    apply eventually_all.mpr
    intro i
    have hg := dropWord_G1 q i.1.property hG1
    have ht : Tendsto (dropCarriers i.1.property) (𝓝 (openChartLines q))
        (𝓝 (parentChartLines (suffixWord q i.1))) := by
      have hh := (dropCarriers_continuous i.1.property).continuousAt.tendsto (x:=openChartLines q)
      rw [dropCarriers_chart] at hh
      exact hh
    exact ht.eventually ((eventually_event_pair_denominators (suffixWord q i.1) (suffixRegular q hQ i.1)
      i.2.val i.2.property.1 hg).and
      (eventually_parent_chain_denominators (suffixWord q i.1) (suffixRegular q hQ i.1) i.2.val i.2.property.2 hg))
  obtain ⟨O,hOsub,hOopen,hObase⟩ := mem_nhds_iff.mp (hgeo.and hden)
  obtain ⟨L,hL,hLO⟩ := (allSuffixCarrierLocus_dense_open q hQ).1.exists_mem_open
    hOopen ⟨openChartLines q,hObase⟩
  rcases hOsub hLO with ⟨hgeometry,hDen⟩
  rcases hgeometry with ⟨hvalid,hmem,hreg,hg1,hinc,hinit,hterminal⟩
  let r := reconstructOpen q L
  rcases hmem with ⟨⟨hrV,hrA⟩,hrP⟩
  refine ⟨r,hrV,hrA,hg1,?_⟩
  intro t
  rcases hrP t with ⟨hS,E,hlabels,horder⟩
  have hgs : cyclicNoncollinear (suffixWord r t) := dropWord_G1 r t.property hg1
  refine ⟨hS,E,hlabels,horder,hgs,?_⟩
  intro c hc hcut
  let i : SuffixEventIndex q := ⟨t,⟨c,hc,hcut⟩⟩
  have hDom := hL i
  have hDe := (hDen i).1
  have hDp := (hDen i).2
  have hincs : ∀ e : Fin (t.val.2.1.val+t.val.2.2.val+1),
      lineValue (dropCarriers t.property L (Sum.inl e)) (suffixWord r t e.castSucc)=0 ∧
      lineValue (dropCarriers t.property L (Sum.inl e)) (suffixWord r t e.succ)=0 := by
    intro e
    exact hinc (dropEdge t.property e)
  have hterms : lineValue (dropCarriers t.property L (Sum.inr ()))
      (suffixWord r t ⟨t.val.2.1.val+t.val.2.2.val+1,by omega⟩)=0 := by
    have hi : dropVertex t.property ⟨t.val.2.1.val+t.val.2.2.val+1,by omega⟩ =
        (⟨N+1,by omega⟩ : Fin (N+2)) := Fin.ext (by dsimp [dropVertex]; have := t.property; omega)
    simpa only [dropCarriers,Sum.map_inr,suffixWord,dropWord,hi] using hterminal
  have hfirst := firstCrossing_transport_of_event_order (suffixWord q t) (suffixWord r t)
    (suffixRegular q hQ t) hS E hlabels horder c hc
  have hF := all_event_nonvanishing (suffixWord q t) (suffixWord r t) (suffixRegular q hQ t)
    hS E hlabels horder c hc (dropCarriers t.property L) hincs hterms hDe hDom.1
  have hFar : parentFarLocus (suffixWord r t) hS (E c)
      (mapped_cut (suffixWord q t) (suffixWord r t) E hlabels c hcut)
      (parentChartLines (suffixWord r t)) := by
    intro T j l hj hjl hz
    exact all_parent_far_nonzero (suffixWord q t) (suffixWord r t) (suffixRegular q hQ t)
      hS E hlabels horder c hc hcut (dropCarriers t.property L) hincs hterms hDp hDom.2 T j l hj hjl
      ((parent_far_numerator_zero_iff (suffixWord r t) hS (E c)
        (mapped_cut (suffixWord q t) (suffixWord r t) E hlabels c hcut) hgs T j l).mp hz)
  exact ⟨hfirst,hF,hFar⟩
end DirectGLSSW.ActiveArc.OpenCarrier
