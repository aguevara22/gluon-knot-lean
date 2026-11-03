import PhysicalResizedSuffix
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc Cursor RetainedWords Primitive Split AuxiliaryCarrierChart
open ConfigurationLocality ConfigurationTransport ConfigurationParent Filter Topology

/-- Exact matched physical first-event domain. All conditions concern the
actual target arc; the crossing labels and full event order are explicit. -/
def MatchedFirstEventDomain {a b : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hQ : Regular q)
    (c : Crossing q) (hcut : c.val.2.val=a)
    (r : Fin (a+b+2) → PlanarPoint ℝ) : Prop :=
  ∃ hR : Regular r, ∃ E : Crossing q ≃ Crossing r,
    ∃ hlabels : ∀ e, (E e).val=e.val,
    (∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
      (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y)) ∧
    FirstCrossing r (E c) ∧ cyclicNoncollinear r ∧
    (∀ S : Support r hR, E c∉S.val → EventCarrierNonvanishing r hR (E c) S) ∧
    parentFarLocus r hR (E c) (mapped_cut q r E hlabels c hcut) (parentChartLines r)

/-- One actual perturbation realizes the first-event domain for both the
original arc and its literal first-corner suffix. No dense/open/map witness
or determinant condition is an input. The size equation only types the suffix. -/
theorem exists_nearby_two_stage_domain {a b u v : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hQ : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hdim : a+b=(u+v)+1)
    (d : Crossing (firstSuffixWord q hdim))
    (hd : FirstCrossing (firstSuffixWord q hdim) d) (hdcut : d.val.2.val=u)
    (hG1 : cyclicNoncollinear q) (hAux : ClosedAuxiliary q hQ)
    (V : Set (Fin (a+b+2) → PlanarPoint ℝ)) (hV : V∈𝓝 q) :
    ∃ r∈V, (∃ hR : Regular r, ClosedAuxiliary r hR) ∧
      MatchedFirstEventDomain q hQ c hcut r ∧
      MatchedFirstEventDomain (firstSuffixWord q hdim) (firstSuffixWord_regular q hdim hQ)
        d hdcut (firstSuffixWord r hdim) := by
  let qs := firstSuffixWord q hdim
  let hs := firstSuffixWord_regular q hdim hQ
  have hgS : cyclicNoncollinear qs := firstSuffixWord_G1 q hdim hG1
  let P0 := fun r : Fin (a+b+2) → PlanarPoint ℝ =>
    ∃ hR : Regular r, ∃ E : Crossing q ≃ Crossing r,
      (∀ e, (E e).val=e.val) ∧
      (∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
        (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y))
  let P1 := fun s : Fin (u+v+2) → PlanarPoint ℝ =>
    ∃ hR : Regular s, ∃ E : Crossing qs ≃ Crossing s,
      (∀ e, (E e).val=e.val) ∧
      (∀ x y : Event qs, (eventOrder qs hs.noTriple).lt x y ↔
        (eventOrder s hR.noTriple).lt (eventMapEquiv qs s E x) (eventMapEquiv qs s E y))
  have hP0 : {r | P0 r}∈𝓝 q := eventually_configuration_event_order q hQ hG1
  have hP1 : {s | P1 s}∈𝓝 qs := eventually_configuration_event_order qs hs hgS
  have hP1' : {r | P1 (firstSuffixWord r hdim)}∈𝓝 q :=
    (firstSuffixWord_continuous hdim).continuousAt.tendsto.eventually hP1
  have hA : {r | ∃ hR : Regular r, ClosedAuxiliary r hR}∈𝓝 q :=
    eventually_closedAuxiliary q hQ hG1 hAux
  let W := V ∩ {r | ∃ hR : Regular r, ClosedAuxiliary r hR} ∩ {r | P0 r} ∩
    {r | P1 (firstSuffixWord r hdim)}
  have hW : W∈𝓝 q := inter_mem (inter_mem (inter_mem hV hA) hP0) hP1'
  have hgeo := eventually_reconstructOpen_regular_G1 q hQ hG1 W hW
  have hden0 := eventually_event_pair_denominators q hQ c hc hG1
  have hden0p := eventually_parent_chain_denominators q hQ c hcut hG1
  have hproj : Tendsto (firstSuffixCarriers hdim) (𝓝 (parentChartLines q))
      (𝓝 (parentChartLines qs)) := by
    have ht := (firstSuffixCarriers_continuous hdim).continuousAt.tendsto (x:=openChartLines q)
    rw [firstSuffixCarriers_chart] at ht
    exact ht
  have hden1 := hproj.eventually ((eventually_event_pair_denominators qs hs d hd hgS).and
    (eventually_parent_chain_denominators qs hs d hdcut hgS))
  have hnear := hgeo.and (hden0.and (hden0p.and hden1))
  obtain ⟨O,hOsub,hOopen,hObase⟩ := mem_nhds_iff.mp hnear
  have hj0 := event_parent_carrier_dense_open q hQ c hc hcut
  have hj1 := event_parent_carrier_dense_open qs hs d hd hdcut
  have hj := hj0.1.inter_of_isOpen_left
    (hj1.1.preimage (firstSuffixCarriers_isOpenMap hdim)) hj0.2
  obtain ⟨L,hL,hLO⟩ := hj.exists_mem_open hOopen ⟨openChartLines q,hObase⟩
  rcases hL with ⟨⟨hF0,hFar0⟩,hF1,hFar1⟩
  rcases hOsub hLO with ⟨hgeometry,hDE0,hDP0,hDE1,hDP1⟩
  rcases hgeometry with ⟨hvalid,hmem,hreg,hg1,hinc,hinit,hterminal⟩
  let r := reconstructOpen q L
  rcases hmem with ⟨⟨⟨hrV,hrA⟩,hrP0⟩,hrP1⟩
  rcases hrP0 with ⟨hR,E,hlabels,horder⟩
  rcases hrP1 with ⟨hS,Es,hslabels,hsorder⟩
  have hfirst := firstCrossing_transport_of_event_order q r hQ hR E hlabels horder c hc
  have hsfirst := firstCrossing_transport_of_event_order qs (firstSuffixWord r hdim)
    hs hS Es hslabels hsorder d hd
  have hincs : ∀ e : Fin (u+v+1),
      lineValue (firstSuffixCarriers hdim L (Sum.inl e))
        (firstSuffixWord r hdim e.castSucc)=0 ∧
      lineValue (firstSuffixCarriers hdim L (Sum.inl e))
        (firstSuffixWord r hdim e.succ)=0 := by
    intro e
    exact hinc (firstSuffixEdge hdim e)
  have hterms : lineValue (firstSuffixCarriers hdim L (Sum.inr ()))
      (firstSuffixWord r hdim ⟨u+v+1,by omega⟩)=0 := by
    have hi : firstSuffixVertex hdim ⟨u+v+1,by omega⟩ = (⟨a+b+1,by omega⟩ : Fin (a+b+2)) :=
      Fin.ext (by dsimp [firstSuffixVertex]; omega)
    simpa only [firstSuffixCarriers,Sum.map_inr,firstSuffixWord,hi] using hterminal
  have hLF0 : parentFarLocus r hR (E c) (mapped_cut q r E hlabels c hcut) (parentChartLines r) := by
    intro T i j hi hij hz
    exact all_parent_far_nonzero q r hQ hR E hlabels horder c hc hcut L hinc hterminal hDP0 hFar0 T i j hi hij
      ((parent_far_numerator_zero_iff r hR (E c) (mapped_cut q r E hlabels c hcut) hg1 T i j).mp hz)
  have hg1s : cyclicNoncollinear (firstSuffixWord r hdim) := firstSuffixWord_G1 r hdim hg1
  have hLF1 : parentFarLocus (firstSuffixWord r hdim) hS (Es d)
      (mapped_cut qs (firstSuffixWord r hdim) Es hslabels d hdcut)
      (parentChartLines (firstSuffixWord r hdim)) := by
    intro T i j hi hij hz
    exact all_parent_far_nonzero qs (firstSuffixWord r hdim) hs hS Es hslabels hsorder d hd hdcut
      (firstSuffixCarriers hdim L) hincs hterms hDP1 hFar1 T i j hi hij
      ((parent_far_numerator_zero_iff (firstSuffixWord r hdim) hS (Es d)
        (mapped_cut qs (firstSuffixWord r hdim) Es hslabels d hdcut) hg1s T i j).mp hz)
  refine ⟨r,hrV,hrA,?_,?_⟩
  · exact ⟨hR,E,hlabels,horder,hfirst,hg1,
      all_event_nonvanishing q r hQ hR E hlabels horder c hc L hinc hterminal hDE0 hF0,hLF0⟩
  · exact ⟨hS,Es,hslabels,hsorder,hsfirst,hg1s,
      all_event_nonvanishing qs (firstSuffixWord r hdim) hs hS Es hslabels hsorder d hd
        (firstSuffixCarriers hdim L) hincs hterms hDE1 hF1,hLF1⟩

end DirectGLSSW.ActiveArc.OpenCarrier
