import ActiveArcJointCarrierChart
import ActiveArcEventLocusTransfer
import ActiveArcParentFarTransfer
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc RetainedWords Split Cursor ConfigurationLocality ConfigurationParent ConfigurationTransport
open AuxiliaryCarrierChart Filter Topology

/-- Every neighborhood of an original Regular G1 arc with a first crossing
contains an actual Regular G1 arc with the same labeled event order and first crossing,
and with both every actual unselected event domain and every actual
nearby parent-support far determinant simultaneously nonzero. -/
theorem exists_nearby_actual_event_parent_domain {a b : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hQ : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hG1 : cyclicNoncollinear q)
    (U : Set (Fin (a+b+2) → PlanarPoint ℝ)) (hU : U ∈ 𝓝 q) :
    ∃ r ∈ U, ∃ hR : Regular r, ∃ E : Crossing q ≃ Crossing r,
    ∃ hlabels : ∀ d, (E d).val=d.val,
      cyclicNoncollinear r ∧
      (∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
        (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y)) ∧
      FirstCrossing r (E c) ∧
      (∀ S : Primitive.Support r hR, E c∉S.val → Primitive.EventCarrierNonvanishing r hR (E c) S) ∧
      ∀ T : Primitive.Support (parent r (E c) (mapped_cut q r E hlabels c hcut))
        (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut)),
      ∀ i j : Fin (openCount (parent r (E c) (mapped_cut q r E hlabels c hcut))
        (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut)) T.val),
      0 < i.val → i.val < j.val →
        planarDet
          (Primitive.OpenVertex (parent r (E c) (mapped_cut q r E hlabels c hcut))
            (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut)) T i-crossingPoint r (E c))
          (Primitive.OpenVertex (parent r (E c) (mapped_cut q r E hlabels c hcut))
            (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut)) T j-crossingPoint r (E c))≠0 := by
  let P := fun r : Fin (a+b+2) → PlanarPoint ℝ =>
    ∃ hR : Regular r, ∃ E : Crossing q ≃ Crossing r,
      (∀ d, (E d).val=d.val) ∧
      (∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
        (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y))
  have hP : {r | P r} ∈ 𝓝 q := eventually_configuration_event_order q hQ hG1
  have hUP : U ∩ {r | P r} ∈ 𝓝 q := Filter.inter_mem hU hP
  obtain ⟨L,hgeometry,⟨hF,hfar⟩,hdenE,hden⟩ :=
    exists_reconstructed_joint_chart q hQ c hc hcut hG1 (U ∩ {r | P r}) hUP
  rcases hgeometry with ⟨hvalid,hmem,hreg,hg1,hinc,hinit,hterminal⟩
  rcases hmem with ⟨hrU,hchart⟩
  rcases hchart with ⟨hR,E,hlabels,horder⟩
  refine ⟨reconstructOpen q L,hrU,hR,E,hlabels,hg1,horder,?_,?_,?_⟩
  · exact firstCrossing_transport_of_event_order q (reconstructOpen q L) hQ hR
      E hlabels horder c hc
  · exact all_event_nonvanishing q (reconstructOpen q L) hQ hR E hlabels horder
      c hc L hinc hterminal hdenE hF
  · intro T i j hi hij
    exact all_parent_far_nonzero q (reconstructOpen q L) hQ hR E hlabels horder
      c hc hcut L hinc hterminal hden hfar T i j hi hij


end DirectGLSSW.ActiveArc.OpenCarrier
