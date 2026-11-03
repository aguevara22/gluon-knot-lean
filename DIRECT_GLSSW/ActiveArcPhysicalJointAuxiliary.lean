import ActiveArcPhysicalJointDomain
import ActiveArcClosedAuxiliaryNeighborhood
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc RetainedWords Split Cursor ConfigurationLocality ConfigurationParent ConfigurationTransport
open AuxiliaryCarrierChart Filter Topology

/-- Every neighborhood of an original source arc with ClosedAuxiliary contains
a genuine nearby arc realizing the event and parent-far families simultaneously,
while preserving all actual closed daughter genericity and labeled event order. -/
theorem exists_nearby_actual_joint_auxiliary_domain {a b : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hQ : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (hG1 : cyclicNoncollinear q) (hAux : Primitive.ClosedAuxiliary q hQ)
    (U : Set (Fin (a+b+2) → PlanarPoint ℝ)) (hU : U ∈ 𝓝 q) :
    ∃ r ∈ U, ∃ hR : Regular r, ∃ E : Crossing q ≃ Crossing r,
    ∃ hlabels : ∀ d, (E d).val=d.val,
      cyclicNoncollinear r ∧ Primitive.ClosedAuxiliary r hR ∧
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
  let A := {r : Fin (a+b+2) → PlanarPoint ℝ | ∃ hR : Regular r, Primitive.ClosedAuxiliary r hR}
  have hA : A ∈ 𝓝 q := eventually_closedAuxiliary q hQ hG1 hAux
  obtain ⟨r,⟨hrU,hrA⟩,hR,E,hlabels,hg1,horder,hfirst,hEvent,hParent⟩ :=
    exists_nearby_actual_event_parent_domain q hQ c hc hcut hG1 (U ∩ A) (Filter.inter_mem hU hA)
  obtain ⟨hR',hAuxr⟩ := hrA
  exact ⟨r,hrU,hR,E,hlabels,hg1,hAuxr,horder,hfirst,hEvent,hParent⟩


end DirectGLSSW.ActiveArc.OpenCarrier
