import ActiveArcEventPairIntersections

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW Cursor RetainedWords Primitive EventCarrierPairClassification

/-- Pair-cardinality, pair-uniqueness and exact common-carrier classification
at the literal actual word indices, discharging the harmless Fin cast. -/
theorem eventCarrierPair_data
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (U : Support q hR) (hu : c∉U.val) :
    let P := fun i => ({(eventCarrierPair q hR c U i).1,(eventCarrierPair q hR c U i).2} :
      Finset (Fin (n+1) ⊕ Unit))
    (∀ i, (P i).card=2) ∧ Function.Injective P ∧
      ∀ i j k, i.val < j.val → j.val < k.val →
        ((∃ x, x∈P i ∧ x∈P j ∧ x∈P k) ↔
          i.val=0 ∧ k.val=j.val+1 ∧ eventCarrierChain q hR U j=Sum.inl c.val.2) := by
  intro P
  let h := Nat.sub_add_cancel (open_count_ge_two q hR U.val)
  let inv := fun i : Fin (openCount q hR U.val) => Fin.cast h.symm i
  let f := fun i : Fin (openCount q hR U.val-2+2) => eventCarrierChain q hR U (Fin.cast h i)
  let r : Fin (n+1) ⊕ Unit := Sum.inl c.val.2
  have hp (i : Fin (openCount q hR U.val)) : P i=eventPair f r (inv i) :=
    eventCarrierPair_finset_eq q hR c U (inv i)
  obtain ⟨hcard,hinj,hcommon⟩ := actual_eventPair_classification q hR c hc U hu
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [hp]
    exact hcard (inv i)
  · intro i j hij
    rw [hp,hp] at hij
    have he := hinj hij
    apply Fin.ext
    exact congrArg (fun z : Fin (openCount q hR U.val-2+2) => z.val) he
  · intro i j k hij hjk
    simp only [hp]
    exact hcommon (inv i) (inv j) (inv k) hij hjk

end DirectGLSSW.ActiveArc.OpenCarrier
