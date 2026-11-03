import ActiveArcEventCarrierChain
import EventCarrierPairClassification

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW Cursor RetainedWords Primitive EventCarrierPairClassification

/-- The generic pair classification on the canonical actual carrier chain.
The Fin cast only normalizes its known cardinality M≥2 to (M−2)+2. All
nondegeneracy and nonrepetition hypotheses come from actual source geometry. -/
theorem actual_eventPair_classification
    {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (U : Support q hR) (hu : c∉U.val) :
    let f := fun i : Fin (openCount q hR U.val-2+2) => eventCarrierChain q hR U
      (Fin.cast (Nat.sub_add_cancel (open_count_ge_two q hR U.val)) i)
    let r : Fin (n+1) ⊕ Unit := Sum.inl c.val.2
    (∀ i, (eventPair f r i).card=2) ∧ Function.Injective (eventPair f r) ∧
      ∀ i j k, i.val<j.val → j.val<k.val →
        ((∃ x, x∈eventPair f r i ∧ x∈eventPair f r j ∧ x∈eventPair f r k) ↔
          i.val=0 ∧ k.val=j.val+1 ∧ f j=r) := by
  intro f r
  have hf : Function.Injective f := by
    intro i j hh
    have he := eventCarrierChain_injective q hR U hh
    apply Fin.ext
    exact congrArg (fun z : Fin (openCount q hR U.val) => z.val) he
  have hr0 : r≠f 0 := eventCarrierChain_right_ne_zero q hR U c hc
  have hr1 : r≠f 1 := eventCarrierChain_right_ne_one q hR U c hc hu
  refine ⟨eventPair_card f r hf hr0,eventPair_injective f r hf hr0 hr1,?_⟩
  intro i j k hij hjk
  exact eventPair_common_iff f r hf i j k hij hjk


end DirectGLSSW.ActiveArc.OpenCarrier
