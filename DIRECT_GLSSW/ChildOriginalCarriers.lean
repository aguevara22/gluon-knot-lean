import ChildPhysicalCarriers

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain ActiveArc ActiveArc.Cursor ActiveArc.Split
open ActiveArc.ExposedChart

/-- Initializing at the inserted supporting edge puts the only artificial
carrier in the TERMINAL slot, never in a physical slot. -/
theorem truncated_cut_label_invariants {n : ℕ} (v : Fin (n+1)) :
    Function.Injective (truncatedCarrierLabel v ∘ cutCarrierLabel v.castSucc) ∧
      (truncatedCarrierLabel v ∘ cutCarrierLabel v.castSucc) (Sum.inr ()) = Fin.last (n+1) := by
  refine ⟨(truncatedCarrierLabel_injective v).comp (cutCarrierLabel_injective v.castSucc),?_⟩
  exact truncatedCarrierLabel_short v

/-- Every actual detached child uses only original carriers. The injection and
both endpoint incidences are outputs; no child-avoidance predicate is assumed. -/
theorem actual_child_original_carriers {a b N : ℕ}
    (Q : Fin N → PlanarPoint ℝ) (K : CarrierLine)
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q) (c : Crossing q)
    (hfirst : c.val.1 = 0) (hcut : c.val.2.val = a)
    (f : Fin (a+b+1) ⊕ Unit → Fin (N+1)) (hf : Function.Injective f)
    (ht : f (Sum.inr ()) = Fin.last N)
    (hinc : ∀ e, lineValue (canonicalAugmentedCarrier Q K (f (Sum.inl e))) (q e.castSucc) = 0 ∧
      lineValue (canonicalAugmentedCarrier Q K (f (Sum.inl e))) (q e.succ) = 0) :
    ∃ g : Fin (a+1) → Fin N, Function.Injective g ∧
      (∀ i, (g i).castSucc = f (Sum.inl (childEdge (b:=b) i))) ∧
      ∀ i, lineValue (polygonCarrierCoordinates Q (g i)) (child q hR c hfirst hcut i) = 0 ∧
        lineValue (polygonCarrierCoordinates Q (g i))
          (child q hR c hfirst hcut (cyclicSuccessor i)) = 0 := by
  obtain ⟨g,hg,he⟩ := exists_child_old_labels f hf ht
  have hi := child_physical_carrier_incidence q hR c hfirst hcut
    (fun e => canonicalAugmentedCarrier Q K (f (Sum.inl e))) hinc
  refine ⟨g,hg,he,?_⟩
  intro i
  have hh := hi i
  dsimp only at hh
  rw [← he i] at hh
  simpa only [canonicalAugmentedCarrier,Fin.coe_castSucc,dif_pos (g i).isLt] using hh

end DirectGLSSW.CyclicCarrierClearing


