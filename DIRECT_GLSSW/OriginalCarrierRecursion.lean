import ChildOriginalCarriers

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain ActiveArc ActiveArc.Cursor ActiveArc.Split
open ActiveArc.ExposedChart TruncationDirection

theorem truncated_cut_supplied_original_family {n : ℕ}
    (Q : Fin (n+1) → PlanarPoint ℝ) (a p : Fin (n+1)) (hp : cyclicSuccessor p = a)
    (scale ε : ℝ) (K : CarrierLine)
    (hleft : lineValue K (Q a+ε • (Q p-Q a)) = 0)
    (hright : lineValue K (Q a+(ε*scale) • (Q (cyclicSuccessor a)-Q a)) = 0)
    (hU : UniversalLocus (canonicalAugmentedCarrier Q K))
    (hT : PairTransverse (canonicalAugmentedCarrier Q K)) :
    let q := cutArc (truncateCyclicCorner Q a p scale ε) a.castSucc
    let f := truncatedCarrierLabel a ∘ cutCarrierLabel a.castSucc
    Function.Injective f ∧ f (Sum.inr ()) = Fin.last (n+1) ∧
      UniversalLocus (canonicalAugmentedCarrier Q K ∘ f) ∧
      PairTransverse (canonicalAugmentedCarrier Q K ∘ f) ∧
      (∀ e : Fin (n+1),
        lineValue (canonicalAugmentedCarrier Q K (f (Sum.inl e))) (q e.castSucc) = 0 ∧
        lineValue (canonicalAugmentedCarrier Q K (f (Sum.inl e))) (q e.succ) = 0) ∧
      lineValue (canonicalAugmentedCarrier Q K (f (Sum.inr ()))) (q ⟨n+1,by omega⟩) = 0 := by
  intro q f
  have hi := truncated_augmented_carrier_incidence Q a p hp scale ε K hleft hright
  have hu := universalLocus_comap _ hU _ (truncatedCarrierLabel_injective a)
  have ht := pairTransverse_comap _ hT _ (truncatedCarrierLabel_injective a)
  have hc := cutArc_universal_supplied (truncateCyclicCorner Q a p scale ε) a.castSucc
    (canonicalAugmentedCarrier Q K ∘ truncatedCarrierLabel a) hu ht hi
  exact ⟨(truncated_cut_label_invariants a).1,(truncated_cut_label_invariants a).2,hc⟩

theorem actual_parent_preserves_original_family {a b N : ℕ}
    (Q : Fin N → PlanarPoint ℝ) (K : CarrierLine)
    (q : Fin (a+b+2) → PlanarPoint ℝ) (c : Crossing q) (hcut : c.val.2.val = a)
    (f : Fin (a+b+1) ⊕ Unit → Fin (N+1)) (hf : Function.Injective f)
    (ht : f (Sum.inr ()) = Fin.last N)
    (hU : UniversalLocus (canonicalAugmentedCarrier Q K))
    (hT : PairTransverse (canonicalAugmentedCarrier Q K))
    (hinc : ∀ e, lineValue (canonicalAugmentedCarrier Q K (f (Sum.inl e))) (q e.castSucc) = 0 ∧
      lineValue (canonicalAugmentedCarrier Q K (f (Sum.inl e))) (q e.succ) = 0)
    (hterminal : lineValue (canonicalAugmentedCarrier Q K (f (Sum.inr ()))) (q ⟨a+b+1,by omega⟩) = 0) :
    let g := f ∘ suffixCarrierMap (a:=a) (b:=b)
    Function.Injective g ∧ g (Sum.inr ()) = Fin.last N ∧
      UniversalLocus (canonicalAugmentedCarrier Q K ∘ g) ∧
      PairTransverse (canonicalAugmentedCarrier Q K ∘ g) ∧
      (∀ e : Fin (b+1),
        lineValue (canonicalAugmentedCarrier Q K (g (Sum.inl e))) (parent q c hcut e.castSucc) = 0 ∧
        lineValue (canonicalAugmentedCarrier Q K (g (Sum.inl e))) (parent q c hcut e.succ) = 0) ∧
      lineValue (canonicalAugmentedCarrier Q K (g (Sum.inr ()))) (parent q c hcut ⟨b+1,by omega⟩) = 0 := by
  intro g
  have hh := universal_supplied_parent q c hcut (canonicalAugmentedCarrier Q K ∘ f)
    (universalLocus_comap _ hU f hf) (pairTransverse_comap _ hT f hf) hinc hterminal
  exact ⟨(parent_label_invariants f hf ht).1,(parent_label_invariants f hf ht).2,hh⟩

end DirectGLSSW.CyclicCarrierClearing


