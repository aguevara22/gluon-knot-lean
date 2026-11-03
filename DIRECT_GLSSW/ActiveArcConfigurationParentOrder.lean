import ActiveArcConfigurationParentCarrier
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationParent
open DirectGLSSW ActiveArc ConfigurationLocality Split CompatibleWords Cursor
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q r : Fin (a+b+2) → PlanarPoint ℝ) (hQ : Regular q) (hR : Regular r)
variable (E : Crossing q ≃ Crossing r) (hlabels : ∀ c, (E c).val=c.val)
variable (horder : ∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
  (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y))
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (hcR : FirstCrossing r (E c))

theorem parentEventMap_intertwine (x : Event (parent q c hcut)) :
    eventMapEquiv q r E (parentEventMap q hQ c hc hcut x)=
      parentEventMap r hR (E c) hcR (mapped_cut q r E hlabels c hcut)
        (eventMapEquiv (parent q c hcut) (parent r (E c) (mapped_cut q r E hlabels c hcut))
          (parentCrossingMap q r hQ hR E hlabels horder c hcut) x) := by
  cases x with
  | inl i =>
    by_cases hi : i=0
    · subst i
      rfl
    · change eventMapEquiv q r E (if i=0 then Sum.inr (c,false) else Sum.inl (Split.vertex i))=
        (if i=0 then Sum.inr (E c,false) else Sum.inl (Split.vertex i))
      simp only [if_neg hi]
      rfl
  | inr v =>
    rcases v with ⟨d,z⟩
    change Sum.inr (E (parentCrossingToOriginal q c hcut d),z)=
      Sum.inr (parentCrossingToOriginal r (E c) (mapped_cut q r E hlabels c hcut)
        (parentCrossingMap q r hQ hR E hlabels horder c hcut d),z)
    rw [parentCrossingMap_original]

include hc hcR in
theorem parent_event_order (x y : Event (parent q c hcut)) :
    (eventOrder (parent q c hcut) (regular_parent q hQ c hcut).noTriple).lt x y ↔
      (eventOrder (parent r (E c) (mapped_cut q r E hlabels c hcut))
        (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut)).noTriple).lt
          (eventMapEquiv (parent q c hcut) (parent r (E c) (mapped_cut q r E hlabels c hcut))
            (parentCrossingMap q r hQ hR E hlabels horder c hcut) x)
          (eventMapEquiv (parent q c hcut) (parent r (E c) (mapped_cut q r E hlabels c hcut))
            (parentCrossingMap q r hQ hR E hlabels horder c hcut) y) := by
  rw [← parentEventMap_lt q hQ c hc hcut]
  rw [horder]
  rw [parentEventMap_intertwine q r hQ hR E hlabels horder c hc hcut hcR,
    parentEventMap_intertwine q r hQ hR E hlabels horder c hc hcut hcR]
  exact parentEventMap_lt r hR (E c) hcR (mapped_cut q r E hlabels c hcut) _ _

end DirectGLSSW.ActiveArc.ConfigurationParent
