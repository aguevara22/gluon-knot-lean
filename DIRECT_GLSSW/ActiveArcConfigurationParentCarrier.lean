import ActiveArcEventMap
import ActiveArcParentEventOrder
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationParent
open DirectGLSSW ActiveArc ConfigurationLocality Split CompatibleWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q r : Fin (a+b+2) → PlanarPoint ℝ) (hQ : Regular q) (hR : Regular r)
variable (E : Crossing q ≃ Crossing r) (hlabels : ∀ c, (E c).val=c.val)
variable (horder : ∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
  (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y))
variable (c : Crossing q) (hcut : c.val.2.val=a)

include hlabels hcut in
theorem mapped_cut : (E c).val.2.val=a :=
  (congrArg (fun z : Fin (a+b+1) × Fin (a+b+1) => z.2.val) (hlabels c)).trans hcut

include hcut in
/-- Membership in the actual shortened parent is precisely visit order after
its right cut visit, not an independent geometric genericity assumption. -/
theorem inParent_iff_event_lt (d : Crossing q) :
    InParent q c d ↔ (eventOrder q hQ.noTriple).lt (Sum.inr (c,true)) (Sum.inr (d,false)) := by
  rw [event_lt_iff]
  change (a ≤ d.val.1.val ∧ (d.val.1.val=a → rightParameter q c < leftParameter q d)) ↔
    c.val.2.val < d.val.1.val ∨
      (c.val.2.val=d.val.1.val ∧ rightParameter q c < leftParameter q d)
  rw [hcut]
  by_cases he : d.val.1.val=a
  · simp [he]
  · have hne : a≠d.val.1.val := Ne.symm he
    simp only [he,false_implies,and_true,hne,false_and,or_false]
    omega

include horder hlabels hcut in
theorem inParent_map_iff (d : Crossing q) :
    InParent r (E c) (E d) ↔ InParent q c d := by
  rw [inParent_iff_event_lt r hR (E c) (mapped_cut q r E hlabels c hcut),
    inParent_iff_event_lt q hQ c hcut]
  exact (horder (Sum.inr (c,true)) (Sum.inr (d,false))).symm

/-- Actual parent crossings are identified through their original physical labels.
Only the ORIGINAL arc order is used; there is no parent G1 premise. -/
def parentCrossingMap : Crossing (parent q c hcut) ≃
    Crossing (parent r (E c) (mapped_cut q r E hlabels c hcut)) :=
  (parentCrossingEquiv q hQ c hcut).trans
    ((E.subtypeEquiv (fun d => (inParent_map_iff q r hQ hR E hlabels horder c hcut d).symm)).trans
      (parentCrossingEquiv r hR (E c) (mapped_cut q r E hlabels c hcut)).symm)

theorem parentCrossingMap_original (d : Crossing (parent q c hcut)) :
    parentCrossingToOriginal r (E c) (mapped_cut q r E hlabels c hcut)
      (parentCrossingMap q r hQ hR E hlabels horder c hcut d)=
    E (parentCrossingToOriginal q c hcut d) := by
  have hh := (parentCrossingEquiv r hR (E c) (mapped_cut q r E hlabels c hcut)).apply_symm_apply
    ((E.subtypeEquiv (fun d => (inParent_map_iff q r hQ hR E hlabels horder c hcut d).symm))
      (parentCrossingEquiv q hQ c hcut d))
  exact congrArg Subtype.val hh

theorem parentCrossingMap_labels (d : Crossing (parent q c hcut)) :
    (parentCrossingMap q r hQ hR E hlabels horder c hcut d).val=d.val := by
  have hh := congrArg Subtype.val (parentCrossingMap_original q r hQ hR E hlabels horder c hcut d)
  rw [hlabels] at hh
  apply Prod.ext
  · apply edge_injective
    exact congrArg Prod.fst hh
  · apply edge_injective
    exact congrArg Prod.snd hh

end DirectGLSSW.ActiveArc.ConfigurationParent
