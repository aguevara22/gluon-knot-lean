import ActiveArcConfigurationParentOrder
import ActiveArcFirstCrossingTransport
import ActiveArcConfigurationOrbits
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationParent
open DirectGLSSW ActiveArc ConfigurationLocality ConfigurationTransport Split CompatibleWords Cursor RetainedWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q r : Fin (a+b+2) → PlanarPoint ℝ) (hQ : Regular q) (hR : Regular r)
variable (E : Crossing q ≃ Crossing r) (hlabels : ∀ c, (E c).val=c.val)
variable (horder : ∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
  (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y))
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)

include hc in
/-- Actual parent order follows from the ORIGINAL chart; mapped first-crossing
is proved from that chart rather than retained as a premise. -/
theorem parent_order (x y : Event (parent q c hcut)) :
    (eventOrder (parent q c hcut) (regular_parent q hQ c hcut).noTriple).lt x y ↔
      (eventOrder (parent r (E c) (mapped_cut q r E hlabels c hcut))
        (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut)).noTriple).lt
          (eventMapEquiv (parent q c hcut) (parent r (E c) (mapped_cut q r E hlabels c hcut))
            (parentCrossingMap q r hQ hR E hlabels horder c hcut) x)
          (eventMapEquiv (parent q c hcut) (parent r (E c) (mapped_cut q r E hlabels c hcut))
            (parentCrossingMap q r hQ hR E hlabels horder c hcut) y) :=
  parent_event_order q r hQ hR E hlabels horder c hc hcut
    (firstCrossing_transport_of_event_order q r hQ hR E hlabels horder c hc) x y

/-- Actual parent NA supports, with parent geometry and order fully discharged. -/
def parentSupportEquiv :
    Primitive.Support (parent q c hcut) (regular_parent q hQ c hcut) ≃
      Primitive.Support (parent r (E c) (mapped_cut q r E hlabels c hcut))
        (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut)) :=
  supportEquiv _ _ _ _ (parentCrossingMap q r hQ hR E hlabels horder c hcut)
    (parent_order q r hQ hR E hlabels horder c hc hcut)

variable (T : Primitive.Support (parent q c hcut) (regular_parent q hQ c hcut))

theorem parentSupportEquiv_card :
    (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T).val.card=T.val.card :=
  supportEquiv_card _ _ _ _ _ _ T

theorem parent_open_count :
    openCount (parent r (E c) (mapped_cut q r E hlabels c hcut))
      (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut))
      (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T).val =
    openCount (parent q c hcut) (regular_parent q hQ c hcut) T.val :=
  retained_count _ _ _ _ (parentCrossingMap q r hQ hR E hlabels horder c hcut)
    (parent_order q r hQ hR E hlabels horder c hc hcut) T.val (start (parent q c hcut))

/-- Entire actual outgoing carrier sequence of the open parent, including its
terminal retained event. Moving Cartesian coordinates are not identified. -/
theorem parent_open_carrier_word :
    List.ofFn (fun i => edgeTag (parent r (E c) (mapped_cut q r E hlabels c hcut))
      (pairing (parent r (E c) (mapped_cut q r E hlabels c hcut))
        (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T).val
        (cornerEvent (parent r (E c) (mapped_cut q r E hlabels c hcut))
          (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut))
          (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T).val
          (start (parent r (E c) (mapped_cut q r E hlabels c hcut))) i)))=
    List.ofFn (fun i => edgeTag (parent q c hcut)
      (pairing (parent q c hcut) T.val
        (cornerEvent (parent q c hcut) (regular_parent q hQ c hcut) T.val (start (parent q c hcut)) i))) :=
  retained_carrier_word _ _ _ _ (parentCrossingMap q r hQ hR E hlabels horder c hcut)
    (parent_order q r hQ hR E hlabels horder c hc hcut)
    (parentCrossingMap_labels q r hQ hR E hlabels horder c hcut) T.val (start (parent q c hcut))

end DirectGLSSW.ActiveArc.ConfigurationParent
