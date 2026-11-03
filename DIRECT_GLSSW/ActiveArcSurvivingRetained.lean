import ActiveArcSurvivingEvents

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.Surviving
open DirectGLSSW ActiveArc PermutationOrbits CompatibleWords
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
variable (S : Finset (Crossing q)) (hS : ∀ d ∈ S, Survives q t d)

/-- Deleting only unselected physical visits gives a bijection on the exact
retained carriers, even when there is no bijection on all events. -/
def retainedEquiv :
    {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x} ≃
      {x : Event q // retained q S x} := by
  let f : {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x} →
      {x : Event q // retained q S x} :=
    fun x => ⟨eventMap q t ht0 ht1 x.val,(eventMap_retained q t ht0 ht1 S x.val).mpr x.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    exact eventMap_injective q t ht0 ht1 (congrArg Subtype.val h)
  · rintro ⟨x,hx⟩
    cases x with
    | inl i => exact ⟨⟨Sum.inl i,by trivial⟩,rfl⟩
    | inr v =>
      rcases v with ⟨d,b⟩
      let e := crossingFromOriginal q t ht1 d (hS d hx)
      have he : e ∈ movingSelection q t ht0 ht1 S := by
        rw [movingSelection_mem]
        exact hx
      exact ⟨⟨Sum.inr (e,b),he⟩,rfl⟩

@[simp] theorem retainedEquiv_val
    (x : {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x}) :
    (retainedEquiv q t ht0 ht1 S hS x).val = eventMap q t ht0 ht1 x.val := rfl

def retainedOrderIso (hM : Regular (moveStart q t)) :
    letI := eventOrder q hR.noTriple
    letI := eventOrder (moveStart q t) hM.noTriple
    {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x} ≃o
      {x : Event q // retained q S x} := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (moveStart q t) hM.noTriple
  refine { toEquiv := retainedEquiv q t ht0 ht1 S hS, map_rel_iff' := ?_ }
  intro x y
  change eventMap q t ht0 ht1 x.val ≤ eventMap q t ht0 ht1 y.val ↔ x.val ≤ y.val
  simpa only [not_lt] using not_congr (eventMap_lt q hR t ht0 ht1 hM y.val x.val)

theorem retainedEquiv_pairing
    (x : {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x}) :
    retainedEquiv q t ht0 ht1 S hS
      (physicalRetainedPairing (moveStart q t) (movingSelection q t ht0 ht1 S) x) =
      physicalRetainedPairing q S (retainedEquiv q t ht0 ht1 S hS x) := by
  apply Subtype.ext
  exact eventMap_pairing q t ht0 ht1 S x.val

theorem retainedOrderIso_incoming (hM : Regular (moveStart q t)) :
    letI := eventOrder q hR.noTriple
    letI := eventOrder (moveStart q t) hM.noTriple
    ∀ (x : {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x}),
      retainedOrderIso q hR t ht0 ht1 S hS hM
        ((orderedCyclicSuccessor {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x} * physicalRetainedPairing (moveStart q t)
          (movingSelection q t ht0 ht1 S)) x) =
      (orderedCyclicSuccessor {x : Event q // retained q S x} * physicalRetainedPairing q S)
        (retainedOrderIso q hR t ht0 ht1 S hS hM x) := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (moveStart q t) hM.noTriple
  intro x
  change retainedOrderIso q hR t ht0 ht1 S hS hM
      (orderedCyclicSuccessor _ (physicalRetainedPairing (moveStart q t) (movingSelection q t ht0 ht1 S) x)) =
    orderedCyclicSuccessor _ (physicalRetainedPairing q S (retainedOrderIso q hR t ht0 ht1 S hS hM x))
  have h := orderedCyclicSuccessor_naturality _ (retainedOrderIso q hR t ht0 ht1 S hS hM)
    (physicalRetainedPairing (moveStart q t) (movingSelection q t ht0 ht1 S) x)
  rw [← h]
  congr 1
  exact retainedEquiv_pairing q t ht0 ht1 S hS x

theorem retainedOrderIso_orbitWord (hM : Regular (moveStart q t)) :
    letI := eventOrder q hR.noTriple
    letI := eventOrder (moveStart q t) hM.noTriple
    ∀ root,
      orbitWord (orderedCyclicSuccessor {x : Event q // retained q S x} * physicalRetainedPairing q S)
        (retainedOrderIso q hR t ht0 ht1 S hS hM root) =
      (orbitWord (orderedCyclicSuccessor {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x} * physicalRetainedPairing (moveStart q t)
        (movingSelection q t ht0 ht1 S)) root).map (retainedOrderIso q hR t ht0 ht1 S hS hM) := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (moveStart q t) hM.noTriple
  intro root
  exact orbitWord_map_injective _ _ (retainedOrderIso q hR t ht0 ht1 S hS hM)
    (retainedOrderIso q hR t ht0 ht1 S hS hM).injective
    (fun x => (retainedOrderIso_incoming q hR t ht0 ht1 S hS hM x).symm) root

end DirectGLSSW.ActiveArc.Cursor.Surviving
