import ActiveArcParentClosedWords

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

/-- The existing canonical actual closed root, packaged with its proved
retention characterization. No new choice of geometric root is made. -/
def parentClosedRetainedRoot
    (C : {C : Component (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T) //
      C≠openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T}) : ParentRetained q c hcut T :=
  ⟨closedRoot (parent q c hcut) (regular_parent q hR c hcut).noTriple T C.val C.property,
    (closedRoot_spec (parent q c hcut) (regular_parent q hR c hcut).noTriple T C.val C.property).2⟩

theorem parentClosedRetainedRoot_component
    (C : {C : Component (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T) //
      C≠openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T}) :
    componentOf (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T)
      (parentClosedRetainedRoot q hR c hcut T C).val=C.val :=
  (closedRoot_spec (parent q c hcut) (regular_parent q hR c hcut).noTriple T C.val C.property).1

/-- Actual parent closed components embedded into actual original closed
components through the physical retained parent labels. -/
def parentClosedComponentMap :
    {C : Component (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T) //
      C≠openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T} →
    {D : Component (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))) //
      D≠openComponent q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))} := fun C =>
  ⟨componentOf (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
    (parentEventMap q hR c hc hcut (parentClosedRetainedRoot q hR c hcut T C).val),
    parent_closed_root_stays_closed q hR c hc hcut S T (parentClosedRetainedRoot q hR c hcut T C)
      (by rw [parentClosedRetainedRoot_component];exact C.property)⟩

/-- The component map is independent of the retained representative, proved
using actual incoming component equivalence. -/
theorem parentClosedComponentMap_componentOf
    (C : {C : Component (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T) //
      C≠openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T})
    (x : ParentRetained q c hcut T)
    (hx : componentOf (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T) x.val=C.val) :
    componentOf (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
      (parentEventMap q hR c hc hcut x.val)=(parentClosedComponentMap q hR c hc hcut S T C).val := by
  apply (componentOf_eq_iff _ _ _).mpr
  apply (mapped_parent_sameCycle_iff q hR c hc hcut S T x (parentClosedRetainedRoot q hR c hcut T C)).mpr
  apply (componentOf_eq_iff _ _ _).mp
  rw [hx,parentClosedRetainedRoot_component]

theorem parentClosedComponentMap_injective : Function.Injective (parentClosedComponentMap q hR c hc hcut S T) := by
  intro C D he
  apply Subtype.ext
  have hh := congrArg Subtype.val he
  have hs := (componentOf_eq_iff _ _ _).mp hh
  have hp := (mapped_parent_sameCycle_iff q hR c hc hcut S T
    (parentClosedRetainedRoot q hR c hcut T C) (parentClosedRetainedRoot q hR c hcut T D)).mp hs
  have he' := (componentOf_eq_iff _ _ _).mpr hp
  simpa only [parentClosedRetainedRoot_component] using he'

/-- Canonically rooted actual closed daughter words agree up to cyclic
rotation. This is ready for a separately proved cyclic amplitude invariance. -/
theorem parentClosedComponentMap_word_isRotated
    (C : {C : Component (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T) //
      C≠openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T}) :
    List.ofFn (RetainedWords.vertex q hR (insert c (pieceSelections q hR c hc hcut S T))
      (closedRoot q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))
        (parentClosedComponentMap q hR c hc hcut S T C).val
        (parentClosedComponentMap q hR c hc hcut S T C).property)) ~r
    List.ofFn (RetainedWords.vertex (parent q c hcut) (regular_parent q hR c hcut) T
      (closedRoot (parent q c hcut) (regular_parent q hR c hcut).noTriple T C.val C.property)) := by
  let x := parentClosedRetainedRoot q hR c hcut T C
  let D := parentClosedComponentMap q hR c hc hcut S T C
  have hx : componentOf (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T) x.val≠
      openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T := by
    rw [parentClosedRetainedRoot_component]
    exact C.property
  have hs := (closedRoot_spec q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) D.val D.property).1
  have hrot := retainedWord_isRotated_of_sameCycle q hR (insert c (pieceSelections q hR c hc hcut S T))
    (closedRoot q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) D.val D.property)
    (parentEventMap q hR c hc hcut x.val) ((componentOf_eq_iff _ _ _).mp hs)
  rw [parent_closed_word q hR c hc hcut S T x hx] at hrot
  exact hrot

end DirectGLSSW.ActiveArc.CompatibleWords
