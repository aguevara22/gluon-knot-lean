import ActiveArcSurvivingComponentRelations

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.Surviving
open DirectGLSSW ActiveArc PermutationOrbits CompatibleWords
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
variable (S : Finset (Crossing q)) (hS : ∀ d∈S, Survives q t d)
variable (hM : Regular (moveStart q t))
include hS

/-- Canonical closed roots are retained; transport their literal physical
labels to obtain the actual original closed component. -/
def closedComponentMap
    (C : {C : Component (incoming (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)) //
      C ≠ openComponent (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)}) :
    {D : Component (incoming q hR.noTriple S) // D ≠ openComponent q hR.noTriple S} := by
  let r : {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x} :=
    ⟨closedRoot (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) C.val C.property,
      (closedRoot_spec (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) C.val C.property).2⟩
  refine ⟨componentOf (incoming q hR.noTriple S) (eventMap q t ht0 ht1 r.val),?_⟩
  intro hh
  have hn := (mapped_open_iff q hR t ht0 ht1 S hS hM r).mp hh
  exact C.property ((closedRoot_spec (moveStart q t) hM.noTriple
    (movingSelection q t ht0 ht1 S) C.val C.property).1.symm.trans hn)

/-- The actual component map does not depend on which retained root represents it. -/
theorem closedComponentMap_componentOf
    (C : {C : Component (incoming (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)) //
      C ≠ openComponent (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)})
    (x : {x : Event (moveStart q t) // retained (moveStart q t) (movingSelection q t ht0 ht1 S) x})
    (hx : componentOf (incoming (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)) x.val = C.val) :
    componentOf (incoming q hR.noTriple S) (eventMap q t ht0 ht1 x.val) =
      (closedComponentMap q hR t ht0 ht1 S hS hM C).val := by
  apply (componentOf_eq_iff _ _ _).mpr
  apply (mapped_sameCycle_iff q hR t ht0 ht1 S hS hM x
    ⟨closedRoot (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) C.val C.property,
      (closedRoot_spec (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) C.val C.property).2⟩).mpr
  apply (componentOf_eq_iff _ _ _).mp
  exact hx.trans (closedRoot_spec (moveStart q t) hM.noTriple
    (movingSelection q t ht0 ht1 S) C.val C.property).1.symm

theorem closedComponentMap_injective :
    Function.Injective (closedComponentMap q hR t ht0 ht1 S hS hM) := by
  intro C D he
  apply Subtype.ext
  have hs := (componentOf_eq_iff _ _ _).mp (congrArg Subtype.val he)
  have hn := (mapped_sameCycle_iff q hR t ht0 ht1 S hS hM
    ⟨closedRoot (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) C.val C.property,
      (closedRoot_spec (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) C.val C.property).2⟩
    ⟨closedRoot (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) D.val D.property,
      (closedRoot_spec (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) D.val D.property).2⟩).mp hs
  have hh := (componentOf_eq_iff _ _ _).mpr hn
  simpa only [(closedRoot_spec (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) C.val C.property).1,
    (closedRoot_spec (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) D.val D.property).1] using hh

theorem closedComponentMap_surjective :
    Function.Surjective (closedComponentMap q hR t ht0 ht1 S hS hM) := by
  intro D
  let y : {x : Event q // retained q S x} :=
    ⟨closedRoot q hR.noTriple S D.val D.property,(closedRoot_spec q hR.noTriple S D.val D.property).2⟩
  let x := (retainedEquiv q t ht0 ht1 S hS).symm y
  have hxy : eventMap q t ht0 ht1 x.val = y.val :=
    congrArg Subtype.val ((retainedEquiv q t ht0 ht1 S hS).apply_symm_apply y)
  have hy : componentOf (incoming q hR.noTriple S) y.val = D.val :=
    (closedRoot_spec q hR.noTriple S D.val D.property).1
  have hxclosed : componentOf (incoming (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)) x.val ≠
      openComponent (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S) := by
    intro hh
    have ho := (mapped_open_iff q hR t ht0 ht1 S hS hM x).mpr hh
    rw [hxy,hy] at ho
    exact D.property ho
  let C : {C : Component (incoming (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)) //
      C ≠ openComponent (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)} := ⟨componentOf (incoming (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)) x.val,hxclosed⟩
  refine ⟨C,Subtype.ext ?_⟩
  have hh := closedComponentMap_componentOf q hR t ht0 ht1 S hS hM C x rfl
  rw [hxy,hy] at hh
  exact hh.symm

/-- A bijection of the actual closed components, derived from deletion and
retained successor conjugacy rather than assumed. -/
def closedComponentEquiv :
    {C : Component (incoming (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)) //
      C ≠ openComponent (moveStart q t) hM.noTriple (movingSelection q t ht0 ht1 S)} ≃
    {D : Component (incoming q hR.noTriple S) // D ≠ openComponent q hR.noTriple S} :=
  Equiv.ofBijective (closedComponentMap q hR t ht0 ht1 S hS hM)
    ⟨closedComponentMap_injective q hR t ht0 ht1 S hS hM,
      closedComponentMap_surjective q hR t ht0 ht1 S hS hM⟩

end DirectGLSSW.ActiveArc.Cursor.Surviving
