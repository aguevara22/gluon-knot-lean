import ActiveArcBeforeFirstWords
import ActiveArcRetainedOrbitComponents
import DirectGLSSW.DaughterRootAmplitude

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.BeforeFirst
open DirectGLSSW ActiveArc PermutationOrbits CompatibleWords
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c)
variable (t : ℝ) (ht0 : 0 ≤ t) (htc : t < leftParameter q c)
variable (S : Finset (Crossing (moveStart q t)))

/-- Every actual incoming component follows the proved physical event relabelling. -/
def componentEquiv :
    Component (incoming (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S) ≃
    Component (incoming q hR.noTriple (selectionEquiv q hR c hc t ht0 htc S)) :=
  componentEquivOfIntertwining (eventEquiv q hR c hc t ht0 htc) _ _
    (eventEquiv_incoming q hR c hc t ht0 htc S)

@[simp] theorem componentEquiv_componentOf (x : Event (moveStart q t)) :
    componentEquiv q hR c hc t ht0 htc S
      (componentOf (incoming (moveStart q t)
        (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S) x) =
    componentOf (incoming q hR.noTriple (selectionEquiv q hR c hc t ht0 htc S))
      (eventEquiv q hR c hc t ht0 htc x) := rfl

@[simp] theorem componentEquiv_open :
    componentEquiv q hR c hc t ht0 htc S
      (openComponent (moveStart q t)
        (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S) =
      openComponent q hR.noTriple (selectionEquiv q hR c hc t ht0 htc S) := rfl

/-- The distinguished open component is fixed, so the map restricts bijectively to closed components. -/
def closedComponentEquiv :
    {C : Component (incoming (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S) //
      C ≠ openComponent (moveStart q t)
        (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S} ≃
    {D : Component (incoming q hR.noTriple (selectionEquiv q hR c hc t ht0 htc S)) //
      D ≠ openComponent q hR.noTriple (selectionEquiv q hR c hc t ht0 htc S)} :=
  (componentEquiv q hR c hc t ht0 htc S).subtypeEquiv (fun C => by
    rw [← componentEquiv_open q hR c hc t ht0 htc S]
    exact not_congr (componentEquiv q hR c hc t ht0 htc S).injective.eq_iff.symm)

@[simp] theorem closedComponentEquiv_val
    (C : {C : Component (incoming (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S) //
      C ≠ openComponent (moveStart q t)
        (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S}) :
    (closedComponentEquiv q hR c hc t ht0 htc S C).val =
      componentEquiv q hR c hc t ht0 htc S C.val := rfl

/-- Canonical closed roots differ only by an actual cyclic rotation of the unchanged point word. -/
theorem closed_word_isRotated
    (C : {C : Component (incoming (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S) //
      C ≠ openComponent (moveStart q t)
        (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S}) :
    let D := closedComponentEquiv q hR c hc t ht0 htc S C
    List.ofFn (RetainedWords.vertex q hR (selectionEquiv q hR c hc t ht0 htc S)
      (closedRoot q hR.noTriple (selectionEquiv q hR c hc t ht0 htc S) D.val D.property)) ~r
    List.ofFn (RetainedWords.vertex (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc) S
      (closedRoot (moveStart q t)
        (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc).noTriple S C.val C.property)) := by
  let hp := before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc
  let r := closedRoot (moveStart q t) hp.noTriple S C.val C.property
  let D := closedComponentEquiv q hR c hc t ht0 htc S C
  have hr : componentOf (incoming (moveStart q t) hp.noTriple S) r = C.val :=
    (closedRoot_spec (moveStart q t) hp.noTriple S C.val C.property).1
  have he : componentOf (incoming q hR.noTriple (selectionEquiv q hR c hc t ht0 htc S))
      (eventEquiv q hR c hc t ht0 htc r) = D.val := by
    rw [← componentEquiv_componentOf,hr]
    rfl
  have hd := (closedRoot_spec q hR.noTriple (selectionEquiv q hR c hc t ht0 htc S) D.val D.property).1
  have hrot := retainedWord_isRotated_of_sameCycle q hR
    (selectionEquiv q hR c hc t ht0 htc S) _ _ ((componentOf_eq_iff _ _ _).mp (hd.trans he.symm))
  rw [closed_root_word q hR c hc t ht0 htc S r (by rw [hr]; exact C.property)] at hrot
  exact hrot

/-- Only the actual closed auxiliary package is transported; no genericity of an open prefix is inferred. -/
theorem closedAuxiliary (hAux : Primitive.ClosedAuxiliary q hR) :
    Primitive.ClosedAuxiliary (moveStart q t)
      (before_first_regular (a:=n) (b:=0) q hR c hc t ht0 htc) := by
  intro U C hC
  let V := supportEquiv q hR c hc t ht0 htc U
  let D := closedComponentEquiv q hR c hc t ht0 htc U.val ⟨C,hC⟩
  have hg := hAux V D.val D.property
  have hw := closed_word_isRotated q hR c hc t ht0 htc U.val ⟨C,hC⟩
  exact DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated hw hg

end DirectGLSSW.ActiveArc.Cursor.BeforeFirst
