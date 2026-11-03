import ActiveArcTinyParentClosedComponents
import ActiveArcRetainedOrbitComponents
import DirectGLSSW.DaughterPointListFilter

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive OpenFirstEdgeGeometry Nonalternation RetainedWords PhysicalSegments PermutationOrbits
attribute [local instance] Classical.propDecidable


variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (η : ℝ) (hη : 0<η) (hη1 : η<1)

/-- A matching closed root has exactly the same actual retained point word. -/
theorem tinyParent_closed_root_word (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) (x : Event (ParentArc q c hcut))
    (hx : componentOf (incoming (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val) x ≠
      openComponent (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val) :
    List.ofFn (RetainedWords.vertex (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (parentTinySelection q c hcut η T.val) (parentEventIntoTiny q c hcut η x)) =
    List.ofFn (RetainedWords.vertex (ParentArc q c hcut) (ParentRegular q hR c hcut)
      T.val x) := by
  let p := incoming (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val
  let r := incoming (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1).noTriple
    (parentTinySelection q c hcut η T.val)
  let E := tinyParentEventInsertionEquiv (q:=q) (hR:=hR) (c:=c) (hc:=hc)
    (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1)
  have hb := tinyParent_incoming_start (q:=q) (hR:=hR) (c:=c) (hc:=hc)
    (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T
  have hs := tinyParent_incoming_step (q:=q) (hR:=hR) (c:=c) (hc:=hc)
    (hcut:=hcut) (η:=η) (hη:=hη) (hη1:=hη1) T
  have hn : ¬ p.SameCycle x (start (ParentArc q c hcut)) := by
    intro hh
    exact hx ((componentOf_eq_iff p _ _).mpr hh)
  have hw := PermutationInsertion.unaffected_orbitWord p r
    (start (ParentArc q c hcut)) (start (TinyArc q c hcut η)) E hb hs x hn
  change orbitWord r (parentEventIntoTiny q c hcut η x) =
    (orbitWord p x).map (parentEventIntoTiny q c hcut η) at hw
  rw [SingletonWords.retainedWord_eq_filtered (a:=b+1) (b:=0)
    (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
    (parentTinySelection q c hcut η T.val) (parentEventIntoTiny q c hcut η x),
    SingletonWords.retainedWord_eq_filtered (a:=b) (b:=0)
      (ParentArc q c hcut) (ParentRegular q hR c hcut) T.val x,hw]
  have hret : ∀ y : Event (ParentArc q c hcut),
      decide (retained (TinyArc q c hcut η) (parentTinySelection q c hcut η T.val)
        (parentEventIntoTiny q c hcut η y)) =
      decide (retained (ParentArc q c hcut) T.val y) := by
    intro y
    have he := parentEventIntoTiny_retained q hR c hcut η T y
    by_cases hp : retained (ParentArc q c hcut) T.val y
    · have ht := he.mpr hp
      simp only [hp,ht,decide_true]
    · have ht : ¬ retained (TinyArc q c hcut η) (parentTinySelection q c hcut η T.val)
          (parentEventIntoTiny q c hcut η y) := fun hh => hp (he.mp hh)
      simp only [hp,ht,decide_false]
  rw [← DaughterPointListFilter.map_filter_comp]
  simp only [hret,List.map_map]
  apply List.map_congr_left
  intro y hy
  exact parentEventIntoTiny_point q hR c hc hcut η hη hη1 y

/-- Canonical actual closed roots differ only by a cyclic rebase. -/
theorem tinyParent_closed_word_isRotated (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut))
    (D : {D : Components (ParentArc q c hcut) (ParentRegular q hR c hcut) T //
      D ≠ openComponent (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val}) :
    let C := tinyParentClosedComponentEquiv q hR c hc hcut η hη hη1 T D
    List.ofFn (ClosedVertex (ParentArc q c hcut) (ParentRegular q hR c hcut) T D.val D.property) ~r
      List.ofFn (ClosedVertex (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
        (tinySupportOfParent q hR c hc hcut η hη hη1 T) C.val C.property) := by
  let C := tinyParentClosedComponentEquiv q hR c hc hcut η hη hη1 T D
  let x := closedRoot (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val D.val D.property
  have hp := (closedRoot_spec (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple
    T.val D.val D.property).1
  have ht := (closedRoot_spec (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1).noTriple
    (parentTinySelection q c hcut η T.val) C.val C.property).1
  have hm := (tinyParentComponentEquiv_componentOf q hR c hc hcut η hη hη1 T x).symm
  rw [show componentOf (incoming (ParentArc q c hcut) (ParentRegular q hR c hcut).noTriple T.val) x = D.val from hp] at hm
  have hm' : componentOf (incoming (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1).noTriple
    (parentTinySelection q c hcut η T.val)) (parentEventIntoTiny q c hcut η x) = C.val := hm
  have hrot := CompatibleWords.retainedWord_isRotated_of_sameCycle
    (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
    (parentTinySelection q c hcut η T.val) (parentEventIntoTiny q c hcut η x)
    (closedRoot (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1).noTriple
      (parentTinySelection q c hcut η T.val) C.val C.property)
    ((componentOf_eq_iff _ _ _).mp (hm'.trans ht.symm))
  rw [tinyParent_closed_root_word q hR c hc hcut η hη hη1 T x (by rw [hp];exact D.property)] at hrot
  exact hrot

end DirectGLSSW.ActiveArc.LiteralTinyParent
