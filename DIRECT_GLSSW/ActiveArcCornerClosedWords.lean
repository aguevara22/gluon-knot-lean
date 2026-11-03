import ActiveArcCornerClosedComponents
import ActiveArcRetainedOrbitComponents
import DirectGLSSW.DaughterPointListFilter

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Primitive RetainedWords PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)

/-- A matching closed root has exactly the same actual retained point word. -/
theorem corner_closed_root_word (T : Nonalternation.Support (suffix q)
    (regular_suffix q hR)) (x : Event (suffix q))
    (hx : componentOf (incoming (suffix q) (regular_suffix q hR).noTriple T.val) x ≠
      openComponent (suffix q) (regular_suffix q hR).noTriple T.val) :
    List.ofFn (RetainedWords.vertex q hR
      (firstEdgeFreeSupportEquiv q hfree hR T).val (suffixEventIntoOriginal q hfree x)) =
    List.ofFn (RetainedWords.vertex (suffix q) (regular_suffix q hR)
      T.val x) := by
  let p := incoming (suffix q) (regular_suffix q hR).noTriple T.val
  let r := incoming q hR.noTriple
    (firstEdgeFreeSupportEquiv q hfree hR T).val
  let E := cornerEventInsertionEquiv (q:=q) (hR:=hR) (hfree:=hfree)
  have hb := corner_incoming_start (q:=q) (hR:=hR) (hfree:=hfree) T
  have hs := corner_incoming_step (q:=q) (hR:=hR) (hfree:=hfree) T
  have hn : ¬ p.SameCycle x (start (suffix q)) := by
    intro hh
    exact hx ((componentOf_eq_iff p _ _).mpr hh)
  have hw := PermutationInsertion.unaffected_orbitWord p r
    (start (suffix q)) (start q) E hb hs x hn
  change orbitWord r (suffixEventIntoOriginal q hfree x) =
    (orbitWord p x).map (suffixEventIntoOriginal q hfree) at hw
  rw [SingletonWords.retainedWord_eq_filtered (a:=1) (b:=b)
    q hR
    (firstEdgeFreeSupportEquiv q hfree hR T).val (suffixEventIntoOriginal q hfree x),
    SingletonWords.retainedWord_eq_filtered (a:=b) (b:=0)
      (suffix q) (regular_suffix q hR) T.val x,hw]
  have hret : ∀ y : Event (suffix q),
      decide (retained q (firstEdgeFreeSupportEquiv q hfree hR T).val
        (suffixEventIntoOriginal q hfree y)) =
      decide (retained (suffix q) T.val y) := by
    intro y
    have he := suffixEventIntoOriginal_retained q hR hfree T y
    by_cases hp : retained (suffix q) T.val y
    · have ht := he.mpr hp
      simp only [hp,ht,decide_true]
    · have ht : ¬ retained q (firstEdgeFreeSupportEquiv q hfree hR T).val
          (suffixEventIntoOriginal q hfree y) := fun hh => hp (he.mp hh)
      simp only [hp,ht,decide_false]
  rw [← DaughterPointListFilter.map_filter_comp]
  simp only [hret,List.map_map]
  apply List.map_congr_left
  intro y hy
  exact suffixEventIntoOriginal_point q hR hfree y

/-- Canonical actual closed roots differ only by a cyclic rebase. -/
theorem corner_closed_word_isRotated (T : Nonalternation.Support (suffix q)
    (regular_suffix q hR))
    (D : {D : Components (suffix q) (regular_suffix q hR) T //
      D ≠ openComponent (suffix q) (regular_suffix q hR).noTriple T.val}) :
    let C := cornerClosedComponentEquiv q hR hfree T D
    List.ofFn (ClosedVertex (suffix q) (regular_suffix q hR) T D.val D.property) ~r
      List.ofFn (ClosedVertex q hR
        (firstEdgeFreeSupportEquiv q hfree hR T) C.val C.property) := by
  let C := cornerClosedComponentEquiv q hR hfree T D
  let x := closedRoot (suffix q) (regular_suffix q hR).noTriple T.val D.val D.property
  have hp := (closedRoot_spec (suffix q) (regular_suffix q hR).noTriple
    T.val D.val D.property).1
  have ht := (closedRoot_spec q hR.noTriple
    (firstEdgeFreeSupportEquiv q hfree hR T).val C.val C.property).1
  have hm := (cornerComponentEquiv_componentOf q hR hfree T x).symm
  rw [show componentOf (incoming (suffix q) (regular_suffix q hR).noTriple T.val) x = D.val from hp] at hm
  have hm' : componentOf (incoming q hR.noTriple
    (firstEdgeFreeSupportEquiv q hfree hR T).val) (suffixEventIntoOriginal q hfree x) = C.val := hm
  have hrot := CompatibleWords.retainedWord_isRotated_of_sameCycle
    q hR
    (firstEdgeFreeSupportEquiv q hfree hR T).val (suffixEventIntoOriginal q hfree x)
    (closedRoot q hR.noTriple
      (firstEdgeFreeSupportEquiv q hfree hR T).val C.val C.property)
    ((componentOf_eq_iff _ _ _).mp (hm'.trans ht.symm))
  rw [corner_closed_root_word q hR hfree T x (by rw [hp];exact D.property)] at hrot
  exact hrot

end DirectGLSSW.ActiveArc.Split
