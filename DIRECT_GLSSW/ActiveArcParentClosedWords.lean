import ActiveArcComplementRootWords

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

private theorem reducedParentSeam :
    letI := eventOrder q hR.noTriple
    letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
    let P := orderedCyclicSuccessor (ParentRetained q c hcut T)*physicalRetainedPairing (parent q c hcut) T
    let Q := orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T)*complementRetainedPairing q hR c hc hcut S T
    let E := parentRetainedOrderIso q hR c hc hcut S T
    Q (complementRetainedStart q hR c hc hcut S T)=(E (parentRetainedStart q c hcut T)).val ∧
      ∀ x, Q (E x).val=@ite (ComplementRetained q hR c hc hcut S T)
        (P x=parentRetainedStart q c hcut T) (Classical.propDecidable _)
        (complementRetainedStart q hR c hc hcut S T) (E (P x)).val := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
  constructor
  · change orderedCyclicSuccessor _ (complementRetainedPairing q hR c hc hcut S T
      (complementRetainedStart q hR c hc hcut S T))=_
    rw [complementRetainedPairing_start]
    exact complementRetained_successor_start q hR c hc hcut S T
  · intro x
    change orderedCyclicSuccessor _ (complementRetainedPairing q hR c hc hcut S T
      (parentRetainedOrderIso q hR c hc hcut S T x).val)=_
    rw [complementRetainedPairing_image]
    simpa only [Equiv.Perm.mul_apply] using
      complementRetained_successor_image q hR c hc hcut S T (physicalRetainedPairing (parent q c hcut) T x)

/-- Actual original and parent component membership agree on the mapped
retained parent labels. This is derived from deletion and the insertion seam. -/
theorem mapped_parent_sameCycle_iff (x y : ParentRetained q c hcut T) :
    (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))).SameCycle
      (parentEventMap q hR c hc hcut x.val) (parentEventMap q hR c hc hcut y.val) ↔
    (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T).SameCycle x.val y.val := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
  let P := orderedCyclicSuccessor (ParentRetained q c hcut T)*physicalRetainedPairing (parent q c hcut) T
  let Q := orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T)*complementRetainedPairing q hR c hc hcut S T
  let E := parentRetainedOrderIso q hR c hc hcut S T
  have hs := reducedParentSeam q hR c hc hcut S T
  have he := PermutationInsertion.inserted_sameCycle_iff P Q
    (parentRetainedStart q c hcut T) (complementRetainedStart q hR c hc hcut S T) E.toEquiv hs.1 hs.2 x y
  exact (complementRetained_sameCycle_iff q hR c hc hcut S T (E x).val (E y).val).trans
    (he.trans (retained_sameCycle_iff_reduced (parent q c hcut) (regular_parent q hR c hcut) T x y).symm)

/-- In particular, the actual parent open component is exactly the mapped
part of the original open component. -/
theorem mapped_parent_open_iff (x : ParentRetained q c hcut T) :
    (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))).SameCycle
      (parentEventMap q hR c hc hcut x.val) (start q) ↔
    (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T).SameCycle x.val (start (parent q c hcut)) := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
  let P := orderedCyclicSuccessor (ParentRetained q c hcut T)*physicalRetainedPairing (parent q c hcut) T
  let Q := orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T)*complementRetainedPairing q hR c hc hcut S T
  let E := parentRetainedOrderIso q hR c hc hcut S T
  have hs := reducedParentSeam q hR c hc hcut S T
  have he := PermutationInsertion.extra_sameCycle_iff P Q
    (parentRetainedStart q c hcut T) (complementRetainedStart q hR c hc hcut S T) E.toEquiv hs.1 hs.2 x
  have he' : Q.SameCycle (E x).val (complementRetainedStart q hR c hc hcut S T) ↔
      P.SameCycle x (parentRetainedStart q c hcut T) :=
    ⟨fun hh => (he.mp hh.symm).symm,fun hh => (he.mpr hh.symm).symm⟩
  exact (complementRetained_sameCycle_iff q hR c hc hcut S T (E x).val
    (complementRetainedStart q hR c hc hcut S T)).trans
    (he'.trans (retained_sameCycle_iff_reduced (parent q c hcut) (regular_parent q hR c hcut) T x
      (parentRetainedStart q c hcut T)).symm)

/-- Every actual parent closed component maps to an actual original closed
component; the component is not merely declared closed. -/
theorem parent_closed_root_stays_closed (x : ParentRetained q c hcut T)
    (hx : componentOf (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T) x.val≠
      openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T) :
    componentOf (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
      (parentEventMap q hR c hc hcut x.val)≠openComponent q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) := by
  intro hh
  apply hx
  apply (componentOf_eq_iff _ _ _).mpr
  exact (mapped_parent_open_iff q hR c hc hcut S T x).mp ((componentOf_eq_iff _ _ _).mp hh)

/-- Literal retained point words on actual parent closed components are
unchanged by insertion of the cut and independent child selections. -/
theorem parent_closed_word (x : ParentRetained q c hcut T)
    (hx : componentOf (incoming (parent q c hcut) (regular_parent q hR c hcut).noTriple T) x.val≠
      openComponent (parent q c hcut) (regular_parent q hR c hcut).noTriple T) :
    List.ofFn (RetainedWords.vertex q hR (insert c (pieceSelections q hR c hc hcut S T))
      (parentEventMap q hR c hc hcut x.val))=
    List.ofFn (RetainedWords.vertex (parent q c hcut) (regular_parent q hR c hcut) T x.val) := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (parent q c hcut) (regular_parent q hR c hcut).noTriple
  let P := orderedCyclicSuccessor (ParentRetained q c hcut T)*physicalRetainedPairing (parent q c hcut) T
  let Q := orderedCyclicSuccessor (ComplementRetained q hR c hc hcut S T)*complementRetainedPairing q hR c hc hcut S T
  let E := parentRetainedOrderIso q hR c hc hcut S T
  have hs := reducedParentSeam q hR c hc hcut S T
  have hn : ¬P.SameCycle x (parentRetainedStart q c hcut T) := by
    intro hh
    apply hx
    exact (componentOf_eq_iff _ _ _).mpr
      ((retained_sameCycle_iff_reduced (parent q c hcut) (regular_parent q hR c hcut) T x
        (parentRetainedStart q c hcut T)).mpr hh)
  have hw := PermutationInsertion.unaffected_orbitWord P Q
    (parentRetainedStart q c hcut T) (complementRetainedStart q hR c hc hcut S T) E.toEquiv hs.1 hs.2 x hn
  have hp := congrArg (List.map (fun y : ComplementRetained q hR c hc hcut S T => eventPoint q y.val)) hw
  change List.ofFn (RetainedWords.vertex q hR (insert c (pieceSelections q hR c hc hcut S T)) (E x).val.val)=_
  rw [complementRetained_pointWord,retainedWord_eq_reduced (parent q c hcut) (regular_parent q hR c hcut) T x.val x.property]
  rw [List.map_map] at hp
  refine hp.trans ?_
  apply List.map_congr_left
  intro y _
  exact parentEventMap_point q hR c hc hcut y.val

end DirectGLSSW.ActiveArc.CompatibleWords
