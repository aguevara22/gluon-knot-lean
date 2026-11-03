import ActiveArcChildReducedSuccessor

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor RetainedWords
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

/-- Exact actual component equivalence on mapped retained child labels. -/
theorem mapped_child_sameCycle_iff (x y : ChildRetained q hR c hc hcut S) :
    (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))).SameCycle
      (childEventMap q hR c hc hcut x.val) (childEventMap q hR c hc hcut y.val) ↔
    (smoothingIncomingPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S).SameCycle x.val y.val := by
  letI := eventOrder q hR.noTriple
  letI := polygonEventOrder (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut)
  let P := orderedCyclicSuccessor (ChildRetained q hR c hc hcut S)*polygonRetainedPairing (child q hR c hc.1 hcut) S
  let Q := orderedCyclicSuccessor (IntervalRetained q hR c hc hcut S T)*intervalRetainedPairing q hR c hc hcut S T
  let E := childRetainedEquiv q hR c hc hcut S T
  have he := sameCycle_iff_of_intertwining E P Q
    (fun z => (childRetainedEquiv_incoming q hR c hc hcut S T z).symm) x y
  exact (intervalRetained_sameCycle_iff q hR c hc hcut S T (E x) (E y)).trans
    (he.symm.trans (polygonRetained_sameCycle_iff (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S x y).symm)

/-- The paired child labels are the actual outgoing-dart convention. -/
theorem mapped_child_dart_sameCycle_iff (x y : ChildRetained q hR c hc hcut S) :
    (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T))).SameCycle
      (childEventMap q hR c hc hcut x.val) (childEventMap q hR c hc hcut y.val) ↔
    (smoothingDartPermutation (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S).SameCycle
      (smoothingPairing (child q hR c hc.1 hcut) S x.val)
      (smoothingPairing (child q hR c hc.1 hcut) S y.val) := by
  exact (mapped_child_sameCycle_iff q hR c hc hcut S T x y).trans
    (sameCycle_iff_of_intertwining (smoothingPairing (child q hR c hc.1 hcut) S)
      _ _ (fun z => (smoothingPermutation_intertwine (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S z).symm) x.val y.val)

/-- Every mapped child retained root belongs to a genuinely closed original
component, since its interval cannot meet the original start complement. -/
theorem child_root_closed (x : ChildRetained q hR c hc hcut S) :
    componentOf (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
      (childEventMap q hR c hc hcut x.val)≠openComponent q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)) := by
  intro he
  have hn := complement_of_retained_sameCycle q hR c hc hcut S T
    (complementRetainedStart q hR c hc hcut S T) (childEventMap q hR c hc hcut x.val)
    ((childEventMap_retained q hR c hc hcut S T x.val).mpr x.property)
    ((componentOf_eq_iff _ _ _).mp he.symm)
  exact hn (childEventMap_in_interval q hR c hc hcut x.val)

/-- Literal actual original retained point word equals the actual cyclic
child outgoing-dart daughter word at its paired retained root. No genericity
or word-equivalence premise is supplied. -/
theorem child_root_word (x : ChildRetained q hR c hc hcut S) :
    List.ofFn (RetainedWords.vertex q hR (insert c (pieceSelections q hR c hc hcut S T))
      (childEventMap q hR c hc hcut x.val))=
    DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) S
      (smoothingPairing (child q hR c hc.1 hcut) S x.val) := by
  letI := eventOrder q hR.noTriple
  letI := polygonEventOrder (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut)
  have hw := childRetainedEquiv_orbitWord q hR c hc hcut S T x
  have hp := congrArg (List.map (fun y : IntervalRetained q hR c hc hcut S T => eventPoint q y.val)) hw
  change List.ofFn (RetainedWords.vertex q hR (insert c (pieceSelections q hR c hc hcut S T))
      (childRetainedEquiv q hR c hc hcut S T x).val)=_
  rw [intervalRetained_pointWord,polygonRetained_pointWord]
  rw [List.map_map] at hp
  refine hp.trans ?_
  apply List.map_congr_left
  intro y _
  exact childEventMap_point q hR c hc hcut y.val

end DirectGLSSW.ActiveArc.CompatibleWords
