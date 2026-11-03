import FilteredCoordinateGap
import ActiveArcCoordinateGapOrder

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW PermutationOrbits RetainedWords SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

/-- The actual right cut visit has a full-orbit coordinate whose strict
prefix contains exactly the child daughter's number of retained events. -/
theorem exists_right_visit_prefix_count :
    let U := pieceSelections q hR c hc hcut S T
    ∃ j : Coord q hR U (start q), eventAt q hR U (start q) j = Sum.inr (c,true) ∧
      (((orbitWord (incoming q hR.noTriple U) (start q)).take j.val).filter
        (fun x => decide (retained q U x))).length =
      (DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S (Sum.inl 0)).length := by
  intro U
  let p := incoming q hR.noTriple (insert c U)
  let A : List (Event q) := List.append [start q,Sum.inr (c,false)] (orbitWord p (Sum.inr (c,true))).tail
  let B := (orbitWord p (start q)).drop 2
  have hw : orbitWord (incoming q hR.noTriple U) (start q) =
      List.append A (Sum.inr (c,true) :: B) := by
    simpa only [List.append_assoc,List.append_eq] using
      unselected_open_orbitWord_splice q hR c hc hcut S T
  have hjlt : A.length < Fintype.card (Fibre (incoming q hR.noTriple U)
      (componentOf (incoming q hR.noTriple U) (start q))) := by
    rw [← orbitWord_length,hw]
    simp only [List.append_eq,List.length_append,List.length_cons]
    omega
  let j : Coord q hR U (start q) := ⟨A.length,hjlt⟩
  have hje : eventAt q hR U (start q) j = Sum.inr (c,true) := by
    have hh := List.getElem_of_append hw (show A.length=j.val from rfl)
    simpa only [orbitWord,List.getElem_ofFn,eventAt] using hh
  refine ⟨j,hje,?_⟩
  have ht := congrArg List.length (child_tail_eq_unselected_filter q hR c hc hcut S T)
  simp only [List.length_tail,List.length_map] at ht
  have hhead := selected_child_word_head q hR c hc hcut S
  have hpos : 0 < (DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S (Sum.inl 0)).length := by
    cases he : DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S (Sum.inl 0) with
    | nil => simp only [he,List.head?_nil,reduceCtorEq] at hhead
    | cons x xs => simp
  change (((orbitWord (incoming q hR.noTriple U) (start q)).take A.length).filter _).length = _
  rw [hw,List.append_eq,List.take_left]
  have hu : c∉U := cut_not_mem_pieceSelections q hR c hc hcut S T
  simp only [A,List.append_eq,List.filter_append,List.filter_cons,List.filter_nil,
    retained,start,hu,decide_false,decide_true,ite_false,ite_true,List.length_append,List.length_cons,List.length_nil]
  change 1 + ((orbitWord p (Sum.inr (c,true))).tail.filter (fun x => decide (retained q U x))).length = _
  change _ = ((orbitWord p (Sum.inr (c,true))).tail.filter (fun x => decide (retained q U x))).length at ht
  omega

end DirectGLSSW.ActiveArc.CompatibleWords
