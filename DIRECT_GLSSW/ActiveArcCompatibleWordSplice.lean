import OrbitJoinWordAtPredecessor
import ActiveArcCutWordTails

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (S : Finset (PolygonCrossing (child q hR c hc.1 hcut)))
variable (T : Finset (Crossing (parent q c hcut)))

/-- Undoing the actual compatible cut joins the two selected orbit words.
Both physical cut labels are displayed before retention deletes them. -/
theorem unselected_open_orbitWord_splice :
    orbitWord (α := Event q) (incoming q hR.noTriple (pieceSelections q hR c hc hcut S T)) (start q) =
      List.append (α := Event q) [start q,Sum.inr (c,false)]
        (List.append (α := Event q)
          (orbitWord (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
            (Sum.inr (c,true))).tail
          (Sum.inr (c,true) ::
            (orbitWord (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
              (start q)).drop 2)) := by
  classical
  let U := pieceSelections q hR c hc hcut S T
  have hu : c∉U := by
    intro hh
    exact ((pieceSelections_range q hR c hc hcut U).mp ⟨S,T,rfl⟩ c hh).1 rfl
  rw [incoming_unselected_eq_swap q hR c U hu]
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using
    orbitWord_mul_swap_join_predecessor _ _ _ _
      (selected_cut_visits_separated q hR c hc hcut S T)
      (by intro hh; cases hh) (incoming_start_first q hR c hc _)

/-- Literal retained word of the compatible unselected support: original
initial mark, actual child tail, actual parent tail. The cut point is not
repeated or inserted into the unselected word. -/
theorem unselected_open_pointWord_splice :
    List.ofFn (RetainedWords.vertex q hR (pieceSelections q hR c hc hcut S T) (start q)) =
      q ⟨0,by omega⟩ ::
        ((DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
          (child_noTriple q hR c hc.1 hcut) S (Sum.inl 0)).tail ++
        (List.ofFn (RetainedWords.vertex (parent q c hcut) (regular_parent q hR c hcut) T
          (start (parent q c hcut)))).tail) := by
  let U := pieceSelections q hR c hc hcut S T
  have hu : c∉U := by
    intro hh
    exact ((pieceSelections_range q hR c hc hcut U).mp ⟨S,T,rfl⟩ c hh).1 rfl
  rw [child_tail_eq_unselected_filter q hR c hc hcut S T,
    parent_tail_eq_unselected_filter q hR c hc hcut S T,
    retainedWord_eq_filtered,unselected_open_orbitWord_splice q hR c hc hcut S T]
  simp only [Event] at *
  have hfalse : (false : Bool) ≠ true := by decide
  simp only [hfalse,List.append_eq,List.filter_append,List.filter_cons,List.filter_nil,List.map_append,
    List.map_cons,List.map_nil,retained,start,show c∉pieceSelections q hR c hc hcut S T from hu,
    decide_false,decide_true,ite_false,ite_true,List.nil_append,List.cons_append]
  simp only [if_neg hfalse,List.map_append]
  rfl

/-- At the crossing endpoint, replacing only the original initial mark by c
makes the child prefix literal, followed by the parent tail without repeated c. -/
theorem unselected_event_pointWord_splice :
    crossingPoint q c ::
      (List.ofFn (RetainedWords.vertex q hR (pieceSelections q hR c hc hcut S T) (start q))).tail =
      DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S (Sum.inl 0) ++
      (List.ofFn (RetainedWords.vertex (parent q c hcut) (regular_parent q hR c hcut) T
        (start (parent q c hcut)))).tail := by
  have hh := selected_child_word_head q hR c hc hcut S
  have he : DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S (Sum.inl 0) =
      crossingPoint q c :: (DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S (Sum.inl 0)).tail := by
    cases hw : DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S (Sum.inl 0) with
    | nil => simp only [hw,List.head?_nil,reduceCtorEq] at hh
    | cons x xs =>
      simp only [hw,List.head?_cons,Option.some.injEq] at hh
      simp only [List.tail_cons,hh]
  rw [unselected_open_pointWord_splice q hR c hc hcut S T,List.tail_cons]
  conv_rhs => rw [he]
  rfl

end DirectGLSSW.ActiveArc.CompatibleWords
