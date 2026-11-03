import ActiveArcCutFilter
import OrbitWordCutTails

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

/-- The child tail is obtained by deleting its actual cut root and then
retaining precisely the original unselected physical support. -/
theorem child_tail_eq_unselected_filter :
    (DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S (Sum.inl 0)).tail =
    (((orbitWord (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
      (Sum.inr (c,true))).tail).filter
        (fun z => decide (retained q (pieceSelections q hR c hc hcut S T) z))).map (eventPoint q) := by
  let U := pieceSelections q hR c hc hcut S T
  let p := incoming q hR.noTriple (insert c U)
  have hu : c ∉ U := by
    intro hh
    exact ((pieceSelections_range q hR c hc hcut U).mp ⟨S,T,rfl⟩ c hh).1 rfl
  have hf := filter_retained_cut_of_avoids q c U hu (orbitWord p (Sum.inr (c,true))).tail
    (orbitWord_separated_not_mem_tail p _ _ (selected_cut_visits_separated q hR c hc hcut S T))
    (orbitWord_root_not_mem_tail p _)
  rw [← selected_child_word_at_cut q hR c hc hcut S T,retainedWord_eq_filtered]
  change (((orbitWord p (Sum.inr (c,true))).filter (fun z => decide (retained q (insert c U) z))).map (eventPoint q)).tail = _
  rw [orbitWord_cons_tail p (Sum.inr (c,true))]
  simp only [List.filter_cons,retained,Finset.mem_insert_self,decide_true,ite_true,List.map_cons,List.tail_cons]
  exact congrArg (List.map (eventPoint q)) hf.symm

/-- The parent tail is the original open selected orbit after removing its
initial mark and the actual left cut visit, with unchanged retention. -/
theorem parent_tail_eq_unselected_filter :
    (List.ofFn (RetainedWords.vertex (parent q c hcut) (regular_parent q hR c hcut) T
      (start (parent q c hcut)))).tail =
    (((orbitWord (incoming q hR.noTriple (insert c (pieceSelections q hR c hc hcut S T)))
      (start q)).drop 2).filter
        (fun z => decide (retained q (pieceSelections q hR c hc hcut S T) z))).map (eventPoint q) := by
  let U := pieceSelections q hR c hc hcut S T
  let p := incoming q hR.noTriple (insert c U)
  have hu : c ∉ U := by
    intro hh
    exact ((pieceSelections_range q hR c hc hcut U).mp ⟨S,T,rfl⟩ c hh).1 rfl
  have hs : p (start q) = Sum.inr (c,false) := incoming_start_first q hR c hc _
  have hsa : start q ≠ Sum.inr (c,false) := by intro hh; cases hh
  have hf := filter_retained_cut_of_avoids q c U hu ((orbitWord p (start q)).drop 2)
    (orbitWord_second_not_mem_drop_two p _ _ hsa hs)
    (orbitWord_separated_not_mem_drop_two p _ _ _ hs (selected_cut_visits_separated q hR c hc hcut S T))
  have hw := parent_open_word q hR c hc hcut S T
  rw [retainedWord_eq_filtered] at hw
  change ((orbitWord p (start q)).filter (fun z => decide (retained q (insert c U) z))).map (eventPoint q) = _ at hw
  rw [orbitWord_first_two p (start q) (Sum.inr (c,false)) hsa hs] at hw
  have ht := congrArg (fun L => L.drop 2) hw
  simp only [List.filter_cons,start,retained,Finset.mem_insert_self,decide_true,ite_true,
    List.map_cons,List.drop_succ_cons,List.drop_zero,List.drop_one] at ht
  exact ht.symm.trans (congrArg (List.map (eventPoint q)) hf.symm)

end DirectGLSSW.ActiveArc.CompatibleWords
