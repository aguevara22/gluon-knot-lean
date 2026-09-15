namespace SM

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {j : ZMod n} {q : Plane} {ε : ℝ}

/-- Remove precisely the visits of the actual newborn crossing. The result
is an equality in Cycle, independent of the chosen list representative. -/
theorem soft_gaussCycle_delete_newborn (hn : 3 ≤ n) (hP : Generic P)
    (hp : SoftCrossingPersistence P j q ε) (hQ : Generic (softInsertion P j q ε))
    (hclass : SoftCrossingClassificationAt P j q ε)
    (ho : SoftInheritedOrderAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    (gaussCycle hn hP).map (softInheritedVisit hp) =
      (gaussCycle (by omega : 3 ≤ n + 1) hQ).filter
        (fun w => decide (w.1 ≠ softNewbornCrossing hclass hloop)) := by
  have hpred : (fun w : Visit (softInsertion P j q ε) =>
      decide (w.1 ≠ softNewbornCrossing hclass hloop)) =
      (fun w => decide (w.1.val ≠ {softOldIndex j (j - 1), softNewIndex j})) := by
    funext w
    have he : w.1 ≠ softNewbornCrossing hclass hloop ↔
        w.1.val ≠ {softOldIndex j (j - 1), softNewIndex j} := by
      constructor
      · intro hne hs
        exact hne (Subtype.ext hs)
      · intro hne hs
        exact hne (congrArg Subtype.val hs)
    simp only [he]
  rw [hpred]
  exact congrArg (fun l : List (Visit (softInsertion P j q ε)) =>
    (l : Cycle (Visit (softInsertion P j q ε))))
    (soft_gaussList_inherited hn hP hp hQ hclass ho)

/-- Filtering the newborn crossing letter removes both occurrences. Mapping
visits to letters need not be injective; Cycle.filter_map preserves repetitions. -/
theorem soft_gaussWord_delete_newborn (hn : 3 ≤ n) (hP : Generic P)
    (hp : SoftCrossingPersistence P j q ε) (hQ : Generic (softInsertion P j q ε))
    (hclass : SoftCrossingClassificationAt P j q ε)
    (ho : SoftInheritedOrderAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) :
    (gaussWord hn hP).map (softInheritedCrossing hp) =
      (gaussWord (by omega : 3 ≤ n + 1) hQ).filter
        (fun c => decide (c ≠ softNewbornCrossing hclass hloop)) := by
  calc
    (gaussWord hn hP).map (softInheritedCrossing hp) =
        ((gaussCycle hn hP).map (softInheritedVisit hp)).map Sigma.fst := by
      simp only [gaussWord, gaussCycle, Cycle.map_coe, List.map_map,
        Function.comp_def, softInheritedVisit_crossing]
    _ = ((gaussCycle (by omega : 3 ≤ n + 1) hQ).filter
        (fun w => decide (w.1 ≠ softNewbornCrossing hclass hloop))).map Sigma.fst :=
      congrArg (Cycle.map Sigma.fst) (soft_gaussCycle_delete_newborn hn hP hp hQ hclass ho hloop)
    _ = (gaussWord (by omega : 3 ≤ n + 1) hQ).filter
        (fun c => decide (c ≠ softNewbornCrossing hclass hloop)) :=
      (Cycle.filter_map _ Sigma.fst _).symm

/-- Both sector conclusions are supplied on one positive interval directly
from parent Generic and admissibility. The crossing/visit maps are constructed,
not hypothesized; this theorem does not yet assert newborn adjacency. -/
theorem soft_small_gauss_word_transport (hn : 3 ≤ n) (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hQ : Generic (softInsertion P j q ε),
      ∃ hp : SoftCrossingPersistence P j q ε,
      ∃ hclass : SoftCrossingClassificationAt P j q ε,
        (¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) →
          (gaussWord hn hP).map (softInheritedCrossing hp) =
            gaussWord (by omega : 3 ≤ n + 1) hQ) ∧
        (∀ hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j,
          (gaussCycle hn hP).map (softInheritedVisit hp) =
            (gaussCycle (by omega : 3 ≤ n + 1) hQ).filter
              (fun w => decide (w.1 ≠ softNewbornCrossing hclass hloop)) ∧
          (gaussWord hn hP).map (softInheritedCrossing hp) =
            (gaussWord (by omega : 3 ≤ n + 1) hQ).filter
              (fun c => decide (c ≠ softNewbornCrossing hclass hloop))) := by
  obtain ⟨δ, hδ, hdata⟩ := soft_small_visit_order_data hn hP j q hq
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨hQ, hp, hclass, ho⟩ := hdata ε hε hεδ
  refine ⟨hQ, hp, hclass, soft_gaussWord_nonloop hn hP hp hQ hclass ho, ?_⟩
  intro hloop
  exact ⟨soft_gaussCycle_delete_newborn hn hP hp hQ hclass ho hloop,
    soft_gaussWord_delete_newborn hn hP hp hQ hclass ho hloop⟩

end
end SM
