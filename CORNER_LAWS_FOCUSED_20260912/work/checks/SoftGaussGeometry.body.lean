namespace SM

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {j : ZMod n} {q : Plane} {ε : ℝ}

/-- The actual incoming newborn visit is followed by the actual return visit
in the cyclic Gauss sequence. The explicit parameter-window helper input is
derived from the source hypotheses in the common-interval theorem below. -/
theorem softNewbornVisits_next (hn : 3 ≤ n)
    (hQ : Generic (softInsertion P j q ε)) (hp : SoftCrossingPersistence P j q ε)
    (hclass : SoftCrossingClassificationAt P j q ε)
    (hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j)
    (hbound : ∀ v : Visit P,
      (v.2.val = j - 1 → visitParameter (softInheritedVisit hp v) <
        visitParameter (softNewbornIncomingVisit hclass hloop)) ∧
      (v.2.val = j → visitParameter (softNewbornReturnVisit hclass hloop) <
        visitParameter (softInheritedVisit hp v))) :
    nextGaussVisit (by omega : 3 ≤ n + 1) hQ (softNewbornIncomingVisit hclass hloop) =
      softNewbornReturnVisit hclass hloop :=
  gauss_next_of_no_visit_between (by omega : 3 ≤ n + 1) hQ
    (softNewbornVisits_distinct hclass hloop)
    (softNewbornVisits_no_between hn hQ.1 hp hclass hloop hbound)

/-- One actual soft-family interval gives the non-loop Gauss word and, in
the loop sector, strict newborn interiors, the physical intervening soft edge,
the empty incoming-to-return arc, its actual next-visit equality, and deletion
of exactly the newborn visits and crossing letter. No zero-centre genericity,
external order correspondence, or empty-arc premise is assumed. -/
theorem soft_small_gauss_geometry (hn : 3 ≤ n) (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ hQ : Generic (softInsertion P j q ε),
      ∃ hp : SoftCrossingPersistence P j q ε,
      ∃ hclass : SoftCrossingClassificationAt P j q ε,
        (¬ (softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) →
          (gaussWord hn hP).map (softInheritedCrossing hp) =
            gaussWord (by omega : 3 ≤ n + 1) hQ) ∧
        (∀ hloop : softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j,
          (0 < visitParameter (softNewbornIncomingVisit hclass hloop) ∧
            visitParameter (softNewbornIncomingVisit hclass hloop) < 1) ∧
          (0 < visitParameter (softNewbornReturnVisit hclass hloop) ∧
            visitParameter (softNewbornReturnVisit hclass hloop) < 1) ∧
          (softNewbornIncomingVisit hclass hloop).2.val + 1 = softOldIndex j j ∧
          softOldIndex j j + 1 = (softNewbornReturnVisit hclass hloop).2.val ∧
          softInsertion P j q ε (softOldIndex j j) = P j ∧
          softInsertion P j q ε (softNewbornReturnVisit hclass hloop).2.val = P j + ε • q ∧
          (∀ w : Visit (softInsertion P j q ε),
            ¬ traversalBetween
              (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
              (visitPosition (by omega : 3 ≤ n + 1) hQ.1 w)
              (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop))) ∧
          nextGaussVisit (by omega : 3 ≤ n + 1) hQ (softNewbornIncomingVisit hclass hloop) =
            softNewbornReturnVisit hclass hloop ∧
          (gaussCycle hn hP).map (softInheritedVisit hp) =
            (gaussCycle (by omega : 3 ≤ n + 1) hQ).filter
              (fun w => decide (w.1 ≠ softNewbornCrossing hclass hloop)) ∧
          (gaussWord hn hP).map (softInheritedCrossing hp) =
            (gaussWord (by omega : 3 ≤ n + 1) hQ).filter
              (fun c => decide (c ≠ softNewbornCrossing hclass hloop))) := by
  obtain ⟨δw, hδw, hword⟩ := soft_small_gauss_word_transport hn hP j q hq
  obtain ⟨δa, hδa, harc⟩ := soft_newborn_small_empty_arc hn hP j q hq
  refine ⟨min δw δa, lt_min hδw hδa, ?_⟩
  intro ε hε hεδ
  obtain ⟨hQ, hp, hclass, hnonloop, hdelete⟩ :=
    hword ε hε (lt_of_lt_of_le hεδ (min_le_left δw δa))
  obtain ⟨hQ', hp', hclass', hgapdata⟩ :=
    harc ε hε (lt_of_lt_of_le hεδ (min_le_right δw δa))
  refine ⟨hQ, hp, hclass, hnonloop, ?_⟩
  intro hloop
  have hbounds := (hgapdata hloop).1
  have hgap : ∀ w : Visit (softInsertion P j q ε),
      ¬ traversalBetween
        (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornIncomingVisit hclass hloop))
        (visitPosition (by omega : 3 ≤ n + 1) hQ.1 w)
        (visitPosition (by omega : 3 ≤ n + 1) hQ.1 (softNewbornReturnVisit hclass hloop)) :=
    (hgapdata hloop).2
  have hi := softNewbornVisits_interior hn hQ.1 hclass hloop
  have hpath := softNewbornVisits_physical_path hn hclass hloop
  have hdel := hdelete hloop
  exact ⟨hi.1, hi.2, hpath.1, hpath.2.1, hpath.2.2.1, hpath.2.2.2,
    hgap, softNewbornVisits_next hn hQ hp hclass hloop hbounds, hdel.1, hdel.2⟩

end
end SM
