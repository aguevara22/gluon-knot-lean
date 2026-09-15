namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Rotate the actual owner-filtered list to any mark of that owner. The
anchored component representative is constructed from its actual membership. -/
theorem componentMarkList_rotate_start (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S)
    (a : Mark P) (ha : owner hn hP S a = q) :
    ∃ k : ℕ, ∃ R : List (Mark P), (componentMarkList hn hP S q).rotate k = a :: R := by
  have ham := ((componentMarkList_data hn hP S q).2.2.2 a).mpr ha
  obtain ⟨L, R, he⟩ := List.mem_iff_append.mp ham
  refine ⟨L.length, R ++ L, ?_⟩
  rw [he, List.rotate_append_length_eq, List.cons_append]

/-- Every literal representative of the actual inherited component filters
to the same actual corner cycle, independently of the chosen first entry. -/
theorem componentCornerCycle_eq_filter_of_list (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (S : Finset (Crossing P)) (q : Component hn hP S)
    (L : List (Mark P)) (hL : componentCycle hn hP S q = (L : Cycle (Mark P))) :
    componentCornerCycle hn hP S q =
      (L.filter (fun a => decide (IsTrueCorner S a)) : Cycle (Mark P)) := by
  unfold componentCornerCycle
  rw [hL]
  rfl

/-- Starting from an actual true corner, construct the first following true
corner and every omitted intermediate mark. The closed block is an actual
prefix of the rotated closed component list, whose action is the actual
successor. The endpoint may equal the anchor; no two-corner premise is used.
Positive geometric compression of this derived block remains a separate step. -/
theorem component_first_trueCorner_block (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : S ∈ independentSupports hn hP)
    (q : Component hn hP S) (a : Mark P) (ha : owner hn hP S a = q)
    (hac : IsTrueCorner S a) :
    ∃ (k : ℕ) (R M : List (Mark P)) (b : Mark P) (B : List (Mark P)),
      (componentMarkList hn hP S q).rotate k = a :: R ∧
      R ++ [a] = M ++ b :: B ∧
      (∀ x ∈ M, ¬ IsTrueCorner S x) ∧ IsTrueCorner S b ∧ owner hn hP S b = q ∧
      (a :: (M ++ [b])) <+: ((a :: R) ++ [a]) ∧
      (componentCornerCycle hn hP S q).next (componentCornerCycle_nodup hn hP S q)
        a ((mem_componentCornerCycle hn hP S q a).mpr ⟨ha, hac⟩) = b ∧
      Set.EqOn (a :: R).formPerm (smoothingSuccessor hn hP S) {m | m ∈ a :: R} := by
  let p : Mark P → Bool := fun m => decide (IsTrueCorner S m)
  have hpa : p a = true := by simp only [p, hac, decide_true]
  obtain ⟨k, R, hrot⟩ := componentMarkList_rotate_start hn hP S q a ha
  have hraw : (componentMarkList hn hP S q : Cycle (Mark P)) = componentCycle hn hP S q :=
    (componentMarkList_data hn hP S q).2.2.1
  have hrotC : ((componentMarkList hn hP S q).rotate k : Cycle (Mark P)) =
      (componentMarkList hn hP S q : Cycle (Mark P)) :=
    Cycle.coe_eq_coe.mpr (List.IsRotated.forall _ _)
  have hL : componentCycle hn hP S q = (a :: R : Cycle (Mark P)) :=
    hraw.symm.trans (hrotC.symm.trans (congrArg (fun L : List (Mark P) => (L : Cycle (Mark P))) hrot))
  have hN := componentCycle_list_nodup hn hP S q (a :: R) hL
  obtain ⟨M, b, B, hsplit, hM, hb, hnext, hprefix, _, _⟩ := firstCornerBlock p a R hN hpa
  have hnot : ∀ x ∈ M, ¬ IsTrueCorner S x := by
    intro x hx hc
    have he := hM x hx
    simp [p, hc] at he
  have hbc : IsTrueCorner S b := by
    simpa only [p, decide_eq_true_eq] using hb
  have hbclosed : b ∈ R ++ [a] := by
    rw [hsplit]
    exact List.mem_append_right M (List.mem_cons_self)
  have hbL : b ∈ a :: R := by
    rcases List.mem_append.mp hbclosed with hbR | hbA
    · exact List.mem_cons_of_mem a hbR
    · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hbA))
  have hbo : owner hn hP S b = q :=
    (componentCycle_list_mem_iff hn hP S q (a :: R) hL b).mp hbL
  have hC : componentCornerCycle hn hP S q = ((a :: R).filter p : Cycle (Mark P)) :=
    componentCornerCycle_eq_filter_of_list hn hP S q (a :: R) hL
  have hNF : ((a :: R).filter p).Nodup := hN.filter p
  have haF : a ∈ (a :: R).filter p := by simp [hpa]
  have haC : a ∈ componentCornerCycle hn hP S q :=
    (mem_componentCornerCycle hn hP S q a).mpr ⟨ha, hac⟩
  have hpair :
      (⟨componentCornerCycle hn hP S q, componentCornerCycle_nodup hn hP S q, haC⟩ :
        {s : Cycle (Mark P) // s.Nodup ∧ a ∈ s}) =
      ⟨((a :: R).filter p : Cycle (Mark P)), hNF, haF⟩ := Subtype.ext hC
  have htransport := congrArg
    (fun s : {s : Cycle (Mark P) // s.Nodup ∧ a ∈ s} => s.val.next s.property.1 a s.property.2) hpair
  change (componentCornerCycle hn hP S q).next (componentCornerCycle_nodup hn hP S q) a haC =
    ((a :: R).filter p).next a haF at htransport
  exact ⟨k, R, M, b, B, hrot, hsplit, hnot, hbc, hbo, hprefix, htransport.trans hnext,
    componentCycle_list_eqOn hn hP S (independent_inheritsMarkOrder hn hP hS) q (a :: R) hL⟩

end
end SM.Carrier
