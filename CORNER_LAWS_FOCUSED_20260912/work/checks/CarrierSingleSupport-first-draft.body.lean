namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The actual full marked traversal, cut at a crossing's actual two visits,
supplies the source split list. Its completeness is proved from the traversal. -/
theorem smoothingSuccessor_singleton_splitList (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (v : Visit P) :
    ∃ A B : List (Mark P),
      (Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)).Nodup ∧
      (∀ m : Mark P, m ∈ Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)) ∧
      smoothingSuccessor hn hP {v.1} =
        (Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B)).formPerm *
          Equiv.swap (Sum.inr v : Mark P) (Sum.inr (visitTwin v)) := by
  have hv : (Sum.inr v : Mark P) ≠ Sum.inr (visitTwin v) := by
    intro h
    exact (visitTwin_ne v).symm (Sum.inr.inj h)
  obtain ⟨A, B, hN, hperm, hfull⟩ :=
    markSuccessor_splitList hn hP (Sum.inr v) (Sum.inr (visitTwin v)) hv
  refine ⟨A, B, hN, hfull, ?_⟩
  have he := smoothingSuccessor_insert hn hP (∅ : Finset (Crossing P)) v
    (Finset.notMem_empty v.1)
  simpa only [Finset.insert_empty, smoothingSuccessor_empty, hperm] using he

/-- The two incoming owners at one actual selected crossing are distinct. -/
theorem owner_singleton_ne (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (v : Visit P) :
    owner hn hP {v.1} (Sum.inr v) ≠ owner hn hP {v.1} (Sum.inr (visitTwin v)) := by
  obtain ⟨A, B, hN, _, he⟩ := smoothingSuccessor_singleton_splitList hn hP v
  intro h
  have hc := (owner_eq_iff hn hP {v.1} _ _).mp h
  rw [he] at hc
  exact splitList_not_sameCycle (Sum.inr v) (Sum.inr (visitTwin v)) A B hN hc

/-- Every actual component of one selected crossing is one of the two endpoint
components. This uses completeness of the actual list, including all vertices. -/
theorem owner_singleton_exhaust (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (v : Visit P) (q : Component hn hP {v.1}) :
    q = owner hn hP {v.1} (Sum.inr v) ∨
      q = owner hn hP {v.1} (Sum.inr (visitTwin v)) := by
  obtain ⟨A, B, hN, hfull, he⟩ := smoothingSuccessor_singleton_splitList hn hP v
  obtain ⟨x, rfl⟩ := owner_surjective hn hP {v.1} q
  have hcL (hx : x ∈ Sum.inr v :: B) :
      owner hn hP {v.1} x = owner hn hP {v.1} (Sum.inr v) := by
    apply (owner_eq_iff hn hP {v.1} _ _).mpr
    rw [he]
    exact ((splitList_left_sameCycle_iff (Sum.inr v) (Sum.inr (visitTwin v)) A B hN x).mpr hx).symm
  have hcR (hx : x ∈ Sum.inr (visitTwin v) :: A) :
      owner hn hP {v.1} x = owner hn hP {v.1} (Sum.inr (visitTwin v)) := by
    apply (owner_eq_iff hn hP {v.1} _ _).mpr
    rw [he]
    exact ((splitList_right_sameCycle_iff (Sum.inr v) (Sum.inr (visitTwin v)) A B hN x).mpr hx).symm
  rcases List.mem_cons.mp (hfull x) with hx | hx
  · exact Or.inl (hcL (List.mem_cons.mpr (Or.inl hx)))
  · rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (hcR (List.mem_cons_of_mem _ hx))
    · rcases List.mem_cons.mp hx with hx | hx
      · exact Or.inr (hcR (List.mem_cons.mpr (Or.inl hx)))
      · exact Or.inl (hcL (List.mem_cons_of_mem _ hx))

/-- Exactly two actual successor-orbit components arise from one selected
crossing. No arbitrary cycle representation or component correspondence is assumed. -/
theorem component_card_singleton (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (v : Visit P) : Fintype.card (Component hn hP {v.1}) = 2 := by
  have hu : (Finset.univ : Finset (Component hn hP {v.1})) =
      {owner hn hP {v.1} (Sum.inr v), owner hn hP {v.1} (Sum.inr (visitTwin v))} := by
    ext q
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact owner_singleton_exhaust hn hP v q
  have hc : (Finset.univ : Finset (Component hn hP {v.1})).card = 2 :=
    Finset.card_eq_two.mpr ⟨_, _, owner_singleton_ne hn hP v, hu⟩
  simpa only [Finset.card_univ] using hc

end
end SM.Carrier
