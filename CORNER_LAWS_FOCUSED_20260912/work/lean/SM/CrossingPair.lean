import SM.GaussVisits

/-! Exhaustion of the actual two-element visit fibre of each crossing. -/

namespace SM

variable {n : ℕ} {P : LabelledTuple n}

theorem crossing_visits_exist (c : Crossing P) :
    ∃ i j : {k // k ∈ c.val}, i ≠ j := by
  classical
  have hc : (Finset.univ : Finset {k // k ∈ c.val}).card = 2 := by
    simpa only [Finset.card_univ] using visits_per_crossing P c
  obtain ⟨i, j, hij, _⟩ := Finset.card_eq_two.mp hc
  exact ⟨i, j, hij⟩

theorem crossing_visits_exhaust (c : Crossing P) (i j : {k // k ∈ c.val})
    (hij : i ≠ j) (k : {l // l ∈ c.val}) : k = i ∨ k = j := by
  classical
  have hp : ({i, j} : Finset {l // l ∈ c.val}) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp only [Finset.card_univ, visits_per_crossing, Finset.card_pair hij]
    exact le_rfl
  have hk : k ∈ ({i, j} : Finset {l // l ∈ c.val}) := by rw [hp]; simp
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hk

theorem crossing_other_visit (c : Crossing P) (i : {k // k ∈ c.val}) :
    ∃ j : {k // k ∈ c.val}, j ≠ i := by
  obtain ⟨a, b, hab⟩ := crossing_visits_exist c
  by_cases hai : a = i
  · exact ⟨b, by simpa only [← hai] using hab.symm⟩
  · exact ⟨a, hai⟩

theorem crossing_unique_visit_iff (c : Crossing P) (p : {k // k ∈ c.val} → Prop) :
    (∃! i, p i) ↔ ∃ i j, i ≠ j ∧ p i ∧ ¬ p j := by
  constructor
  · rintro ⟨i, hi, hu⟩
    obtain ⟨j, hji⟩ := crossing_other_visit c i
    exact ⟨i, j, hji.symm, hi, fun hj => hji (hu j hj)⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨i, hi, ?_⟩
    intro k hk
    rcases crossing_visits_exhaust c i j hij k with he | he
    · exact he
    · exact (hj (he ▸ hk)).elim

noncomputable def crossingVisitPosition (hn : 3 ≤ n) (hP : G1 P)
    (c : Crossing P) (i : {k // k ∈ c.val}) : TraversalPoint n :=
  visitPosition hn hP ⟨c, i⟩

theorem crossingVisitPosition_injective (hn : 3 ≤ n) (hP : Generic P)
    (c : Crossing P) : Function.Injective (crossingVisitPosition hn hP.1 c) := by
  intro i j h
  have he := visitPosition_injective hn hP h
  exact Sigma.mk.inj_iff.mp he |>.2 |> eq_of_heq

theorem crossingVisitPosition_ne (hn : 3 ≤ n) (hP : Generic P)
    {c d : Crossing P} (hcd : c ≠ d) (i : {k // k ∈ c.val})
    (j : {k // k ∈ d.val}) :
    crossingVisitPosition hn hP.1 c i ≠ crossingVisitPosition hn hP.1 d j := by
  intro he
  exact hcd (congrArg Sigma.fst (visitPosition_injective hn hP he))

end SM
