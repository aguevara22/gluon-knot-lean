import SM.TripleCenter

/-! One actual neighbourhood on which every third crossing parameter remains
strictly outside the two selected crossing parameters on the common edge. -/

namespace SM

open Filter Topology

def OutsidePair (x a b : ℝ) : Prop := (x < a ∧ x < b) ∨ (a < x ∧ b < x)

theorem outsidePair_not_between {x a b : ℝ} (h : OutsidePair x a b) :
    ¬ (a < x ∧ x < b) ∧ ¬ (b < x ∧ x < a) := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> constructor <;> rintro ⟨h1, h2⟩ <;> linarith

theorem outsidePair_persists {α : Type*} [TopologicalSpace α] {t₀ : α}
    {f a b : α → ℝ} (hf : ContinuousAt f t₀) (ha : ContinuousAt a t₀)
    (hb : ContinuousAt b t₀) (hab : a t₀ = b t₀) (hne : f t₀ ≠ a t₀) :
    ∀ᶠ t in 𝓝 t₀, OutsidePair (f t) (a t) (b t) := by
  rcases lt_or_gt_of_ne hne with hlo | hhi
  · have hb0 : f t₀ < b t₀ := by rw [← hab]; exact hlo
    exact ((continuousAt_preserves_strict_order hf ha hlo).and
      (continuousAt_preserves_strict_order hf hb hb0)).mono (fun _ h => Or.inl h)
  · have hb0 : b t₀ < f t₀ := by rw [← hab]; exact hhi
    exact ((continuousAt_preserves_strict_order ha hf hhi).and
      (continuousAt_preserves_strict_order hb hf hb0)).mono (fun _ h => Or.inr h)

variable {n : ℕ} [NeZero n]

def OtherCrossingsOutside (P : LabelledTuple n) (i j k : ZMod n) : Prop :=
  ∀ h : ZMod n, h ≠ i → h ≠ j → h ≠ k → IsCrossing P {i, h} →
    OutsidePair (edgeParameter P i h) (edgeParameter P i j) (edgeParameter P i k)

theorem uniqueTriple_crossings {P : LabelledTuple n} {i j k : ZMod n}
    (hc : concurrenceTriples P = {{i, j, k}}) :
    IsCrossing P {i, j} ∧ IsCrossing P {i, k} ∧ IsCrossing P {j, k} := by
  obtain ⟨hij, hjk, hik, q, hi, hj, hk⟩ := uniqueTriple_data hc
  exact ⟨isCrossing_of_common_interiors hij hi hj,
    isCrossing_of_common_interiors hik hi hk, isCrossing_of_common_interiors hjk hj hk⟩

theorem uniqueTriple_outside_persists (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : G1 P) {i j k : ZMod n} (hc : concurrenceTriples P = {{i, j, k}}) :
    ∀ᶠ Q in 𝓝 P, OtherCrossingsOutside Q i j k := by
  have hsel := uniqueTriple_crossings hc
  have hparam : ∀ᶠ Q in 𝓝 P, ∀ h : ZMod n,
      h ≠ i → h ≠ j → h ≠ k → IsCrossing P {i, h} →
      OutsidePair (edgeParameter Q i h) (edgeParameter Q i j) (edgeParameter Q i k) := by
    apply eventually_all.mpr
    intro h
    by_cases hhi : h = i
    · exact Eventually.of_forall (fun _ hne => (hne hhi).elim)
    by_cases hhj : h = j
    · exact Eventually.of_forall (fun _ _ hne => (hne hhj).elim)
    by_cases hhk : h = k
    · exact Eventually.of_forall (fun _ _ _ hne => (hne hhk).elim)
    by_cases hh : IsCrossing P {i, h}
    · exact (outsidePair_persists (continuousAt_edgeParameter hn hP hh)
        (continuousAt_edgeParameter hn hP hsel.1) (continuousAt_edgeParameter hn hP hsel.2.1)
        (uniqueTriple_parameters_eq hn hP hc)
        (uniqueTriple_outside_parameter_ne hn hP hc hhi hhj hhk hh)).mono
        (fun _ h _ _ _ _ => h)
    · exact Eventually.of_forall (fun _ _ _ _ hcross => (hh hcross).elim)
  filter_upwards [g1_crossings_locally_constant hn hP, hparam] with Q hQ hparamQ
  intro h hhi hhj hhk hcross
  exact hparamQ h hhi hhj hhk ((hQ.2 {i, h}).mp hcross)

end SM
