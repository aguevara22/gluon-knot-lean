import SM.TurnSupports
import SM.StrictBetween

/-! Central regularity and the unique zero turn at a flat wall, derived from
the printed singleton point-zero and strict betweenness hypotheses. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} {j : ZMod n}

theorem flat_fusion (h : StrictBetween (P (j - 1)) (P j) (P (j + 1))) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      edge P (j - 1) = t • (P (j + 1) - P (j - 1)) ∧
      edge P j = (1 - t) • (P (j + 1) - P (j - 1)) := by
  simpa only [edge, sub_add_cancel] using strictBetween_fusion h

theorem flat_center_regular (hn : 4 ≤ n) (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1))) : Regular P := by
  intro i
  by_cases hi : i = j
  · subst i
    simpa only [edge, sub_add_cancel] using strictBetween_regularPair hb
  · have hd : det (edge P (i - 1)) (edge P i) ≠ 0 := by
      exact sign_ne_zero.mp ((turn_det P i) ▸ singlePointTriple_turn_ne_zero hn hz hi)
    refine ⟨singlePointTriple_edge_ne_zero hn hz (i - 1),
      singlePointTriple_edge_ne_zero hn hz i, ?_⟩
    rintro ⟨r, _, hr⟩
    exact no_multiple_of_det_ne_zero hd r hr

theorem flat_center_geometry (hn : 4 ≤ n) (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1))) :
    Function.Injective P ∧ (∀ i, edge P i ≠ 0) ∧ Regular P ∧
      (∀ i, turn P i = 0 ↔ i = j) ∧
      (∃ r : ℝ, 0 < r ∧ edge P j = r • edge P (j - 1)) ∧
      principalTurn P j = 0 := by
  have hr := flat_center_regular hn hz hb
  have hp : ∃ r : ℝ, 0 < r ∧ edge P j = r • edge P (j - 1) := by
    simpa only [edge, sub_add_cancel] using strictBetween_positive_multiple hb
  refine ⟨singlePointTriple_vertices_injective hn hz,
    singlePointTriple_edge_ne_zero hn hz, hr, ?_, hp,
    (principalTurn_eq_zero_iff (hr j)).mpr hp⟩
  intro i
  constructor
  · intro he
    by_contra hne
    exact singlePointTriple_turn_ne_zero hn hz hne he
  · rintro rfl
    exact singlePointTriple_turn_zero hz

end SM
