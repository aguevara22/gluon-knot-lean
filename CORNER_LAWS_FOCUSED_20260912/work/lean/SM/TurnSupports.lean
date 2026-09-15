import SM.SinglePointTriple

/-! Distinct cyclic centres have distinct three-vertex turn supports for n>=4.
All modular wraparound cases, including n=4, are retained. -/

namespace SM

variable {n : ℕ} [NeZero n]

def turnSupport (i : ZMod n) : Finset (ZMod n) := {i - 1, i, i + 1}

theorem small_natCast_ne_zero {m : ℕ} (hm : 0 < m) (hmn : m < n) :
    (m : ZMod n) ≠ 0 := by
  intro he
  have hd : n ∣ m := (ZMod.natCast_eq_zero_iff m n).mp he
  have hle : n ≤ m := Nat.le_of_dvd hm hd
  omega

theorem turnSupport_card (hn : 3 ≤ n) (i : ZMod n) : (turnSupport i).card = 3 := by
  letI : Fact (1 < n) := ⟨by omega⟩
  exact Finset.card_triple_eq_three_iff.mpr
    ⟨prev_ne_self i, prev_ne_next hn i, (next_ne_self i).symm⟩

theorem turnSupport_injective (hn : 4 ≤ n) : Function.Injective (turnSupport (n := n)) := by
  intro i j he
  have h1 : (1 : ZMod n) ≠ 0 := by
    simpa using small_natCast_ne_zero (n := n) (m := 1) (by omega) (by omega)
  have h2 : (2 : ZMod n) ≠ 0 := by
    simpa using small_natCast_ne_zero (n := n) (m := 2) (by omega) (by omega)
  have h3 : (3 : ZMod n) ≠ 0 := by
    simpa using small_natCast_ne_zero (n := n) (m := 3) (by omega) (by omega)
  have hi : i ∈ turnSupport j := by rw [← he]; simp [turnSupport]
  simp only [turnSupport, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with hi | hi | hi
  · have hm : i - 1 ∈ turnSupport j := by rw [← he]; simp [turnSupport]
    rw [hi] at hm
    simp only [turnSupport, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exact (h1 (by linear_combination -hm)).elim
    · exact (h2 (by linear_combination -hm)).elim
    · exact (h3 (by linear_combination -hm)).elim
  · exact hi
  · have hm : i + 1 ∈ turnSupport j := by rw [← he]; simp [turnSupport]
    rw [hi] at hm
    simp only [turnSupport, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exact (h3 (by linear_combination hm)).elim
    · exact (h2 (by linear_combination hm)).elim
    · exact (h1 (by linear_combination hm)).elim

theorem singlePointTriple_turn_ne_zero (hn : 4 ≤ n) {P : LabelledTuple n}
    {j : ZMod n} (h : pointZeroTriples P = {turnSupport j}) {i : ZMod n} (hi : i ≠ j) :
    turn P i ≠ 0 := by
  letI : Fact (1 < n) := ⟨by omega⟩
  exact chi_nonzero_outside_singleton h (prev_ne_self i) (next_ne_self i).symm
    (prev_ne_next (by omega) i) (fun he => hi (turnSupport_injective hn he))

theorem singlePointTriple_turn_zero {P : LabelledTuple n} {j : ZMod n}
    (h : pointZeroTriples P = {turnSupport j}) : turn P j = 0 := by
  have hp := singlePointTriple_data h
  exact hp.2 (j - 1) (by simp [turnSupport]) j (by simp [turnSupport])
    (j + 1) (by simp [turnSupport])

end SM
