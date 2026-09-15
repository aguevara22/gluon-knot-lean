import SM.GaussWord
import SM.Chambers

/-! Visits of an actual crossing to a specified edge, and exhaustion of all
visits on that edge by the other crossing label. -/

namespace SM

variable {n : ℕ} {P : LabelledTuple n}

def pairVisit {i j : ZMod n} (hc : IsCrossing P {i, j}) : Visit P :=
  ⟨⟨{i, j}, hc⟩, i, by simp⟩

theorem pairVisit_parameter (hn : 3 ≤ n) (hP : G1 P) {i j : ZMod n}
    (hc : IsCrossing P {i, j}) : visitParameter (pairVisit hc) = edgeParameter P i j :=
  crossingParameter_eq_edgeParameter hn hP hc

theorem visit_ext {v w : Visit P} (hc : v.1.val = w.1.val)
    (he : v.2.val = w.2.val) : v = w := by
  have hcross : v.1 = w.1 := Subtype.ext hc
  cases v with
  | mk c i =>
    cases w with
    | mk d j =>
      dsimp only at hcross he
      cases hcross
      have hij : i = j := Subtype.ext he
      cases hij
      rfl

theorem crossing_pair_of_mem (c : Crossing P) (i : ZMod n) (hi : i ∈ c.val) :
    ∃ j, j ≠ i ∧ c.val = {i, j} := by
  obtain ⟨a, b, hs, hr, _⟩ := c.property
  have hba : b ≠ a := (remote_endpoints a b hr).1
  rw [hs] at hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact ⟨b, hba, hs⟩
  · exact ⟨a, hba.symm, by simpa only [Finset.pair_comm] using hs⟩

theorem visit_on_edge_pair (v : Visit P) {i : ZMod n} (hi : v.2.val = i) :
    ∃ j, j ≠ i ∧ ∃ hc : IsCrossing P {i, j}, v = pairVisit hc := by
  have hm : i ∈ v.1.val := hi ▸ v.2.property
  obtain ⟨j, hji, hs⟩ := crossing_pair_of_mem v.1 i hm
  have hc : IsCrossing P {i, j} := hs ▸ v.1.property
  exact ⟨j, hji, hc, visit_ext hs hi⟩

theorem visitKey_lt_iff (hn : 3 ≤ n) (hP : G1 P) (v w : Visit P) :
    visitKey hn hP v < visitKey hn hP w ↔
      v.2.val.val < w.2.val.val ∨
        v.2.val = w.2.val ∧ visitParameter v < visitParameter w := by
  letI : NeZero n := ⟨by omega⟩
  exact traversalKey_lt_iff (visitPosition hn hP v) (visitPosition hn hP w)

theorem visit_between_same_edge (hn : 3 ≤ n) (hP : G1 P) {v w u : Visit P}
    (he : v.2.val = w.2.val)
    (hl : visitKey hn hP v < visitKey hn hP u)
    (hr : visitKey hn hP u < visitKey hn hP w) :
    u.2.val = v.2.val ∧ visitParameter v < visitParameter u ∧
      visitParameter u < visitParameter w := by
  have h₁ := (visitKey_lt_iff hn hP v u).mp hl
  have h₂ := (visitKey_lt_iff hn hP u w).mp hr
  rcases h₁ with h₁ | ⟨h₁, hp₁⟩
  · rcases h₂ with h₂ | ⟨h₂, _⟩
    · rw [← he] at h₂
      exact (lt_asymm h₁ h₂).elim
    · rw [h₂, ← he] at h₁
      exact (lt_irrefl _ h₁).elim
  · rcases h₂ with h₂ | ⟨_, hp₂⟩
    · rw [← h₁, ← he] at h₂
      exact (lt_irrefl _ h₂).elim
    · exact ⟨h₁.symm, hp₁, hp₂⟩

end SM
