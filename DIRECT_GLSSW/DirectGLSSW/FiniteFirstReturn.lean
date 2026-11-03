import DirectGLSSW.OrderedEventSuccessor

namespace DirectGLSSW.FiniteFirstReturn

/-- Forward cyclic distance between two labels, taking the positive full turn when equal. -/
def forwardGap {N : ℕ} (i j : Fin N) : ℕ :=
  if i.val < j.val then j.val - i.val else N - i.val + j.val

/-- The forward cyclic distance is positive, including equal endpoints. -/
theorem forwardGap_pos {N : ℕ} (i j : Fin N) :
    0 < forwardGap i j := by
  unfold forwardGap
  split_ifs <;> have hi := i.isLt <;> have hj := j.isLt <;> omega

/-- A forward cyclic distance fits in one full traversal. -/
theorem forwardGap_le {N : ℕ} (i j : Fin N) :
    forwardGap i j ≤ N := by
  unfold forwardGap
  split_ifs <;> have hi := i.isLt <;> have hj := j.isLt <;> omega

/-- The value after fewer than `N` cyclic-successor steps is the corresponding
modular label, written with one explicit wrap. -/
theorem cyclicSuccessorPerm_pow_val_of_lt {N : ℕ} (i : Fin N) {k : ℕ}
    (hk : k < N) :
    ((cyclicSuccessorPerm N ^ k) i).val =
      if i.val + k < N then i.val + k else i.val + k - N := by
  cases k with
  | zero =>
      simp only [pow_zero, Equiv.Perm.one_apply]
      simp [Nat.mod_eq_of_lt i.isLt]
  | succ k =>
      have hk' : k < N := by omega
      rw [cyclicSuccessorPerm_pow_succ]
      rw [cyclicVertexIndex_val i hk']
      split_ifs <;> have hi := i.isLt <;> omega

/-- Advancing by the forward gap reaches the target label. -/
theorem cyclicSuccessor_pow_forwardGap {N : ℕ} (i j : Fin N) :
    (cyclicSuccessorPerm N ^ forwardGap i j) i = j := by
  by_cases hij : i.val < j.val
  · have hd : forwardGap i j < N := by
      unfold forwardGap
      simp only [if_pos hij]
      have hi := i.isLt
      have hj := j.isLt
      omega
    apply Fin.ext
    rw [cyclicSuccessorPerm_pow_val_of_lt i hd]
    unfold forwardGap
    split_ifs <;> have hi := i.isLt <;> have hj := j.isLt <;> omega
  · by_cases heq : i.val = j.val
    · have hd : forwardGap i j = N := by
        unfold forwardGap
        simp [heq, hij]
      rw [hd, cyclicSuccessorPerm_pow_card]
      exact Fin.ext heq
    · have hji : j.val < i.val := by omega
      have hd : forwardGap i j < N := by
        unfold forwardGap
        simp only [if_neg hij]
        have hi := i.isLt
        have hj := j.isLt
        omega
      apply Fin.ext
      rw [cyclicSuccessorPerm_pow_val_of_lt i hd]
      unfold forwardGap
      split_ifs <;> have hi := i.isLt <;> have hj := j.isLt <;> omega

/-- The first element of a finite ordered subtype after `c` is reached at its
positive forward gap, with no earlier return to the predicate. -/
theorem orderedSubtype_firstReturn {N : ℕ}
    (P : Fin N → Prop) [DecidablePred P] (c : {i : Fin N // P i}) :
  let next := orderedCyclicSuccessor {i : Fin N // P i} c
  let d := forwardGap c.val next.val
  0 < d ∧ d ≤ N ∧
    (cyclicSuccessorPerm N ^ d) c.val = next.val ∧
    ∀ k : ℕ, 0 < k → k < d →
      ¬ P ((cyclicSuccessorPerm N ^ k) c.val) := by
  classical
  let next := orderedCyclicSuccessor {i : Fin N // P i} c
  let d := forwardGap c.val next.val
  have hdpos : 0 < d := forwardGap_pos c.val next.val
  have hdle : d ≤ N := forwardGap_le c.val next.val
  have hreach : (cyclicSuccessorPerm N ^ d) c.val = next.val :=
    cyclicSuccessor_pow_forwardGap c.val next.val
  refine ⟨hdpos, hdle, hreach, ?_⟩
  intro k hkpos hkd hPk
  let y : Fin N := (cyclicSuccessorPerm N ^ k) c.val
  have hkN : k < N := lt_of_lt_of_le hkd hdle
  have hyval := cyclicSuccessorPerm_pow_val_of_lt c.val hkN
  have hspec := orderedCyclicSuccessor_order_spec {i : Fin N // P i} c
  by_cases hcn : c.val.val < next.val.val
  · have hgap : d = next.val.val - c.val.val := by
      change forwardGap c.val next.val = _
      unfold forwardGap
      rw [if_pos hcn]
    have hkbelow : k < next.val.val - c.val.val := by
      rw [← hgap]
      exact hkd
    rcases hspec with ⟨hinc, hmin⟩ | ⟨hmax, hmin⟩
    · have hcy : c.val.val < y.val := by
        have hlinear : c.val.val + k < next.val.val := by omega
        have hsum : c.val.val + k < N := lt_trans hlinear next.val.isLt
        have hy : y.val = c.val.val + k := by simpa [y, hsum] using hyval
        rw [hy]
        omega
      have hyn : y.val < next.val.val := by
        have hlinear : c.val.val + k < next.val.val := by omega
        have hsum : c.val.val + k < N := lt_trans hlinear next.val.isLt
        have hy : y.val = c.val.val + k := by simpa [y, hsum] using hyval
        rw [hy]
        omega
      have hz : P y := hPk
      let z : {i : Fin N // P i} := ⟨y, hz⟩
      have hcz : c < z := by
        change c.val < z.val
        change c.val.val < y.val
        exact hcy
      have hzn : z < next := by
        change z.val < next.val
        change y.val < next.val.val
        exact hyn
      have hnextz := hmin z hcz
      exact (not_lt_of_ge hnextz) hzn
    · have hnextc : next ≤ c := hmax next
      change next.val.val ≤ c.val.val at hnextc
      omega
  · have hji : next.val.val ≤ c.val.val := by omega
    have hgap : d = N - c.val.val + next.val.val := by
      change forwardGap c.val next.val = _
      unfold forwardGap
      rw [if_neg hcn]
    have hkbelow : k < N - c.val.val + next.val.val := by
      rw [← hgap]
      exact hkd
    rcases hspec with ⟨hinc, hmin⟩ | ⟨hmax, hmin⟩
    · have : c.val.val < next.val.val := by
        change c < next at hinc
        exact hinc
      omega
    · by_cases hbefore : k < N - c.val.val
      · have hcy : c.val.val < y.val := by
          have hsum : c.val.val + k < N := by omega
          have hy : y.val = c.val.val + k := by simpa [y, hsum] using hyval
          rw [hy]
          omega
        have hz : P y := hPk
        let z : {i : Fin N // P i} := ⟨y, hz⟩
        have hzc : z ≤ c := by
          have := hmax z
          change z.val ≤ c.val at this
          exact this
        change y ≤ c.val at hzc
        change y.val ≤ c.val.val at hzc
        omega
      · have hyn : y.val < next.val.val := by
          have hsum : ¬ c.val.val + k < N := by omega
          have hy : y.val = c.val.val + k - N := by simpa [y, hsum] using hyval
          have hafter : N - c.val.val ≤ k := by omega
          have hrest : k - (N - c.val.val) < next.val.val := by omega
          have heq : c.val.val + k - N = k - (N - c.val.val) := by omega
          rw [hy]
          rw [heq]
          exact hrest
        have hz : P y := hPk
        let z : {i : Fin N // P i} := ⟨y, hz⟩
        have hnextz := hmin z
        change next.val ≤ z.val at hnextz
        change next.val.val ≤ y.val at hnextz
        omega

end DirectGLSSW.FiniteFirstReturn
