namespace SM.IncreasingBoundaryTriple

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] contractedSize_neZero

/-- Expand both retained endpoints of an arbitrary contracted interval. -/
def expandInterval (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) : BoundaryInterval n where
  left := t.expandPosition J.left
  right := t.expandPosition J.right
  increasing := t.expandPosition_strict J.increasing

def expandTriple (t : IncreasingBoundaryTriple n)
    (u : IncreasingBoundaryTriple t.contractedSize) : IncreasingBoundaryTriple n where
  lower := t.expandPosition u.lower
  middle := t.expandPosition u.middle
  upper := t.expandPosition u.upper
  lower_middle := t.expandPosition_strict u.lower_middle
  middle_upper := t.expandPosition_strict u.middle_upper

/-- The distinguished formal leaf retains exactly the two critical endpoints. -/
def contractedLeaf (t : IncreasingBoundaryTriple n) : BoundaryInterval t.contractedSize where
  left := ⟨t.lower.val, by have := t.contractedSize_bounds; omega⟩
  right := ⟨t.lower.val + 1, by have := t.contractedSize_bounds; omega⟩
  increasing := by change t.lower.val < t.lower.val + 1; omega

theorem contractedLeaf_leaves (t : IncreasingBoundaryTriple n) : t.contractedLeaf.leaves = 1 := by
  simp [contractedLeaf, BoundaryInterval.leaves]

theorem expandInterval_contractedLeaf (t : IncreasingBoundaryTriple n) :
    t.expandInterval t.contractedLeaf = t.spanInterval := by
  apply BoundaryInterval.eq_of_endpoints
  · exact t.expandPosition_lower
  · exact t.expandPosition_upper

/-- Containment of the complete old arc is exactly containment of the
distinguished new leaf; no extra cut or marked-composition assumption is used. -/
theorem expandInterval_contains (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) :
    ((t.expandInterval J).left ≤ t.lower ∧ t.upper ≤ (t.expandInterval J).right) ↔
      (J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right) := by
  change (t.expandPosition J.left ≤ t.lower ∧ t.upper ≤ t.expandPosition J.right) ↔ _
  rw [← t.expandPosition_lower, ← t.expandPosition_upper]
  exact and_congr t.expandPosition_strict.le_iff_le t.expandPosition_strict.le_iff_le

theorem expandInterval_injective (t : IncreasingBoundaryTriple n) :
    Function.Injective t.expandInterval := by
  intro I J he
  apply BoundaryInterval.eq_of_endpoints
  · exact t.expandPosition_strict.injective (congrArg BoundaryInterval.left he)
  · exact t.expandPosition_strict.injective (congrArg BoundaryInterval.right he)

/-- Contract any interval whose two endpoints survive. In particular this
includes every interval containing the entire critical arc. -/
def contractInterval (t : IncreasingBoundaryTriple n) (I : BoundaryInterval n)
    (hl : I.left ≤ t.lower ∨ t.upper ≤ I.left)
    (hr : I.right ≤ t.lower ∨ t.upper ≤ I.right) : BoundaryInterval t.contractedSize where
  left := t.contractPosition I.left hl
  right := t.contractPosition I.right hr
  increasing := by
    apply t.expandPosition_strict.lt_iff_lt.mp
    rw [t.expand_contractPosition, t.expand_contractPosition]
    exact I.increasing

theorem expand_contractInterval (t : IncreasingBoundaryTriple n) (I : BoundaryInterval n)
    (hl : I.left ≤ t.lower ∨ t.upper ≤ I.left)
    (hr : I.right ≤ t.lower ∨ t.upper ≤ I.right) :
    t.expandInterval (t.contractInterval I hl hr) = I := by
  apply BoundaryInterval.eq_of_endpoints
  · exact t.expand_contractPosition I.left hl
  · exact t.expand_contractPosition I.right hr

theorem contract_expandInterval (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize) :
    t.contractInterval (t.expandInterval J) (t.expandPosition_survives J.left)
      (t.expandPosition_survives J.right) = J := by
  apply t.expandInterval_injective
  exact t.expand_contractInterval _ _ _

/-- Every containing source interval is represented, including the critical
interval and the complete boundary interval. -/
theorem containing_interval_is_expanded (t : IncreasingBoundaryTriple n)
    (I : BoundaryInterval n) (hI : I.left ≤ t.lower ∧ t.upper ≤ I.right) :
    ∃ J : BoundaryInterval t.contractedSize,
      t.expandInterval J = I ∧ J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right := by
  let J := t.contractInterval I (Or.inl hI.1) (Or.inr hI.2)
  have he : t.expandInterval J = I := t.expand_contractInterval I _ _
  refine ⟨J, he, (t.expandInterval_contains J).mp ?_⟩
  simpa only [he] using hI

theorem expandInterval_full (t : IncreasingBoundaryTriple n) (hn : 3 ≤ n)
    (hproper : t.spanInterval ≠ fullBoundaryInterval hn) :
    t.expandInterval (fullBoundaryInterval (t.contractedSize_of_proper hn hproper)) =
      fullBoundaryInterval hn := by
  apply BoundaryInterval.eq_of_endpoints
  · apply Fin.ext
    exact t.expandPosition_initial
  · apply Fin.ext
    exact t.expandPosition_final

/-- A contracted interval properly containing the formal leaf has at least
two leaves, so its unit-array equation has the required zero right side. -/
theorem containing_contracted_nonleaf (t : IncreasingBoundaryTriple n)
    (J : BoundaryInterval t.contractedSize)
    (hJ : J.left ≤ t.contractedLeaf.left ∧ t.contractedLeaf.right ≤ J.right)
    (hne : J ≠ t.contractedLeaf) : 2 ≤ J.leaves := by
  have hl : J.left.val ≤ t.lower.val := hJ.1
  have hr : t.lower.val + 1 ≤ J.right.val := hJ.2
  by_contra h
  have hv : J.right.val - J.left.val < 2 := Nat.lt_of_not_ge h
  have he : J = t.contractedLeaf := by
    apply BoundaryInterval.eq_of_endpoints
    · apply Fin.ext
      change J.left.val = t.lower.val
      omega
    · apply Fin.ext
      change J.right.val = t.lower.val + 1
      omega
  exact hne he

end
end SM.IncreasingBoundaryTriple
