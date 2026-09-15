namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Equality of every actual triple inside J is equality of the complete
restricted arrays; no condition is imposed on entries outside J. -/
theorem restrictTripleArray_eq_of_local (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ t : IncreasingBoundaryTriple n, J.left ≤ t.lower → t.upper ≤ J.right → H₁ t = H₂ t) :
    restrictTripleArray J H₁ = restrictTripleArray J H₂ := by
  funext t
  exact h (J.liftTriple t) (J.globalPosition_bounds t.lower).1 (J.globalPosition_bounds t.upper).2

/-- Inverse coordinates depend only on actual triples inside their own
interval. The one-leaf convention is proved separately before using a closed
full local interval at larger arity. -/
theorem farOnlyCoordinates_local (J : BoundaryInterval n) (H₁ H₂ : TripleArray n R)
    (h : ∀ t : IncreasingBoundaryTriple n, J.left ≤ t.lower → t.upper ≤ J.right → H₁ t = H₂ t) :
    farOnlyCoordinates H₁ J = farOnlyCoordinates H₂ J := by
  by_cases hj : J.leaves = 1
  · rw [farOnlyCoordinates_leaf H₁ J hj, farOnlyCoordinates_leaf H₂ J hj]
  · have hJ : 2 ≤ J.leaves := by have := J.leaves_pos; omega
    let K := fullBoundaryInterval (by omega : 3 ≤ J.leaves + 1)
    have he := congrArg (fun H : TripleArray (J.leaves + 1) R => farOnlyCoordinates H)
      (restrictTripleArray_eq_of_local J H₁ H₂ h)
    have h₁ := congrFun (farOnlyCoordinates_restrict J H₁) K
    have h₂ := congrFun (farOnlyCoordinates_restrict J H₂) K
    change farOnlyCoordinates H₁ (J.liftInterval K) = farOnlyCoordinates (restrictTripleArray J H₁) K at h₁
    change farOnlyCoordinates H₂ (J.liftInterval K) = farOnlyCoordinates (restrictTripleArray J H₂) K at h₂
    rw [J.lift_fullInterval hJ] at h₁ h₂
    exact h₁.trans ((congrFun he K).trans h₂.symm)

/-- If one critical triple is the only array entry that can differ, every
interval not containing its full span has unchanged inverse coordinate. This
is the locality step in the single-triple wall response, before wall geometry. -/
theorem farOnlyCoordinates_unchanged_off_critical (H₁ H₂ : TripleArray n R)
    (critical : IncreasingBoundaryTriple n)
    (h : ∀ t : IncreasingBoundaryTriple n, t ≠ critical → H₁ t = H₂ t)
    (J : BoundaryInterval n) (hJ : ¬ (J.left ≤ critical.lower ∧ critical.upper ≤ J.right)) :
    farOnlyCoordinates H₁ J = farOnlyCoordinates H₂ J := by
  apply farOnlyCoordinates_local J H₁ H₂
  intro t hl hr
  apply h t
  intro ht
  subst t
  exact hJ ⟨hl, hr⟩

end
end SM
