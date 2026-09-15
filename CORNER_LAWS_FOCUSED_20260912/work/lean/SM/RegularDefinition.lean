import SM.RegularLocus

/-! Full source def:regular. The local-angle clauses use only the source's
two-edge domain, not global genericity or regularity. The global locus is
equivalent both to the printed edge predicate and to actual unique existence.
The complete definition is invariant/equivariant under cyclic relabelling. -/

namespace SM

variable {n : ℕ}

theorem regular_definition (hn : 3 ≤ n) (P : LabelledTuple n) :
    (Regular P ↔ ∀ i, edge P i ≠ 0 ∧
      ¬ ∃ r : ℝ, r < 0 ∧ edge P i = r • edge P (i - 1)) ∧
    (Regular P ↔ ∀ i, ∃! θ, PrincipalAngleSpec (edge P (i - 1)) (edge P i) θ) ∧
    (Generic P → Regular P) ∧
    (∀ i, RegularPair (edge P (i - 1)) (edge P i) →
      PrincipalAngleSpec (edge P (i - 1)) (edge P i) (principalTurn P i) ∧
      (∀ θ, PrincipalAngleSpec (edge P (i - 1)) (edge P i) θ → θ = principalTurn P i) ∧
      (principalTurn P i = 0 ↔ ∃ r : ℝ, 0 < r ∧ edge P i = r • edge P (i - 1))) ∧
    (∀ a : ZMod n, Regular (shift a P) ↔ Regular P) ∧
    (∀ a i : ZMod n, principalTurn (shift a P) i = principalTurn P (i + a)) := by
  refine ⟨regular_iff_edges P, regular_iff_principalTurns_exist P,
    generic_regular hn, ?_, fun a => regular_shift a P, fun a i => principalTurn_shift a P i⟩
  intro i hi
  exact ⟨principalTurn_spec hi, fun _ hθ => principalTurn_unique hθ, principalTurn_eq_zero_iff hi⟩

end SM
