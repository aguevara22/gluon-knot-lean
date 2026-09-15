namespace SM.WallGerm

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Every permitted source size is covered: FlatAt proves n+1 >= 4,
so the child size is m+3 for a constructed natural m. No extra arity
restriction is imposed by the earlier normalized tuple calculation. -/
theorem flat_incident_signed_response_all_sizes (w : WallGerm (n + 1)) (j g : ZMod (n + 1))
    (hf : w.FlatAt j) (hg : incident j g) :
    ∃ d : ℤ, (d = -1 ∨ d = 1) ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ w.radius ∧
      ∀ sMinus sPlus : w.Parameter, ∀ hMinus : sMinus.val < 0, ∀ hPlus : 0 < sPlus.val,
        |sMinus.val| < δ → |sPlus.val| < δ →
        (-(turn (w.curve sPlus) j : ℤ) + (turn (w.curve sMinus) j : ℤ) = 2 * d) ∧
        (treeCoefficient (w.curve sPlus) (w.generic_punctured sPlus (ne_of_gt hPlus)).1 g
            (by have := hf.1; omega) -
          treeCoefficient (w.curve sMinus) (w.generic_punctured sMinus (ne_of_lt hMinus)).1 g
            (by have := hf.1; omega) =
          d * treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1)
            (fusionIndex j g) (by have := hf.1; omega)) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by have := hf.1; omega⟩
  exact w.flat_incident_signed_response j g hf hg

end
end SM.WallGerm
