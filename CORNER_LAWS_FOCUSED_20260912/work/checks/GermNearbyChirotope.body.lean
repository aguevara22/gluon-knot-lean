namespace SM.WallGerm

noncomputable section
variable {n : ℕ}

/-- Every actual punctured parameter has a representative arbitrarily close
to the center on the same connected generic side, with the entire chirotope
unchanged. The representative is explicitly constructed at distance δ/2. -/
theorem nearby_same_chirotope (w : WallGerm n) (δ : ℝ) (hδ : 0 < δ) (hδr : δ ≤ w.radius)
    (s : w.Parameter) (hs : s.val ≠ 0) :
    ∃ u : w.Parameter, u.val ≠ 0 ∧ |u.val| < δ ∧
      ∀ i j k : ZMod n, chi (w.curve u) i j k = chi (w.curve s) i j k := by
  obtain ⟨b, r, hr⟩ := w.sideTime_surjective_punctured s hs
  let t0 : w.SideParameter := ⟨δ / 2, by constructor <;> linarith⟩
  refine ⟨w.sideTime b t0, w.sideTime_ne_zero b t0, ?_, ?_⟩
  · have hv : |(w.sideTime b t0).val| = δ / 2 := by
      cases b <;> simp [sideTime, t0, abs_of_pos (by linarith : 0 < δ / 2)]
    rw [hv]
    linarith
  · intro i j k
    have hc := generic_family_chi_constant (w.continuous_sideTuple b) t0 r i j k
    change chi (w.curve (w.sideTime b t0)) i j k = chi (w.curve (w.sideTime b r)) i j k at hc
    rw [hr] at hc
    exact hc

end
end SM.WallGerm
