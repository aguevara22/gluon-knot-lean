namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {k : ℕ}

/-- The actual dot-product coordinate on the line from the first selected
point to the last. Its endpoints will be proved to have coordinates0 and1. -/
def selectedLineCoordinate (P : LabelledTuple n) (g : ZMod n)
    (r : Fin (k + 1) → Fin n) (l : Fin (k + 1)) : ℝ :=
  let ω := boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0)
  planeDot ω (boundaryWord P g (r l) - boundaryWord P g (r 0)) / planeDot ω ω

/-- Zero actual determinants on the selected line supply all affine data
and distinct coordinates; no separate collinearity or injectivity oracle is
assumed. This uses only WeakGeneric, even with arbitrarily many silent zeros. -/
theorem weak_selected_line_coordinates {P : LabelledTuple n} (hP : WeakGeneric P)
    (g : ZMod n) (hk : 0 < k) (r : Fin (k + 1) → Fin n) (hr : StrictMono r)
    (hcol : ∀ l, det (boundaryWord P g (r l) - boundaryWord P g (r 0))
      (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0)) = 0) :
    (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0) ≠ 0) ∧
    (∀ l, boundaryWord P g (r l) = boundaryWord P g (r 0) +
      selectedLineCoordinate P g r l •
        (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0))) ∧
    Function.Injective (selectedLineCoordinate P g r) ∧
    selectedLineCoordinate P g r 0 = 0 ∧
    selectedLineCoordinate P g r (Fin.last k) = 1 := by
  let p := boundaryWord P g (r 0)
  let ω := boundaryWord P g (r (Fin.last k)) - p
  have hω : ω ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hi := hr.injective (weak_boundaryWord_injective hP g he)
    have hv := congrArg Fin.val hi
    change k = 0 at hv
    omega
  have hline : ∀ l, boundaryWord P g (r l) = p + selectedLineCoordinate P g r l • ω := by
    intro l
    have hd : det ω (boundaryWord P g (r l) - p) = 0 := by
      rw [det_swap]
      change -det (boundaryWord P g (r l) - boundaryWord P g (r 0))
        (boundaryWord P g (r (Fin.last k)) - boundaryWord P g (r 0)) = 0
      rw [hcol l, neg_zero]
    have hs := scalar_of_det_zero hω hd
    change boundaryWord P g (r l) - p = selectedLineCoordinate P g r l • ω at hs
    calc
      _ = p + (boundaryWord P g (r l) - p) := by abel
      _ = _ := by rw [hs]
  refine ⟨hω, hline, weak_line_coordinate_injective hP g r hr p ω _ hline, ?_, ?_⟩
  · simp [selectedLineCoordinate, planeDot]
  · exact div_self (ne_of_gt (planeDot_self_pos hω))

end
end SM
