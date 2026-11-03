import DiagonalCornerSides

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Actual cut neighbours on both sides of every original vertex, including
the extra cells needed to form the two retained staircase rectangles. -/
theorem diagonalCorner_neighbours_exist {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (k : Fin (componentArcLength D (T.baseArc C).val)) :
    ∃ a0 a b b1 : ℝ,
      secantAxisAdjacent T C a0 a ∧
      secantAxisAdjacent T C a ((k.val : ℝ)+1/2) ∧
      secantAxisAdjacent T C ((k.val : ℝ)+1/2) b ∧
      secantAxisAdjacent T C b b1 := by
  have hk : (k.val : ℝ)+1 ≤ (componentArcLength D (T.baseArc C).val : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt k.isLt
  have hk0 : (0 : ℝ)≤k.val := Nat.cast_nonneg _
  have hp := secantAxisCuts_original_knot T C k.val k.isLt
  obtain ⟨a,ha⟩ := secantAxis_predecessor_exists T C _ hp (by linarith)
  obtain ⟨b,hb⟩ := secantAxis_successor_exists T C _ hp (by linarith)
  have hwa := secantAxisAdjacent_width T C _ _ ha
  have hwb := secantAxisAdjacent_width T C _ _ hb
  obtain ⟨a0,h0⟩ := secantAxis_predecessor_exists T C a ha.1 (by linarith)
  obtain ⟨b1,h1⟩ := secantAxis_successor_exists T C b hb.2.1 (by linarith)
  exact ⟨a0,a,b,b1,h0,ha,hb,h1⟩

end
end DirectGLSSW.HOMFLY.PrincipalTurning

