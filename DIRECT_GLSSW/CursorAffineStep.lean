import ActiveArcCursorGeometry
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor

/-- Successive moves on the same actual physical edge have the original affine parameter. -/
theorem moveStart_moveStart {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (θ τ : ℝ) :
    moveStart (moveStart q θ) τ = moveStart q (θ+(1-θ)*τ) := by
  funext i
  by_cases hi : i=0
  · subst i
    have h10 : (1 : Fin (n+2)) ≠ 0 := Fin.ne_of_val_ne (by simp)
    simp only [moveStart_zero,moveStart_eq q θ 1 h10,affinePoint_suffix]
  · rw [moveStart_eq _ τ i hi,moveStart_eq q θ i hi,moveStart_eq q _ i hi]

/-- A genuine positive original-event gap produces a positive step radius in
local physical-edge coordinates. -/
theorem exists_original_event_radius (θ σ η : ℝ) (hθ : θ<1)
    (hgap : θ+(1-θ)*σ<η) :
    ∃ R : ℝ, 0<R ∧ ∀ ε : ℝ, 0<ε → ε<R →
      θ+(1-θ)*σ < θ+(1-θ)*(σ+ε) ∧ θ+(1-θ)*(σ+ε)<η := by
  have hd : 0<1-θ := sub_pos.mpr hθ
  refine ⟨(η-(θ+(1-θ)*σ))/(1-θ),div_pos (sub_pos.mpr hgap) hd,?_⟩
  intro ε hε hεR
  have hm : ε*(1-θ)<η-(θ+(1-θ)*σ) := (lt_div_iff₀ hd).mp hεR
  have hp : 0<(1-θ)*ε := mul_pos hd hε
  have he : θ+(1-θ)*(σ+ε)=(θ+(1-θ)*σ)+(1-θ)*ε := by ring
  rw [he]
  constructor
  · exact lt_add_of_pos_right _ hp
  · nlinarith only [hm]

/-- The same chosen local radius controls the actual composed word and both
sides of the original event interval. No matching equation is assumed. -/
theorem exists_moveStart_original_event_radius {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (θ σ η : ℝ) (hθ : θ<1)
    (hgap : θ+(1-θ)*σ<η) :
    ∃ R : ℝ, 0<R ∧ ∀ ε : ℝ, 0<ε → ε<R →
      moveStart (moveStart q θ) (σ+ε)=moveStart q (θ+(1-θ)*(σ+ε)) ∧
      θ+(1-θ)*σ < θ+(1-θ)*(σ+ε) ∧ θ+(1-θ)*(σ+ε)<η := by
  obtain ⟨R,hR,H⟩ := exists_original_event_radius θ σ η hθ hgap
  exact ⟨R,hR,fun ε hε hεR => ⟨moveStart_moveStart q θ (σ+ε),H ε hε hεR⟩⟩
end DirectGLSSW.ActiveArc.Cursor
