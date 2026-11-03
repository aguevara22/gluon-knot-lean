import ActiveArcFirstCrossing
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor
open DirectGLSSW ActiveArc
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)

/-- The actual first-edge cursor is the positive endpoint perturbation used by
the finite current event calculation. -/
theorem moveStart_event_plus (c : Crossing q) (hc : c.val.1=0) (ε : ℝ) :
    moveStart q (leftParameter q c+ε) 0 =
      crossingPoint q c + ε • (q 1-q 0) := by
  rw [moveStart_zero,(leftParameter_spec q c).2.2,hc]
  change affinePoint (q 0) (q 1) (leftParameter q c+ε)=
    affinePoint (q 0) (q 1) (leftParameter q c)+ε • (q 1-q 0)
  apply Prod.ext <;> simp only [affinePoint,Prod.fst_add,Prod.snd_add,
    Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

/-- The same physical cursor gives the negative endpoint perturbation. -/
theorem moveStart_event_minus (c : Crossing q) (hc : c.val.1=0) (ε : ℝ) :
    moveStart q (leftParameter q c-ε) 0 =
      crossingPoint q c + (-ε) • (q 1-q 0) := by
  simpa only [sub_eq_add_neg] using moveStart_event_plus q c hc (-ε)

/-- A single positive radius supplies all actual physical before/after cursor
values and both regular arcs, not just one pair of sample points. -/
theorem exists_physical_event_window (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ ε : ℝ, 0<ε → ε<ρ →
      0≤leftParameter q c-ε ∧ leftParameter q c-ε<leftParameter q c ∧
      leftParameter q c<leftParameter q c+ε ∧ leftParameter q c+ε<afterBound q c ∧
      Regular (moveStart q (leftParameter q c-ε)) ∧
      Regular (moveStart q (leftParameter q c+ε)) := by
  let ρ := min (leftParameter q c) (afterBound q c-leftParameter q c)
  have hp := (leftParameter_spec q c).1
  have hb := parameter_lt_afterBound q c
  have hr : 0<ρ := lt_min hp (sub_pos.mpr hb)
  refine ⟨ρ,hr,?_⟩
  intro ε he her
  have hleft : ε<leftParameter q c := lt_of_lt_of_le her (min_le_left _ _)
  have hright : ε<afterBound q c-leftParameter q c :=
    lt_of_lt_of_le her (min_le_right _ _)
  have hm0 : 0≤leftParameter q c-ε := by linarith
  have hmc : leftParameter q c-ε<leftParameter q c := by linarith
  have hcp : leftParameter q c<leftParameter q c+ε := by linarith
  have hpb : leftParameter q c+ε<afterBound q c := by linarith
  refine ⟨hm0,hmc,hcp,hpb,?_,?_⟩
  · exact (regular_first_window_iff q hR c hc _ hm0 (lt_trans hmc hb)).mpr (ne_of_lt hmc)
  · exact (regular_first_window_iff q hR c hc _ (by linarith) hpb).mpr (ne_of_gt hcp)




end DirectGLSSW.ActiveArc.Cursor
