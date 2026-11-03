import PhysicalParentG1
import PhysicalTraversalSelection
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.TraversalClosure
open DirectGLSSW ActiveArc Cursor Split Primitive OpenCarrier

/-- There is a legal actual post-event state carrying all four geometry/domain
invariants. Its G1 is derived by parameter selection, not presumed at the cut. -/
theorem exists_after_first_full_state {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (hG : cyclicNoncollinear q) (hAux : ClosedAuxiliary q hR)
    (hleft : RemainingLeft q) (c : Crossing q) (hc : FirstCrossing q c) :
    ∃ t : ℝ, leftParameter q c<t ∧ t<afterBound q c ∧
      ∃ hM : Regular (moveStart q t), cyclicNoncollinear (moveStart q t) ∧
        ClosedAuxiliary (moveStart q t) hM ∧ RemainingLeft (moveStart q t) := by
  obtain ⟨ρ,hρ,H⟩ := after_first_state_closure q hR hG hAux c hc
  let δ := min ρ (afterBound q c-leftParameter q c)/2
  have hδ : 0<δ := half_pos (lt_min hρ (sub_pos.mpr (parameter_lt_afterBound q c)))
  have hδρ : δ<ρ := by
    have hmin := min_le_left ρ (afterBound q c-leftParameter q c)
    dsimp [δ]
    linarith
  have hδb : δ<afterBound q c-leftParameter q c := by
    have hmin := min_le_right ρ (afterBound q c-leftParameter q c)
    have hb := parameter_lt_afterBound q c
    dsimp [δ]
    linarith
  let t := leftParameter q c+δ
  have hct : leftParameter q c<t := by dsimp [t]; linarith
  have htb : t<afterBound q c := by dsimp [t]; linarith
  have hnear : |t-leftParameter q c|<ρ := by
    rw [show t-leftParameter q c=δ by dsimp [t];ring,abs_of_pos hδ]
    exact hδρ
  obtain ⟨hM,hGm,hAuxm⟩ := H t hct htb hnear
  exact ⟨t,hct,htb,hM,hGm,hAuxm,
    remainingLeft_moveStart q hleft t (lt_of_lt_of_le htb (afterBound_le_one q c))⟩

/-- Parent closure requires only canonical parent far nonvanishing beyond the
original working invariants; no target G1/AUX/turn hypothesis is supplied. -/
theorem parent_full_state_of_parentFar {a b : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (hG : cyclicNoncollinear q) (hAux : ClosedAuxiliary q hR)
    (hleft : RemainingLeft q) (c : Crossing q) (hc : FirstCrossing q c)
    (hcut : c.val.2.val=a) (hL : parentFarLocus q hR c hcut (parentChartLines q)) :
    cyclicNoncollinear (parent q c hcut) ∧
      ClosedAuxiliary (parent q c hcut) (regular_parent q hR c hcut) ∧
      RemainingLeft (parent q c hcut) := by
  obtain ⟨hA,hT⟩ := parent_basic_state_closure q hR hAux hleft c hc hcut
  exact ⟨parent_G1_of_parentFar q hR hG c hcut hL,hA,hT⟩
end DirectGLSSW.ActiveArc.TraversalClosure
