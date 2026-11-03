import ActiveArcAfterFirstAuxiliary
import ActiveArcParentClosedAuxiliary
import ActiveArcCornerClosedAuxiliary
import ActiveArcOpenRegularNeighborhood

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.TraversalClosure
open DirectGLSSW ActiveArc Cursor Split Primitive Filter Topology
attribute [local instance] Classical.propDecidable

/-- Every actual vertex-triple determinant is affine in the first cursor. -/
lemma moveStart_det_affine {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (i j k : Fin (n+2)) (t : ℝ) :
    planarDet (moveStart q t j-moveStart q t k) (moveStart q t i-moveStart q t k) =
      planarDet (q j-q k) (q i-q k) + t *
       (planarDet (moveStart q 1 j-moveStart q 1 k) (moveStart q 1 i-moveStart q 1 k)-
        planarDet (q j-q k) (q i-q k)) := by
  have hm (s : ℝ) (v : Fin (n+2)) :
      moveStart q s v = if v=0 then affinePoint (q 0) (q 1) s else q v := by
    by_cases hv : v=0
    · subst v; simp [moveStart_zero]
    · rw [if_neg hv]; exact moveStart_eq q s v hv
  simp only [hm]
  rcases eq_or_ne i 0 with rfl|hi <;> rcases eq_or_ne j 0 with rfl|hj <;>
    rcases eq_or_ne k 0 with rfl|hk <;> simp [*,affinePoint,planarDet] <;> ring

private lemma affine_nonzero_punctured (A B t₀ : ℝ) (hA : A≠0) :
    ∀ᶠ t in 𝓝 t₀, t≠t₀ → A+t*B≠0 := by
  by_cases h₀ : A+t₀*B=0
  · have hB : B≠0 := by intro h; simp only [h,mul_zero,add_zero] at h₀; exact hA h₀
    exact Eventually.of_forall (by
      intro t ht hz
      have hh : (t-t₀)*B=0 := by nlinarith [hz,h₀]
      exact ht (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hB)))
  · have hc : Continuous (fun t : ℝ => A+t*B) := by fun_prop
    exact (hc.continuousAt.eventually_ne h₀).mono (fun _ h _ => h)

/-- The whole all-distinct-triples G1 condition holds in a punctured cursor
neighborhood of ANY parameter. No genericity at the event parameter is assumed. -/
theorem eventually_moveStart_G1_punctured {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hG : cyclicNoncollinear q) (t₀ : ℝ) :
    ∀ᶠ t in 𝓝 t₀, t≠t₀ → cyclicNoncollinear (moveStart q t) := by
  have H : ∀ᶠ t in 𝓝 t₀, ∀ i j k : Fin (n+2), i≠j → j≠k → i≠k →
      t≠t₀ → planarDet (moveStart q t j-moveStart q t k)
        (moveStart q t i-moveStart q t k)≠0 := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    apply eventually_all.mpr
    intro k
    by_cases hij : i=j
    · exact Eventually.of_forall (fun _ h => False.elim (h hij))
    by_cases hjk : j=k
    · exact Eventually.of_forall (fun _ _ h => False.elim (h hjk))
    by_cases hik : i=k
    · exact Eventually.of_forall (fun _ _ _ h => False.elim (h hik))
    have hh := affine_nonzero_punctured (planarDet (q j-q k) (q i-q k))
      (planarDet (moveStart q 1 j-moveStart q 1 k) (moveStart q 1 i-moveStart q 1 k)-
        planarDet (q j-q k) (q i-q k)) t₀ (hG i j k hij hjk hik)
    filter_upwards [hh] with t ht
    intro _ _ _ hne
    rw [moveStart_det_affine]
    exact ht hne
  exact H.mono (fun _ h ht i j k hij hjk hik => h i j k hij hjk hik ht)

/-- Actual cursor closure after a first event. The parameter is chosen away
from the finitely many vertex-triple incidences, rather than assuming G1. -/
theorem after_first_state_closure {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (hG : cyclicNoncollinear q) (hAux : ClosedAuxiliary q hR)
    (c : Crossing q) (hc : FirstCrossing q c) :
    ∃ ρ : ℝ, 0<ρ ∧ ∀ t : ℝ, leftParameter q c<t → t<afterBound q c →
      |t-leftParameter q c|<ρ →
      ∃ hM : Regular (moveStart q t), cyclicNoncollinear (moveStart q t) ∧
        ClosedAuxiliary (moveStart q t) hM := by
  obtain ⟨ρ,hρ,hnear⟩ := Metric.eventually_nhds_iff.mp
    (eventually_moveStart_G1_punctured q hG (leftParameter q c))
  refine ⟨ρ,hρ,?_⟩
  intro t hct htb ht
  let ht0 : 0≤t := (lt_trans (leftParameter_spec q c).1 hct).le
  let hM := (regular_first_window_iff q hR c hc t ht0 htb).mpr (ne_of_gt hct)
  refine ⟨hM,?_,Surviving.after_first_closedAuxiliary q hR c hc t hct htb hAux⟩
  exact hnear (by simpa only [Real.dist_eq] using ht) (ne_of_gt hct)

/-- Positive physical turns are preserved by a forward cursor before edge end. -/
theorem cursor_turn_pos {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (t : ℝ) (ht : t<1) (e f : Fin (n+1))
    (hpos : 0<planarDet (q e.succ-q e.castSucc) (q f.succ-q f.castSucc)) :
    0<planarDet (moveStart q t e.succ-moveStart q t e.castSucc)
      (moveStart q t f.succ-moveStart q t f.castSucc) := by
  rw [det_tangent_moveStart]
  exact mul_pos (mul_pos (tangentScale_pos t ht e) (tangentScale_pos t ht f)) hpos
end DirectGLSSW.ActiveArc.TraversalClosure
