import ActiveArcSuffix

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor
open Split
attribute [local instance] Classical.propDecidable

/-- A crossing-free first edge has no singular cursor time. -/
theorem firstEdgeFree_not_critical {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hfree : ∀ c : Crossing q, c.val.1≠0) (t : ℝ) : t∉criticalParameters q := by
  intro ht
  obtain ⟨c,hc,_⟩ := (mem_criticalParameters q t).mp ht
  exact hfree c hc

/-- Shrinking a physical crossing-free first edge preserves actual Regularity. -/
theorem firstEdgeFree_regular_moveStart {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hR : Regular q) (hfree : ∀ c : Crossing q, c.val.1≠0)
    (t : ℝ) (ht0 : 0≤t) (ht1 : t<1) : Regular (moveStart q t) :=
  regular_moveStart q hR t ht0 ht1 (firstEdgeFree_not_critical q hfree t)

/-- No first-edge crossing can be created by shrinking that edge. -/
theorem firstEdgeFree_moveStart {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hfree : ∀ c : Crossing q, c.val.1≠0)
    (t : ℝ) (ht0 : 0≤t) (ht1 : t<1) :
    ∀ c : Crossing (moveStart q t), c.val.1≠0 := by
  intro c
  exact hfree (crossingToOriginal q t ht0 ht1 c)

/-- The literal corner suffix is unchanged by moving only the first mark. -/
theorem corner_suffix_moveStart {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ)
    (t : ℝ) : suffix (moveStart q t)=suffix q := by
  funext i
  change moveStart q t (vertex i)=q (vertex i)
  apply moveStart_eq
  intro hi
  have hv := congrArg Fin.val hi
  simp only [vertex,Fin.val_zero] at hv
  omega

/-- The shrinking corner head uses the same affine coordinate as approach. -/
theorem corner_moveStart_approach_endpoint {b : ℕ}
    (q : Fin (1+b+2) → PlanarPoint ℝ) (η : ℝ) :
    moveStart q (1-η) 0=affinePoint (q 1) (q 0) η := by
  rw [moveStart_zero]
  ext <;> simp [affinePoint] <;> ring






end DirectGLSSW.ActiveArc.Cursor
