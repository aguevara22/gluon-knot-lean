import ActiveArcCornerMovingGammaM

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CornerProjector
open Cursor Split Primitive RetainedWords CompatibleWords OpenFirstEdgeGeometry
attribute [local instance] Classical.propDecidable

/-- The actual left-corner current tends to minus the current of the literal
suffix, with original closed auxiliary data transported internally. -/
theorem exists_actual_left_corner_GammaM_limit
    {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (hfree : ∀ c : Crossing q, c.val.1≠0) (hAux : ClosedAuxiliary q hR)
    (hRI : GLSSWRootIndependence) (hleft : 0<planarDet (q 1-q 0) (q 2-q 1))
    (hfar : ∀ T : Primitive.Support (suffix q) (regular_suffix q hR),
      ∀ k j, 1<k → k<j → j≤openCount (suffix q) (regular_suffix q hR) T.val →
        polygonHDet (fun k => if k=0 then q 0 else
          rootedPolygonWord (OpenVertex (suffix q) (regular_suffix q hR) T)
            (openLast (suffix q) (regular_suffix q hR) T.val) (k-1)) 1 k j≠0) :
    ∃ (ρ : ℝ) (_hρ : 0<ρ) (hρ1 : ρ≤1), ∀ (η : ℝ) (hη : 0<η) (hηρ : η<ρ),
    let ht0 : 0≤1-η := le_of_lt (sub_pos.mpr (lt_of_lt_of_le hηρ hρ1))
    let ht1 : 1-η<1 := sub_lt_self 1 hη
    GammaM (moveStart q (1-η))
      (firstEdgeFree_regular_moveStart q hR hfree (1-η) ht0 ht1)
      (firstEdgeFree_closedAuxiliary_moveStart q hR hfree hAux (1-η) ht0 ht1) =
    -GammaM (suffix q) (regular_suffix q hR) (corner_closedAuxiliary_suffix q hR hfree hAux) := by
  obtain ⟨ρ,hρ,hρ1,hgood⟩ := exists_weighted_left_corner_projector q hR
    (corner_closedAuxiliary_suffix q hR hfree hAux) hleft hfar
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro η hη hηρ
  dsimp only
  rw [firstEdgeFree_moving_GammaM_eq_weighted_approach q hR hfree hAux hRI η hη
    (lt_of_lt_of_le hηρ hρ1)]
  exact hgood η hη hηρ

/-- Endpoint-inclusive vertex parity cancels the minus sign at an ordinary
original left corner; the physical normalized current is unchanged. -/
theorem exists_normalized_left_corner_transport
    {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (hfree : ∀ c : Crossing q, c.val.1≠0) (hAux : ClosedAuxiliary q hR)
    (hRI : GLSSWRootIndependence) (hleft : 0<planarDet (q 1-q 0) (q 2-q 1))
    (hfar : ∀ T : Primitive.Support (suffix q) (regular_suffix q hR),
      ∀ k j, 1<k → k<j → j≤openCount (suffix q) (regular_suffix q hR) T.val →
        polygonHDet (fun k => if k=0 then q 0 else
          rootedPolygonWord (OpenVertex (suffix q) (regular_suffix q hR) T)
            (openLast (suffix q) (regular_suffix q hR) T.val) (k-1)) 1 k j≠0) :
    ∃ (ρ : ℝ) (_hρ : 0<ρ) (hρ1 : ρ≤1), ∀ (η : ℝ) (hη : 0<η) (hηρ : η<ρ),
    let ht0 : 0≤1-η := le_of_lt (sub_pos.mpr (lt_of_lt_of_le hηρ hρ1))
    let ht1 : 1-η<1 := sub_lt_self 1 hη
    (-1:ℚ)^(List.ofFn (moveStart q (1-η))).length *
      GammaM (moveStart q (1-η))
        (firstEdgeFree_regular_moveStart q hR hfree (1-η) ht0 ht1)
        (firstEdgeFree_closedAuxiliary_moveStart q hR hfree hAux (1-η) ht0 ht1) =
    (-1:ℚ)^(List.ofFn (suffix q)).length *
      GammaM (suffix q) (regular_suffix q hR) (corner_closedAuxiliary_suffix q hR hfree hAux) := by
  obtain ⟨ρ,hρ,hρ1,hgood⟩ := exists_actual_left_corner_GammaM_limit q hR hfree hAux hRI hleft hfar
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro η hη hηρ
  have hj := hgood η hη hηρ
  dsimp only at hj ⊢
  rw [hj]
  simp only [List.length_ofFn]
  rw [show 1+b+2=(b+2)+1 by omega,pow_succ]
  ring



end DirectGLSSW.ActiveArc.CornerProjector
