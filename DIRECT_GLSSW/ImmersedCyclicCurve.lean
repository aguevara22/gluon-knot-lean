import ImmersedRoundingCells
import ImmersedPolygonTurnInteger

set_option autoImplicit false
open scoped Topology
namespace DirectGLSSW.ImmersedGlobalRounding
open DirectGLSSW.HOMFLY.PrincipalTurning DirectGLSSW.HOMFLY.PolygonDrawingBridge

noncomputable def center {n : ℕ} (q : Fin n → PlanarPoint ℝ) (i : Fin n) : ℂ :=
  Complex.equivRealProd.symm (q i)
noncomputable def incoming {n : ℕ} (q : Fin n → PlanarPoint ℝ) (i : Fin n) : ℂ :=
  polygonEdgeVector q ((cyclicSuccessorPerm n).symm i)
noncomputable def polygonCell {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (i : Fin n) (δ : RoundingFraction) : ℝ → ℂ :=
  cell (center q i) (incoming q i) (polygonEdgeVector q i) δ
noncomputable def polygonVelocity {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (i : Fin n) (δ : RoundingFraction) : ℝ → ℂ :=
  velocity (incoming q i) (polygonEdgeVector q i) δ
noncomputable def phase {n : ℕ} (base : Fin n) (k : ℤ) : Fin n :=
  (cyclicSuccessorPerm n ^ k) base

theorem phase_succ {n : ℕ} (base : Fin n) (k : ℤ) :
    phase base (k+1) = cyclicSuccessorPerm n (phase base k) := by
  unfold phase
  rw [show k+1=1+k by omega,zpow_add,zpow_one,Equiv.Perm.mul_apply]
theorem phase_previous {n : ℕ} (base : Fin n) (k : ℤ) :
    cyclicSuccessorPerm n (phase base (k-1)) = phase base k := by
  simpa using (phase_succ base (k-1)).symm

theorem center_next {n : ℕ} (q : Fin n → PlanarPoint ℝ) (i : Fin n) :
    center q (cyclicSuccessorPerm n i) = center q i + polygonEdgeVector q i := by
  apply Complex.ext <;> simp [center,polygonEdgeVector,cyclicTangent,
    Complex.equivRealProd_symm_apply]

theorem polygonCell_next_join {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (i : Fin n) (δ : RoundingFraction) :
    polygonCell q i δ 1 = polygonCell q (cyclicSuccessorPerm n i) δ 0 := by
  rw [polygonCell,polygonCell,(cell_endpoints _ _ _ δ).2,(cell_endpoints _ _ _ δ).1]
  simp only [incoming,Equiv.symm_apply_apply,center_next]
  rw [sub_smul,one_smul]
  abel

theorem polygonVelocity_endpoints {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (i : Fin n) (δ : RoundingFraction) :
    polygonVelocity q i δ 0 = incoming q i ∧
    polygonVelocity q i δ 1 = polygonEdgeVector q i := velocity_endpoints _ _ δ

noncomputable def curve {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (base : Fin n) (δ : RoundingFraction) (t : ℝ) : ℂ :=
  polygonCell q (phase base (Int.floor t)) δ (Int.fract t)
noncomputable def curveVelocity {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (base : Fin n) (δ : RoundingFraction) (t : ℝ) : ℂ :=
  polygonVelocity q (phase base (Int.floor t)) δ (Int.fract t)

theorem phase_period {n : ℕ} (base : Fin n) (k : ℤ) :
    phase base (k+n) = phase base k := by
  simp only [phase,zpow_add,Equiv.Perm.mul_apply,zpow_natCast,cyclicSuccessorPerm_pow_card]

theorem curve_periodic {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (base : Fin n) (δ : RoundingFraction) : Function.Periodic (curve q base δ) n := by
  intro t
  simp only [curve,Int.floor_add_natCast,Int.fract_add_natCast,phase_period]

theorem curveVelocity_periodic {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (base : Fin n) (δ : RoundingFraction) : Function.Periodic (curveVelocity q base δ) n := by
  intro t
  simp only [curveVelocity,Int.floor_add_natCast,Int.fract_add_natCast,phase_period]

theorem curveVelocity_continuous {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (base : Fin n) (δ : RoundingFraction) : Continuous (curveVelocity q base δ) := by
  apply continuous_integer_cells (fun k t => polygonVelocity q (phase base k) δ t)
  · intro k
    exact velocity_continuous _ _ δ
  · intro k
    rw [(polygonVelocity_endpoints _ _ _).2,(polygonVelocity_endpoints _ _ _).1]
    unfold incoming
    rw [← phase_previous base k,Equiv.symm_apply_apply]

theorem curveVelocity_ne_zero {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hedge : ∀ i, polygonEdgeVector q i ≠ 0)
    (hshort : ∀ i, polygonEdgeVector q i / incoming q i ∈ Complex.slitPlane)
    (base : Fin n) (δ : RoundingFraction) (t : ℝ) : curveVelocity q base δ t ≠ 0 :=
  velocity_ne_zero _ _ (hedge _) (hedge _) (hshort _) δ _
    ⟨Int.fract_nonneg t,(Int.fract_lt_one t).le⟩

end DirectGLSSW.ImmersedGlobalRounding




