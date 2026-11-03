import PrincipalTurning
import DirectGLSSW.PolygonGeometry
import DirectGLSSW.OrderedEventSuccessor

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open DirectGLSSW
open Filter Topology

namespace DirectGLSSW.HOMFLY.PLWinding

/-- A point avoids every actual closed PL edge, including both endpoints. -/
def AvoidsPolygonEdges {n : ℕ} (q : Fin n → ℂ) (z : ℂ) : Prop :=
  ∀ i : Fin n, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    z ≠ q i + (t : ℂ) * (q (cyclicSuccessorPerm n i) - q i)

theorem avoidsPolygonEdges_iff_literal {n : ℕ} (q : Fin n → ℂ) (z : ℂ) :
    AvoidsPolygonEdges q z ↔
      ∀ i : Fin n, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        z ≠ q i + (t : ℂ) * (q (cyclicSuccessorPerm n i) - q i) := Iff.rfl

private theorem offset_ne_zero {n : ℕ} (q : Fin n → ℂ) (z : ℂ)
    (hAvoid : AvoidsPolygonEdges q z) (i : Fin n) : q i - z ≠ 0 := by
  have hz : z ≠ q i := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
      (hAvoid i 0 (by norm_num) (by norm_num))
  exact sub_ne_zero.mpr hz.symm

private theorem edge_ratio_slitPlane {n : ℕ} (q : Fin n → ℂ) (z : ℂ)
    (hAvoid : AvoidsPolygonEdges q z) (i : Fin n) :
    (q (cyclicSuccessorPerm n i) - z) / (q i - z) ∈ Complex.slitPlane := by
  let v : ℂ := q (cyclicSuccessorPerm n i)
  let a : ℂ := q i - z
  let b : ℂ := v - z
  let w : ℂ := b / a
  have ha : a ≠ 0 := offset_ne_zero q z hAvoid i
  have hslit : 0 < w.re ∨ w.im ≠ 0 := by
    by_contra hbad
    push_neg at hbad
    let r : ℝ := w.re
    have hr : r ≤ 0 := hbad.1
    have hw : w = (r : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa [r] using hbad.2
    have hb : b = (r : ℂ) * a := by
      calc
        b = (b / a) * a := (div_mul_cancel₀ b ha).symm
        _ = (r : ℂ) * a := by change w * a = _; rw [hw]
    have hden : 0 < 1 - r := by linarith
    have hdenC : ((1 - r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hden)
    let t : ℝ := 1 / (1 - r)
    have ht0 : 0 ≤ t := le_of_lt (div_pos (by norm_num) hden)
    have ht1 : t ≤ 1 := by
      dsimp [t]
      exact (div_le_iff₀ hden).2 (by linarith)
    have hz : z = q i + (t : ℂ) * (v - q i) := by
      apply mul_left_cancel₀ hdenC
      calc
        ((1 - r : ℝ) : ℂ) * z = v - (r : ℂ) * q i := by
          dsimp [a,b] at hb
          push_cast
          linear_combination -hb
        _ = ((1 - r : ℝ) : ℂ) *
              (q i + (t : ℂ) * (v - q i)) := by
          have htC : (t : ℂ) = 1 / ((1 - r : ℝ) : ℂ) := by
            simp only [t, Complex.ofReal_div, Complex.ofReal_one]
          have hdenC' : (1 : ℂ) - (r : ℂ) ≠ 0 := by
            simpa only [Complex.ofReal_sub, Complex.ofReal_one] using hdenC
          rw [htC]
          field_simp [hdenC']
          ring
    exact hAvoid i t ht0 ht1 hz
  exact Complex.mem_slitPlane_iff.mpr hslit

/-- Finite principal-angle expression; its geometric use is restricted by
`AvoidsPolygonEdges`. -/
noncomputable def edgeArgSum {n : ℕ} (q : Fin n → ℂ) (z : ℂ) : ℝ :=
  ∑ i : Fin n, Complex.arg ((q (cyclicSuccessorPerm n i) - z) / (q i - z))

theorem edgeArgSum_eq_finite_principal_args {n : ℕ} (q : Fin n → ℂ) (z : ℂ) :
    edgeArgSum q z =
      ∑ i : Fin n, Complex.arg
        ((q (cyclicSuccessorPerm n i) - z) / (q i - z)) := rfl

/-- Literal finite PL winding on its exact off-trace domain. -/
noncomputable def winding {n : ℕ} (q : Fin n → ℂ) (z : ℂ)
    (_hAvoid : AvoidsPolygonEdges q z) : ℝ :=
  edgeArgSum q z / (2 * Real.pi)

theorem winding_eq_finite_principal_arg_sum {n : ℕ} (q : Fin n → ℂ) (z : ℂ)
    (hAvoid : AvoidsPolygonEdges q z) :
    winding q z hAvoid =
      (∑ i : Fin n,
        Complex.arg ((q (cyclicSuccessorPerm n i) - z) / (q i - z))) /
        (2 * Real.pi) := rfl

/-- The literal principal-angle sum is continuous at every point off the
actual closed edges; avoiding an edge is exactly what excludes its branch cut. -/
theorem edgeArgSum_div_continuousAt {n : ℕ} (q : Fin n → ℂ) (z : ℂ)
    (hAvoid : AvoidsPolygonEdges q z) :
    ContinuousAt (fun ζ : ℂ => edgeArgSum q ζ / (2 * Real.pi)) z := by
  have hterm (i : Fin n) : ContinuousAt
      (fun ζ : ℂ => Complex.arg
        ((q (cyclicSuccessorPerm n i) - ζ) / (q i - ζ))) z := by
    have hr : ContinuousAt
        (fun ζ : ℂ => (q (cyclicSuccessorPerm n i) - ζ) / (q i - ζ)) z :=
      (continuousAt_const.sub continuousAt_id).div
        (continuousAt_const.sub continuousAt_id) (offset_ne_zero q z hAvoid i)
    exact ContinuousAt.comp
      (f := fun ζ : ℂ => (q (cyclicSuccessorPerm n i) - ζ) / (q i - ζ))
      (x := z) (Complex.continuousAt_arg (edge_ratio_slitPlane q z hAvoid i)) hr
  have hs (s : Finset (Fin n)) : ContinuousAt
      (fun ζ : ℂ => ∑ i ∈ s,
        Complex.arg ((q (cyclicSuccessorPerm n i) - ζ) / (q i - ζ))) z := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℝ)) z)
    | @insert i s hi ih =>
        simpa only [Finset.sum_insert hi] using (hterm i).add ih
  exact (hs Finset.univ).div continuousAt_const
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)

theorem edgeArgSum_coe_angle_zero {n : ℕ} (q : Fin n → ℂ) (z : ℂ)
    (hAvoid : AvoidsPolygonEdges q z) :
    (edgeArgSum q z : Real.Angle) = 0 := by
  change Real.Angle.coeHom
      (∑ i : Fin n,
        Complex.arg ((q (cyclicSuccessorPerm n i) - z) / (q i - z))) = 0
  rw [map_sum]
  simp only [Real.Angle.coe_coeHom]
  have hterm (i : Fin n) :
      ((Complex.arg ((q (cyclicSuccessorPerm n i) - z) / (q i - z)) : ℝ) :
        Real.Angle) =
      ((q (cyclicSuccessorPerm n i) - z).arg : Real.Angle) -
        ((q i - z).arg : Real.Angle) :=
    Complex.arg_div_coe_angle
      (offset_ne_zero q z hAvoid (cyclicSuccessorPerm n i))
      (offset_ne_zero q z hAvoid i)
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib]
  have hperm :
      (∑ i : Fin n, ((q (cyclicSuccessorPerm n i) - z).arg : Real.Angle)) =
        ∑ i : Fin n, ((q i - z).arg : Real.Angle) :=
    Fintype.sum_equiv (cyclicSuccessorPerm n) _ _ (fun _ => rfl)
  rw [hperm, sub_self]

/-- Integrality is derived from the literal sum, with no Whitney or crossing formula. -/
theorem existsUnique_edgeArgSum_integer {n : ℕ} (q : Fin n → ℂ) (z : ℂ)
    (hAvoid : AvoidsPolygonEdges q z) :
    ∃! k : ℤ, edgeArgSum q z = (k : ℝ) * (2 * Real.pi) := by
  obtain ⟨k, hk⟩ := Real.Angle.coe_eq_zero_iff.mp
    (edgeArgSum_coe_angle_zero q z hAvoid)
  refine ⟨k, ?_, ?_⟩
  · simpa only [zsmul_eq_mul] using hk.symm
  · intro j hj
    have hk' : edgeArgSum q z = (k : ℝ) * (2 * Real.pi) := by
      simpa only [zsmul_eq_mul] using hk.symm
    have hcast : (j : ℝ) = (k : ℝ) :=
      mul_right_cancel₀
        (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
        (hj.symm.trans hk')
    exact_mod_cast hcast

theorem winding_is_integer {n : ℕ} (q : Fin n → ℂ) (z : ℂ)
    (hAvoid : AvoidsPolygonEdges q z) :
    ∃! k : ℤ, winding q z hAvoid = (k : ℝ) := by
  obtain ⟨k, hk, huniq⟩ := existsUnique_edgeArgSum_integer q z hAvoid
  refine ⟨k, ?_, ?_⟩
  · rw [winding, hk]
    field_simp [Real.pi_ne_zero]
  · intro j hj
    apply huniq j
    have hden : (2 : ℝ) * Real.pi ≠ 0 :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    calc
      edgeArgSum q z = winding q z hAvoid * (2 * Real.pi) := by
        rw [winding]
        exact (div_mul_cancel₀ _ hden).symm
      _ = (j : ℝ) * (2 * Real.pi) := by rw [hj]

/-- The integer determined uniquely by the literal finite winding sum. -/
noncomputable def windingIndex {n : ℕ} (q : Fin n → ℂ) (z : ℂ)
    (hAvoid : AvoidsPolygonEdges q z) : ℤ :=
  Classical.choose (existsUnique_edgeArgSum_integer q z hAvoid)

theorem windingIndex_characterization {n : ℕ} (q : Fin n → ℂ) (z : ℂ)
    (hAvoid : AvoidsPolygonEdges q z) :
    edgeArgSum q z = (windingIndex q z hAvoid : ℝ) * (2 * Real.pi) ∧
    ∀ j : ℤ, edgeArgSum q z = (j : ℝ) * (2 * Real.pi) →
      j = windingIndex q z hAvoid :=
  Classical.choose_spec (existsUnique_edgeArgSum_integer q z hAvoid)

theorem edgeArgSum_eq_windingIndex {n : ℕ} (q : Fin n → ℂ) (z : ℂ)
    (hAvoid : AvoidsPolygonEdges q z) :
    edgeArgSum q z = (windingIndex q z hAvoid : ℝ) * (2 * Real.pi) :=
  (windingIndex_characterization q z hAvoid).1

theorem winding_eq_windingIndex {n : ℕ} (q : Fin n → ℂ) (z : ℂ)
    (hAvoid : AvoidsPolygonEdges q z) :
    winding q z hAvoid = (windingIndex q z hAvoid : ℝ) := by
  rw [winding, edgeArgSum_eq_windingIndex q z hAvoid]
  field_simp [Real.pi_ne_zero]

/-- The literal integer winding is locally constant on the complement of
the actual PL trace, with no crossing-count or Whitney identity. -/
theorem windingIndex_eventually_eq {n : ℕ} (q : Fin n → ℂ) (z : ℂ)
    (hAvoid : AvoidsPolygonEdges q z) :
    ∀ᶠ ζ in 𝓝 z, ∀ hζ : AvoidsPolygonEdges q ζ,
      windingIndex q ζ hζ = windingIndex q z hAvoid := by
  have hmem : Set.Ioo (edgeArgSum q z / (2 * Real.pi) - (1 : ℝ) / 2)
      (edgeArgSum q z / (2 * Real.pi) + (1 : ℝ) / 2) ∈
        𝓝 (edgeArgSum q z / (2 * Real.pi)) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [(edgeArgSum_div_continuousAt q z hAvoid).eventually hmem] with ζ hζ
  intro hAvoidζ
  have hz : edgeArgSum q z / (2 * Real.pi) =
      (windingIndex q z hAvoid : ℝ) :=
    winding_eq_windingIndex q z hAvoid
  have hζ' : edgeArgSum q ζ / (2 * Real.pi) =
      (windingIndex q ζ hAvoidζ : ℝ) :=
    winding_eq_windingIndex q ζ hAvoidζ
  rw [hz, hζ'] at hζ
  have hlt : windingIndex q ζ hAvoidζ < windingIndex q z hAvoid + 1 := by
    exact_mod_cast (show (windingIndex q ζ hAvoidζ : ℝ) <
      (windingIndex q z hAvoid : ℝ) + 1 by linarith [hζ.2])
  have hgt : windingIndex q z hAvoid < windingIndex q ζ hAvoidζ + 1 := by
    exact_mod_cast (show (windingIndex q z hAvoid : ℝ) <
      (windingIndex q ζ hAvoidζ : ℝ) + 1 by linarith [hζ.1])
  omega

end DirectGLSSW.HOMFLY.PLWinding






