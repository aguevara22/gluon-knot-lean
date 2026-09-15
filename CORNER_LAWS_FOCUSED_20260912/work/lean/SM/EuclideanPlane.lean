import SM.Chirotope
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Actual Euclidean geometry of Plane=R×R, expressed through its coordinate
identification with C. The Euclidean length is not the product-space norm. -/

namespace SM

def planeComplex (u : Plane) : ℂ := ⟨u.1, u.2⟩

theorem planeComplex_injective : Function.Injective planeComplex := by
  intro u v h
  exact Prod.ext (congrArg Complex.re h) (congrArg Complex.im h)

theorem planeComplex_zero : planeComplex 0 = 0 := rfl

theorem planeComplex_ne_zero {u : Plane} (h : u ≠ 0) : planeComplex u ≠ 0 := by
  intro he
  exact h (planeComplex_injective he)

theorem planeComplex_smul (r : ℝ) (u : Plane) :
    planeComplex (r • u) = r • planeComplex u := by
  apply Complex.ext <;> simp [planeComplex]

theorem planeComplex_neg (u : Plane) : planeComplex (-u) = -planeComplex u := rfl

def planeDot (u v : Plane) : ℝ := u.1 * v.1 + u.2 * v.2

noncomputable def euclideanLength (u : Plane) : ℝ := ‖planeComplex u‖

theorem euclideanLength_formula (u : Plane) :
    euclideanLength u = Real.sqrt (u.1 * u.1 + u.2 * u.2) := by
  rw [euclideanLength, Complex.norm_def]
  rfl

theorem euclideanLength_pos {u : Plane} (hu : u ≠ 0) : 0 < euclideanLength u :=
  norm_pos_iff.mpr (planeComplex_ne_zero hu)

theorem planeDot_self_pos {u : Plane} (hu : u ≠ 0) : 0 < planeDot u u := by
  have hz : ¬ (u.1 = 0 ∧ u.2 = 0) := fun h => hu (Prod.ext h.1 h.2)
  dsimp [planeDot]
  rcases not_and_or.mp hz with h | h
  · nlinarith [mul_self_pos.mpr h, sq_nonneg u.2]
  · nlinarith [mul_self_pos.mpr h, sq_nonneg u.1]

theorem planeDot_smul_right (u v : Plane) (r : ℝ) :
    planeDot u (r • v) = r * planeDot u v := by
  change u.1 * (r * v.1) + u.2 * (r * v.2) = r * (u.1 * v.1 + u.2 * v.2)
  ring

theorem det_smul_self (u : Plane) (r : ℝ) : det u (r • u) = 0 := by
  change u.1 * (r * u.2) - u.2 * (r * u.1) = 0
  ring

def cornerRotor (u v : Plane) : ℂ := star (planeComplex u) * planeComplex v

theorem cornerRotor_re (u v : Plane) : (cornerRotor u v).re = planeDot u v := by
  change u.1 * v.1 - (-u.2) * v.2 = u.1 * v.1 + u.2 * v.2
  ring

theorem cornerRotor_im (u v : Plane) : (cornerRotor u v).im = det u v := by
  change u.1 * v.2 + (-u.2) * v.1 = u.1 * v.2 - u.2 * v.1
  ring

theorem cornerRotor_norm (u v : Plane) :
    ‖cornerRotor u v‖ = euclideanLength u * euclideanLength v := by
  simp only [cornerRotor, norm_mul, norm_star, euclideanLength]

theorem cornerRotor_ne_zero {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) :
    cornerRotor u v ≠ 0 :=
  mul_ne_zero (star_ne_zero.mpr (planeComplex_ne_zero hu)) (planeComplex_ne_zero hv)

/-- The coefficient is computed from the actual dot product, and the identity
follows from the vanishing determinant, not from a supplied collinearity oracle. -/
theorem scalar_of_det_zero {u v : Plane} (hu : u ≠ 0) (hd : det u v = 0) :
    v = (planeDot u v / planeDot u u) • u := by
  have hp := planeDot_self_pos hu
  have h₁ : v.1 * planeDot u u = planeDot u v * u.1 := by
    dsimp [planeDot]
    dsimp [det] at hd
    linear_combination -u.2 * hd
  have h₂ : v.2 * planeDot u u = planeDot u v * u.2 := by
    dsimp [planeDot]
    dsimp [det] at hd
    linear_combination u.1 * hd
  apply Prod.ext
  · change v.1 = (planeDot u v / planeDot u u) * u.1
    calc
      v.1 = (v.1 * planeDot u u) / planeDot u u := (mul_div_cancel_right₀ _ hp.ne').symm
      _ = (planeDot u v * u.1) / planeDot u u := by rw [h₁]
      _ = (planeDot u v / planeDot u u) * u.1 := by ring
  · change v.2 = (planeDot u v / planeDot u u) * u.2
    calc
      v.2 = (v.2 * planeDot u u) / planeDot u u := (mul_div_cancel_right₀ _ hp.ne').symm
      _ = (planeDot u v * u.2) / planeDot u u := by rw [h₂]
      _ = (planeDot u v / planeDot u u) * u.2 := by ring

end SM
