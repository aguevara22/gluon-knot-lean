import SM.RotationNumber

/-! A concrete unit direction and its dot product with actual edge vectors.
The coordinate identities use the genuine Euclidean length and argument. -/

namespace SM

noncomputable def unitDirection (a : ℝ) : Plane := (Real.cos a, Real.sin a)

theorem planeDot_add_right (u v w : Plane) :
    planeDot u (v + w) = planeDot u v + planeDot u w := by
  simp [planeDot]
  ring

def planeDotAddHom (u : Plane) : Plane →+ ℝ where
  toFun := planeDot u
  map_zero' := by simp [planeDot]
  map_add' := planeDot_add_right u

theorem planeDot_sum {ι : Type*} [Fintype ι] (u : Plane) (f : ι → Plane) :
    planeDot u (∑ i, f i) = ∑ i, planeDot u (f i) :=
  map_sum (planeDotAddHom u) f Finset.univ

theorem unitDirection_projection (a : ℝ) (v : Plane) :
    planeDot (unitDirection a) v =
      euclideanLength v * Real.cos ((planeComplex v).arg - a) := by
  have hr : euclideanLength v * Real.cos (planeComplex v).arg = v.1 :=
    Complex.norm_mul_cos_arg (planeComplex v)
  have hi : euclideanLength v * Real.sin (planeComplex v).arg = v.2 :=
    Complex.norm_mul_sin_arg (planeComplex v)
  change Real.cos a * v.1 + Real.sin a * v.2 = _
  rw [← hr, ← hi, Real.cos_sub]
  ring

theorem no_positive_edge_projection {n : ℕ} [NeZero n] (P : LabelledTuple n) (u : Plane) :
    ¬ ∀ i : ZMod n, 0 < planeDot u (edge P i) := by
  intro h
  have hp : 0 < ∑ i : ZMod n, planeDot u (edge P i) :=
    Finset.sum_pos (fun i _ => h i) Finset.univ_nonempty
  rw [← planeDot_sum, sum_edges] at hp
  simpa only [planeDot, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero,
    lt_self_iff_false] using hp

end SM
