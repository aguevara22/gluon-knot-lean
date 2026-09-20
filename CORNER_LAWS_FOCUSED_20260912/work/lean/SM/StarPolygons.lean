import SM.PositiveRotationSeed
import SM.ShiftTheorem

/-! Towards def:star and lem:star-generic (i)-(iii) (sm-5-transport.tex:5, 16). Written 2026-09-13 by a Claude Code prover subagent of the pod
executor (workflow prove-transport-lane / prove:stars-Kr), checked with `lake env lean` (placeholder-free, standard axioms) and
ported verbatim from work/drafts/StarPolygons.lean (only this header added and #print lines removed). -/

/-! SM def:star (the stars `K_r`, `r ≥ 1`) and lem:star-generic (i)–(iii), from
reference/SM/sm-5-transport.tex (frame SM15, lines 5–14 and 16–70).

Notation. `N = 2r+1`; `unitPoint N k = u_k = (cos(2πk/N), sin(2πk/N))` for `k : ZMod N`;
`star r = K_r` with `K_r i = u_{r(i-1)}` (the source label `t ∈ {1..N}` is the residue `i`,
the source label `N` being the residue `0`); `starNeg r = K_{-r} = reversal (star r)`;
`starAngle r = 2πr/N`; `starRadius r = ρ = cos(πr/N)`; `rotationMap θ = R` is the rotation
of the plane by `θ` about the origin, given as an explicit `ℝ`-linear map on `ℝ × ℝ`;
`shift 1 = σ`; `reversal = ρ` (the traversal reversal `i ↦ 2 - i`).

The accepted seed `positiveRotationSeed r` (vertex `i = u_{r i}`) is `shift 1 (star r)`,
i.e. `star r = shift (-1) (positiveRotationSeed r)`; its regularity, principal turns and
rotation number are transported through the accepted shift lemmas. -/

namespace SM

/-- `u_k = (cos(2πk/N), sin(2πk/N))`, `k ∈ ℤ/N` (def:star). The residue is read through its
canonical representative `k.val`; `unitPoint_intCast` shows any integer representative gives
the same point. -/
noncomputable def unitPoint (N : ℕ) (k : ZMod N) : Plane :=
  (Real.cos (2 * Real.pi * (k.val : ℝ) / N), Real.sin (2 * Real.pi * (k.val : ℝ) / N))

/-- def:star: `K_r = (μ_1, …, μ_N)`, `μ_t = u_{r(t-1)}`, `N = 2r+1`. -/
noncomputable def star (r : ℕ) : LabelledTuple (2 * r + 1) :=
  fun i => unitPoint (2 * r + 1) ((r : ZMod (2 * r + 1)) * (i - 1))

/-- def:star: `K_{-r} = \overline{K_r}`. -/
noncomputable def starNeg (r : ℕ) : LabelledTuple (2 * r + 1) := reversal (star r)

/-- The angle `2πr/N` of the rotation `R`. -/
noncomputable def starAngle (r : ℕ) : ℝ := 2 * Real.pi * (r : ℝ) / ((2 * r + 1 : ℕ) : ℝ)

/-- The radius `ρ = cos(πr/N)` of lem:star-generic(ii). -/
noncomputable def starRadius (r : ℕ) : ℝ := Real.cos (Real.pi * (r : ℝ) / ((2 * r + 1 : ℕ) : ℝ))

/-- Rotation of the plane by `θ` about the origin, as an explicit linear map on `ℝ × ℝ`. -/
noncomputable def rotationMap (θ : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun v := (Real.cos θ * v.1 - Real.sin θ * v.2, Real.sin θ * v.1 + Real.cos θ * v.2)
  map_add' u v := by
    ext <;> simp <;> ring
  map_smul' c v := by
    ext <;> simp <;> ring

theorem rotationMap_apply (θ : ℝ) (v : Plane) :
    rotationMap θ v = (Real.cos θ * v.1 - Real.sin θ * v.2, Real.sin θ * v.1 + Real.cos θ * v.2) :=
  rfl

theorem rotationMap_cos_sin (θ a : ℝ) :
    rotationMap θ (Real.cos a, Real.sin a) = (Real.cos (a + θ), Real.sin (a + θ)) := by
  rw [rotationMap_apply, Real.cos_add, Real.sin_add]
  ext <;> dsimp <;> ring

/-! ### The points `u_k` -/

theorem unitPoint_def (N : ℕ) (k : ZMod N) :
    unitPoint N k =
      (Real.cos (2 * Real.pi * (k.val : ℝ) / N), Real.sin (2 * Real.pi * (k.val : ℝ) / N)) := rfl

/-- Any integer representative of the residue gives the same point. -/
theorem unitPoint_intCast (N : ℕ) [NeZero N] (m : ℤ) :
    unitPoint N (m : ZMod N) =
      (Real.cos (2 * Real.pi * (m : ℝ) / N), Real.sin (2 * Real.pi * (m : ℝ) / N)) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hv : ((((m : ZMod N).val : ℕ) : ℤ) : ℝ) = ((m % (N : ℤ) : ℤ) : ℝ) := by
    rw [ZMod.val_intCast]
  have hm : ((m % (N : ℤ) : ℤ) : ℝ) + ((m / (N : ℤ) : ℤ) : ℝ) * (N : ℝ) = (m : ℝ) := by
    exact_mod_cast Int.emod_add_ediv_mul m N
  have key : 2 * Real.pi * (m : ℝ) / N =
      2 * Real.pi * (((m : ZMod N).val : ℕ) : ℝ) / N + ((m / (N : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [Int.cast_natCast] at hv
    rw [hv, ← hm]
    field_simp
  rw [unitPoint_def, key, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem unitPoint_natCast (N : ℕ) [NeZero N] (m : ℕ) :
    unitPoint N (m : ZMod N) =
      (Real.cos (2 * Real.pi * (m : ℝ) / N), Real.sin (2 * Real.pi * (m : ℝ) / N)) := by
  have h := unitPoint_intCast N (m : ℤ)
  simp only [Int.cast_natCast] at h
  exact h

/-- Every `u_k` lies on the unit circle. -/
theorem unitPoint_dot_self (N : ℕ) (k : ZMod N) : planeDot (unitPoint N k) (unitPoint N k) = 1 := by
  rw [unitPoint_def]
  dsimp [planeDot]
  linear_combination Real.cos_sq_add_sin_sq (2 * Real.pi * (k.val : ℝ) / N)

/-- `R_{2πm/N} u_k = u_{k+m}`. -/
theorem rotationMap_unitPoint (N : ℕ) [NeZero N] (k : ZMod N) (m : ℕ) :
    rotationMap (2 * Real.pi * (m : ℝ) / N) (unitPoint N k) = unitPoint N (k + m) := by
  have hk : k + (m : ZMod N) = ((k.val + m : ℕ) : ZMod N) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
  rw [hk, unitPoint_natCast, unitPoint_def, rotationMap_cos_sin]
  congr 2 <;> · push_cast; ring

/-- The `N` points `u_k` are distinct. -/
theorem unitPoint_injective (N : ℕ) [NeZero N] : Function.Injective (unitPoint N) := by
  intro a b h
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  rw [unitPoint_def, unitPoint_def, Prod.ext_iff] at h
  obtain ⟨hcos, hsin⟩ := h
  have hang := Real.Angle.cos_sin_inj hcos hsin
  obtain ⟨j, hj⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
  have hreal : (a.val : ℝ) - (b.val : ℝ) = (j : ℝ) * (N : ℝ) := by
    have hpi : (2 * Real.pi) ≠ 0 := Real.two_pi_pos.ne'
    rw [div_sub_div_same, div_eq_iff hN.ne'] at hj
    have : 2 * Real.pi * ((a.val : ℝ) - b.val) = 2 * Real.pi * ((j : ℝ) * N) := by
      linear_combination hj
    exact mul_left_cancel₀ hpi this
  have hint : ((a.val : ℤ) - (b.val : ℤ)) = j * (N : ℤ) := by exact_mod_cast hreal
  have hdvd : (N : ℤ) ∣ ((a.val : ℤ) - (b.val : ℤ)) := ⟨j, by rw [hint]; ring⟩
  have habs : |((a.val : ℤ) - (b.val : ℤ))| < (N : ℤ) := by
    have ha := ZMod.val_lt a
    have hb := ZMod.val_lt b
    rw [abs_lt]
    constructor <;> omega
  have hz := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have hval : a.val = b.val := by omega
  exact ZMod.val_injective N hval

/-! ### The star and the accepted seed -/

theorem star_apply (r : ℕ) (i : ZMod (2 * r + 1)) :
    star r i = unitPoint (2 * r + 1) ((r : ZMod (2 * r + 1)) * (i - 1)) := rfl

theorem starAngle_eq (r : ℕ) : starAngle r = positiveSeedAngle r := by
  unfold starAngle positiveSeedAngle
  push_cast
  ring

/-- The accepted seed vertex `i` is `u_{r i}`. -/
theorem positiveRotationSeed_eq_unitPoint (r : ℕ) (j : ZMod (2 * r + 1)) :
    positiveRotationSeed r j = unitPoint (2 * r + 1) ((r : ZMod (2 * r + 1)) * j) := by
  have hj : (r : ZMod (2 * r + 1)) * j = ((r * j.val : ℕ) : ZMod (2 * r + 1)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [hj, unitPoint_natCast]
  unfold positiveRotationSeed cyclicComplexSeed positiveSeedRatio complexPlane
  rw [← Complex.exp_nat_mul]
  have hx : ((j.val : ℕ) : ℂ) * ((positiveSeedAngle r : ℂ) * Complex.I) =
      (((j.val : ℝ) * positiveSeedAngle r : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hx, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hang : (j.val : ℝ) * positiveSeedAngle r = 2 * Real.pi * ((r * j.val : ℕ) : ℝ) / ((2 * r + 1 : ℕ) : ℝ) := by
    unfold positiveSeedAngle
    push_cast
    ring
  rw [hang]

/-- `K_r` is the accepted seed shifted back by one label: `K_r = σ⁻¹ (positiveRotationSeed r)`. -/
theorem star_eq_shift_seed (r : ℕ) : star r = shift (-1) (positiveRotationSeed r) := by
  funext i
  rw [star_apply]
  change _ = positiveRotationSeed r (i + -1)
  rw [positiveRotationSeed_eq_unitPoint, sub_eq_add_neg]

/-- `σ K_r = positiveRotationSeed r`. -/
theorem shift_one_star (r : ℕ) : shift 1 (star r) = positiveRotationSeed r := by
  rw [star_eq_shift_seed, shift_add]
  norm_num [shift_zero]

/-! ### lem:star-generic: `gcd(r, N) = 1` -/

theorem star_gcd (r : ℕ) : Nat.gcd r (2 * r + 1) = 1 := by
  have h1 := Nat.gcd_dvd_left r (2 * r + 1)
  have h2 := Nat.gcd_dvd_right r (2 * r + 1)
  have h3 : Nat.gcd r (2 * r + 1) ∣ 1 := by
    have := Nat.dvd_sub h2 (Dvd.dvd.mul_left h1 2)
    rwa [show 2 * r + 1 - 2 * r = 1 by omega] at this
  exact Nat.dvd_one.mp h3

theorem star_coprime (r : ℕ) : Nat.Coprime r (2 * r + 1) := star_gcd r

/-- Multiplication by `r` permutes the residues modulo `N`. -/
theorem star_isUnit (r : ℕ) : IsUnit (r : ZMod (2 * r + 1)) :=
  (ZMod.isUnit_iff_coprime r (2 * r + 1)).mpr (star_coprime r)

/-! ### lem:star-generic(i): `σ K_r = R(K_r)`, turns and rotation number -/

/-- `μ_{t+1} = R(μ_t)` for every `t`. -/
theorem star_succ (r : ℕ) (i : ZMod (2 * r + 1)) :
    star r (i + 1) = rotationMap (starAngle r) (star r i) := by
  rw [star_apply, star_apply, starAngle, rotationMap_unitPoint]
  congr 1
  ring

/-- lem:star-generic(i), first assertion: `σ K_r = R ∘ K_r`. -/
theorem shift_one_star_eq_rotation (r : ℕ) :
    shift 1 (star r) = (rotationMap (starAngle r)) ∘ star r := by
  funext i
  exact star_succ r i

theorem starAngle_pos {r : ℕ} (hr : 0 < r) : 0 < starAngle r := by
  rw [starAngle_eq]
  exact positiveSeedAngle_pos hr

theorem starAngle_lt_pi (r : ℕ) : starAngle r < Real.pi := by
  rw [starAngle_eq]
  exact positiveSeedAngle_lt_pi r

theorem starAngle_mem_Ioo {r : ℕ} (hr : 0 < r) : starAngle r ∈ Set.Ioo 0 Real.pi :=
  ⟨starAngle_pos hr, starAngle_lt_pi r⟩

theorem star_regular {r : ℕ} (hr : 0 < r) : Regular (star r) := by
  rw [star_eq_shift_seed]
  exact regular_shift_forward _ (positiveRotationSeed_regular hr)

/-- Every principal turn of `K_r` equals `2πr/N`. -/
theorem star_principalTurn {r : ℕ} (hr : 0 < r) (i : ZMod (2 * r + 1)) :
    principalTurn (star r) i = starAngle r := by
  rw [star_eq_shift_seed, principalTurn_shift]
  unfold positiveRotationSeed
  rw [cyclicComplexSeed_principalTurn (by omega) (positiveSeedRatio_pow r)
    (positiveSeedRatio_ne_zero r) (positiveSeedRatio_ne_one hr), positiveSeedRatio_arg hr,
    starAngle_eq]

/-- All turns of `K_r` are left. -/
theorem star_turn {r : ℕ} (hr : 0 < r) (i : ZMod (2 * r + 1)) : turn (star r) i = 1 := by
  rw [turn_det, ← principalAngle_sign (star_regular hr i)]
  change SignType.sign (principalTurn (star r) i) = 1
  rw [star_principalTurn hr]
  exact sign_eq_one_iff.mpr (starAngle_pos hr)

theorem star_leftTurns {r : ℕ} (hr : 0 < r) : leftTurns (star r) = 2 * r + 1 := by
  unfold leftTurns
  rw [Finset.filter_true_of_mem (fun i _ => star_turn hr i), Finset.card_univ, ZMod.card]

theorem star_rotationNumber {r : ℕ} (hr : 0 < r) : rotationNumber (star r) = (r : ℝ) := by
  rw [star_eq_shift_seed, rotationNumber_shift, positiveRotationSeed_rotation hr]

/-! ### lem:star-generic(ii): the edge lines are tangent to the circle of radius `ρ` -/

theorem star_dot_self (r : ℕ) (i : ZMod (2 * r + 1)) : planeDot (star r i) (star r i) = 1 :=
  unitPoint_dot_self _ _

theorem star_euclideanLength (r : ℕ) (i : ZMod (2 * r + 1)) : euclideanLength (star r i) = 1 := by
  rw [euclideanLength_formula]
  have h := star_dot_self r i
  unfold planeDot at h
  rw [h, Real.sqrt_one]

theorem star_dot_succ (r : ℕ) (i : ZMod (2 * r + 1)) :
    planeDot (star r i) (star r (i + 1)) = Real.cos (starAngle r) := by
  rw [star_succ, rotationMap_apply]
  have h := star_dot_self r i
  unfold planeDot at h ⊢
  dsimp only
  linear_combination Real.cos (starAngle r) * h

theorem star_det_succ (r : ℕ) (i : ZMod (2 * r + 1)) :
    det (star r i) (star r (i + 1)) = Real.sin (starAngle r) := by
  rw [star_succ, rotationMap_apply]
  have h := star_dot_self r i
  unfold planeDot at h
  unfold det
  dsimp only
  linear_combination Real.sin (starAngle r) * h

/-- The midpoint of edge `t` is the edge point at parameter `1/2`. -/
theorem star_midpoint_eq (r : ℕ) (i : ZMod (2 * r + 1)) :
    edgePoint (star r) i (1 / 2) = (1 / 2 : ℝ) • (star r i + star r (i + 1)) := by
  unfold edgePoint edge
  ext <;> dsimp <;> ring

/-- The edge is orthogonal to the radius through its midpoint. -/
theorem star_midpoint_dot_edge (r : ℕ) (i : ZMod (2 * r + 1)) :
    planeDot (edgePoint (star r) i (1 / 2)) (edge (star r) i) = 0 := by
  have ha := star_dot_self r i
  have hb := star_dot_self r (i + 1)
  unfold planeDot at ha hb ⊢
  unfold edgePoint edge
  dsimp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
    Prod.snd_sub, smul_eq_mul]
  linear_combination (1 / 2 : ℝ) * hb - (1 / 2 : ℝ) * ha

/-- The squared distance of the midpoint from the origin is `(1 + cos θ)/2`. -/
theorem star_midpoint_dot_self (r : ℕ) (i : ZMod (2 * r + 1)) :
    planeDot (edgePoint (star r) i (1 / 2)) (edgePoint (star r) i (1 / 2)) =
      (1 + Real.cos (starAngle r)) / 2 := by
  have ha := star_dot_self r i
  have hb := star_dot_self r (i + 1)
  have hab := star_dot_succ r i
  unfold planeDot at ha hb hab ⊢
  unfold edgePoint edge
  dsimp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
    Prod.snd_sub, smul_eq_mul]
  linear_combination (1 / 4 : ℝ) * ha + (1 / 4 : ℝ) * hb + (1 / 2 : ℝ) * hab

theorem starRadius_sq (r : ℕ) : starRadius r ^ 2 = (1 + Real.cos (starAngle r)) / 2 := by
  unfold starRadius
  rw [Real.cos_sq]
  have h : 2 * (Real.pi * (r : ℝ) / ((2 * r + 1 : ℕ) : ℝ)) = starAngle r := by
    unfold starAngle
    ring
  rw [h]
  ring

theorem starRadius_pos (r : ℕ) : 0 < starRadius r := by
  unfold starRadius
  have hN : (0 : ℝ) < ((2 * r + 1 : ℕ) : ℝ) := by positivity
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have : 0 ≤ Real.pi * (r : ℝ) / ((2 * r + 1 : ℕ) : ℝ) := by positivity
    linarith [Real.pi_pos]
  · rw [div_lt_iff₀ hN]
    have : (r : ℝ) * 2 < ((2 * r + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    nlinarith [Real.pi_pos]

/-- lem:star-generic(ii): the midpoint of every edge is at distance `ρ = cos(πr/N)` from
the origin. -/
theorem star_midpoint_length (r : ℕ) (i : ZMod (2 * r + 1)) :
    euclideanLength (edgePoint (star r) i (1 / 2)) = starRadius r := by
  rw [euclideanLength_formula]
  have h := star_midpoint_dot_self r i
  unfold planeDot at h
  rw [h, ← starRadius_sq, Real.sqrt_sq (starRadius_pos r).le]

/-! Algebra of the dot product on `Plane`. -/

theorem planeDot_comm (u v : Plane) : planeDot u v = planeDot v u := by
  unfold planeDot
  ring

theorem planeDot_add_left (u v w : Plane) : planeDot (u + v) w = planeDot u w + planeDot v w := by
  simp only [planeDot, Prod.fst_add, Prod.snd_add]
  ring

theorem star_planeDot_add_right (u v w : Plane) : planeDot u (v + w) = planeDot u v + planeDot u w := by
  simp only [planeDot, Prod.fst_add, Prod.snd_add]
  ring

theorem planeDot_sub_left (u v w : Plane) : planeDot (u - v) w = planeDot u w - planeDot v w := by
  simp only [planeDot, Prod.fst_sub, Prod.snd_sub]
  ring

theorem planeDot_sub_right (u v w : Plane) : planeDot u (v - w) = planeDot u v - planeDot u w := by
  simp only [planeDot, Prod.fst_sub, Prod.snd_sub]
  ring

theorem planeDot_smul_left (r : ℝ) (u v : Plane) : planeDot (r • u) v = r * planeDot u v := by
  simp only [planeDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem planeDot_zero_left (u : Plane) : planeDot 0 u = 0 := by
  simp [planeDot]

theorem edgePoint_eq_midpoint_add {n : ℕ} (P : LabelledTuple n) (i : ZMod n) (t : ℝ) :
    edgePoint P i t = edgePoint P i (1 / 2) + (t - 1 / 2) • edge P i := by
  unfold edgePoint
  ext <;> dsimp <;> ring

/-- The squared distance of a general point of the edge line from the origin: the line
meets the circle of radius `ρ` only at the midpoint (tangency). -/
theorem star_edgePoint_dot_self (r : ℕ) (i : ZMod (2 * r + 1)) (t : ℝ) :
    planeDot (edgePoint (star r) i t) (edgePoint (star r) i t) =
      starRadius r ^ 2 + (t - 1 / 2) ^ 2 * planeDot (edge (star r) i) (edge (star r) i) := by
  have hm := star_midpoint_dot_self r i
  have hme := star_midpoint_dot_edge r i
  have hem : planeDot (edge (star r) i) (edgePoint (star r) i (1 / 2)) = 0 := by
    rw [planeDot_comm]
    exact hme
  rw [edgePoint_eq_midpoint_add (star r) i t, planeDot_add_left, star_planeDot_add_right,
    star_planeDot_add_right, planeDot_smul_left, planeDot_smul_left, planeDot_smul_right,
    planeDot_smul_right, hme, hem, hm, starRadius_sq]
  ring

theorem star_edge_dot_self (r : ℕ) (i : ZMod (2 * r + 1)) :
    planeDot (edge (star r) i) (edge (star r) i) = 2 - 2 * Real.cos (starAngle r) := by
  have ha := star_dot_self r i
  have hb := star_dot_self r (i + 1)
  have hab := star_dot_succ r i
  unfold planeDot at ha hb hab ⊢
  unfold edge
  dsimp only [Prod.fst_sub, Prod.snd_sub]
  linear_combination ha + hb - 2 * hab

theorem star_edge_dot_self_pos {r : ℕ} (hr : 0 < r) (i : ZMod (2 * r + 1)) :
    0 < planeDot (edge (star r) i) (edge (star r) i) := by
  rw [star_edge_dot_self]
  have hs := Real.sin_pos_of_pos_of_lt_pi (starAngle_pos hr) (starAngle_lt_pi r)
  have hcs := Real.cos_sq_add_sin_sq (starAngle r)
  have hc1 : Real.cos (starAngle r) ≤ 1 := Real.cos_le_one _
  nlinarith

/-- Tangency: every point of the edge line is at distance `≥ ρ` from the origin, with
equality exactly at the midpoint. -/
theorem star_edgeLine_tangent {r : ℕ} (hr : 0 < r) (i : ZMod (2 * r + 1)) (t : ℝ) :
    starRadius r ≤ euclideanLength (edgePoint (star r) i t) ∧
      (euclideanLength (edgePoint (star r) i t) = starRadius r ↔ t = 1 / 2) := by
  have hpos := star_edge_dot_self_pos hr i
  have hρ := starRadius_pos r
  have h := star_edgePoint_dot_self r i t
  have hlen : euclideanLength (edgePoint (star r) i t) =
      Real.sqrt (starRadius r ^ 2 + (t - 1 / 2) ^ 2 * planeDot (edge (star r) i) (edge (star r) i)) := by
    rw [euclideanLength_formula, ← h]
    rfl
  rw [hlen]
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (t - 1 / 2)]
  · constructor
    · intro he
      have hsq : starRadius r ^ 2 + (t - 1 / 2) ^ 2 * planeDot (edge (star r) i) (edge (star r) i) =
          starRadius r ^ 2 := by
        have h0 : 0 ≤ starRadius r ^ 2 + (t - 1 / 2) ^ 2 * planeDot (edge (star r) i) (edge (star r) i) := by
          nlinarith [sq_nonneg (t - 1 / 2)]
        rw [← Real.sq_sqrt h0, he]
      have hz : (t - 1 / 2) ^ 2 * planeDot (edge (star r) i) (edge (star r) i) = 0 := by linarith
      rcases mul_eq_zero.mp hz with h1 | h1
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
        linarith
      · exact absurd h1 hpos.ne'
    · intro ht
      rw [ht]
      simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
        add_zero]
      exact Real.sqrt_sq hρ.le

/-- lem:star-generic(ii), last assertion: the origin lies strictly to the left of every
directed edge, `det(ℓ_t, 0 - μ_t) > 0`. -/
theorem star_origin_strictlyLeft {r : ℕ} (hr : 0 < r) (i : ZMod (2 * r + 1)) :
    strictlyLeft (star r) i 0 := by
  unfold strictlyLeft
  have h : det (edge (star r) i) (0 - star r i) = det (star r i) (star r (i + 1)) := by
    unfold det edge
    dsimp
    ring
  rw [h, star_det_succ]
  exact Real.sin_pos_of_pos_of_lt_pi (starAngle_pos hr) (starAngle_lt_pi r)

theorem star_origin_det {r : ℕ} (hr : 0 < r) (i : ZMod (2 * r + 1)) :
    0 < det (edge (star r) i) (-(star r i)) := by
  have h := star_origin_strictlyLeft hr i
  unfold strictlyLeft at h
  simpa only [zero_sub] using h

/-! ### lem:star-generic(iii): genericity -/

/-- No three distinct points of a circle are collinear: the line through two points of a
circle meets it nowhere else. -/
theorem circle_three_points {a b c : Plane} {K : ℝ}
    (ha : planeDot a a = K) (hb : planeDot b b = K) (hc : planeDot c c = K)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : det (b - a) (c - a) ≠ 0 := by
  intro hd
  have hu : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hv := scalar_of_det_zero hu hd
  set l := planeDot (b - a) (c - a) / planeDot (b - a) (b - a) with hl
  have hc' : c = a + l • (b - a) := by
    rw [← hv]
    abel
  have hupos : 0 < planeDot (b - a) (b - a) := planeDot_self_pos hu
  have hb' : planeDot (a + (b - a)) (a + (b - a)) = K := by
    rw [add_sub_cancel]
    exact hb
  rw [hc'] at hc
  rw [planeDot_add_left, star_planeDot_add_right, star_planeDot_add_right, planeDot_smul_left,
    planeDot_smul_right, planeDot_smul_left, planeDot_smul_right] at hc
  rw [planeDot_add_left, star_planeDot_add_right, star_planeDot_add_right] at hb'
  have hcomm : planeDot (b - a) a = planeDot a (b - a) := planeDot_comm _ _
  rw [hcomm] at hc hb'
  have key : l * (l - 1) * planeDot (b - a) (b - a) = 0 := by
    linear_combination hc - ha - l * (hb' - ha)
  rcases mul_eq_zero.mp key with h0 | h0
  · rcases mul_eq_zero.mp h0 with h1 | h1
    · apply hac
      rw [hc', h1, zero_smul, add_zero]
    · apply hbc
      rw [hc', sub_eq_zero.mp h1, one_smul, add_sub_cancel]
  · exact hupos.ne' h0

/-- Two vectors orthogonal to one nonzero vector of the plane are parallel. -/
theorem det_eq_zero_of_planeDot_eq_zero {x u v : Plane} (hx : x ≠ 0)
    (hu : planeDot x u = 0) (hv : planeDot x v = 0) : det u v = 0 := by
  have h1 : x.1 * det u v = 0 := by
    unfold planeDot at hu hv
    unfold det
    linear_combination v.2 * hu - u.2 * hv
  have h2 : x.2 * det u v = 0 := by
    unfold planeDot at hu hv
    unfold det
    linear_combination -v.1 * hu + u.1 * hv
  by_contra hd
  apply hx
  ext
  · exact (mul_eq_zero.mp h1).resolve_right hd
  · exact (mul_eq_zero.mp h2).resolve_right hd

/-- The residue permutation `t ↦ r(t-1)` makes the `N` star vertices distinct. -/
theorem star_injective (r : ℕ) : Function.Injective (star r) := by
  intro i j h
  rw [star_apply, star_apply] at h
  have h1 := unitPoint_injective _ h
  have h2 := (star_isUnit r).mul_left_cancel h1
  exact sub_left_inj.mp h2

/-- (G1) for `K_r`: `N` distinct points of the unit circle, no three collinear. -/
theorem star_G1 (r : ℕ) : G1 (star r) := by
  intro i j k hij hjk hik
  unfold chi
  apply sign_ne_zero.mpr
  apply circle_three_points (star_dot_self r i) (star_dot_self r j) (star_dot_self r k)
  · exact fun h => hij (star_injective r h)
  · exact fun h => hik (star_injective r h)
  · exact fun h => hjk (star_injective r h)

/-- Every point of the edge line `t` has the same dot product with the midpoint `m_t`: the
edge line is the tangent `{x : ⟨x, m_t⟩ = ρ²}` of the circle of radius `ρ` at `m_t`. -/
theorem star_edgePoint_dot_midpoint (r : ℕ) (i : ZMod (2 * r + 1)) (t : ℝ) :
    planeDot (edgePoint (star r) i t) (edgePoint (star r) i (1 / 2)) =
      (1 + Real.cos (starAngle r)) / 2 := by
  rw [edgePoint_eq_midpoint_add (star r) i t, planeDot_add_left, planeDot_smul_left,
    planeDot_comm (edge _ _), star_midpoint_dot_edge, star_midpoint_dot_self]
  ring

theorem star_midpoint_ne_zero (r : ℕ) (i : ZMod (2 * r + 1)) :
    edgePoint (star r) i (1 / 2) ≠ 0 := by
  intro h0
  have h := star_midpoint_length r i
  rw [h0] at h
  have hz : euclideanLength (0 : Plane) = 0 := by
    simp [euclideanLength, planeComplex_zero]
  rw [hz] at h
  exact (starRadius_pos r).ne h

/-- The edge line `t` meets the unit circle only at the two endpoints of the edge. -/
theorem star_chord_points {r : ℕ} (hr : 0 < r) (i : ZMod (2 * r + 1)) {p : Plane}
    (hp : planeDot p p = 1)
    (hpm : planeDot p (edgePoint (star r) i (1 / 2)) = (1 + Real.cos (starAngle r)) / 2) :
    p = star r i ∨ p = star r (i + 1) := by
  have : Fact (1 < 2 * r + 1) := ⟨by omega⟩
  by_contra hne
  obtain ⟨hpa, hpb⟩ := not_or.mp hne
  have hm0 := star_midpoint_ne_zero r i
  have ha : planeDot (star r i) (edgePoint (star r) i (1 / 2)) =
      (1 + Real.cos (starAngle r)) / 2 := by
    have h := star_edgePoint_dot_midpoint r i 0
    rwa [edgePoint_zero] at h
  have hb : planeDot (star r (i + 1)) (edgePoint (star r) i (1 / 2)) =
      (1 + Real.cos (starAngle r)) / 2 := by
    have h := star_edgePoint_dot_midpoint r i 1
    rwa [edgePoint_one] at h
  have hu : planeDot (edgePoint (star r) i (1 / 2)) (star r (i + 1) - star r i) = 0 := by
    rw [planeDot_sub_right, planeDot_comm _ (star r (i + 1)), planeDot_comm _ (star r i), hb, ha,
      sub_self]
  have hv : planeDot (edgePoint (star r) i (1 / 2)) (p - star r i) = 0 := by
    rw [planeDot_sub_right, planeDot_comm _ p, planeDot_comm _ (star r i), hpm, ha, sub_self]
  have hdet := det_eq_zero_of_planeDot_eq_zero hm0 hu hv
  have hab : star r i ≠ star r (i + 1) := fun h => next_ne_self i (star_injective r h).symm
  exact circle_three_points (star_dot_self r i) (star_dot_self r (i + 1)) hp hab
    (Ne.symm hpa) (Ne.symm hpb) hdet

/-- The `N` edge midpoints (tangency points) are pairwise distinct: coinciding midpoints
would put four vertices on one chord line. -/
theorem star_midpoint_injective {r : ℕ} (hr : 0 < r) {i j : ZMod (2 * r + 1)}
    (h : edgePoint (star r) i (1 / 2) = edgePoint (star r) j (1 / 2)) : i = j := by
  have : Fact (1 < 2 * r + 1) := ⟨by omega⟩
  have hj : star r j = star r i ∨ star r j = star r (i + 1) := by
    apply star_chord_points hr i (star_dot_self r j)
    rw [h]
    have h0 := star_edgePoint_dot_midpoint r j 0
    rwa [edgePoint_zero] at h0
  have hj1 : star r (j + 1) = star r i ∨ star r (j + 1) = star r (i + 1) := by
    apply star_chord_points hr i (star_dot_self r (j + 1))
    rw [h]
    have h1 := star_edgePoint_dot_midpoint r j 1
    rwa [edgePoint_one] at h1
  have h2 : (2 : ZMod (2 * r + 1)) ≠ 0 := by
    have h2' : ((2 : ℕ) : ZMod (2 * r + 1)) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    exact_mod_cast h2'
  rcases hj with hj | hj
  · exact (star_injective r hj).symm
  · have hji : j = i + 1 := star_injective r hj
    rcases hj1 with hj1 | hj1
    · have hh := star_injective r hj1
      rw [hji] at hh
      exfalso
      apply h2
      linear_combination hh
    · have hh := star_injective r hj1
      rw [hji] at hh
      exfalso
      have h1 : (1 : ZMod (2 * r + 1)) = 0 := by linear_combination hh
      exact one_ne_zero h1

/-- (G2) for `K_r`: the `N` edge lines are distinct tangents of one circle, and at most two
tangents pass through any point, so no three edge interiors are concurrent. -/
theorem star_G2 {r : ℕ} (hr : 0 < r) : G2 (star r) := by
  rintro ⟨i, j, k, x, hij, hjk, hik, ⟨ti, _, _, hxi⟩, ⟨tj, _, _, hxj⟩, ⟨tk, _, _, hxk⟩⟩
  have hxi' := star_edgePoint_dot_midpoint r i ti
  rw [← hxi] at hxi'
  have hxj' := star_edgePoint_dot_midpoint r j tj
  rw [← hxj] at hxj'
  have hxk' := star_edgePoint_dot_midpoint r k tk
  rw [← hxk] at hxk'
  have hcpos : 0 < (1 + Real.cos (starAngle r)) / 2 := by
    rw [← starRadius_sq]
    exact pow_pos (starRadius_pos r) 2
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, planeDot_zero_left] at hxi'
    exact hcpos.ne hxi'
  have hu : planeDot x (edgePoint (star r) j (1 / 2) - edgePoint (star r) i (1 / 2)) = 0 := by
    rw [planeDot_sub_right, hxj', hxi', sub_self]
  have hv : planeDot x (edgePoint (star r) k (1 / 2) - edgePoint (star r) i (1 / 2)) = 0 := by
    rw [planeDot_sub_right, hxk', hxi', sub_self]
  have hdet := det_eq_zero_of_planeDot_eq_zero hx0 hu hv
  refine circle_three_points (star_midpoint_dot_self r i) (star_midpoint_dot_self r j)
    (star_midpoint_dot_self r k) ?_ ?_ ?_ hdet
  · exact fun h => hij (star_midpoint_injective hr h)
  · exact fun h => hik (star_midpoint_injective hr h)
  · exact fun h => hjk (star_midpoint_injective hr h)

/-- lem:star-generic(iii): `K_r` is generic. -/
theorem star_generic {r : ℕ} (hr : 0 < r) : Generic (star r) := ⟨star_G1 r, star_G2 hr⟩

/-! ### `K_{-r} = \overline{K_r}` (lem:shift transport) -/

theorem starNeg_generic {r : ℕ} (hr : 0 < r) : Generic (starNeg r) :=
  (generic_reversal _).mpr (star_generic hr)

theorem starNeg_regular {r : ℕ} (hr : 0 < r) : Regular (starNeg r) :=
  regular_reversal_forward (star_regular hr)

theorem starNeg_turn {r : ℕ} (hr : 0 < r) (i : ZMod (2 * r + 1)) : turn (starNeg r) i = -1 := by
  unfold starNeg
  rw [turn_reversal, star_turn hr]

theorem starNeg_principalTurn {r : ℕ} (hr : 0 < r) (i : ZMod (2 * r + 1)) :
    principalTurn (starNeg r) i = -starAngle r := by
  unfold starNeg
  rw [principalTurn_reversal (star_regular hr), star_principalTurn hr]

theorem starNeg_rotationNumber {r : ℕ} (hr : 0 < r) : rotationNumber (starNeg r) = -(r : ℝ) := by
  unfold starNeg
  rw [rotationNumber_reversal (star_regular hr), star_rotationNumber hr]

theorem starNeg_leftTurns {r : ℕ} (hr : 0 < r) : leftTurns (starNeg r) = 0 := by
  unfold leftTurns
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  rw [starNeg_turn hr]
  decide

/-! ### The printed lemma -/

/-- lem:star-generic, clauses (i)–(iii) as printed (frame SM15), for `r ≥ 1` and `N = 2r+1`:
`gcd(r,N) = 1`;
(i) `σ K_r = R(K_r)` with `R = rotationMap (2πr/N)`, every principal turn equals
`2πr/N ∈ (0, π)`, all turns are left, `rot(K_r) = r`;
(ii) every edge line is tangent to the circle of radius `ρ = cos(πr/N)` about the origin at
the edge midpoint (`‖m_t‖ = ρ`, `⟨m_t, ℓ_t⟩ = 0`, and the line is at distance `≥ ρ` with
equality only at `m_t`), and the origin lies strictly to the left of every directed edge;
(iii) `K_r` is generic, hence `K_{-r} = \overline{K_r}` is generic with all turns right and
`rot(K_{-r}) = -r`. -/
theorem star_generic_lemma {r : ℕ} (hr : 1 ≤ r) :
    Nat.gcd r (2 * r + 1) = 1 ∧
    (shift 1 (star r) = (rotationMap (starAngle r)) ∘ star r ∧
      (∀ i, principalTurn (star r) i = starAngle r) ∧
      starAngle r ∈ Set.Ioo 0 Real.pi ∧
      (∀ i, turn (star r) i = 1) ∧
      rotationNumber (star r) = (r : ℝ)) ∧
    (∀ i, euclideanLength (edgePoint (star r) i (1 / 2)) = starRadius r ∧
      planeDot (edgePoint (star r) i (1 / 2)) (edge (star r) i) = 0 ∧
      (∀ t : ℝ, starRadius r ≤ euclideanLength (edgePoint (star r) i t) ∧
        (euclideanLength (edgePoint (star r) i t) = starRadius r ↔ t = 1 / 2)) ∧
      strictlyLeft (star r) i 0) ∧
    (Generic (star r) ∧ Generic (starNeg r) ∧ (∀ i, turn (starNeg r) i = -1) ∧
      rotationNumber (starNeg r) = -(r : ℝ)) := by
  have hr' : 0 < r := hr
  refine ⟨star_gcd r, ⟨shift_one_star_eq_rotation r, star_principalTurn hr',
    starAngle_mem_Ioo hr', star_turn hr', star_rotationNumber hr'⟩, ?_,
    ⟨star_generic hr', starNeg_generic hr', starNeg_turn hr', starNeg_rotationNumber hr'⟩⟩
  intro i
  exact ⟨star_midpoint_length r i, star_midpoint_dot_edge r i, star_edgeLine_tangent hr' i,
    star_origin_strictlyLeft hr' i⟩

end SM
