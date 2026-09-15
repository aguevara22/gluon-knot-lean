-- Ported 09:39Z 2026-09-14 from work/drafts/cerounding/NonVacuity.lean (ce:rounding pre-review, non-vacuity evidence CE-R11) by the pod executor; body verbatim except the docstring's axiom-command phrase reworded to 'the axiom report' (no command directives in ported files).
import SM.CeSmoothingRecord

/-! # Non-vacuity witness for the ce:rounding vocabulary (row 89, fidelity risk CE-R11)

Pre-review deliverable (work/drafts/cerounding/PREREVIEW.md).  Imports ONLY the accepted row-90
vocabulary module SM/CeSmoothingRecord.lean; no draft file of the ce:rounding lane is imported, so
nothing here depends on Statements_FINAL.lean / Skeleton_FINAL.lean.

Check: `cd work/lean && lake env lean ../drafts/cerounding/NonVacuity.lean` — 0 errors, 0 warnings, no placeholder
proof anywhere; the axiom report of every declaration = [propext, Classical.choice, Quot.sound].

## What is proved

* `SM.CeRoundingNonVacuity.circle : SpatialLink 1` — the round unit circle at height `0`,
  `t ↦ (cos 2πt, 0, sin 2πt)` written as `t ↦ (Re E t, 0, Im E t)` with `E t = exp(2πi t)`:
  `C^∞`, `1`-periodic, injective on the circle (`embedded`), nonvanishing derivative (`regular`).
* `circle_cuspedProjection : circle.CuspedProjection` — the printed input class of ce:rounding is
  inhabited: no cusp (`cuspSet = ∅`), no double point (`occSetOf = ∅`), every other clause vacuous.
* `circle_regularGenericProjection : circle.RegularGenericProjection`.
* `constSmoothing : circle.CleanCuspSmoothing circle.projLoop` — the constant (identity) clean cusp
  smoothing of the cusp-free link (every per-cusp field is vacuous, `agree` is `rfl`); so the row-90
  class `CleanCuspSmoothing` (WITH its `collar` field) is inhabited.
* `constFamily : CuspRoundingFamily circle` — the constant family `G λ = circle` is a
  `CuspRoundingFamily` (row 90's object; its K-3 non-vacuity), and the three extra clauses of the
  row-89 draft's `CuspRoundingWitness` (`intervals_disjoint_circle`, `U`, `clean_in`) hold for it
  (`constFamily_intervals_disjoint_circle`, `constFamily_clean_in`) — stated here without importing
  the draft.

## Why `Complex.exp` is re-derived (§0)

The import closure of SM/CeSmoothingRecord.lean contains Mathlib's trigonometric BASICS
(`Complex.exp_eq_exp_iff_exists_int`, `Complex.exp_periodic`, …) but neither
`Mathlib.Analysis.SpecialFunctions.ExpDeriv` nor `…Trigonometric.Deriv`; so `Complex.hasDerivAt_exp`
and `Complex.contDiff_exp` are unavailable.  §0 re-proves them from `Complex.exp_bound_sq` with
Mathlib's own proofs (≈ 20 lines) rather than adding a Mathlib import. -/

namespace SM

namespace CeRoundingNonVacuity

open SmoothFront
open scoped ContDiff

noncomputable section

/-! ## 0. `Complex.exp` is `C^∞` with derivative itself (Mathlib's proofs, re-derived) -/

theorem hasDerivAt_cexp (z : ℂ) : HasDerivAt Complex.exp (Complex.exp z) z := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have h12 : (1 : ℕ) < 2 := by norm_num
  refine (Asymptotics.IsBigO.of_bound ‖Complex.exp z‖ ?_).trans_isLittleO
    (Asymptotics.isLittleO_pow_id h12)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one]
  simp only [Metric.mem_ball, dist_zero_right, norm_pow]
  exact fun w hw => Complex.exp_bound_sq z w hw.le

theorem deriv_cexp : deriv Complex.exp = Complex.exp :=
  funext fun z => (hasDerivAt_cexp z).deriv

theorem differentiable_cexp : Differentiable ℂ Complex.exp :=
  fun z => (hasDerivAt_cexp z).differentiableAt

theorem contDiff_cexp_nat (n : ℕ) : ContDiff ℂ n Complex.exp := by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact contDiff_zero.2 Complex.continuous_exp
  | succ n ih =>
    rw [Nat.cast_add_one, contDiff_succ_iff_deriv]
    refine ⟨differentiable_cexp, fun h => absurd h (WithTop.natCast_ne_top n), ?_⟩
    rwa [deriv_cexp]

theorem contDiff_cexp : ContDiff ℂ ∞ Complex.exp :=
  (contDiff_all_iff_nat.2 contDiff_cexp_nat) ⊤

/-! ## 1. The unit circle `E t = exp(2πi t)` -/

/-- the angular frequency `2πi` (named `om`: `ω` is reserved notation under `open scoped ContDiff`) -/
def om : ℂ := 2 * Real.pi * Complex.I

theorem om_ne_zero : om ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) Complex.I_ne_zero

/-- the unit circle, traversed once per unit of the parameter -/
def E (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * om)

theorem E_ne_zero (t : ℝ) : E t ≠ 0 := Complex.exp_ne_zero _

/-- two parameters give the same point of the circle iff they differ by an integer -/
theorem E_eq_iff (s t : ℝ) : E s = E t ↔ SameT s t := by
  unfold E SameT om
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have h1 : ((s : ℂ) - t - n) * (2 * Real.pi * Complex.I) = 0 := by
      rw [sub_mul, sub_mul, hn]; ring
    have h2 : (s : ℂ) - t - n = 0 := (mul_eq_zero.1 h1).resolve_right om_ne_zero
    have h3 : (t : ℂ) = ((s + ((-n : ℤ) : ℝ) : ℝ) : ℂ) := by
      push_cast
      linear_combination -h2
    exact_mod_cast h3
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [hn]; push_cast; ring

theorem E_add_one (t : ℝ) : E (t + 1) = E t := by
  unfold E om
  rw [show ((t + 1 : ℝ) : ℂ) * (2 * Real.pi * Complex.I)
      = (t : ℂ) * (2 * Real.pi * Complex.I) + 2 * Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_periodic _

theorem contDiff_E : ContDiff ℝ ∞ E := by
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ) * om) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  exact (contDiff_cexp.restrict_scalars ℝ).comp h1

/-- the real derivative of the circle: `E' = om · E` -/
theorem hasDerivAt_E (t : ℝ) : HasDerivAt E (om * E t) t := by
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) t := by
    have h := Complex.ofRealCLM.hasFDerivAt (x := t) |>.hasDerivAt
    rw [Complex.ofRealCLM_apply] at h
    exact h
  have hin : HasDerivAt (fun t : ℝ => (t : ℂ) * om) ((1 : ℂ) * om) t := h0.mul_const om
  have hout := ((hasDerivAt_cexp ((t : ℂ) * om)).hasFDerivAt.restrictScalars ℝ)
  have h := hout.comp_hasDerivAt t hin
  refine h.congr_deriv ?_
  simp [E]

/-! ## 2. The round circle at height `0` as a space curve -/

/-- `x`-coordinate `cos 2πt` -/
def x (t : ℝ) : ℝ := (E t).re
/-- `z`-coordinate `sin 2πt` -/
def z (t : ℝ) : ℝ := (E t).im
/-- the space curve `(cos 2πt, 0, sin 2πt)` -/
def T (t : ℝ) : Space := (x t, 0, z t)

theorem hasDerivAt_x (t : ℝ) : HasDerivAt x (om * E t).re t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_E t)
  exact h

theorem hasDerivAt_z (t : ℝ) : HasDerivAt z (om * E t).im t := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_E t)
  exact h

theorem contDiff_T : ContDiff ℝ ∞ T := by
  have hx : ContDiff ℝ ∞ x := Complex.reCLM.contDiff.comp contDiff_E
  have hz : ContDiff ℝ ∞ z := Complex.imCLM.contDiff.comp contDiff_E
  exact hx.prodMk (contDiff_const.prodMk hz)

theorem T_periodic : Function.Periodic T 1 := by
  intro t
  simp only [T, x, z, E_add_one]

theorem hasDerivAt_T (t : ℝ) :
    HasDerivAt T ((om * E t).re, (0 : ℝ), (om * E t).im) t :=
  (hasDerivAt_x t).prodMk ((hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_z t))

theorem omE_ne_zero (t : ℝ) : om * E t ≠ 0 := mul_ne_zero om_ne_zero (E_ne_zero t)

theorem deriv_T_ne_zero (t : ℝ) : deriv T t ≠ 0 := by
  rw [(hasDerivAt_T t).deriv]
  intro h
  apply omE_ne_zero t
  apply Complex.ext
  · have := congrArg Prod.fst h
    simpa using this
  · have := congrArg (fun p : Space => p.2.2) h
    simpa using this

/-- the `xz` projection of `T` is `E` itself (as a pair) -/
theorem xzOf_T (t : ℝ) : xzOf T t = ((E t).re, (E t).im) := rfl

theorem hasDerivAt_xzOf_T (t : ℝ) :
    HasDerivAt (xzOf T) ((om * E t).re, (om * E t).im) t :=
  (hasDerivAt_x t).prodMk (hasDerivAt_z t)

theorem deriv_xzOf_T_ne_zero (t : ℝ) : deriv (xzOf T) t ≠ 0 := by
  rw [(hasDerivAt_xzOf_T t).deriv]
  intro h
  apply omE_ne_zero t
  apply Complex.ext
  · have := congrArg Prod.fst h
    simpa using this
  · have := congrArg Prod.snd h
    simpa using this

/-! ## 3. The spatial link and its (cusp-free, crossing-free) projection -/

/-- the round circle at height `0`: one parameter circle, no cusp, no double point -/
def circle : SpatialLink 1 where
  T := fun _ => T
  smooth := fun _ => contDiff_T
  periodic := fun _ => T_periodic
  embedded := fun i j s t h => by
    refine ⟨Subsingleton.elim i j, ?_⟩
    have hx : x s = x t := congrArg Prod.fst h
    have hz : z s = z t := congrArg (fun p : Space => p.2.2) h
    exact (E_eq_iff s t).1 (Complex.ext hx hz)
  regular := fun _ t => deriv_T_ne_zero t

theorem circle_T (i : Fin 1) : circle.T i = T := rfl

theorem not_isCusp (i : Fin 1) (t : ℝ) : ¬ circle.IsCusp i t :=
  deriv_xzOf_T_ne_zero t

theorem cuspSet_eq_empty : circle.cuspSet = ∅ :=
  Set.subset_empty_iff.1 fun p hp => not_isCusp p.1 p.2 hp.2

theorem noCusp (k : circle.cuspSet) : False := not_isCusp k.1.1 k.1.2 k.2.2

/-- a coincidence of the projection is a coincidence of the parameters on the circle -/
theorem sameT_of_proj_eq {p q : Param 1}
    (he : (circle.projLoop p.1).γ p.2 = (circle.projLoop q.1).γ q.2) : SameT p.2 q.2 := by
  have he' : ((E p.2).re, (E p.2).im) = ((E q.2).re, (E q.2).im) := he
  exact (E_eq_iff p.2 q.2).1 (Complex.ext (congrArg Prod.fst he') (congrArg Prod.snd he'))

theorem not_isDoubleOf (p q : Param 1) : ¬ IsDoubleOf circle.projLoop p q := by
  rintro ⟨hne, he⟩
  exact hne ⟨Subsingleton.elim _ _, sameT_of_proj_eq he⟩

theorem occSetOf_eq_empty : occSetOf circle.projLoop = ∅ := by
  apply Set.subset_empty_iff.1
  rintro p ⟨hp, q, hq, hne, he⟩
  obtain ⟨n, hn⟩ := sameT_of_proj_eq he
  have h0 : n = 0 := by
    have h1 : (n : ℝ) < 1 := by linarith [hp.1, hp.2, hq.1, hq.2]
    have h2 : (-1 : ℝ) < n := by linarith [hp.1, hp.2, hq.1, hq.2]
    have h3 : n < (1 : ℤ) := by exact_mod_cast h1
    have h4 : (-1 : ℤ) < n := by exact_mod_cast h2
    omega
  apply hne
  refine Prod.ext (Subsingleton.elim _ _) ?_
  rw [hn, h0]
  simp

/-- **CE-R11**: the printed input class of ce:rounding is inhabited -/
theorem circle_cuspedProjection : circle.CuspedProjection where
  cusps_finite := by rw [cuspSet_eq_empty]; exact Set.finite_empty
  exact_germ := fun p hp => (not_isCusp p.1 p.2 hp.2).elim
  doubles_finite := by rw [occSetOf_eq_empty]; exact Set.finite_empty
  transverse := fun p q hd => (not_isDoubleOf p q hd).elim
  no_triple := fun p q _ hpq _ _ => (not_isDoubleOf p q hpq).elim
  heights_distinct := fun p q hd => (not_isDoubleOf p q hd).elim

theorem exists_cuspedProjection : ∃ L : SpatialLink 1, L.CuspedProjection :=
  ⟨circle, circle_cuspedProjection⟩

/-- the projection is already an ordinary finite regular generic diagram -/
theorem circle_regularGenericProjection : circle.RegularGenericProjection where
  regular := fun _ t => deriv_xzOf_T_ne_zero t
  doubles_finite := by rw [occSetOf_eq_empty]; exact Set.finite_empty
  transverse := fun p q hd => (not_isDoubleOf p q hd).elim
  no_triple := fun p q _ hpq _ _ => (not_isDoubleOf p q hpq).elim
  heights_distinct := fun p q hd => (not_isDoubleOf p q hd).elim

/-! ## 4. The constant clean smoothing and the constant rounding family -/

/-- the constant (identity) clean cusp smoothing of the cusp-free link: every per-cusp clause is
vacuous (`cuspSet = ∅`), `agree` is definitional; the row-90 class WITH `collar` is inhabited -/
def constSmoothing : circle.CleanCuspSmoothing circle.projLoop where
  U := fun k => (noCusp k).elim
  a := fun k => (noCusp k).elim
  b := fun k => (noCusp k).elim
  disc := fun k => (noCusp k).elim
  center := fun k => (noCusp k).elim
  disjoint := fun k => (noCusp k).elim
  a_lt := fun k => (noCusp k).elim
  lt_b := fun k => (noCusp k).elim
  len := fun k => (noCusp k).elim
  clean := fun k => (noCusp k).elim
  arc_in := fun k => (noCusp k).elim
  arc_simple := fun k => (noCusp k).elim
  agree := fun _ _ _ => rfl
  collar := fun k => (noCusp k).elim
  inside := fun k => (noCusp k).elim
  regular := fun k => (noCusp k).elim
  simple := fun k => (noCusp k).elim
  no_crossing := fun k => (noCusp k).elim

theorem cleanCuspSmoothing_nonempty : Nonempty (circle.CleanCuspSmoothing circle.projLoop) :=
  ⟨constSmoothing⟩

/-- "With no cusps take the constant family": the constant family is a `CuspRoundingFamily`
(row 90's object) for the round circle -/
def constFamily : CuspRoundingFamily circle where
  fam := { G := fun _ => circle, joint_smooth := fun i => (circle.smooth i).comp contDiff_snd }
  start := rfl
  a := fun k => (noCusp k).elim
  b := fun k => (noCusp k).elim
  a_lt := fun k => (noCusp k).elim
  lt_b := fun k => (noCusp k).elim
  len := fun k => (noCusp k).elim
  intervals_disjoint := fun k => (noCusp k).elim
  fixed_outside := fun _ _ _ _ => rfl
  generic := fun _ _ _ => circle_regularGenericProjection
  clean := fun _ _ _ => ⟨constSmoothing⟩
  same_doubles := fun _ _ _ _ _ => Iff.rfl
  same_data := fun _ _ _ _ _ _ => ⟨rfl, Iff.rfl⟩

theorem cuspRoundingFamily_nonempty : Nonempty (CuspRoundingFamily circle) := ⟨constFamily⟩

theorem constFamily_G (lam : ℝ) : constFamily.fam.G lam = circle := rfl

/-- the row-89 draft's extra clause `intervals_disjoint_circle` holds for the constant family -/
theorem constFamily_intervals_disjoint_circle :
    ∀ k k' : circle.cuspSet, k ≠ k' → k.1.1 = k'.1.1 → ∀ n : ℤ,
      Disjoint (Set.Ioo (constFamily.a k) (constFamily.b k))
        (Set.Ioo (constFamily.a k' + n) (constFamily.b k' + n)) :=
  fun k => (noCusp k).elim

/-- the row-89 draft's extra clause `clean_in` holds for the constant family with the (vacuous)
neighbourhoods `U` -/
theorem constFamily_clean_in (lam : ℝ) (_h0 : 0 < lam) (_h1 : lam ≤ 1) :
    ∃ cs : circle.CleanCuspSmoothing (constFamily.fam.G lam).projLoop,
      cs.U = (fun k => (noCusp k).elim) ∧ cs.a = constFamily.a ∧ cs.b = constFamily.b :=
  ⟨constSmoothing, funext fun k => (noCusp k).elim, funext fun k => (noCusp k).elim,
    funext fun k => (noCusp k).elim⟩

end

end CeRoundingNonVacuity

end SM
