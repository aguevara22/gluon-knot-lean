import SM.CeSmoothingRecord
import SM.Rounding
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # SM ce:rounding — Lemma ce:rounding (row 89): statement, construction, chain, assembly, row

Assembled 2026-09-14 from Skeleton_FINAL.lean (judge's synthesis of the two architects' skeletons) and
the five proof units U-P, U-G, U-C, U-L, U-E (PLAN_FINAL.md §4): design A's construction and chain
(chart-rectangle clean neighbourhoods, cutoff in the parameter, normalized clearance, time clamp) on
design B's literal clauses (circle-disjoint intervals, one neighbourhood `U` per cusp tied to the clean
smoothing, the constant family as a witness), over the LIBRARY vocabulary of SM/CeSmoothingRecord.lean
(row 90; AUTHOR_NOTES decision D-1) — so the memo's record consequences (`isDoubleOf_iff`,
`deriv_eq_of_isDouble`, `occSetOf_eq`, `crossSignOf_eq`) are IMPORTED and PROVED there; row 90's
`collar` clause is supplied by the construction.

§1-3 = Statements_FINAL.lean (byte for byte from `namespace SM` to its cut marker).  §4 the
construction of the printed proof (sm-3:3063-3169) as explicit definitions, with the leaf lemmas of the
five units (tagged U-P, U-G, U-C, U-L, U-E in their docstrings; the units' helper lemmas carry the
prefixes `up_`, `ug_`, `uc_`, `ul_`, `ue_`); §4.7 the slices as spatial embeddings and the family; §5
the witness from the choices and the constant family; §6 the row.  Every declaration is fully proved;
the axioms of `SM.ce_rounding` are `propext`, `Classical.choice`, `Quot.sound`.
Check: `cd work/lean && lake env lean ../drafts/cerounding/CeRounding_Assembled.lean` — 0 errors. -/
namespace SM

open Link SmoothFront
open scoped ContDiff

noncomputable section
open Classical

/-! ## 1. Clause readings proved on the imported vocabulary -/

namespace SpatialLink

variable {c : ℕ} (L : SpatialLink c)

/-- two `SpatialLink`s with the same maps are equal (the other fields are proofs) -/
theorem ext' {L L' : SpatialLink c} (h : L.T = L'.T) : L = L' := by
  cases L; cases L'; cases h; rfl

/-- "no … cusps on another branch": a double point never sits at a cusp — a consequence of
`transverse`, since the determinant with a vanishing velocity is `0` -/
theorem CuspedProjection.not_isCusp_of_isDouble (h : L.CuspedProjection) {p q : Fin c × ℝ}
    (hd : IsDoubleOf L.projLoop p q) : ¬ L.IsCusp p.1 p.2 := by
  intro hc
  apply h.transverse p q hd
  unfold IsCusp at hc
  rw [hc]
  simp [det]

end SpatialLink

namespace CuspRoundingFamily

variable {c : ℕ} {L : SpatialLink c} (R : CuspRoundingFamily L)

/-- "retains every original crossing with its oriented [decorated data]": the oriented branches
(projected velocities) at every original double point are `L`'s — a consequence of `clean` through
the library's `CleanCuspSmoothing.deriv_eq_of_isDouble`.  A theorem, not a field: the printed
decorated data (sign, height order) are the fields of `same_data`. -/
theorem deriv_eq_of_isDouble (hfin : L.cuspSet.Finite) {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1)
    {p q : Fin c × ℝ} (hd : IsDoubleOf L.projLoop p q) :
    deriv (xzOf ((R.fam.G lam).T p.1)) p.2 = deriv (xzOf (L.T p.1)) p.2 :=
  (Classical.choice (R.clean lam h0 h1)).deriv_eq_of_isDouble hfin hd

end CuspRoundingFamily

/-! ## 2. Row 89 ce:rounding: the conclusion as a witness structure -/

/-- The conclusion of ce:rounding as delivered by row 89: the library's `CuspRoundingFamily L`
(row 90's object; "a jointly smooth family L_λ … of oriented spatial embeddings with L_0 = L, fixed
outside disjoint cusp parameter intervals, such that for every λ > 0 its xz projection is an ordinary
finite regular generic diagram. It cleanly smooths the cusps, creates no crossing, and retains every
original crossing with its oriented decorated data. All original parameter circles, component labels
and traversal orientations are retained.") together with two clauses the memo's structure
understates, read literally:
* "disjoint cusp parameter intervals": disjoint ON THE CIRCLE — no integer translate of one interval
  of a circle meets another interval of the same circle (the library's `intervals_disjoint` is the
  `n = 0` case);
* "It cleanly smooths the cusps": in one clean cusp neighbourhood `U k` per cusp (the printed `V`),
  chosen once for the whole family, and on the SAME parameter intervals `(a k, b k)` on which it is
  "fixed outside" (the printed proof: "Each modified portion is one regular embedded oriented arc in
  a clean cusp neighbourhood").
The family is indexed by all of `ℝ` (`SpatialFamily`); the printed clauses concern `0 ≤ λ ≤ 1`. -/
structure CuspRoundingWitness {c : ℕ} (L : SpatialLink c) extends CuspRoundingFamily L where
  /-- "disjoint cusp parameter intervals", on the circle -/
  intervals_disjoint_circle : ∀ k k', k ≠ k' → k.1.1 = k'.1.1 → ∀ n : ℤ,
    Disjoint (Set.Ioo (a k) (b k)) (Set.Ioo (a k' + n) (b k' + n))
  /-- the clean cusp neighbourhoods, one per cusp, for the whole family -/
  U : L.cuspSet → Set Plane
  /-- "It cleanly smooths the cusps": in `U`, on the intervals `(a, b)` of the fixing clause -/
  clean_in : ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
    ∃ cs : L.CleanCuspSmoothing (fam.G lam).projLoop, cs.U = U ∧ cs.a = a ∧ cs.b = b

/-! ## 3. The row bundle: one field per printed sentence of the conclusion -/

/-- Lemma ce:rounding (sm-3:3029-3062), one field per printed sentence.  `exists_family` carries the
theorem; the remaining fields are the printed sentences read on a witness (projections of
`CuspRoundingWitness`, in the pattern of the accepted `RoundingData`), plus the printed "With no cusps
take the constant family".  The two closing disclaimers ("an ordinary spatial deformation, not
asserted Legendrian or positive transverse … no self-linking transport statement") assert nothing
and have no field. -/
structure CeRoundingData : Prop where
  /-- "There is a jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings with L_0 = L,
  fixed outside disjoint cusp parameter intervals, such that for every λ > 0 its xz projection is an
  ordinary finite regular generic diagram. It cleanly smooths the cusps, creates no crossing, and
  retains every original crossing with its oriented decorated data." — for every `L` of the printed
  input class on a nonempty union of circles -/
  exists_family : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    Nonempty (CuspRoundingWitness L)
  /-- "a jointly smooth family L_λ … of oriented spatial embeddings with L_0 = L": joint `C^∞`
  smoothness of the uncurried map, every slice embedded and regular, start at `L` -/
  smooth_embeddings_start : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingWitness L),
    (∀ i, ContDiff ℝ ∞ (fun p : ℝ × ℝ => (W.fam.G p.1).T i p.2)) ∧
    (∀ (lam : ℝ) (i j : Fin c) (s t : ℝ), (W.fam.G lam).T i s = (W.fam.G lam).T j t →
      i = j ∧ SameT s t) ∧
    (∀ (lam : ℝ) (i : Fin c) (t : ℝ), deriv ((W.fam.G lam).T i) t ≠ 0) ∧
    W.fam.G 0 = L
  /-- "fixed outside disjoint cusp parameter intervals" (disjoint on the circle) -/
  fixed_outside_disjoint : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingWitness L),
    (∀ k, W.a k < k.1.2 ∧ k.1.2 < W.b k ∧ W.b k - W.a k < 1) ∧
    (∀ k k', k ≠ k' → k.1.1 = k'.1.1 → ∀ n : ℤ,
      Disjoint (Set.Ioo (W.a k) (W.b k)) (Set.Ioo (W.a k' + n) (W.b k' + n))) ∧
    ∀ (lam : ℝ) (i : Fin c) (t : ℝ),
      (∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (W.a k) (W.b k)) →
      (W.fam.G lam).T i t = L.T i t
  /-- "such that for every λ > 0 its xz projection is an ordinary finite regular generic diagram" -/
  generic_slices : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingWitness L) (lam : ℝ),
    0 < lam → lam ≤ 1 → (W.fam.G lam).RegularGenericProjection
  /-- "It cleanly smooths the cusps, creates no crossing, and retains every original crossing with
  its oriented decorated data." -/
  clean_no_new_retains : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingWitness L) (lam : ℝ),
    0 < lam → lam ≤ 1 →
    (∃ cs : L.CleanCuspSmoothing (W.fam.G lam).projLoop, cs.U = W.U ∧ cs.a = W.a ∧ cs.b = W.b) ∧
    (∀ p q : Fin c × ℝ, IsDoubleOf (W.fam.G lam).projLoop p q ↔ IsDoubleOf L.projLoop p q) ∧
    ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q →
      crossSignOf (W.fam.G lam).projLoop p q = crossSignOf L.projLoop p q ∧
      ((W.fam.G lam).height p < (W.fam.G lam).height q ↔ L.height p < L.height q)
  /-- "All original parameter circles, component labels and traversal orientations are retained":
  every slice lives on the same `c` parameter circles `ℝ/ℤ` (1-periodic in the same parameter), and
  outside the cusp intervals it is `L` itself -/
  circles_retained : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingWitness L) (lam : ℝ) (i : Fin c),
    Function.Periodic ((W.fam.G lam).T i) 1 ∧
    ∀ t : ℝ, (∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (W.a k) (W.b k)) →
      (W.fam.G lam).T i t = L.T i t
  /-- "With no cusps take the constant family": for a cuspless `L` of the class the constant family
  is a witness -/
  const_of_no_cusps : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    L.cuspSet = ∅ → ∃ W : CuspRoundingWitness L, ∀ lam : ℝ, W.fam.G lam = L

/-- row 90's object: a witness is in particular a `CuspRoundingFamily` (non-vacuity of the class row
90 quantifies over, its K-3) -/
theorem CeRoundingData.exists_cuspRoundingFamily (h : CeRoundingData) {c : ℕ} (L : SpatialLink c)
    (hc : 0 < c) (hL : L.CuspedProjection) : Nonempty (CuspRoundingFamily L) :=
  let ⟨W⟩ := h.exists_family L hc hL
  ⟨W.toCuspRoundingFamily⟩


/-! ## 4. The construction (printed proof, sm-3:3063-3169), as explicit definitions

* **Cutoff (U-P).**  The printed `ρ` ("a smooth real cutoff equal to one near zero, with support
  strictly inside `(−b, b)`", sm-3:3083-3084) is realised in the PARAMETER `t` as the 1-periodic
  `periodicBump r (t − t₀) = φ((cos 2π(t−t₀) − cos 2πr) / (cos πr − cos 2πr))`, `φ = Real.smoothTransition`:
  smooth and periodic by composition (proved), `= 1` where `dist(t − t₀, ℤ) ≤ r/2`, `= 0` where
  `dist ≥ r` (leaves).  Composed with the inverse of the coordinate `u` it is a printed `ρ`; `r < η`
  gives the collars on which the change vanishes (row 90's `collar`).
* **Chart (U-G).**  `GermData.chart` is ce:positive-chart `X = (x − x₀)/A`, `Z = 3(z − z₀ − y₀(x − x₀))/(2A)`;
  on the chart interval `J = (t₀ − δ, t₀ + δ)` (`δ ≤ 1/3`, so `J` embeds in the circle) the projection is
  `(u², u³)` (`chart_proj`); `u` is strictly monotone or antitone on `J` (`u' = y' ≠ 0`).
* **Clean neighbourhood (U-G, U-C).**  Instead of the printed open disc `V` we take, per cusp, the closed
  rectangle `rect = [−M², 2M²] × [u₋³, u₊³]` in normalized coordinates (`u₋ < 0 < u₊` the values of `u` at
  the ends `a = t₀ − η`, `b = t₀ + η` of the cusp parameter interval, `M = max(|u₋|, u₊)`), pulled back by
  the affine inverse chart: `U = unchart '' rect`, convex compact with nonempty interior (`IsDisc`).  The
  closed arc `[a, b]` is exactly `U ∩ p(L)` because `Z = u³` is strictly monotone (ce:cubic-difference;
  no inverse function of `u` is needed).  The printed clearance `d` (sm-3:3078-3082, 3085-3090) is the
  field `remote` of `CuspChoice` (normalized sup-norm distance of the remote projected image), chosen by
  compactness in `exists_remote_clearance`/`exists_eta` (U-E).
* **Displacement (U-L).**  `disp μ t = (μ ε A u(t) χ(t)) • (1, 0, y₀)` = ce:physical-displacement with
  `Δy = 0`; `core μ i t = L.T i t + Σ_{cusps k of circle i} disp_k μ t`; in the chart the moved arc is
  `(u² + μ ε u χ, u³)` = ce:rounding-formula (`chart_core`).  Amplitude `ε ≤ M` keeps `X ∈ [−M², 2M²]`
  (the bound is taken in normalized coordinates, replacing `|A| ε M √(1+y₀²) < d/2`).
* **Slices as spatial links (proved).**  Embeddedness and spatial regularity of a slice are DERIVED from
  the clean-smoothing witness on the raw loops `coreLoop μ` through the library consequences: a spatial
  coincidence projects to a double point of the smoothing = a double point of `L` (`isDoubleOf_iff`) with
  distinct unchanged heights; a zero of `deriv core` would be a zero of the projected velocity, excluded
  on the arcs by `arc_regular` and elsewhere by `L`'s own regularity (`core_xz_regular`).
* **Time.**  The library's `SpatialFamily` indexes the slices by all of `ℝ` and demands embedded slices
  everywhere; the printed formula is only claimed embedded on `[0, 1]` ("embeddedness outside [0,1] is
  not claimed", sm-3:3103-3104).  The family is `G λ = slice (φ λ)`, `φ = Real.smoothTransition` (`φ 0 = 0`,
  `φ 1 = 1`, `φ λ ∈ (0,1]` for `λ > 0`): on `[0,1]` it is the printed family in the reparametrized time
  `μ = φ(λ)` (CE-5).  Should the row-90 unit adopt the strip reading `ContDiffOn … (Icc 0 1 ×ˢ univ)`,
  replace `φ` by `max 0 (min 1 λ)` in `fam` (five lines; `core` is jointly smooth on all of `ℝ × ℝ`). -/

namespace SpatialLink

variable {c : ℕ} (L : SpatialLink c)
/-! ### 4.1 Unit P′ — the periodic cutoff from the accepted transition profile -/

/-- the 1-periodic smooth cutoff of radius `r` (for `0 < r < 1/2`): `1` where `dist(s, ℤ) ≤ r/2`, `0`
where `dist(s, ℤ) ≥ r`, values in `[0, 1]` — the printed `ρ` in the parameter -/
def periodicBump (r s : ℝ) : ℝ :=
  Real.smoothTransition ((Real.cos (2 * Real.pi * s) - Real.cos (2 * Real.pi * r)) /
    (Real.cos (Real.pi * r) - Real.cos (2 * Real.pi * r)))

theorem periodicBump_contDiff (r : ℝ) : ContDiff ℝ ∞ (periodicBump r) := by
  unfold periodicBump
  apply Real.smoothTransition.contDiff.comp
  fun_prop

theorem periodicBump_periodic (r : ℝ) : Function.Periodic (periodicBump r) 1 := by
  intro s
  simp only [periodicBump, mul_add, mul_one]
  rw [Real.cos_add_two_pi]

theorem periodicBump_nonneg (r s : ℝ) : 0 ≤ periodicBump r s := Real.smoothTransition.nonneg _

theorem periodicBump_le_one (r s : ℝ) : periodicBump r s ≤ 1 := Real.smoothTransition.le_one _

/-- (U-P helper) the denominator of the cutoff is positive: `cos πr > cos 2πr` for `0 < r < 1/2`
(`cos` strictly decreasing on `[0, π]`, `πr < 2πr ≤ π`) -/
theorem up_denom_pos {r : ℝ} (hr : 0 < r) (hr' : r < 1 / 2) :
    0 < Real.cos (Real.pi * r) - Real.cos (2 * Real.pi * r) := by
  have hpi := Real.pi_pos
  have h1 : 0 ≤ Real.pi * r := by positivity
  have h2 : 2 * Real.pi * r ≤ Real.pi := by nlinarith
  have h3 : Real.pi * r < 2 * Real.pi * r := by nlinarith
  linarith [Real.cos_lt_cos_of_nonneg_of_le_pi h1 h2 h3]

/-- `ρ(0) = 1` ("equal to one near zero"; `cos 0 = 1 ≥ cos πr`) -/
theorem periodicBump_zero {r : ℝ} (hr : 0 < r) (hr' : r < 1 / 2) : periodicBump r 0 = 1 := by
  unfold periodicBump
  apply Real.smoothTransition.one_of_one_le
  rw [one_le_div (up_denom_pos hr hr'), mul_zero, Real.cos_zero]
  linarith [Real.cos_le_one (Real.pi * r)]

/-- (U-P helper) `cos 2πs` depends on `s` only modulo `ℤ`, and then only on `|s − n|`
(`2π`-periodicity and evenness of `cos`) -/
theorem up_cos_eq_cos_abs (s : ℝ) (n : ℤ) :
    Real.cos (2 * Real.pi * s) = Real.cos (2 * Real.pi * |s - n|) := by
  have h : 2 * Real.pi * |s - n| = |2 * Real.pi * (s - n)| := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  rw [h, Real.cos_abs]
  have : 2 * Real.pi * (s - n) = 2 * Real.pi * s - n * (2 * Real.pi) := by ring
  rw [this, Real.cos_sub_int_mul_two_pi]

/-- `ρ = 1` on `dist(s, ℤ) ≤ r/2` -/
theorem periodicBump_eq_one {r : ℝ} (hr : 0 < r) (hr' : r < 1 / 2) {s : ℝ} {n : ℤ}
    (hs : |s - n| ≤ r / 2) : periodicBump r s = 1 := by
  unfold periodicBump
  apply Real.smoothTransition.one_of_one_le
  rw [one_le_div (up_denom_pos hr hr'), up_cos_eq_cos_abs s n]
  have hpi := Real.pi_pos
  have h1 : 0 ≤ 2 * Real.pi * |s - n| := by positivity
  have h2 : Real.pi * r ≤ Real.pi := by nlinarith
  have h3 : 2 * Real.pi * |s - n| ≤ Real.pi * r := by nlinarith
  linarith [Real.cos_le_cos_of_nonneg_of_le_pi h1 h2 h3]

/-- "with support strictly inside": `ρ = 0` where `dist(s, ℤ) ≥ r` -/
theorem periodicBump_eq_zero {r : ℝ} (hr : 0 < r) (hr' : r < 1 / 2) {s : ℝ}
    (hs : ∀ n : ℤ, r ≤ |s - n|) : periodicBump r s = 0 := by
  unfold periodicBump
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ (up_denom_pos hr hr').le
  rw [up_cos_eq_cos_abs s (round s)]
  have hpi := Real.pi_pos
  have hle := abs_sub_round s
  have hge := hs (round s)
  have h1 : 0 ≤ 2 * Real.pi * r := by positivity
  have h2 : 2 * Real.pi * |s - round s| ≤ Real.pi := by nlinarith
  have h3 : 2 * Real.pi * r ≤ 2 * Real.pi * |s - round s| := by nlinarith
  linarith [Real.cos_le_cos_of_nonneg_of_le_pi h1 h2 h3]

theorem exists_int_abs_lt_of_periodicBump_ne_zero {r : ℝ} (hr : 0 < r) (hr' : r < 1 / 2) {s : ℝ}
    (hs : periodicBump r s ≠ 0) : ∃ n : ℤ, |s - n| < r := by
  by_contra h
  push Not at h
  exact hs (periodicBump_eq_zero hr hr' h)

/-! ### 4.2 The exact germ data and the positive chart (sm-3:3060-3072) -/

/-- the data of one exact cusp germ (ce:exact-germ), with the chart interval shrunk to `δ ≤ 1/3` so
that it embeds in the circle -/
structure GermData (i : Fin c) (t₀ : ℝ) where
  A : ℝ
  δ : ℝ
  A_ne : A ≠ 0
  δ_pos : 0 < δ
  δ_le : δ ≤ 1 / 3
  /-- "on a parameter interval with smooth coordinate u = y − y₀" -/
  y_deriv_ne : ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), deriv (yOf (L.T i)) t ≠ 0
  /-- the three displayed formulas -/
  formula : ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ),
    L.T i t = ((L.T i t₀).1 + A * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 2,
      yOf (L.T i) t,
      (L.T i t₀).2.2 + A * yOf (L.T i) t₀ * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 2
        + (2 * A / 3) * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 3)

/-- the printed hypothesis supplies the data (shrink `δ` to `min δ (1/3)`) -/
theorem exists_germData {i : Fin c} {t₀ : ℝ} (h : L.ExactCuspGerm i t₀) :
    Nonempty (L.GermData i t₀) := by
  obtain ⟨A, δ, hA, hδ, hy, hf⟩ := h
  have hsub : Set.Ioo (t₀ - min δ (1 / 3)) (t₀ + min δ (1 / 3)) ⊆ Set.Ioo (t₀ - δ) (t₀ + δ) :=
    Set.Ioo_subset_Ioo (by linarith [min_le_left δ (1 / 3)]) (by linarith [min_le_left δ (1 / 3)])
  exact ⟨⟨A, min δ (1 / 3), hA, lt_min hδ (by norm_num), min_le_right _ _,
    fun t ht => hy t (hsub ht), fun t ht => hf t (hsub ht)⟩⟩

namespace GermData

variable {L} {i : Fin c} {t₀ : ℝ}

/-- `x₀` (the germ data only fixes the cusp; the argument is for field notation) -/
def x₀ (_g : L.GermData i t₀) : ℝ := (L.T i t₀).1
/-- `y₀` -/
def y₀ (_g : L.GermData i t₀) : ℝ := yOf (L.T i) t₀
/-- `z₀` -/
def z₀ (_g : L.GermData i t₀) : ℝ := (L.T i t₀).2.2

variable (g : L.GermData i t₀)
/-- the chart coordinate `u = y − y₀`, as a function of the parameter -/
def u (t : ℝ) : ℝ := yOf (L.T i) t - g.y₀
/-- the chart interval -/
def J : Set ℝ := Set.Ioo (t₀ - g.δ) (t₀ + g.δ)
/-- ce:positive-chart: `X = (x − x₀)/A`, `Z = 3(z − z₀ − y₀(x − x₀))/(2A)` -/
def chart (p : Plane) : Plane :=
  ((p.1 - g.x₀) / g.A, 3 * (p.2 - g.z₀ - g.y₀ * (p.1 - g.x₀)) / (2 * g.A))
/-- its affine inverse -/
def unchart (w : Plane) : Plane :=
  (g.x₀ + g.A * w.1, g.z₀ + g.y₀ * g.A * w.1 + (2 * g.A / 3) * w.2)

theorem u_t₀ : g.u t₀ = 0 := by simp [u, y₀]

theorem u_smooth : ContDiff ℝ ∞ g.u := ((L.smooth i).snd.fst).sub contDiff_const

theorem t₀_mem_J : t₀ ∈ g.J := ⟨by linarith [g.δ_pos], by linarith [g.δ_pos]⟩

theorem isOpen_J : IsOpen g.J := isOpen_Ioo

theorem chart_unchart (w : Plane) : g.chart (g.unchart w) = w := by
  have hA := g.A_ne
  ext <;> simp only [chart, unchart] <;> field_simp <;> ring

theorem unchart_chart (p : Plane) : g.unchart (g.chart p) = p := by
  have hA := g.A_ne
  ext <;> simp only [chart, unchart] <;> field_simp <;> ring

theorem chart_injective : Function.Injective g.chart :=
  Function.LeftInverse.injective g.unchart_chart

theorem unchart_continuous : Continuous g.unchart := by
  unfold unchart; fun_prop

theorem chart_continuous : Continuous g.chart := by
  unfold chart; fun_prop

/-- "sends the front to `(u², u³)`" -/
theorem chart_proj {t : ℝ} (ht : t ∈ g.J) : g.chart (xzOf (L.T i) t) = (g.u t ^ 2, g.u t ^ 3) := by
  have hA := g.A_ne
  have hf := g.formula t ht
  have h1 : (L.T i t).1 = (L.T i t₀).1 + g.A * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 2 :=
    congrArg Prod.fst hf
  have h3 : (L.T i t).2.2 = (L.T i t₀).2.2
      + g.A * yOf (L.T i) t₀ * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 2
      + (2 * g.A / 3) * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 3 :=
    congrArg (fun p : Space => p.2.2) hf
  ext
  · simp only [chart, xzOf, xOf, zOf, u, x₀, y₀, z₀]
    rw [h1]; field_simp; ring
  · simp only [chart, xzOf, xOf, zOf, u, x₀, y₀, z₀]
    rw [h1, h3]; field_simp; ring

/-- the chart is affine: the displacement `(s, 0, y₀ s)` (physical, ce:physical-displacement) is the
normalized displacement `(s, 0)` -/
theorem chart_add_disp (p : Plane) (s : ℝ) :
    g.chart (p + s • ((g.A : ℝ), g.A * g.y₀)) = g.chart p + (s, 0) := by
  have hA := g.A_ne
  ext <;> simp only [chart, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, Prod.fst_zero,
    Prod.snd_zero] <;> field_simp <;> ring

/-- strict monotonicity from a positive derivative on an open interval (Rolle applied to the chord
difference; Mathlib's `strictMonoOn_of_deriv_pos` of `Mathlib.Analysis.Calculus.Deriv.MeanValue`
is not in the import closure of this file) -/
theorem ug_strictMonoOn_of_deriv_pos {f : ℝ → ℝ} {a b : ℝ} (hf : Differentiable ℝ f)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < deriv f x) : StrictMonoOn f (Set.Ioo a b) := by
  intro x hx y hy hxy
  by_contra hcon
  push Not at hcon
  set m := (f y - f x) / (y - x) with hm
  have hm0 : m ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  let g : ℝ → ℝ := fun t => f t - f x - m * (t - x)
  have hg : ∀ t, HasDerivAt g (deriv f t - m) t := fun t => by
    have := ((hf t).hasDerivAt.sub_const (f x)).sub
      (((hasDerivAt_id t).sub_const x).const_mul m)
    rw [mul_one] at this
    exact this
  have hgx : g x = 0 := by simp [g]
  have hgy : g y = 0 := by
    simp only [g, hm]
    rw [div_mul_cancel₀ _ (by linarith : y - x ≠ 0)]; ring
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_zero hxy
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (hgx.trans hgy.symm)
  rw [(hg c).deriv] at hc'
  have := hpos c ⟨hx.1.trans hc.1, hc.2.trans hy.2⟩
  linarith

/-- strict antitonicity from a negative derivative on an open interval -/
theorem ug_strictAntiOn_of_deriv_neg {f : ℝ → ℝ} {a b : ℝ} (hf : Differentiable ℝ f)
    (hneg : ∀ x ∈ Set.Ioo a b, deriv f x < 0) : StrictAntiOn f (Set.Ioo a b) := by
  have h := ug_strictMonoOn_of_deriv_pos (f := -f) hf.neg (fun x hx => by
    rw [deriv.neg]; linarith [hneg x hx])
  intro x hx y hy hxy
  have := h hx hy hxy
  simpa using this
/-- `u` is strictly monotone or strictly antitone on the chart interval (`u' = y' ≠ 0` there,
continuous, so of one sign: "The coordinate u may increase or decrease") -/
theorem u_strictMonoOn_or_strictAntiOn : StrictMonoOn g.u g.J ∨ StrictAntiOn g.u g.J := by
  have hu : g.u = fun t => yOf (L.T i) t - g.y₀ := rfl
  have hd : ∀ t, deriv g.u t = deriv (yOf (L.T i)) t := fun t => by
    rw [hu, deriv_sub_const]
  have hne : ∀ t ∈ g.J, deriv g.u t ≠ 0 := fun t ht => by
    rw [hd]; exact g.y_deriv_ne t ht
  have hcont : Continuous (deriv g.u) := g.u_smooth.continuous_deriv (by exact_mod_cast le_top)
  have hdiff : Differentiable ℝ g.u := g.u_smooth.differentiable (by simp)
  have hpre : IsPreconnected g.J := isPreconnected_Ioo
  -- the continuous nonvanishing derivative cannot change sign on the interval (IVT)
  have key : ∀ s ∈ g.J, ∀ t ∈ g.J, 0 < deriv g.u s → deriv g.u t < 0 → False := by
    intro s hs t ht hsp htn
    obtain ⟨x, hx, hx0⟩ := hpre.intermediate_value ht hs hcont.continuousOn ⟨htn.le, hsp.le⟩
    exact hne x hx hx0
  by_cases h : ∃ s ∈ g.J, 0 < deriv g.u s
  · obtain ⟨s, hs, hsp⟩ := h
    left
    refine ug_strictMonoOn_of_deriv_pos hdiff ?_
    intro x hx
    rcases lt_or_gt_of_ne (hne x hx) with hlt | hgt
    · exact (key s hs x hx hsp hlt).elim
    · exact hgt
  · push Not at h
    right
    refine ug_strictAntiOn_of_deriv_neg hdiff ?_
    intro x hx
    exact lt_of_le_of_ne (h x hx) (hne x hx)

theorem u_injOn : Set.InjOn g.u g.J := by
  rcases g.u_strictMonoOn_or_strictAntiOn with h | h
  · exact h.injOn
  · exact h.injOn

/-- "The cubic coordinate is injective" (ce:cubic-difference) -/
theorem cube_injective : Function.Injective (fun u : ℝ => u ^ 3) :=
  (Odd.strictMono_pow (by decide : Odd 3)).injective

/-- "hence the full local arc is injective even at its cusp" -/
theorem proj_injOn_J : Set.InjOn (xzOf (L.T i)) g.J := by
  intro s hs t ht he
  have h1 := g.chart_proj hs
  have h2 := g.chart_proj ht
  rw [he, h2] at h1
  have h3 : g.u t ^ 3 = g.u s ^ 3 := (Prod.ext_iff.mp h1).2
  exact g.u_injOn hs ht (cube_injective h3).symm

/-! #### The rectangle package of a cusp interval `[t₀ − η, t₀ + η]` -/

/-- the smaller end value of `u` -/
def uMin (η : ℝ) : ℝ := min (g.u (t₀ - η)) (g.u (t₀ + η))
/-- the larger end value of `u` -/
def uMax (η : ℝ) : ℝ := max (g.u (t₀ - η)) (g.u (t₀ + η))
/-- `M = max(|u₋|, |u₊|)`, the bound of `|u|` on the interval -/
def M (η : ℝ) : ℝ := max |g.uMin η| |g.uMax η|
/-- the clean rectangle in normalized coordinates -/
def rect (η : ℝ) : Set Plane :=
  Set.Icc (-(g.M η) ^ 2) (2 * (g.M η) ^ 2) ×ˢ Set.Icc ((g.uMin η) ^ 3) ((g.uMax η) ^ 3)
/-- the sup-norm radius of the rectangle -/
def radius (η : ℝ) : ℝ := max (2 * (g.M η) ^ 2) ((g.M η) ^ 3)

theorem rect_convex (η : ℝ) : Convex ℝ (g.rect η) := (convex_Icc _ _).prod (convex_Icc _ _)

theorem rect_isCompact (η : ℝ) : IsCompact (g.rect η) := isCompact_Icc.prod isCompact_Icc

theorem rect_subset_closedBall (η : ℝ) : g.rect η ⊆ Metric.closedBall 0 (g.radius η) := by
  intro p hp
  obtain ⟨⟨h1l, h1u⟩, ⟨h2l, h2u⟩⟩ := hp
  rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have hM2 : 0 ≤ (g.M η) ^ 2 := sq_nonneg _
  have hmin : |g.uMin η| ≤ g.M η := le_max_left _ _
  have hmax : |g.uMax η| ≤ g.M η := le_max_right _ _
  have hmin3 : -(g.M η) ^ 3 ≤ (g.uMin η) ^ 3 := by
    have : |(g.uMin η) ^ 3| ≤ (g.M η) ^ 3 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hmin 3
    linarith [neg_abs_le ((g.uMin η) ^ 3)]
  have hmax3 : (g.uMax η) ^ 3 ≤ (g.M η) ^ 3 := by
    have : |(g.uMax η) ^ 3| ≤ (g.M η) ^ 3 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hmax 3
    linarith [le_abs_self ((g.uMax η) ^ 3)]
  apply max_le
  · exact le_trans (abs_le.mpr ⟨by linarith, h1u⟩) (le_max_left _ _)
  · exact le_trans (abs_le.mpr ⟨by linarith, by linarith⟩) (le_max_right _ _)

/-- for `0 < η < δ` the two end values of `u` have opposite signs: `u₋ < 0 < u₊` -/
theorem uMin_neg {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) : g.uMin η < 0 := by
  have hm : t₀ - η ∈ g.J := ⟨by linarith, by linarith⟩
  have hp : t₀ + η ∈ g.J := ⟨by linarith, by linarith⟩
  have h0 := g.u_t₀
  rcases g.u_strictMonoOn_or_strictAntiOn with h | h
  · have := h hm g.t₀_mem_J (by linarith)
    rw [h0] at this
    exact lt_of_le_of_lt (min_le_left _ _) this
  · have := h g.t₀_mem_J hp (by linarith)
    rw [h0] at this
    exact lt_of_le_of_lt (min_le_right _ _) this

theorem uMax_pos {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) : 0 < g.uMax η := by
  have hm : t₀ - η ∈ g.J := ⟨by linarith, by linarith⟩
  have hp : t₀ + η ∈ g.J := ⟨by linarith, by linarith⟩
  have h0 := g.u_t₀
  rcases g.u_strictMonoOn_or_strictAntiOn with h | h
  · have := h g.t₀_mem_J hp (by linarith)
    rw [h0] at this
    exact lt_of_lt_of_le this (le_max_right _ _)
  · have := h hm g.t₀_mem_J (by linarith)
    rw [h0] at this
    exact lt_of_lt_of_le this (le_max_left _ _)

theorem M_pos {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) : 0 < g.M η :=
  lt_of_lt_of_le (abs_pos.mpr (g.uMax_pos hη hηδ).ne') (le_max_right _ _)

/-- on the closed cusp interval `u` runs through `[u₋, u₊]` -/
theorem u_mem_Icc_of_mem {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) {t : ℝ}
    (ht : t ∈ Set.Icc (t₀ - η) (t₀ + η)) : g.u t ∈ Set.Icc (g.uMin η) (g.uMax η) := by
  have hm : t₀ - η ∈ g.J := ⟨by linarith, by linarith⟩
  have hp : t₀ + η ∈ g.J := ⟨by linarith, by linarith⟩
  have htJ : t ∈ g.J := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rcases g.u_strictMonoOn_or_strictAntiOn with h | h
  · exact ⟨le_trans (min_le_left _ _) (h.monotoneOn hm htJ ht.1),
      le_trans (h.monotoneOn htJ hp ht.2) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (h.antitoneOn htJ hp ht.2),
      le_trans (h.antitoneOn hm htJ ht.1) (le_max_left _ _)⟩

/-- and, conversely, a chart parameter whose `u` lies in `[u₋, u₊]` is on the closed interval -/
theorem mem_Icc_of_u_mem {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) {t : ℝ} (ht : t ∈ g.J)
    (hu : g.u t ∈ Set.Icc (g.uMin η) (g.uMax η)) : t ∈ Set.Icc (t₀ - η) (t₀ + η) := by
  have hm : t₀ - η ∈ g.J := ⟨by linarith, by linarith⟩
  have hp : t₀ + η ∈ g.J := ⟨by linarith, by linarith⟩
  rcases g.u_strictMonoOn_or_strictAntiOn with h | h
  · -- `u` increasing: `u₋ = u(t₀ − η)`, `u₊ = u(t₀ + η)`
    have hlt : g.u (t₀ - η) < g.u (t₀ + η) := h hm hp (by linarith)
    have hmin : g.uMin η = g.u (t₀ - η) := min_eq_left hlt.le
    have hmax : g.uMax η = g.u (t₀ + η) := max_eq_right hlt.le
    rw [hmin, hmax] at hu
    constructor
    · by_contra hc
      push Not at hc
      exact absurd hu.1 (not_le.mpr (h ht hm hc))
    · by_contra hc
      push Not at hc
      exact absurd hu.2 (not_le.mpr (h hp ht hc))
  · -- `u` decreasing: `u₋ = u(t₀ + η)`, `u₊ = u(t₀ − η)`
    have hlt : g.u (t₀ + η) < g.u (t₀ - η) := h hm hp (by linarith)
    have hmin : g.uMin η = g.u (t₀ + η) := min_eq_right hlt.le
    have hmax : g.uMax η = g.u (t₀ - η) := max_eq_left hlt.le
    rw [hmin, hmax] at hu
    constructor
    · by_contra hc
      push Not at hc
      exact absurd hu.2 (not_le.mpr (h ht hm hc))
    · by_contra hc
      push Not at hc
      exact absurd hu.1 (not_le.mpr (h hp ht hc))

/-- on the open interval `u` is strictly inside `(u₋, u₊)` -/
theorem u_mem_Ioo_of_mem {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) {t : ℝ}
    (ht : t ∈ Set.Ioo (t₀ - η) (t₀ + η)) : g.u t ∈ Set.Ioo (g.uMin η) (g.uMax η) := by
  have hm : t₀ - η ∈ g.J := ⟨by linarith, by linarith⟩
  have hp : t₀ + η ∈ g.J := ⟨by linarith, by linarith⟩
  have htJ : t ∈ g.J := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rcases g.u_strictMonoOn_or_strictAntiOn with h | h
  · exact ⟨lt_of_le_of_lt (min_le_left _ _) (h hm htJ ht.1),
      lt_of_lt_of_le (h htJ hp ht.2) (le_max_right _ _)⟩
  · exact ⟨lt_of_le_of_lt (min_le_right _ _) (h htJ hp ht.2),
      lt_of_lt_of_le (h hm htJ ht.1) (le_max_left _ _)⟩

theorem abs_u_le_M {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) {t : ℝ}
    (ht : t ∈ Set.Icc (t₀ - η) (t₀ + η)) : |g.u t| ≤ g.M η := by
  have h := g.u_mem_Icc_of_mem hη hηδ ht
  exact abs_le_max_abs_abs h.1 h.2

end GermData

/-! ### 4.3 The choices at one cusp (sm-3:3073-3096, "Disjoint clean supports and positive charts") -/

/-- The constants chosen at the cusp `k`: the germ data, the half-width `η` of the cusp parameter
interval `[t₀ − η, t₀ + η]` inside the chart, the cutoff radius `r < η`, the amplitude `ε ≤ M`, and the
clearance `remote`: every parameter of another circle, or of this circle outside the chart interval
(modulo the period), projects outside the normalized square of radius `radius η` — the printed "a
sufficiently small open page neighbourhood V meets only the exact-chart arc". -/
structure CuspChoice (k : L.cuspSet) where
  g : L.GermData k.1.1 k.1.2
  η : ℝ
  r : ℝ
  ε : ℝ
  η_pos : 0 < η
  η_lt : η < g.δ
  r_pos : 0 < r
  r_lt : r < η
  ε_pos : 0 < ε
  ε_le : ε ≤ g.M η
  remote : ∀ q : Param c, (q.1 ≠ k.1.1 ∨ ∀ n : ℤ, q.2 + n ∉ g.J) →
    g.radius η < ‖g.chart (xzOf (L.T q.1) q.2)‖

namespace CuspChoice

variable {L} {k : L.cuspSet} (ch : L.CuspChoice k)

/-- the left end of the cusp parameter interval -/
def a : ℝ := k.1.2 - ch.η
/-- the right end -/
def b : ℝ := k.1.2 + ch.η
/-- the clean neighbourhood: the rectangle pulled back by the inverse chart -/
def U : Set Plane := ch.g.unchart '' ch.g.rect ch.η
/-- the cutoff in the parameter -/
def chi (t : ℝ) : ℝ := periodicBump ch.r (t - k.1.2)
/-- ce:physical-displacement at time `μ`: `Δx = A μ ε u ρ`, `Δy = 0`, `Δz = A y₀ μ ε u ρ` -/
def disp (μ t : ℝ) : Space :=
  (μ * ch.ε * ch.g.A * ch.g.u t * ch.chi t) • ((1 : ℝ), (0 : ℝ), ch.g.y₀)

theorem a_lt : ch.a < k.1.2 := by unfold a; linarith [ch.η_pos]
theorem lt_b : k.1.2 < ch.b := by unfold b; linarith [ch.η_pos]
theorem len : ch.b - ch.a < 1 := by
  unfold a b; linarith [ch.η_lt, ch.g.δ_le]
theorem r_lt_half : ch.r < 1 / 2 := by linarith [ch.r_lt, ch.η_lt, ch.g.δ_le]

theorem Icc_subset_J : Set.Icc ch.a ch.b ⊆ ch.g.J := fun t ht =>
  ⟨by unfold a at ht; linarith [ht.1, ch.η_lt], by unfold b at ht; linarith [ht.2, ch.η_lt]⟩

theorem chi_contDiff : ContDiff ℝ ∞ ch.chi :=
  (periodicBump_contDiff ch.r).comp (contDiff_id.sub contDiff_const)

theorem chi_periodic : Function.Periodic ch.chi 1 := fun t => by
  simp only [chi]
  rw [show t + 1 - k.1.2 = (t - k.1.2) + 1 by ring]
  exact periodicBump_periodic ch.r _

theorem chi_nonneg (t : ℝ) : 0 ≤ ch.chi t := periodicBump_nonneg _ _
theorem chi_le_one (t : ℝ) : ch.chi t ≤ 1 := periodicBump_le_one _ _

theorem chi_cusp : ch.chi k.1.2 = 1 := by
  simp only [chi, sub_self]
  exact periodicBump_zero ch.r_pos ch.r_lt_half

/-- the cutoff vanishes off the open cusp interval (modulo the period): "The cutoff vanishes on
collars of the chart ends" -/
theorem chi_eq_zero_of_notMem {t : ℝ} (h : ∀ n : ℤ, t + n ∉ Set.Ioo ch.a ch.b) : ch.chi t = 0 := by
  unfold chi
  apply periodicBump_eq_zero ch.r_pos ch.r_lt_half
  intro n
  by_contra hlt
  push Not at hlt
  rw [abs_sub_lt_iff] at hlt
  apply h (-n)
  have hr := ch.r_lt
  unfold a b
  push_cast
  constructor <;> linarith [hlt.1, hlt.2]

theorem disp_zero (t : ℝ) : ch.disp 0 t = 0 := by simp [disp]

theorem disp_eq_zero_of_notMem (μ : ℝ) {t : ℝ} (h : ∀ n : ℤ, t + n ∉ Set.Ioo ch.a ch.b) :
    ch.disp μ t = 0 := by
  simp [disp, ch.chi_eq_zero_of_notMem h]

/-- `Δy = 0` -/
theorem disp_snd_fst (μ t : ℝ) : (ch.disp μ t).2.1 = 0 := by simp [disp]

theorem disp_contDiff (μ : ℝ) : ContDiff ℝ ∞ (ch.disp μ) := by
  unfold disp
  have h1 := ch.g.u_smooth
  have h2 := ch.chi_contDiff
  fun_prop

theorem disp_periodic (μ : ℝ) : Function.Periodic (ch.disp μ) 1 := fun t => by
  simp only [disp, GermData.u, chi]
  rw [show t + 1 - k.1.2 = (t - k.1.2) + 1 by ring, periodicBump_periodic]
  have : yOf (L.T k.1.1) (t + 1) = yOf (L.T k.1.1) t := by
    simp only [yOf, L.periodic k.1.1 t]
  rw [this]

/-- the projected displacement is `(μ ε u χ) • (A, A y₀)` -/
theorem xz_disp (μ t : ℝ) :
    ((ch.disp μ t).1, (ch.disp μ t).2.2) =
      (μ * ch.ε * ch.g.u t * ch.chi t) • ((ch.g.A : ℝ), ch.g.A * ch.g.y₀) := by
  simp only [disp, Prod.smul_mk, smul_eq_mul]
  ext <;> simp <;> ring

/-- U-C helper: the inverse chart is affine, so it commutes with convex combinations -/
theorem uc_unchart_convex_comb (w w' : Plane) {a b : ℝ} (hab : a + b = 1) :
    ch.g.unchart (a • w + b • w') = a • ch.g.unchart w + b • ch.g.unchart w' := by
  have hb : b = 1 - a := by linarith
  subst hb
  ext <;> simp only [GermData.unchart, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] <;> ring

/-- U-C helper: `U` is convex (affine image of the convex rectangle) -/
theorem uc_convex_U : Convex ℝ ch.U := by
  intro p hp q hq a b ha hb hab
  obtain ⟨w, hw, rfl⟩ := hp
  obtain ⟨w', hw', rfl⟩ := hq
  exact ⟨a • w + b • w', ch.g.rect_convex ch.η hw hw' ha hb hab,
    ch.uc_unchart_convex_comb w w' hab⟩

/-- U-C helper: `U` is the preimage of the rectangle under the chart -/
theorem uc_U_eq_preimage : ch.U = ch.g.chart ⁻¹' ch.g.rect ch.η := by
  ext p
  constructor
  · rintro ⟨w, hw, rfl⟩
    show ch.g.chart (ch.g.unchart w) ∈ ch.g.rect ch.η
    rw [ch.g.chart_unchart]; exact hw
  · intro h; exact ⟨_, h, ch.g.unchart_chart p⟩

/-- U-C helper: a point whose chart lies in the open rectangle is interior to `U` -/
theorem uc_mem_interior_U_of_chart {p : Plane}
    (hp : ch.g.chart p ∈ Set.Ioo (-(ch.g.M ch.η) ^ 2) (2 * (ch.g.M ch.η) ^ 2) ×ˢ
      Set.Ioo ((ch.g.uMin ch.η) ^ 3) ((ch.g.uMax ch.η) ^ 3)) : p ∈ interior ch.U := by
  rw [ch.uc_U_eq_preimage]
  apply preimage_interior_subset_interior_preimage ch.g.chart_continuous
  rw [Set.mem_preimage, GermData.rect, interior_prod_eq, interior_Icc, interior_Icc]
  exact hp

/-- U-C helper: the cusp point is interior to `U` (`chart c = (0, 0)`, and `u₋ < 0 < u₊`, `0 < M`) -/
theorem uc_center_mem_interior_U : xzOf (L.T k.1.1) k.1.2 ∈ interior ch.U := by
  apply ch.uc_mem_interior_U_of_chart
  rw [ch.g.chart_proj ch.g.t₀_mem_J, ch.g.u_t₀]
  have hM := ch.g.M_pos ch.η_pos ch.η_lt
  have hmin := ch.g.uMin_neg ch.η_pos ch.η_lt
  have hmax := ch.g.uMax_pos ch.η_pos ch.η_lt
  have hM2 : 0 < (ch.g.M ch.η) ^ 2 := pow_pos hM 2
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [zero_pow two_ne_zero]; linarith
  · rw [zero_pow two_ne_zero]; linarith
  · rw [zero_pow three_ne_zero]; exact Odd.pow_neg (by decide) hmin
  · rw [zero_pow three_ne_zero]; exact pow_pos hmax 3

theorem isDisc_U : IsDisc ch.U := by
  exact ⟨ch.uc_convex_U, (ch.g.rect_isCompact ch.η).image ch.g.unchart_continuous,
    ⟨_, ch.uc_center_mem_interior_U⟩⟩

theorem center_mem_interior_U : xzOf (L.T k.1.1) k.1.2 ∈ interior ch.U := by
  exact ch.uc_center_mem_interior_U

/-- points of `U` have normalized sup-norm at most `radius` -/
theorem norm_chart_le_of_mem_U {p : Plane} (hp : p ∈ ch.U) :
    ‖ch.g.chart p‖ ≤ ch.g.radius ch.η := by
  obtain ⟨w, hw, rfl⟩ := hp
  rw [ch.g.chart_unchart]
  simpa using ch.g.rect_subset_closedBall ch.η hw

/-- `p ∈ U` iff its chart lies in the rectangle -/
theorem mem_U_iff (p : Plane) : p ∈ ch.U ↔ ch.g.chart p ∈ ch.g.rect ch.η := by
  constructor
  · rintro ⟨w, hw, rfl⟩; rw [ch.g.chart_unchart]; exact hw
  · intro h; exact ⟨_, h, ch.g.unchart_chart p⟩

/-- "clean": the arc lies in `U` (sm-3:3080-3082) -/
theorem arc_in {t : ℝ} (ht : t ∈ Set.Icc ch.a ch.b) : xzOf (L.T k.1.1) t ∈ ch.U := by
  rw [ch.mem_U_iff, ch.g.chart_proj (ch.Icc_subset_J ht)]
  have hη := ch.η_pos
  have hηδ := ch.η_lt
  have ht' : t ∈ Set.Icc (k.1.2 - ch.η) (k.1.2 + ch.η) := ht
  have hu : ch.g.u t ∈ Set.Icc (ch.g.uMin ch.η) (ch.g.uMax ch.η) := ch.g.u_mem_Icc_of_mem hη hηδ ht'
  have hM : |ch.g.u t| ≤ ch.g.M ch.η := ch.g.abs_u_le_M hη hηδ ht'
  have hsq : (ch.g.u t) ^ 2 ≤ (ch.g.M ch.η) ^ 2 := sq_le_sq' (abs_le.mp hM).1 (abs_le.mp hM).2
  have hmono := (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).monotone
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith [sq_nonneg (ch.g.u t), sq_nonneg (ch.g.M ch.η)]
  · nlinarith [sq_nonneg (ch.g.M ch.η)]
  · exact hmono hu.1
  · exact hmono hu.2

/-- "clean": a point of the projection in `U` lies on the closed cusp arc (modulo the period) — the
remote parameters are excluded by `remote`, the chart parameters by the monotonicity of `Z = u³` -/
theorem clean {q : Param c} (hq : xzOf (L.T q.1) q.2 ∈ ch.U) :
    q.1 = k.1.1 ∧ ∃ n : ℤ, q.2 + n ∈ Set.Icc ch.a ch.b := by
  have hle := ch.norm_chart_le_of_mem_U hq
  have hi : q.1 = k.1.1 := by
    by_contra hne
    exact absurd (ch.remote q (Or.inl hne)) (not_lt.mpr hle)
  have hex : ∃ n : ℤ, q.2 + n ∈ ch.g.J := by
    by_contra hnone
    push Not at hnone
    exact absurd (ch.remote q (Or.inr hnone)) (not_lt.mpr hle)
  obtain ⟨n, hn⟩ := hex
  refine ⟨hi, n, ?_⟩
  rw [hi] at hq
  have hper : xzOf (L.T k.1.1) (q.2 + n) = xzOf (L.T k.1.1) q.2 :=
    (L.projLoop k.1.1).eq_add_int n q.2
  rw [← hper, ch.mem_U_iff, ch.g.chart_proj hn] at hq
  have hcube : ch.g.u (q.2 + n) ^ 3 ∈ Set.Icc (ch.g.uMin ch.η ^ 3) (ch.g.uMax ch.η ^ 3) :=
    (Set.mem_prod.mp hq).2
  have hmono := Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)
  have hu : ch.g.u (q.2 + n) ∈ Set.Icc (ch.g.uMin ch.η) (ch.g.uMax ch.η) :=
    ⟨hmono.le_iff_le.mp hcube.1, hmono.le_iff_le.mp hcube.2⟩
  exact ch.g.mem_Icc_of_u_mem ch.η_pos ch.η_lt hn hu

/-- the closed arc carries no double point of `L` -/
theorem arc_simple {t : ℝ} (ht : t ∈ Set.Icc ch.a ch.b) {q : Param c}
    (hq : ¬ SameParam (k.1.1, t) q) : xzOf (L.T q.1) q.2 ≠ xzOf (L.T k.1.1) t := by
  intro heq
  have hmem : xzOf (L.T q.1) q.2 ∈ ch.U := by rw [heq]; exact ch.arc_in ht
  obtain ⟨hi, n, hn⟩ := ch.clean hmem
  apply hq
  refine ⟨hi.symm, -n, ?_⟩
  have hper : xzOf (L.T k.1.1) (q.2 + n) = xzOf (L.T k.1.1) q.2 :=
    (L.projLoop k.1.1).eq_add_int n q.2
  rw [hi] at heq
  have hinj : q.2 + n = t :=
    ch.g.proj_injOn_J (ch.Icc_subset_J hn) (ch.Icc_subset_J ht) (hper.trans heq)
  push_cast
  linarith

/-- **U-C leaf.** the cutoff vanishes on the two collars `(a, a + (η − r))` and `(b − (η − r), b)` of the
cusp interval ("The cutoff vanishes on collars of the chart ends", sm-3:3105-3106; row 90's `collar`):
there `r < |t − t₀| < η` and every other translate is at distance `≥ 1 − η > r` -/
theorem chi_eq_zero_on_collar {t : ℝ}
    (ht : t ∈ Set.Ioo ch.a (ch.a + (ch.η - ch.r)) ∪ Set.Ioo (ch.b - (ch.η - ch.r)) ch.b) :
    ch.chi t = 0 := by
  unfold chi
  apply periodicBump_eq_zero ch.r_pos ch.r_lt_half
  have hr := ch.r_pos
  have hrη := ch.r_lt
  have hηδ := ch.η_lt
  have hδ := ch.g.δ_le
  -- `r < |t − t₀| < η`
  have hs : t - k.1.2 ∈ Set.Ioo (-ch.η) (-ch.r) ∨ t - k.1.2 ∈ Set.Ioo ch.r ch.η := by
    rcases ht with h | h
    · left; unfold a at h; constructor <;> linarith [h.1, h.2]
    · right; unfold b at h; constructor <;> linarith [h.1, h.2]
  -- every other translate is at distance `≥ 1 − η > r`
  have key : ∀ m : ℝ, (m ≤ -1 ∨ m = 0 ∨ 1 ≤ m) → ch.r ≤ |t - k.1.2 - m| := by
    intro m hm
    rcases hm with hm | hm | hm
    · exact le_abs.mpr (Or.inl (by rcases hs with h | h <;> linarith [h.1, h.2]))
    · subst hm
      rcases hs with h | h
      · exact le_abs.mpr (Or.inr (by linarith [h.2]))
      · exact le_abs.mpr (Or.inl (by linarith [h.1]))
    · exact le_abs.mpr (Or.inr (by rcases hs with h | h <;> linarith [h.1, h.2]))
  intro n
  apply key
  rcases lt_trichotomy n 0 with hn | hn | hn
  · left; exact_mod_cast (show n ≤ -1 by omega)
  · right; left; rw [hn]; simp
  · right; right; exact_mod_cast (show 1 ≤ n by omega)

theorem disp_eq_zero_of_chi (μ : ℝ) {t : ℝ} (h : ch.chi t = 0) : ch.disp μ t = 0 := by
  simp [disp, h]

theorem b_eq : ch.b = ch.a + 2 * ch.η := by unfold a b; ring

end CuspChoice

/-! ### 4.4 The global choices and the rounding family (sm-3:3097-3119) -/

/-- The complete package of choices: one `CuspChoice` at every cusp, with pairwise disjoint clean
neighbourhoods ("shrink their neighbourhoods to make them pairwise disjoint"). -/
structure Choices where
  fin : Fintype L.cuspSet
  ch : ∀ k : L.cuspSet, L.CuspChoice k
  disjoint : ∀ k k', k ≠ k' → Disjoint (ch k).U (ch k').U

namespace Choices

variable {L} (C : L.Choices)

/-- the rounded link at time `μ`: `L` plus the displacements of the cusps of each circle -/
def core (μ : ℝ) (i : Fin c) (t : ℝ) : Space :=
  letI : Fintype L.cuspSet := C.fin
  L.T i t + ∑ k : L.cuspSet, if k.1.1 = i then (C.ch k).disp μ t else 0

theorem core_zero : C.core 0 = L.T := by
  funext i t
  simp [core, CuspChoice.disp_zero]

theorem core_contDiff (μ : ℝ) (i : Fin c) : ContDiff ℝ ∞ (C.core μ i) := by
  letI : Fintype L.cuspSet := C.fin
  unfold core
  apply (L.smooth i).add
  apply ContDiff.sum
  intro k _
  split_ifs
  · exact (C.ch k).disp_contDiff μ
  · exact contDiff_const

theorem core_periodic (μ : ℝ) (i : Fin c) : Function.Periodic (C.core μ i) 1 := by
  letI : Fintype L.cuspSet := C.fin
  intro t
  unfold core
  rw [L.periodic i t]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  split_ifs
  · exact (C.ch k).disp_periodic μ t
  · rfl

/-- joint smoothness in `(λ, t)` of the time-clamped family -/
theorem core_joint_contDiff (i : Fin c) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => C.core (Real.smoothTransition p.1) i p.2) := by
  letI : Fintype L.cuspSet := C.fin
  unfold core
  apply ContDiff.add
  · exact (L.smooth i).comp contDiff_snd
  · apply ContDiff.sum
    intro k _
    split_ifs
    · unfold CuspChoice.disp
      have h1 : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
      have h2 := (C.ch k).g.u_smooth
      have h3 := (C.ch k).chi_contDiff
      fun_prop
    · exact contDiff_const

/-- `Δy = 0`: the height function is untouched -/
theorem yOf_core (μ : ℝ) (i : Fin c) : yOf (C.core μ i) = yOf (L.T i) := by
  letI : Fintype L.cuspSet := C.fin
  funext t
  simp only [yOf, core, Prod.snd_add, Prod.fst_add]
  have : (∑ k : L.cuspSet, if k.1.1 = i then (C.ch k).disp μ t else 0).2.1 = 0 := by
    rw [Prod.snd_sum, Prod.fst_sum]
    apply Finset.sum_eq_zero
    intro k _
    split_ifs
    · exact (C.ch k).disp_snd_fst μ t
    · rfl
  rw [this, add_zero]

/-- "fixed outside disjoint cusp parameter intervals" -/
theorem core_eq_of_notMem (μ : ℝ) (i : Fin c) {t : ℝ}
    (h : ∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (C.ch k).a (C.ch k).b) :
    C.core μ i t = L.T i t := by
  letI : Fintype L.cuspSet := C.fin
  unfold core
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  intro k _
  split_ifs with hk
  · exact (C.ch k).disp_eq_zero_of_notMem μ (h k hk)
  · rfl

/-- the projection of the rounded link at time `μ`, as plain loops (no embeddedness needed) -/
def coreLoop (μ : ℝ) (i : Fin c) : SmoothLoop where
  γ := xzOf (C.core μ i)
  smooth := ((C.core_contDiff μ i).fst).prodMk ((C.core_contDiff μ i).snd.snd)
  periodic := fun t => by
    show xzOf (C.core μ i) (t + 1) = xzOf (C.core μ i) t
    simp only [xzOf, xOf, zOf, C.core_periodic μ i t]

@[simp] theorem coreLoop_γ (μ : ℝ) (i : Fin c) : (C.coreLoop μ i).γ = xzOf (C.core μ i) := rfl

/-! ### 4.5 The local analysis on one cusp arc (sm-3:3099-3131) -/

/-- **U-L leaf.** "disjoint cusp parameter intervals", on the circle: the open arcs of two cusps of one
circle have no common point modulo the period (each closed arc lies in its own disc, `arc_in`, the
discs are disjoint, and the projection is 1-periodic) -/
theorem arcs_disjoint_circle (k k' : L.cuspSet) (hne : k ≠ k') (hi : k.1.1 = k'.1.1) (n : ℤ) :
    Disjoint (Set.Ioo (C.ch k).a (C.ch k).b) (Set.Ioo ((C.ch k').a + n) ((C.ch k').b + n)) := by
  rw [Set.disjoint_left]
  intro t ht ht'
  have h1 : xzOf (L.T k.1.1) t ∈ (C.ch k).U := (C.ch k).arc_in ⟨ht.1.le, ht.2.le⟩
  have h2 : xzOf (L.T k'.1.1) (t - n) ∈ (C.ch k').U :=
    (C.ch k').arc_in ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  have h3 : xzOf (L.T k'.1.1) (t - n) = xzOf (L.T k'.1.1) t := by
    have := (L.projLoop k'.1.1).eq_add_int (-n) t
    simp only [projLoop_γ] at this
    rw [← this]; congr 1; push_cast; ring
  rw [h3, ← hi] at h2
  exact Set.disjoint_left.mp (C.disjoint k k' hne) h1 h2

/-- on the open arc of `k` the other cusps of the circle contribute nothing (their cutoffs vanish) -/
theorem chi_eq_zero_of_ne {k k' : L.cuspSet} (hne : k ≠ k') (hi : k.1.1 = k'.1.1) {t : ℝ}
    (ht : t ∈ Set.Ioo (C.ch k).a (C.ch k).b) : (C.ch k').chi t = 0 := by
  apply (C.ch k').chi_eq_zero_of_notMem
  intro n hn
  have hd := C.arcs_disjoint_circle k k' hne hi (-n)
  apply Set.disjoint_left.mp hd ht
  constructor <;> push_cast <;> linarith [hn.1, hn.2]

/-- on the open arc of `k` the rounded link is `L` plus the displacement of `k` alone -/
theorem core_on_arc (μ : ℝ) (k : L.cuspSet) {t : ℝ} (ht : t ∈ Set.Ioo (C.ch k).a (C.ch k).b) :
    C.core μ k.1.1 t = L.T k.1.1 t + (C.ch k).disp μ t := by
  letI : Fintype L.cuspSet := C.fin
  unfold core
  congr 1
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hne
    split_ifs with hi
    · rw [(C.ch k').disp_eq_zero_of_chi μ (C.chi_eq_zero_of_ne (Ne.symm hne) hi.symm ht)]
    · rfl
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem chart_core (μ : ℝ) (k : L.cuspSet) {t : ℝ} (ht : t ∈ Set.Ioo (C.ch k).a (C.ch k).b) :
    (C.ch k).g.chart (xzOf (C.core μ k.1.1) t) =
      ((C.ch k).g.u t ^ 2 + μ * (C.ch k).ε * (C.ch k).g.u t * (C.ch k).chi t, (C.ch k).g.u t ^ 3) := by
  have hJ : t ∈ (C.ch k).g.J := (C.ch k).Icc_subset_J ⟨ht.1.le, ht.2.le⟩
  have h1 : xzOf (C.core μ k.1.1) t = xzOf (L.T k.1.1) t +
      (μ * (C.ch k).ε * (C.ch k).g.u t * (C.ch k).chi t) •
        (((C.ch k).g.A : ℝ), (C.ch k).g.A * (C.ch k).g.y₀) := by
    rw [← (C.ch k).xz_disp μ t]
    simp only [xzOf, xOf, zOf, C.core_on_arc μ k ht, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  rw [h1, (C.ch k).g.chart_add_disp, (C.ch k).g.chart_proj hJ, Prod.mk_add_mk, add_zero]

/-- "keep every moved point inside V": the rounded arc stays in `U` for `0 ≤ μ ≤ 1` -/
theorem inside {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (k : L.cuspSet) {t : ℝ}
    (ht : t ∈ Set.Ioo (C.ch k).a (C.ch k).b) : xzOf (C.core μ k.1.1) t ∈ (C.ch k).U := by
  have hη := (C.ch k).η_pos
  have hηδ := (C.ch k).η_lt
  have hIcc : t ∈ Set.Icc (k.1.2 - (C.ch k).η) (k.1.2 + (C.ch k).η) := ⟨ht.1.le, ht.2.le⟩
  have hM := (C.ch k).g.abs_u_le_M hη hηδ hIcc
  have hu := (C.ch k).g.u_mem_Icc_of_mem hη hηδ hIcc
  have hMpos := (C.ch k).g.M_pos hη hηδ
  have hχ0 := (C.ch k).chi_nonneg t
  have hχ1 := (C.ch k).chi_le_one t
  have hε := (C.ch k).ε_pos
  have hεM := (C.ch k).ε_le
  have hsq : (C.ch k).g.u t ^ 2 ≤ (C.ch k).g.M (C.ch k).η ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hM 2
  have hprod : |μ * (C.ch k).ε * (C.ch k).g.u t * (C.ch k).chi t| ≤ (C.ch k).g.M (C.ch k).η ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hμ.1, abs_of_nonneg hε.le, abs_of_nonneg hχ0]
    have h1 : μ * (C.ch k).ε ≤ (C.ch k).g.M (C.ch k).η := by nlinarith [hμ.1, hμ.2]
    have h2 : μ * (C.ch k).ε * |(C.ch k).g.u t| ≤ (C.ch k).g.M (C.ch k).η * (C.ch k).g.M (C.ch k).η :=
      mul_le_mul h1 hM (abs_nonneg _) hMpos.le
    have h3 : μ * (C.ch k).ε * |(C.ch k).g.u t| * (C.ch k).chi t ≤
        (C.ch k).g.M (C.ch k).η * (C.ch k).g.M (C.ch k).η * 1 :=
      mul_le_mul h2 hχ1 hχ0 (by positivity)
    nlinarith
  rw [(C.ch k).mem_U_iff, C.chart_core μ k ht, GermData.rect, Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
  obtain ⟨hp1, hp2⟩ := abs_le.mp hprod
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith [sq_nonneg ((C.ch k).g.u t)]
  · nlinarith
  · exact (Odd.pow_le_pow (by decide : Odd 3)).mpr hu.1
  · exact (Odd.pow_le_pow (by decide : Odd 3)).mpr hu.2

/-- U-L helper: the chart coordinate `u = y − y₀` has derivative `y′` (`HasDerivAt` form) -/
theorem ul_hasDerivAt_u {i : Fin c} {t₀ : ℝ} (g : L.GermData i t₀) (t : ℝ) :
    HasDerivAt g.u (deriv (yOf (L.T i)) t) t := by
  have hy : HasDerivAt (yOf (L.T i)) (deriv (yOf (L.T i)) t) t :=
    (((L.smooth i).snd.fst).differentiable (by simp) t).hasDerivAt
  unfold GermData.u
  exact hy.sub_const g.y₀

/-- U-L helper: the two chart coordinates of the rounded arc, as real functions of the parameter,
are `u² + μ ε u χ` and `u³` on the open arc (`chart_core` read componentwise) -/
theorem ul_chart_core_coords (μ : ℝ) (k : L.cuspSet) {s : ℝ}
    (hs : s ∈ Set.Ioo (C.ch k).a (C.ch k).b) :
    (xOf (C.core μ k.1.1) s - (C.ch k).g.x₀) / (C.ch k).g.A =
        (C.ch k).g.u s ^ 2 + μ * (C.ch k).ε * (C.ch k).g.u s * (C.ch k).chi s ∧
      3 * (zOf (C.core μ k.1.1) s - (C.ch k).g.z₀ -
          (C.ch k).g.y₀ * (xOf (C.core μ k.1.1) s - (C.ch k).g.x₀)) / (2 * (C.ch k).g.A) =
        (C.ch k).g.u s ^ 3 := by
  have h := C.chart_core μ k hs
  simp only [GermData.chart, xzOf, Prod.mk.injEq] at h
  exact h

/-- "the two projected derivatives are never simultaneously zero for λ > 0": `dZ/du = 3u² ≠ 0` off
the centre, `dX/du = μ ε ρ(0) = μ ε` at the centre; composed with the smooth coordinate `u` (either
direction) -/
theorem arc_regular {μ : ℝ} (hμ : 0 < μ) (k : L.cuspSet) {t : ℝ}
    (ht : t ∈ Set.Ioo (C.ch k).a (C.ch k).b) : deriv (xzOf (C.core μ k.1.1)) t ≠ 0 := by
  intro hd
  have hJ : t ∈ (C.ch k).g.J := (C.ch k).Icc_subset_J ⟨ht.1.le, ht.2.le⟩
  have hε := (C.ch k).ε_pos
  have hu' : deriv (yOf (L.T k.1.1)) t ≠ 0 := (C.ch k).g.y_deriv_ne t hJ
  -- the projected velocity vanishes componentwise
  have hxd : HasDerivAt (xOf (C.core μ k.1.1)) (deriv (xOf (C.core μ k.1.1)) t) t :=
    (((C.core_contDiff μ k.1.1).fst).differentiable (by simp) t).hasDerivAt
  have hzd : HasDerivAt (zOf (C.core μ k.1.1)) (deriv (zOf (C.core μ k.1.1)) t) t :=
    (((C.core_contDiff μ k.1.1).snd.snd).differentiable (by simp) t).hasDerivAt
  have h0 : (deriv (xOf (C.core μ k.1.1)) t, deriv (zOf (C.core μ k.1.1)) t) = (0 : Plane) := by
    rw [← (hxd.prodMk hzd).deriv]; exact hd
  have hx0 : deriv (xOf (C.core μ k.1.1)) t = 0 := (Prod.ext_iff.mp h0).1
  have hz0 : deriv (zOf (C.core μ k.1.1)) t = 0 := (Prod.ext_iff.mp h0).2
  rw [hx0] at hxd
  rw [hz0] at hzd
  -- the chart coordinates of the rounded arc have zero derivative …
  have hP : HasDerivAt (fun s => (xOf (C.core μ k.1.1) s - (C.ch k).g.x₀) / (C.ch k).g.A)
      (0 / (C.ch k).g.A) t := (hxd.sub_const _).div_const _
  have hQ : HasDerivAt (fun s => 3 * (zOf (C.core μ k.1.1) s - (C.ch k).g.z₀ -
      (C.ch k).g.y₀ * (xOf (C.core μ k.1.1) s - (C.ch k).g.x₀)) / (2 * (C.ch k).g.A))
      (3 * (0 - (C.ch k).g.y₀ * 0) / (2 * (C.ch k).g.A)) t :=
    (((hzd.sub_const _).sub ((hxd.sub_const _).const_mul _)).const_mul 3).div_const _
  -- … and equal `u² + μ ε u χ`, `u³` near `t`
  have hnhds : Set.Ioo (C.ch k).a (C.ch k).b ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
  have hu := ul_hasDerivAt_u (C.ch k).g t
  have hχ : HasDerivAt (C.ch k).chi (deriv (C.ch k).chi t) t :=
    (((C.ch k).chi_contDiff).differentiable (by simp) t).hasDerivAt
  have hP' : HasDerivAt (fun s => (C.ch k).g.u s ^ 2 + μ * (C.ch k).ε * (C.ch k).g.u s * (C.ch k).chi s)
      (2 * (C.ch k).g.u t * deriv (yOf (L.T k.1.1)) t +
        (μ * (C.ch k).ε * deriv (yOf (L.T k.1.1)) t * (C.ch k).chi t +
          μ * (C.ch k).ε * (C.ch k).g.u t * deriv (C.ch k).chi t)) t := by
    refine ((hu.fun_pow 2).fun_add ((hu.const_mul (μ * (C.ch k).ε)).fun_mul hχ)).congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have hQ' : HasDerivAt (fun s => (C.ch k).g.u s ^ 3)
      (3 * (C.ch k).g.u t ^ 2 * deriv (yOf (L.T k.1.1)) t) t := by
    refine (hu.fun_pow 3).congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub]
  have hPe := Filter.eventuallyEq_of_mem hnhds fun s hs => (C.ul_chart_core_coords μ k hs).1
  have hQe := Filter.eventuallyEq_of_mem hnhds fun s hs => (C.ul_chart_core_coords μ k hs).2
  have e1 := (hP'.congr_of_eventuallyEq hPe).unique hP
  have e2 := (hQ'.congr_of_eventuallyEq hQe).unique hQ
  -- `3 u² u′ = 0` forces `u t = 0`, i.e. `t = t₀`
  have hu0 : (C.ch k).g.u t = 0 := by
    have h3 : (3 : ℝ) * (C.ch k).g.u t ^ 2 * deriv (yOf (L.T k.1.1)) t = 0 := by
      rw [e2]; ring
    rcases mul_eq_zero.mp h3 with h4 | h4
    · have : (C.ch k).g.u t ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    · exact absurd h4 hu'
  have ht0 : t = k.1.2 :=
    (C.ch k).g.u_injOn hJ (C.ch k).g.t₀_mem_J (by rw [hu0, (C.ch k).g.u_t₀])
  have hχ1 : (C.ch k).chi t = 1 := by rw [ht0]; exact (C.ch k).chi_cusp
  -- then `x′(t₀) = μ ε A u′(t₀) ≠ 0`
  rw [hu0, hχ1] at e1
  have h5 : μ * (C.ch k).ε * deriv (yOf (L.T k.1.1)) t = 0 := by
    have := e1; ring_nf at this ⊢; linarith
  rcases mul_eq_zero.mp h5 with h6 | h6
  · exact absurd h6 (mul_pos hμ hε).ne'
  · exact absurd h6 hu'

/-- "distinct parameters anywhere in that chart have different projected points at every λ"
(ce:cubic-difference: `Z = u³` is injective) -/
theorem arc_injOn (μ : ℝ) (k : L.cuspSet) :
    Set.InjOn (xzOf (C.core μ k.1.1)) (Set.Ioo (C.ch k).a (C.ch k).b) := by
  intro s hs t ht he
  have h1 := C.chart_core μ k hs
  have h2 := C.chart_core μ k ht
  rw [he, h2] at h1
  have h3 : (C.ch k).g.u t ^ 3 = (C.ch k).g.u s ^ 3 := (Prod.ext_iff.mp h1).2
  exact (C.ch k).g.u_injOn ((C.ch k).Icc_subset_J ⟨hs.1.le, hs.2.le⟩)
    ((C.ch k).Icc_subset_J ⟨ht.1.le, ht.2.le⟩) (GermData.cube_injective h3).symm

/-- "a moved point cannot meet a remote parameter … different modifications cannot meet each other
… together with strict local injectivity these facts exclude every new projected crossing" -/
theorem arc_no_crossing {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (k : L.cuspSet) {t : ℝ}
    (ht : t ∈ Set.Ioo (C.ch k).a (C.ch k).b) {q : Param c} (hq : ¬ SameParam (k.1.1, t) q) :
    xzOf (C.core μ q.1) q.2 ≠ xzOf (C.core μ k.1.1) t := by
  intro he
  have hin : xzOf (C.core μ k.1.1) t ∈ (C.ch k).U := C.inside hμ k ht
  by_cases hq' : ∃ k' : L.cuspSet, k'.1.1 = q.1 ∧
      ∃ n : ℤ, q.2 + n ∈ Set.Ioo (C.ch k').a (C.ch k').b
  · -- case 1/2: `q` lies (mod 1) on an open arc: the same arc (`arc_injOn`) or another (disjoint discs)
    obtain ⟨k', hk', n, hn⟩ := hq'
    have h1 : xzOf (C.core μ k'.1.1) (q.2 + n) ∈ (C.ch k').U := C.inside hμ k' hn
    have h2 : xzOf (C.core μ k'.1.1) (q.2 + n) = xzOf (C.core μ q.1) q.2 := by
      have := (C.coreLoop μ k'.1.1).eq_add_int n q.2
      simp only [coreLoop_γ] at this
      rw [this, hk']
    rw [h2, he] at h1
    have hkk : k = k' := by
      by_contra hne
      exact Set.disjoint_left.mp (C.disjoint k k' hne) hin h1
    rw [← hkk] at hn hk' h2
    have h3 : q.2 + n = t := C.arc_injOn μ k hn ht (by rw [h2, he])
    exact hq ⟨hk', -n, by push_cast; linarith⟩
  · -- case 3: `q` lies on no open arc, so it is an unmoved point of `L` in `U k`; `clean` puts it on
    -- the closed arc, hence at an END of the arc, whose `u`-value is `uMin` or `uMax`, while `u t`
    -- lies strictly between them; but `Z = u³` is injective
    push Not at hq'
    have hL : C.core μ q.1 q.2 = L.T q.1 q.2 := C.core_eq_of_notMem μ q.1 hq'
    have hxz : xzOf (L.T q.1) q.2 = xzOf (C.core μ k.1.1) t := by
      rw [← he]; simp only [xzOf, xOf, zOf, hL]
    have hin' : xzOf (L.T q.1) q.2 ∈ (C.ch k).U := hxz ▸ hin
    obtain ⟨hq1, n, hn⟩ := (C.ch k).clean hin'
    have hnot : q.2 + n ∉ Set.Ioo (C.ch k).a (C.ch k).b := hq' k hq1.symm n
    have hend : q.2 + n = (C.ch k).a ∨ q.2 + n = (C.ch k).b := by
      rcases eq_or_lt_of_le hn.1 with h1 | h1
      · exact Or.inl h1.symm
      · rcases eq_or_lt_of_le hn.2 with h2 | h2
        · exact Or.inr h2
        · exact absurd ⟨h1, h2⟩ hnot
    have hJ : q.2 + n ∈ (C.ch k).g.J := (C.ch k).Icc_subset_J hn
    have hper : xzOf (L.T k.1.1) (q.2 + n) = xzOf (L.T q.1) q.2 := by
      have := (L.projLoop k.1.1).eq_add_int n q.2
      simp only [projLoop_γ] at this
      rw [this, hq1]
    have hch := (C.ch k).g.chart_proj hJ
    rw [hper, hxz, C.chart_core μ k ht] at hch
    have h3 : (C.ch k).g.u t ^ 3 = (C.ch k).g.u (q.2 + n) ^ 3 := (Prod.ext_iff.mp hch).2
    have h4 : (C.ch k).g.u t = (C.ch k).g.u (q.2 + n) := GermData.cube_injective h3
    have hIoo := (C.ch k).g.u_mem_Ioo_of_mem (C.ch k).η_pos (C.ch k).η_lt ht
    rw [h4] at hIoo
    have ea : (C.ch k).a = k.1.2 - (C.ch k).η := rfl
    have eb : (C.ch k).b = k.1.2 + (C.ch k).η := rfl
    unfold GermData.uMin GermData.uMax at hIoo
    obtain ⟨h6, h7⟩ := hIoo
    rw [min_lt_iff] at h6
    rw [lt_max_iff] at h7
    rcases hend with h5 | h5
    · rw [h5, ea] at h6 h7
      rcases h6 with h6 | h6 <;> rcases h7 with h7 | h7 <;> linarith
    · rw [h5, eb] at h6 h7
      rcases h6 with h6 | h6 <;> rcases h7 with h7 | h7 <;> linarith

/-- on the collars of a cusp interval the rounded link is `L` (row 90's `collar`) -/
theorem core_on_collar (μ : ℝ) (k : L.cuspSet) {t : ℝ}
    (ht : t ∈ Set.Ioo (C.ch k).a ((C.ch k).a + ((C.ch k).η - (C.ch k).r)) ∪
      Set.Ioo ((C.ch k).b - ((C.ch k).η - (C.ch k).r)) (C.ch k).b) :
    C.core μ k.1.1 t = L.T k.1.1 t := by
  have hb := (C.ch k).b_eq
  have hr := (C.ch k).r_pos
  have hη := (C.ch k).η_pos
  have hmem : t ∈ Set.Ioo (C.ch k).a (C.ch k).b := by
    rcases ht with h | h
    · exact ⟨h.1, by linarith [h.2]⟩
    · exact ⟨by linarith [h.1], h.2⟩
  rw [C.core_on_arc μ k hmem, (C.ch k).disp_eq_zero_of_chi μ ((C.ch k).chi_eq_zero_on_collar ht),
    add_zero]

/-- U-L helper: the cutoff of a cusp vanishes at a parameter whose orbit avoids the closed support
interval `[t₀ − r, t₀ + r]` (`periodicBump_eq_zero`) -/
theorem ul_chi_eq_zero_of_notMem_Icc {k : L.cuspSet} (ch : L.CuspChoice k) {s : ℝ}
    (h : ∀ n : ℤ, s + n ∉ Set.Icc (k.1.2 - ch.r) (k.1.2 + ch.r)) : ch.chi s = 0 := by
  unfold CuspChoice.chi
  apply periodicBump_eq_zero ch.r_pos ch.r_lt_half
  intro n
  have hr := ch.r_pos
  have hn := h (-n)
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hn
  push_cast at hn
  rcases hn with h1 | h1
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- **U-L leaf.** a parameter whose orbit avoids every open cusp arc of its circle has a neighbourhood
on which the rounded link is `L`: the cutoffs are supported in the compact sub-arcs `[t₀ − r, t₀ + r]`
(`periodicBump_eq_zero`), whose integer translates form a closed set (`eventually_add_int_notMem_Icc`),
and there are finitely many cusps (`Filter.eventually_all`) -/
theorem core_eventuallyEq_of_notMem (μ : ℝ) (i : Fin c) {t : ℝ}
    (h : ∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (C.ch k).a (C.ch k).b) :
    C.core μ i =ᶠ[nhds t] L.T i := by
  letI : Fintype L.cuspSet := C.fin
  have hr : ∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ,
      t + n ∉ Set.Icc (k.1.2 - (C.ch k).r) (k.1.2 + (C.ch k).r) := by
    intro k hk n hn
    apply h k hk n
    have := (C.ch k).r_lt
    exact ⟨by unfold CuspChoice.a; linarith [hn.1], by unfold CuspChoice.b; linarith [hn.2]⟩
  have hev : ∀ᶠ (s : ℝ) in nhds t, ∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ,
      s + (n : ℝ) ∉ Set.Icc (k.1.2 - (C.ch k).r) (k.1.2 + (C.ch k).r) := by
    rw [Filter.eventually_all]
    intro k
    by_cases hk : k.1.1 = i
    · have := eventually_add_int_notMem_Icc (by linarith [(C.ch k).r_pos]) (hr k hk)
      exact this.mono fun s hs _ => hs
    · exact Filter.Eventually.of_forall fun s hk' => absurd hk' hk
  refine hev.mono fun s hs => ?_
  show C.core μ i s = L.T i s
  unfold core
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  intro k _
  split_ifs with hk
  · exact (C.ch k).disp_eq_zero_of_chi μ (ul_chi_eq_zero_of_notMem_Icc (C.ch k) (hs k hk))
  · rfl

/-- **U-L leaf.** a parameter whose orbit avoids every open cusp arc of its circle is not a cusp: a
zero of the projected velocity at `t` puts `(i, fract t)` into `cuspSet` (the velocity is 1-periodic),
and every cusp lies strictly inside its own arc (`a_lt`, `lt_b`) -/
theorem deriv_xz_ne_zero_of_notMem (i : Fin c) {t : ℝ}
    (h : ∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (C.ch k).a (C.ch k).b) :
    deriv (xzOf (L.T i)) t ≠ 0 := by
  intro hd
  have e : Int.fract t = t + ((-⌊t⌋ : ℤ) : ℝ) := by rw [← Int.self_sub_floor]; push_cast; ring
  have hmem : (i, Int.fract t) ∈ L.cuspSet := by
    refine ⟨⟨Int.fract_nonneg t, Int.fract_lt_one t⟩, ?_⟩
    show deriv (xzOf (L.T i)) (Int.fract t) = 0
    rw [e, ← projLoop_γ, (L.projLoop i).deriv_eq_add_int, projLoop_γ]
    exact hd
  apply h ⟨(i, Int.fract t), hmem⟩ rfl (-⌊t⌋)
  rw [← e]
  exact ⟨(C.ch ⟨(i, Int.fract t), hmem⟩).a_lt, (C.ch ⟨(i, Int.fract t), hmem⟩).lt_b⟩

/-- "For positive λ the result is therefore precisely a finite regular generic diagram": the projected
velocity of a positive slice vanishes nowhere — on the open arcs by `arc_regular`, elsewhere it is
`L`'s, and `L` has no cusp there -/
theorem core_xz_regular {μ : ℝ} (hμ : 0 < μ) (i : Fin c) (t : ℝ) :
    deriv (xzOf (C.core μ i)) t ≠ 0 := by
  by_cases hout : ∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (C.ch k).a (C.ch k).b
  · have he : xzOf (C.core μ i) =ᶠ[nhds t] xzOf (L.T i) :=
      (C.core_eventuallyEq_of_notMem μ i hout).fun_comp (fun v : Space => (v.1, v.2.2))
    rw [he.deriv_eq]
    exact C.deriv_xz_ne_zero_of_notMem i hout
  · push Not at hout
    obtain ⟨k, hk, n, hn⟩ := hout
    have hreg := C.arc_regular hμ k hn
    have hper := (C.coreLoop μ k.1.1).deriv_eq_add_int n t
    simp only [coreLoop_γ] at hper
    rw [hper] at hreg
    rw [← hk]
    exact hreg

/-- the clean cusp smoothing witness at every time `0 < μ ≤ 1` — the library's `CleanCuspSmoothing`
(row 90), including its `collar` clause -/
def smoothing {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) : L.CleanCuspSmoothing (C.coreLoop μ) where
  U := fun k => (C.ch k).U
  a := fun k => (C.ch k).a
  b := fun k => (C.ch k).b
  disc := fun k => (C.ch k).isDisc_U
  center := fun k => (C.ch k).center_mem_interior_U
  disjoint := C.disjoint
  a_lt := fun k => (C.ch k).a_lt
  lt_b := fun k => (C.ch k).lt_b
  len := fun k => (C.ch k).len
  clean := fun k q hq => (C.ch k).clean hq
  arc_in := fun k t ht => (C.ch k).arc_in ht
  arc_simple := fun k t ht q hq => (C.ch k).arc_simple ht hq
  agree := fun i t h => by
    show xzOf (C.core μ i) t = xzOf (L.T i) t
    rw [xzOf, xzOf, xOf, zOf, xOf, zOf, C.core_eq_of_notMem μ i h]
  collar := fun k => ⟨(C.ch k).η - (C.ch k).r, by linarith [(C.ch k).r_lt], fun t ht => by
    show xzOf (C.core μ k.1.1) t = xzOf (L.T k.1.1) t
    rw [xzOf, xzOf, xOf, zOf, xOf, zOf, C.core_on_collar μ k ht]⟩
  inside := fun k t ht => C.inside ⟨hμ.le, hμ1⟩ k ht
  regular := fun k t ht => C.arc_regular hμ k ht
  simple := fun k => C.arc_injOn μ k
  no_crossing := fun k t ht q hq => C.arc_no_crossing ⟨hμ.le, hμ1⟩ k ht hq

end Choices

/-! ### 4.7 The slices are spatial embeddings (sm-3:3145-3153) and the family -/

namespace Choices

variable {L} (C : L.Choices)

/-- two `SmoothLoop`s with the same map are equal -/
theorem _root_.SM.SmoothLoop.ext' {a b : SmoothLoop} (h : a.γ = b.γ) : a = b := by
  cases a; cases b; cases h; rfl

theorem coreLoop_zero : C.coreLoop 0 = L.projLoop := by
  funext i
  apply SmoothLoop.ext'
  show xzOf (C.core 0 i) = xzOf (L.T i)
  rw [C.core_zero]

/-- "Spatial injectivity follows for the whole family": a spatial coincidence would project to a new
coincidence (excluded) or to an old double point (distinct unchanged heights) -/
theorem core_embedded (h : L.CuspedProjection) {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1)
    (i j : Fin c) (s t : ℝ) (he : C.core μ i s = C.core μ j t) : i = j ∧ SameT s t := by
  by_contra hne
  have hns : ¬ SameParam (i, s) (j, t) := fun ⟨h1, n, hn⟩ => hne ⟨h1, n, hn⟩
  have hxz : xzOf (C.core μ i) s = xzOf (C.core μ j) t := by
    simp only [xzOf, xOf, zOf, he]
  have hy : yOf (C.core μ i) s = yOf (C.core μ j) t := by simp only [yOf, he]
  rw [C.yOf_core, C.yOf_core] at hy
  have hd : IsDoubleOf L.projLoop (i, s) (j, t) := by
    rcases eq_or_lt_of_le hμ.1 with h0 | h0
    · subst h0
      refine ⟨hns, ?_⟩
      show xzOf (L.T i) s = xzOf (L.T j) t
      rwa [C.core_zero] at hxz
    · exact ((C.smoothing h0 hμ.2).isDoubleOf_iff (i, s) (j, t)).mp ⟨hns, hxz⟩
  exact h.heights_distinct _ _ hd hy

/-- the derivative of a smooth spatial map is the triple of the derivatives of its coordinates (the
pattern of the accepted `TransverseKnot.deriv_T`) -/
theorem _root_.SM.deriv_space {T : ℝ → Space} (hT : ContDiff ℝ ∞ T) (t : ℝ) :
    deriv T t = (deriv (xOf T) t, deriv (yOf T) t, deriv (zOf T) t) := by
  have hx : HasDerivAt (xOf T) (deriv (xOf T) t) t :=
    ((hT.fst).differentiable (by simp) t).hasDerivAt
  have hy : HasDerivAt (yOf T) (deriv (yOf T) t) t :=
    ((hT.snd.fst).differentiable (by simp) t).hasDerivAt
  have hz : HasDerivAt (zOf T) (deriv (zOf T) t) t :=
    ((hT.snd.snd).differentiable (by simp) t).hasDerivAt
  exact (hx.prodMk (hy.prodMk hz)).deriv

/-- and the derivative of its `xz` projection is the pair (`TransverseKnot.deriv_xz`) -/
theorem _root_.SM.deriv_xzOf {T : ℝ → Space} (hT : ContDiff ℝ ∞ T) (t : ℝ) :
    deriv (xzOf T) t = (deriv (xOf T) t, deriv (zOf T) t) := by
  have hx : HasDerivAt (xOf T) (deriv (xOf T) t) t :=
    ((hT.fst).differentiable (by simp) t).hasDerivAt
  have hz : HasDerivAt (zOf T) (deriv (zOf T) t) t :=
    ((hT.snd.snd).differentiable (by simp) t).hasDerivAt
  exact (hx.prodMk hz).deriv

/-- "Spatial immersion holds for every λ": the projected velocity is nonzero for `μ > 0`
(`core_xz_regular`), and at `μ = 0` the link is `L` -/
theorem core_regular (_h : L.CuspedProjection) {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (i : Fin c)
    (t : ℝ) : deriv (C.core μ i) t ≠ 0 := by
  rcases eq_or_lt_of_le hμ.1 with h0 | h0
  · subst h0; rw [C.core_zero]; exact L.regular i t
  · intro h0'
    apply C.core_xz_regular h0 i t
    rw [deriv_space (C.core_contDiff μ i)] at h0'
    rw [deriv_xzOf (C.core_contDiff μ i)]
    have h1 := (Prod.ext_iff.mp h0').1
    have h2 := (Prod.ext_iff.mp (Prod.ext_iff.mp h0').2).2
    simp only [Prod.fst_zero, Prod.snd_zero] at h1 h2
    rw [h1, h2]
    rfl

def slice (h : L.CuspedProjection) {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) : SpatialLink c where
  T := C.core μ
  smooth := C.core_contDiff μ
  periodic := C.core_periodic μ
  embedded := C.core_embedded h ⟨h0, h1⟩
  regular := C.core_regular h ⟨h0, h1⟩

@[simp] theorem slice_T (h : L.CuspedProjection) {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) :
    (C.slice h h0 h1).T = C.core μ := rfl

theorem slice_projLoop (h : L.CuspedProjection) {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) :
    (C.slice h h0 h1).projLoop = C.coreLoop μ := by
  funext i
  apply SmoothLoop.ext'
  rfl

theorem slice_height (h : L.CuspedProjection) {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (p : Param c) :
    (C.slice h h0 h1).height p = L.height p := by
  show yOf (C.core μ p.1) p.2 = yOf (L.T p.1) p.2
  rw [C.yOf_core]

/-- the printed family in the clamped time `μ = φ(λ)`, `φ = Real.smoothTransition` -/
def fam (h : L.CuspedProjection) : SpatialFamily c where
  G := fun lam => C.slice h (Real.smoothTransition.nonneg lam) (Real.smoothTransition.le_one lam)
  joint_smooth := C.core_joint_contDiff

theorem fam_G (h : L.CuspedProjection) (lam : ℝ) :
    (C.fam h).G lam = C.slice h (Real.smoothTransition.nonneg lam) (Real.smoothTransition.le_one lam) :=
  rfl

theorem fam_zero (h : L.CuspedProjection) : (C.fam h).G 0 = L := by
  apply ext'
  rw [fam_G, slice_T, Real.smoothTransition.zero, C.core_zero]

/-- for `λ > 0` the slice of the family is a positive slice `μ ∈ (0, 1]` -/
theorem smoothTransition_mem {lam : ℝ} (hlam : 0 < lam) :
    0 < Real.smoothTransition lam ∧ Real.smoothTransition lam ≤ 1 :=
  ⟨Real.smoothTransition.pos_of_pos hlam, Real.smoothTransition.le_one lam⟩

/-- every positive slice is an ordinary finite regular generic diagram (the library's
`CleanCuspSmoothing` consequences, SM/CeSmoothingRecord.lean §2, on the witness `smoothing`) -/
theorem slice_generic (h : L.CuspedProjection) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    (C.slice h hμ.le hμ1).RegularGenericProjection := by
  have ρ := C.smoothing hμ hμ1
  have hpl := C.slice_projLoop h hμ.le hμ1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i t
    exact C.core_xz_regular hμ i t
  · rw [hpl, ρ.occSetOf_eq]; exact h.doubles_finite
  · intro p q hd
    rw [hpl] at hd
    have hd' := (ρ.isDoubleOf_iff p q).mp hd
    have h1 := ρ.deriv_eq_of_isDouble h.cusps_finite hd'
    have h2 := ρ.deriv_eq_of_isDouble h.cusps_finite hd'.symm
    simp only [coreLoop_γ] at h1 h2
    rw [slice_T, h1, h2]
    exact h.transverse p q hd'
  · intro p q r hpq hqr hpr
    rw [hpl] at hpq hqr hpr
    exact h.no_triple p q r ((ρ.isDoubleOf_iff p q).mp hpq) ((ρ.isDoubleOf_iff q r).mp hqr)
      ((ρ.isDoubleOf_iff p r).mp hpr)
  · intro p q hd
    rw [hpl] at hd
    rw [C.slice_height, C.slice_height]
    exact h.heights_distinct p q ((ρ.isDoubleOf_iff p q).mp hd)

/-! ### 4.8 Existence of the choices (sm-3:3073-3096) -/

end Choices

/-- distinct cusps have distinct images (a common image would be a double point at a cusp,
excluded by `transverse`) -/
theorem cusp_image_injective (h : L.CuspedProjection) (k k' : L.cuspSet)
    (he : xzOf (L.T k.1.1) k.1.2 = xzOf (L.T k'.1.1) k'.1.2) : k = k' := by
  by_contra hne
  have hk : k.1.2 ∈ Set.Ico (0 : ℝ) 1 ∧ L.IsCusp k.1.1 k.1.2 := k.2
  have hk' : k'.1.2 ∈ Set.Ico (0 : ℝ) 1 ∧ L.IsCusp k'.1.1 k'.1.2 := k'.2
  have hns : ¬ SameParam k.1 k'.1 := fun hs =>
    hne (Subtype.ext (SameParam.eq_of_mem_Ico hk.1 hk'.1 hs))
  have hd : IsDoubleOf L.projLoop k.1 k'.1 := ⟨hns, he⟩
  exact CuspedProjection.not_isCusp_of_isDouble L h hd hk.2

/-- finitely many distinct cusp images have a positive minimal gap -/
theorem exists_gap (h : L.CuspedProjection) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ k k' : L.cuspSet, k ≠ k' →
      2 * gap < dist (xzOf (L.T k.1.1) k.1.2) (xzOf (L.T k'.1.1) k'.1.2) := by
  have : Fintype L.cuspSet := h.cusps_finite.fintype
  set S : Finset (L.cuspSet × L.cuspSet) := Finset.univ.filter (fun p => p.1 ≠ p.2) with hS
  by_cases hne : S.Nonempty
  · obtain ⟨p₀, hp₀, hmin⟩ := S.exists_min_image
      (fun p => dist (xzOf (L.T p.1.1.1) p.1.1.2) (xzOf (L.T p.2.1.1) p.2.1.2)) hne
    have hp₀ne : p₀.1 ≠ p₀.2 := (Finset.mem_filter.mp hp₀).2
    have hpos : 0 < dist (xzOf (L.T p₀.1.1.1) p₀.1.1.2) (xzOf (L.T p₀.2.1.1) p₀.2.1.2) := by
      rw [dist_pos]
      intro heq
      exact hp₀ne (L.cusp_image_injective h _ _ heq)
    refine ⟨dist (xzOf (L.T p₀.1.1.1) p₀.1.1.2) (xzOf (L.T p₀.2.1.1) p₀.2.1.2) / 4,
      div_pos hpos (by norm_num), fun k k' hkk' => ?_⟩
    have := hmin (k, k') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkk'⟩)
    linarith
  · refine ⟨1, one_pos, fun k k' hkk' => ?_⟩
    exact absurd ⟨(k, k'), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkk'⟩⟩ hne

/-- **U-E helper.** the Lipschitz constant `|A| (2 + |y₀|)` of the inverse chart is positive -/
theorem ue_lip_pos {i : Fin c} {t₀ : ℝ} (g : L.GermData i t₀) : 0 < |g.A| * (2 + |g.y₀|) :=
  mul_pos (abs_pos.mpr g.A_ne) (by positivity)

/-- **U-E helper.** the inverse chart is Lipschitz (sup norm) with constant `|A| (2 + |y₀|)`,
measured from the cusp image `unchart 0` -/
theorem ue_norm_unchart_sub_le {i : Fin c} {t₀ : ℝ} (g : L.GermData i t₀) (w : Plane) :
    ‖g.unchart w - xzOf (L.T i) t₀‖ ≤ |g.A| * (2 + |g.y₀|) * ‖w‖ := by
  have h1 : |w.1| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using norm_fst_le w
  have h2 : |w.2| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using norm_snd_le w
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  have hA : 0 ≤ |g.A| := abs_nonneg _
  have hy : 0 ≤ |g.y₀| := abs_nonneg _
  rw [norm_prod_le_iff]
  constructor
  · simp only [GermData.unchart, xzOf, xOf, zOf, GermData.x₀, Prod.fst_sub, Real.norm_eq_abs,
      add_sub_cancel_left, abs_mul]
    calc |g.A| * |w.1| ≤ |g.A| * ‖w‖ := mul_le_mul_of_nonneg_left h1 hA
      _ ≤ |g.A| * (2 + |g.y₀|) * ‖w‖ := by nlinarith [mul_nonneg hA hw, mul_nonneg (mul_nonneg hA hw) hy]
  · simp only [GermData.unchart, xzOf, xOf, zOf, GermData.z₀, Prod.snd_sub, Real.norm_eq_abs]
    rw [show (L.T i t₀).2.2 + g.y₀ * g.A * w.1 + 2 * g.A / 3 * w.2 - (L.T i t₀).2.2
        = g.y₀ * g.A * w.1 + 2 * g.A / 3 * w.2 by ring]
    calc |g.y₀ * g.A * w.1 + 2 * g.A / 3 * w.2|
        ≤ |g.y₀ * g.A * w.1| + |2 * g.A / 3 * w.2| := abs_add_le _ _
      _ = |g.y₀| * |g.A| * |w.1| + 2 * |g.A| / 3 * |w.2| := by
          rw [abs_mul, abs_mul, abs_mul, abs_div, abs_mul, abs_two, abs_of_pos (by norm_num : (0:ℝ) < 3)]
      _ ≤ |g.y₀| * |g.A| * ‖w‖ + 2 * |g.A| / 3 * ‖w‖ := by
          gcongr
      _ ≤ |g.A| * (2 + |g.y₀|) * ‖w‖ := by nlinarith [mul_nonneg hA hw]

/-- "Its distance from that complement is positive": the cusp image is not in the compact projected
image of the complement of the chart interval (nor of the other circles), so its normalized distance
is positive -/
theorem exists_remote_clearance (h : L.CuspedProjection) (k : L.cuspSet)
    (g : L.GermData k.1.1 k.1.2) :
    ∃ d : ℝ, 0 < d ∧ ∀ q : Param c, (q.1 ≠ k.1.1 ∨ ∀ n : ℤ, q.2 + n ∉ g.J) →
      d < ‖g.chart (xzOf (L.T q.1) q.2)‖ := by
  -- the evaluation map on parameters is continuous (discrete circle index)
  have hFc : Continuous (fun q : Param c => xzOf (L.T q.1) q.2) :=
    continuous_prod_of_discrete_left.mpr (fun j => (L.projLoop j).continuous)
  -- the compact set of remote parameters
  have hS₁c : IsCompact (Set.Icc (k.1.2 - 1 / 2) (k.1.2 + 1 / 2) ∩ {t : ℝ | ∀ n : ℤ, t + n ∉ g.J}) := by
    apply isCompact_Icc.inter_right
    have : {t : ℝ | ∀ n : ℤ, t + n ∉ g.J} = ⋂ n : ℤ, (fun t : ℝ => t + (n : ℝ)) ⁻¹' (g.J)ᶜ := by
      ext t; simp
    rw [this]
    exact isClosed_iInter (fun n => g.isOpen_J.isClosed_compl.preimage (continuous_add_const _))
  have hKpc : IsCompact (({k.1.1} ×ˢ (Set.Icc (k.1.2 - 1 / 2) (k.1.2 + 1 / 2) ∩
      {t : ℝ | ∀ n : ℤ, t + n ∉ g.J})) ∪ ({j : Fin c | j ≠ k.1.1} ×ˢ Set.Icc (0 : ℝ) 1)) :=
    (isCompact_singleton.prod hS₁c).union ((Set.toFinite _).isCompact.prod isCompact_Icc)
  have hKc := hKpc.image hFc
  -- the cusp image is not in its projected image (`transverse`: no double point at a cusp)
  have hk : k.1.2 ∈ Set.Ico (0 : ℝ) 1 ∧ L.IsCusp k.1.1 k.1.2 := k.2
  have hp₀ : xzOf (L.T k.1.1) k.1.2 ∉ (fun q : Param c => xzOf (L.T q.1) q.2) ''
      (({k.1.1} ×ˢ (Set.Icc (k.1.2 - 1 / 2) (k.1.2 + 1 / 2) ∩ {t : ℝ | ∀ n : ℤ, t + n ∉ g.J})) ∪
        ({j : Fin c | j ≠ k.1.1} ×ˢ Set.Icc (0 : ℝ) 1)) := by
    rintro ⟨q, hq, hFq⟩
    have hns : ¬ SameParam k.1 q := by
      rintro ⟨h1, n, hn⟩
      rcases hq with ⟨_, _, hJ⟩ | ⟨hj, _⟩
      · apply hJ (-n)
        rw [hn]; push_cast
        simpa using g.t₀_mem_J
      · exact hj h1.symm
    have hd : IsDoubleOf L.projLoop k.1 q := ⟨hns, hFq.symm⟩
    exact CuspedProjection.not_isCusp_of_isDouble L h hd hk.2
  -- a ball about the cusp image misses that compact set
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hKc.isClosed.isOpen_compl _ hp₀
  have hlip := L.ue_lip_pos g
  refine ⟨ε / (2 * (|g.A| * (2 + |g.y₀|))), by positivity, fun q hq => ?_⟩
  -- every remote parameter has a representative in the compact set
  have hmem : ∃ q' ∈ ({k.1.1} ×ˢ (Set.Icc (k.1.2 - 1 / 2) (k.1.2 + 1 / 2) ∩
      {t : ℝ | ∀ n : ℤ, t + n ∉ g.J})) ∪ ({j : Fin c | j ≠ k.1.1} ×ˢ Set.Icc (0 : ℝ) 1),
      xzOf (L.T q'.1) q'.2 = xzOf (L.T q.1) q.2 := by
    by_cases hqi : q.1 = k.1.1
    · have hJ : ∀ n : ℤ, q.2 + n ∉ g.J := hq.resolve_left (not_not.mpr hqi)
      refine ⟨(k.1.1, q.2 + round (k.1.2 - q.2)), Or.inl ⟨rfl, ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · have := abs_sub_round (k.1.2 - q.2)
        rw [abs_le] at this
        linarith [this.1, this.2]
      · have := abs_sub_round (k.1.2 - q.2)
        rw [abs_le] at this
        linarith [this.1, this.2]
      · intro n hn
        apply hJ (round (k.1.2 - q.2) + n)
        push_cast
        rwa [← add_assoc]
      · show xzOf (L.T k.1.1) (q.2 + ((round (k.1.2 - q.2) : ℤ) : ℝ)) = xzOf (L.T q.1) q.2
        rw [L.xz_add_int, hqi]
    · refine ⟨(q.1, Int.fract q.2), Or.inr ⟨hqi, Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, ?_⟩
      show xzOf (L.T q.1) (Int.fract q.2) = xzOf (L.T q.1) q.2
      have e : Int.fract q.2 = q.2 + ((-⌊q.2⌋ : ℤ) : ℝ) := by
        rw [← Int.self_sub_floor]; push_cast; ring
      rw [e, L.xz_add_int]
  obtain ⟨q', hq', hFq'⟩ := hmem
  have hin : xzOf (L.T q.1) q.2 ∈ (fun q : Param c => xzOf (L.T q.1) q.2) ''
      (({k.1.1} ×ˢ (Set.Icc (k.1.2 - 1 / 2) (k.1.2 + 1 / 2) ∩ {t : ℝ | ∀ n : ℤ, t + n ∉ g.J})) ∪
        ({j : Fin c | j ≠ k.1.1} ×ˢ Set.Icc (0 : ℝ) 1)) := ⟨q', hq', hFq'⟩
  have hnot : xzOf (L.T q.1) q.2 ∉ Metric.ball (xzOf (L.T k.1.1) k.1.2) ε := fun hb => hball hb hin
  rw [Metric.mem_ball, not_lt, dist_eq_norm] at hnot
  -- transport through the affine chart: `‖p − p₀‖ ≤ lip · ‖chart p‖`
  have hL := L.ue_norm_unchart_sub_le g (g.chart (xzOf (L.T q.1) q.2))
  rw [g.unchart_chart] at hL
  have hεle : ε ≤ |g.A| * (2 + |g.y₀|) * ‖g.chart (xzOf (L.T q.1) q.2)‖ := le_trans hnot hL
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- "Choose b > 0 so small that the closed subarc lies inside V": by continuity of `u` at `t₀` the
rectangle radius tends to `0` with `η`, and the physical neighbourhood `U` shrinks to the cusp
image -/
theorem exists_eta (k : L.cuspSet) (g : L.GermData k.1.1 k.1.2) {d ρ₀ : ℝ} (hd : 0 < d)
    (hρ₀ : 0 < ρ₀) :
    ∃ η : ℝ, 0 < η ∧ η < g.δ ∧ g.radius η < d ∧
      g.unchart '' g.rect η ⊆ Metric.closedBall (xzOf (L.T k.1.1) k.1.2) ρ₀ := by
  have hlip : 0 < |g.A| * (2 + |g.y₀|) := L.ue_lip_pos g
  -- the target size of `|u|` at the ends
  set ε₁ : ℝ := min 1 (min (d / 2) (ρ₀ / (2 * (|g.A| * (2 + |g.y₀|))))) with hε₁
  have hε₁_pos : 0 < ε₁ := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hε₁_le1 : ε₁ ≤ 1 := min_le_left _ _
  have hε₁_led : ε₁ ≤ d / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε₁_leρ : ε₁ ≤ ρ₀ / (2 * (|g.A| * (2 + |g.y₀|))) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hρ : ε₁ * (2 * (|g.A| * (2 + |g.y₀|))) ≤ ρ₀ := (le_div_iff₀ (by positivity)).mp hε₁_leρ
  -- continuity of `u` at `t₀`, `u t₀ = 0`
  have hcont : ContinuousAt g.u k.1.2 := g.u_smooth.continuous.continuousAt
  obtain ⟨η₁, hη₁, hu⟩ := Metric.continuousAt_iff.mp hcont ε₁ hε₁_pos
  set η : ℝ := min (η₁ / 2) (g.δ / 2) with hη
  have hη_pos : 0 < η := lt_min (by linarith) (by linarith [g.δ_pos])
  have hη_lt₁ : η < η₁ := (min_le_left _ _).trans_lt (by linarith)
  have hη_ltδ : η < g.δ := (min_le_right _ _).trans_lt (by linarith [g.δ_pos])
  -- the end values of `u` are small
  have huL : |g.u (k.1.2 - η)| < ε₁ := by
    have := hu (x := k.1.2 - η) (by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
    rwa [g.u_t₀, Real.dist_eq, sub_zero] at this
  have huR : |g.u (k.1.2 + η)| < ε₁ := by
    have := hu (x := k.1.2 + η) (by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
    rwa [g.u_t₀, Real.dist_eq, sub_zero] at this
  have hM : g.M η < ε₁ := by
    unfold GermData.M GermData.uMin GermData.uMax
    apply max_lt
    · exact (abs_min_le_max_abs_abs).trans_lt (max_lt huL huR)
    · exact (abs_max_le_max_abs_abs).trans_lt (max_lt huL huR)
  have hM0 : 0 ≤ g.M η := le_trans (abs_nonneg _) (le_max_left _ _)
  have hM1 : g.M η ≤ 1 := by linarith
  have hM2 : g.M η ^ 2 ≤ g.M η := by nlinarith
  have hM3 : g.M η ^ 3 ≤ g.M η := by nlinarith
  have hrad : g.radius η ≤ 2 * g.M η := by
    unfold GermData.radius
    apply max_le <;> linarith
  refine ⟨η, hη_pos, hη_ltδ, ?_, ?_⟩
  · linarith
  · rintro p ⟨w, hw, rfl⟩
    have hwn : ‖w‖ ≤ g.radius η := by
      have := g.rect_subset_closedBall η hw
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hL := L.ue_norm_unchart_sub_le g w
    have hlipw : |g.A| * (2 + |g.y₀|) * ‖w‖ ≤ |g.A| * (2 + |g.y₀|) * (2 * g.M η) :=
      mul_le_mul_of_nonneg_left (hwn.trans hrad) hlip.le
    nlinarith

/-- the choices at one cusp, with the clean neighbourhood inside a prescribed ball about the cusp
image -/
theorem exists_cuspChoice_within (h : L.CuspedProjection) (k : L.cuspSet) {ρ₀ : ℝ}
    (hρ₀ : 0 < ρ₀) :
    ∃ ch : L.CuspChoice k, ch.U ⊆ Metric.closedBall (xzOf (L.T k.1.1) k.1.2) ρ₀ := by
  obtain ⟨g⟩ := L.exists_germData (h.exact_germ k.1 k.2)
  obtain ⟨d, hd, hremote⟩ := L.exists_remote_clearance h k g
  obtain ⟨η, hη, hηδ, hrad, hsub⟩ := L.exists_eta k g hd hρ₀
  refine ⟨⟨g, η, η / 2, g.M η, hη, hηδ, by linarith, by linarith, g.M_pos hη hηδ, le_rfl,
    fun q hq => lt_trans hrad (hremote q hq)⟩, ?_⟩
  exact hsub

/-- "Make these choices at each of the finitely many cusps": the package of choices exists -/
theorem exists_choices (h : L.CuspedProjection) : Nonempty L.Choices := by
  obtain ⟨gap, hgap, hsep⟩ := L.exists_gap h
  have hch : ∀ k : L.cuspSet, ∃ ch : L.CuspChoice k,
      ch.U ⊆ Metric.closedBall (xzOf (L.T k.1.1) k.1.2) gap :=
    fun k => L.exists_cuspChoice_within h k hgap
  choose ch hch using hch
  refine ⟨{ fin := h.cusps_finite.fintype, ch := ch, disjoint := ?_ }⟩
  intro k k' hne
  apply Set.disjoint_of_subset (hch k) (hch k')
  exact Metric.closedBall_disjoint_closedBall (by linarith [hsep k k' hne])

/-! ## 5. Assembly: the witness from the choices (sm-3:3097-3170) -/

namespace Choices

variable {L} (C : L.Choices)

/-- the `CuspRoundingWitness` delivered by the construction -/
def witness (h : L.CuspedProjection) : CuspRoundingWitness L where
  fam := C.fam h
  start := C.fam_zero h
  a := fun k => (C.ch k).a
  b := fun k => (C.ch k).b
  a_lt := fun k => (C.ch k).a_lt
  lt_b := fun k => (C.ch k).lt_b
  len := fun k => (C.ch k).len
  intervals_disjoint := fun k k' hne hi => by
    simpa using C.arcs_disjoint_circle k k' hne hi 0
  fixed_outside := fun lam i t ht => C.core_eq_of_notMem _ i ht
  generic := fun lam hlam _ =>
    C.slice_generic h (smoothTransition_mem hlam).1 (smoothTransition_mem hlam).2
  clean := fun lam hlam _ => by
    rw [fam_G, C.slice_projLoop]
    exact ⟨C.smoothing (smoothTransition_mem hlam).1 (smoothTransition_mem hlam).2⟩
  same_doubles := fun lam hlam _ p q => by
    rw [fam_G, C.slice_projLoop]
    exact (C.smoothing (smoothTransition_mem hlam).1 (smoothTransition_mem hlam).2).isDoubleOf_iff p q
  same_data := fun lam hlam _ p q hd => by
    refine ⟨?_, ?_⟩
    · rw [fam_G, C.slice_projLoop]
      exact (C.smoothing (smoothTransition_mem hlam).1
        (smoothTransition_mem hlam).2).crossSignOf_eq h.cusps_finite hd
    · rw [fam_G, C.slice_height, C.slice_height]
  intervals_disjoint_circle := C.arcs_disjoint_circle
  U := fun k => (C.ch k).U
  clean_in := fun lam hlam _ => by
    rw [fam_G, C.slice_projLoop]
    exact ⟨C.smoothing (smoothTransition_mem hlam).1 (smoothTransition_mem hlam).2, rfl, rfl, rfl⟩

end Choices

/-- the existence sentence of ce:rounding -/
theorem exists_cuspRoundingWitness (h : L.CuspedProjection) : Nonempty (CuspRoundingWitness L) := by
  obtain ⟨C⟩ := L.exists_choices h
  exact ⟨C.witness h⟩

/-! ### "With no cusps take the constant family." (sm-3:3054) -/

section NoCusps

variable (h0 : L.cuspSet = ∅)
include h0

theorem noCusp (k : L.cuspSet) : False := by
  obtain ⟨p, hp⟩ := k
  rw [h0] at hp
  exact hp

/-- a cuspless link has a regular projection everywhere (every parameter reduces to the fundamental
period, where no cusp exists) -/
theorem regular_of_no_cusps (i : Fin c) (t : ℝ) : deriv (xzOf (L.T i)) t ≠ 0 := by
  intro hd
  have hmem : (i, Int.fract t) ∈ L.cuspSet := by
    refine ⟨⟨Int.fract_nonneg t, Int.fract_lt_one t⟩, ?_⟩
    show deriv (xzOf (L.T i)) (Int.fract t) = 0
    have e : Int.fract t = t + ((-⌊t⌋ : ℤ) : ℝ) := by rw [← Int.self_sub_floor]; push_cast; ring
    rw [e, ← projLoop_γ, (L.projLoop i).deriv_eq_add_int, projLoop_γ]
    exact hd
  rw [h0] at hmem
  exact hmem

/-- the trivial clean smoothing of a cuspless projection (no arcs, nothing replaced) -/
def constSmoothing : L.CleanCuspSmoothing L.projLoop where
  U := fun k => (L.noCusp h0 k).elim
  a := fun k => (L.noCusp h0 k).elim
  b := fun k => (L.noCusp h0 k).elim
  disc := fun k => (L.noCusp h0 k).elim
  center := fun k => (L.noCusp h0 k).elim
  disjoint := fun k => (L.noCusp h0 k).elim
  a_lt := fun k => (L.noCusp h0 k).elim
  lt_b := fun k => (L.noCusp h0 k).elim
  len := fun k => (L.noCusp h0 k).elim
  clean := fun k => (L.noCusp h0 k).elim
  arc_in := fun k => (L.noCusp h0 k).elim
  arc_simple := fun k => (L.noCusp h0 k).elim
  agree := fun _ _ _ => rfl
  collar := fun k => (L.noCusp h0 k).elim
  inside := fun k => (L.noCusp h0 k).elim
  regular := fun k => (L.noCusp h0 k).elim
  simple := fun k => (L.noCusp h0 k).elim
  no_crossing := fun k => (L.noCusp h0 k).elim

/-- the constant family is a witness for a cuspless `L` of the class -/
def constWitness (h : L.CuspedProjection) : CuspRoundingWitness L where
  fam := { G := fun _ => L, joint_smooth := fun i => (L.smooth i).comp contDiff_snd }
  start := rfl
  a := fun k => (L.noCusp h0 k).elim
  b := fun k => (L.noCusp h0 k).elim
  a_lt := fun k => (L.noCusp h0 k).elim
  lt_b := fun k => (L.noCusp h0 k).elim
  len := fun k => (L.noCusp h0 k).elim
  intervals_disjoint := fun k => (L.noCusp h0 k).elim
  fixed_outside := fun _ _ _ _ => rfl
  generic := fun _ _ _ =>
    ⟨L.regular_of_no_cusps h0, h.doubles_finite, h.transverse, h.no_triple, h.heights_distinct⟩
  clean := fun _ _ _ => ⟨L.constSmoothing h0⟩
  same_doubles := fun _ _ _ _ _ => Iff.rfl
  same_data := fun _ _ _ _ _ _ => ⟨rfl, Iff.rfl⟩
  intervals_disjoint_circle := fun k => (L.noCusp h0 k).elim
  U := fun k => (L.noCusp h0 k).elim
  clean_in := fun _ _ _ => ⟨L.constSmoothing h0, rfl, rfl, rfl⟩

theorem constWitness_G (h : L.CuspedProjection) (lam : ℝ) :
    (L.constWitness h0 h).fam.G lam = L := rfl

end NoCusps

end SpatialLink

/-! ## 6. The row -/

/-- Lemma ce:rounding (row 89), assembled from the chain. -/
theorem ce_rounding : CeRoundingData where
  exists_family := fun L _ h => L.exists_cuspRoundingWitness h
  smooth_embeddings_start := fun _ W =>
    ⟨W.fam.joint_smooth, fun lam => (W.fam.G lam).embedded, fun lam => (W.fam.G lam).regular, W.start⟩
  fixed_outside_disjoint := fun _ W =>
    ⟨fun k => ⟨W.a_lt k, W.lt_b k, W.len k⟩, W.intervals_disjoint_circle, W.fixed_outside⟩
  generic_slices := fun _ W lam h1 h2 => W.generic lam h1 h2
  clean_no_new_retains := fun _ W lam h1 h2 =>
    ⟨W.clean_in lam h1 h2, W.same_doubles lam h1 h2, W.same_data lam h1 h2⟩
  circles_retained := fun _ W lam i =>
    ⟨(W.fam.G lam).periodic i, fun t ht => W.fixed_outside lam i t ht⟩
  const_of_no_cusps := fun L _ h h0 => ⟨L.constWitness h0 h, fun _ => rfl⟩

end

end SM
