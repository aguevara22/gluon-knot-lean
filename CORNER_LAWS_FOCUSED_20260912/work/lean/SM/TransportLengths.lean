import SM.EuclideanPlane
import SM.DirectionProjection
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.MetricSpace.Bounded

/-! Towards lem:transport-lengths (sm-5-transport.tex:76). Written 2026-09-13 by a Claude Code prover subagent of the pod
executor (workflow prove-transport-lane / prove:transport-lengths), checked with `lake env lean` (placeholder-free, standard axioms) and
ported verbatim from work/drafts/TransportLengths.lean (only this header added and #print lines removed). -/

/-! # SM lem:transport-lengths (positive closing lengths along a direction path)

Source: `reference/SM/sm-5-transport.tex`, frame SM15, lines 76–131.

Statement as printed: let `u_1(t), …, u_n(t)` be continuous unit vectors on a compact
interval, lying in no closed semicircle at any parameter.  There are continuous strictly
positive lengths `l_i(t)` with `∑ l_i(t) u_i(t) = 0`.  At either endpoint any prescribed
positive closing lengths can be joined to the selected lengths while keeping the directions
fixed.

Encoding.  `Plane = ℝ × ℝ` with the SM coordinate dot product `planeDot`, the SM
determinant `det` and the SM Euclidean length `euclideanLength` (all from
`SM.Polygon`/`SM.EuclideanPlane`; `planeDot_add_right` from `SM.DirectionProjection`).  The compact interval is `Set.Icc a b` with `a ≤ b`;
the direction functions are `u : ι → ℝ → Plane`, `ContinuousOn (u i) (Icc a b)`, unit on
`Icc a b`; "lying in no closed semicircle" at `t` is
`¬ ∃ v, euclideanLength v = 1 ∧ ∀ i, 0 ≤ planeDot v (u i t)` (a closed semicircle of the
unit circle is `{w : ⟨v, w⟩ ≥ 0}` for a unit `v`).  The finite index type `ι` is arbitrary
(it covers `ZMod n`, `Fin n`); a `ZMod n` corollary is included.

Proof (as in the source): pointwise positive closing lengths exist (origin interior to the
convex hull — here obtained from a compactness gap on the unit circle and the nearest-point
variational inequality on the compact convex set of convex combinations); local continuous
positive closing lengths by a two-coordinate Cramer correction; global ones by a finite
cover of the compact interval and a continuous partition of unity; the endpoint join is the
convexity of the set of positive closing length vectors at fixed directions. -/

namespace SM

open Set Filter Topology

/-! ### Elementary facts about the coordinate dot product, determinant and length -/

theorem planeDot_self_nonneg (u : Plane) : 0 ≤ planeDot u u :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem tl_planeDot_smul_left (u v : Plane) (r : ℝ) :
    planeDot (r • u) v = r * planeDot u v := by
  change (r * u.1) * v.1 + (r * u.2) * v.2 = r * (u.1 * v.1 + u.2 * v.2)
  ring

theorem planeDot_neg_right (u v : Plane) : planeDot u (-v) = -planeDot u v := by
  change u.1 * (-v.1) + u.2 * (-v.2) = -(u.1 * v.1 + u.2 * v.2)
  ring

theorem tl_planeDot_sub_right (u v w : Plane) :
    planeDot u (v - w) = planeDot u v - planeDot u w := by
  change u.1 * (v.1 - w.1) + u.2 * (v.2 - w.2) = (u.1 * v.1 + u.2 * v.2) - (u.1 * w.1 + u.2 * w.2)
  ring

theorem det_zero_left (v : Plane) : det 0 v = 0 := by
  simp [det]

theorem det_zero_right (v : Plane) : det v 0 = 0 := by
  simp [det]

theorem det_self (v : Plane) : det v v = 0 := by
  simp only [det]; ring

theorem euclideanLength_eq_sqrt (u : Plane) :
    euclideanLength u = Real.sqrt (planeDot u u) :=
  euclideanLength_formula u

theorem euclideanLength_nonneg (u : Plane) : 0 ≤ euclideanLength u :=
  norm_nonneg _

theorem euclideanLength_mul_self (u : Plane) :
    euclideanLength u * euclideanLength u = planeDot u u := by
  rw [euclideanLength_eq_sqrt]
  exact Real.mul_self_sqrt (planeDot_self_nonneg u)

theorem euclideanLength_smul (r : ℝ) (u : Plane) :
    euclideanLength (r • u) = |r| * euclideanLength u := by
  simp only [euclideanLength, planeComplex_smul, norm_smul, Real.norm_eq_abs]

/-- Lagrange's identity. -/
theorem planeDot_mul_planeDot (u v : Plane) :
    planeDot u u * planeDot v v = planeDot u v ^ 2 + det u v ^ 2 := by
  simp only [planeDot, det]; ring

/-- Cauchy–Schwarz for the coordinate dot product. -/
theorem planeDot_le_euclideanLength_mul (u v : Plane) :
    planeDot u v ≤ euclideanLength u * euclideanLength v := by
  have h1 : planeDot u v ^ 2 ≤ planeDot u u * planeDot v v := by
    rw [planeDot_mul_planeDot]; nlinarith [sq_nonneg (det u v)]
  calc planeDot u v ≤ |planeDot u v| := le_abs_self _
    _ = Real.sqrt (planeDot u v ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (planeDot u u * planeDot v v) := Real.sqrt_le_sqrt h1
    _ = euclideanLength u * euclideanLength v := by
      rw [Real.sqrt_mul (planeDot_self_nonneg u), euclideanLength_eq_sqrt, euclideanLength_eq_sqrt]

theorem aux_cramer {D e a b c d : ℝ} (hD : D ≠ 0) (h : e * D = a * b + c * d) :
    e + -a / D * b + -c / D * d = 0 := by
  have he : e = (a * b + c * d) / D := by rw [← h, mul_div_assoc, div_self hD, mul_one]
  rw [he]; ring

/-- Cramer's rule in the plane: the two-coordinate correction closes a vector
(`transport:cramer`). -/
theorem cramer_closing {E p q : Plane} (hD : det p q ≠ 0) :
    E + (-det E q / det p q) • p + (-det p E / det p q) • q = 0 := by
  simp only [det] at hD ⊢
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_zero]
    exact aux_cramer hD (by ring)
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_zero]
    exact aux_cramer hD (by ring)

theorem continuous_planeDot {X : Type*} [TopologicalSpace X] {f g : X → Plane}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => planeDot (f x) (g x) := by
  unfold planeDot
  exact (hf.fst.mul hg.fst).add (hf.snd.mul hg.snd)

theorem continuous_det {X : Type*} [TopologicalSpace X] {f g : X → Plane}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => det (f x) (g x) := by
  unfold det
  exact (hf.fst.mul hg.snd).sub (hf.snd.mul hg.fst)

/-! ### Pointwise positive closing lengths -/

section Pointwise

variable {ι : Type*} [Fintype ι]

/-- The "no closed half-plane" condition for a finite family, in the `v ≠ 0` form. -/
def NoClosedHalfPlane (w : ι → Plane) : Prop :=
  ∀ v : Plane, v ≠ 0 → ∃ i, planeDot v (w i) < 0

omit [Fintype ι] in
theorem NoClosedHalfPlane.nonempty {w : ι → Plane} (hw : NoClosedHalfPlane w) : Nonempty ι := by
  obtain ⟨i, _⟩ := hw ((1 : ℝ), (0 : ℝ)) (by
    intro h
    have := congrArg Prod.fst h
    simp at this)
  exact ⟨i⟩

/-- Compactness gap: the family is uniformly outside every closed half-plane through the
origin. -/
theorem NoClosedHalfPlane.exists_gap {w : ι → Plane} (hw : NoClosedHalfPlane w) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : Plane, planeDot v v = 1 → ∃ i, planeDot v (w i) ≤ -δ := by
  classical
  have : Nonempty ι := hw.nonempty
  set S : Set Plane := {v | planeDot v v = 1} with hS
  have hScl : IsClosed S :=
    isClosed_eq (continuous_planeDot continuous_id continuous_id) continuous_const
  have hSb : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : Plane)]
    refine ⟨1, fun v hv => ?_⟩
    have hv' : v.1 * v.1 + v.2 * v.2 = 1 := hv
    rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    refine max_le (abs_le_one_iff_mul_self_le_one.mpr ?_) (abs_le_one_iff_mul_self_le_one.mpr ?_)
    · nlinarith [mul_self_nonneg v.2]
    · nlinarith [mul_self_nonneg v.1]
  have hScmp : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSb
  have hSne : S.Nonempty := ⟨((1 : ℝ), (0 : ℝ)), by
    show (1 : ℝ) * 1 + 0 * 0 = 1
    norm_num⟩
  set g : Plane → ℝ := fun v => ∑ i, min 0 (planeDot v (w i)) with hg
  have hgc : Continuous g :=
    continuous_finsetSum _ fun i _ =>
      continuous_const.min (continuous_planeDot continuous_id continuous_const)
  obtain ⟨v₀, hv₀S, hmax⟩ := hScmp.exists_isMaxOn hSne hgc.continuousOn
  have hv₀ne : v₀ ≠ 0 := by
    intro h
    have hv₀' : planeDot v₀ v₀ = 1 := hv₀S
    rw [h] at hv₀'
    simp [planeDot] at hv₀'
  obtain ⟨i₀, hi₀⟩ := hw v₀ hv₀ne
  have hgneg : g v₀ < 0 := by
    calc g v₀ = ∑ i, min 0 (planeDot v₀ (w i)) := rfl
      _ ≤ ∑ i, (if i = i₀ then min 0 (planeDot v₀ (w i)) else 0) := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs
          · exact le_rfl
          · exact min_le_left _ _
      _ = min 0 (planeDot v₀ (w i₀)) := by simp [Finset.sum_ite_eq']
      _ < 0 := min_lt_iff.mpr (Or.inr hi₀)
  set n : ℕ := Fintype.card ι with hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  set δ : ℝ := -g v₀ / n with hδ
  have hδpos : 0 < δ := div_pos (neg_pos.mpr hgneg) hnpos
  refine ⟨δ, hδpos, fun v hv => ?_⟩
  have hgv : g v ≤ g v₀ := isMaxOn_iff.mp hmax v hv
  have hsum : ∑ i, min 0 (planeDot v (w i)) ≤ ∑ _i : ι, -δ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn, hδ]
    have : (n : ℝ) * -(-g v₀ / n) = g v₀ := by
      field_simp
    rw [this]
    exact hgv
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨i, ?_⟩
  rcases min_le_iff.mp hi with h | h
  · exfalso; linarith
  · exact h

/-- Nearest-point variational inequality on a compact convex set. -/
theorem exists_nearest_point {K : Set Plane} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKc : Convex ℝ K) (x : Plane) :
    ∃ p ∈ K, ∀ y ∈ K, 0 ≤ planeDot (p - x) (y - p) := by
  have hcont : Continuous fun y : Plane => planeDot (y - x) (y - x) :=
    continuous_planeDot (continuous_id.sub continuous_const) (continuous_id.sub continuous_const)
  obtain ⟨p, hpK, hpmin⟩ := hK.exists_isMinOn hKne hcont.continuousOn
  refine ⟨p, hpK, fun y hy => ?_⟩
  by_contra hneg
  push Not at hneg
  set A := planeDot (p - x) (y - p) with hA
  set B := planeDot (y - p) (y - p) with hB
  have hB0 : 0 ≤ B := planeDot_self_nonneg _
  set s : ℝ := min 1 (-A / (B + 1)) with hs
  have hs0 : 0 < s := lt_min one_pos (div_pos (neg_pos.mpr hneg) (by linarith))
  have hs1 : s ≤ 1 := min_le_left _ _
  have hs2 : s ≤ -A / (B + 1) := min_le_right _ _
  have h3 : s * (B + 1) ≤ -A := (le_div_iff₀ (by linarith)).mp hs2
  have hz : p + s • (y - p) ∈ K := hKc.add_smul_sub_mem hpK hy ⟨hs0.le, hs1⟩
  have hmin : planeDot (p - x) (p - x) ≤
      planeDot (p + s • (y - p) - x) (p + s • (y - p) - x) := isMinOn_iff.mp hpmin _ hz
  have hexp : planeDot (p + s • (y - p) - x) (p + s • (y - p) - x)
      = planeDot (p - x) (p - x) + 2 * s * A + s ^ 2 * B := by
    simp only [hA, hB, planeDot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have h4 : 2 * A + s * B < 0 := by nlinarith
  have h5 : s * (2 * A + s * B) < 0 := mul_neg_of_pos_of_neg hs0 h4
  have h6 : 2 * s * A + s ^ 2 * B = s * (2 * A + s * B) := by ring
  linarith

/-- The set of convex combinations of the family (its convex hull, as an explicit image). -/
def convexCombinations (w : ι → Plane) : Set Plane :=
  (fun a : ι → ℝ => ∑ i, a i • w i) '' stdSimplex ℝ ι

theorem isCompact_convexCombinations (w : ι → Plane) : IsCompact (convexCombinations w) :=
  (isCompact_stdSimplex ℝ ι).image
    (continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const)

theorem convex_convexCombinations (w : ι → Plane) : Convex ℝ (convexCombinations w) := by
  refine (convex_stdSimplex ℝ ι).is_linear_image ⟨fun a b => ?_, fun c a => ?_⟩
  · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  · simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem mem_convexCombinations (w : ι → Plane) (i : ι) : w i ∈ convexCombinations w := by
  classical
  refine ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, ?_⟩
  simp [Pi.single_apply, ite_smul]

/-- Pointwise step of SM lem:transport-lengths: a finite family in no closed half-plane
through the origin admits strictly positive closing lengths
(`transport:positive-close`). -/
theorem NoClosedHalfPlane.exists_positive_closing {w : ι → Plane} (hw : NoClosedHalfPlane w) :
    ∃ l : ι → ℝ, (∀ i, 0 < l i) ∧ ∑ i, l i • w i = 0 := by
  classical
  have : Nonempty ι := hw.nonempty
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  obtain ⟨δ, hδ, hgap⟩ := hw.exists_gap
  have hKcpt := isCompact_convexCombinations w
  have hKconv := convex_convexCombinations w
  have hKne : (convexCombinations w).Nonempty := ⟨w i₀, mem_convexCombinations w i₀⟩
  set b : Plane := ∑ i, w i with hb
  set ε : ℝ := δ / (euclideanLength b + 1) with hε
  have hbnn := euclideanLength_nonneg b
  have hεpos : 0 < ε := div_pos hδ (by linarith)
  have hεb : ε * euclideanLength b < δ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  set x : Plane := -(ε • b) with hx
  obtain ⟨p, hpK, hproj⟩ := exists_nearest_point hKcpt hKne hKconv x
  by_cases hpx : p = x
  · rw [hpx] at hpK
    obtain ⟨a, ha, hax⟩ := hpK
    refine ⟨fun i => a i + ε, fun i => add_pos_of_nonneg_of_pos (ha.1 i) hεpos, ?_⟩
    simp only [add_smul, Finset.sum_add_distrib, hax, ← Finset.smul_sum, ← hb, hx]
    exact neg_add_cancel _
  · exfalso
    set q : Plane := p - x with hq
    have hqne : q ≠ 0 := sub_ne_zero.mpr hpx
    set r : ℝ := euclideanLength q with hr
    have hrpos : 0 < r := euclideanLength_pos hqne
    have hrr : r * r = planeDot q q := euclideanLength_mul_self q
    have hunit : planeDot ((1 / r) • q) ((1 / r) • q) = 1 := by
      rw [tl_planeDot_smul_left, planeDot_smul_right, ← hrr]
      field_simp
    obtain ⟨i, hi⟩ := hgap _ hunit
    rw [tl_planeDot_smul_left] at hi
    have hi' : planeDot q (w i) ≤ -δ * r := by
      have := mul_le_mul_of_nonneg_left hi hrpos.le
      rw [← mul_assoc, mul_one_div_cancel hrpos.ne', one_mul] at this
      linarith
    have hproj_i := hproj (w i) (mem_convexCombinations w i)
    have hexp : planeDot q (w i - p) = planeDot q (w i) - planeDot q q + ε * planeDot q b := by
      have hp : p = q + x := by rw [hq]; abel
      rw [hp, tl_planeDot_sub_right, planeDot_add_right, hx, planeDot_neg_right, planeDot_smul_right]
      ring
    have hCS : planeDot q b ≤ r * euclideanLength b := planeDot_le_euclideanLength_mul q b
    have h1 : ε * planeDot q b ≤ ε * (r * euclideanLength b) :=
      mul_le_mul_of_nonneg_left hCS hεpos.le
    have h2 : r * (ε * euclideanLength b) < r * δ := mul_lt_mul_of_pos_left hεb hrpos
    nlinarith

end Pointwise

/-! ### Local continuous positive closing lengths (Cramer correction) -/

section Local

variable {ι : Type*} [Fintype ι]

/-- Two independent directions exist when the family lies in no closed half-plane. -/
theorem NoClosedHalfPlane.exists_det_ne_zero {w : ι → Plane} (hw : NoClosedHalfPlane w) :
    ∃ p q : ι, det (w p) (w q) ≠ 0 := by
  by_contra hall
  push Not at hall
  have hne : ∃ i₀, w i₀ ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨i, hi⟩ := hw ((1 : ℝ), (0 : ℝ)) (by
      intro h1
      have := congrArg Prod.fst h1
      simp at this)
    rw [h i] at hi
    simp [planeDot] at hi
  obtain ⟨i₀, hi₀⟩ := hne
  set v : Plane := (-(w i₀).2, (w i₀).1) with hv
  have hvne : v ≠ 0 := by
    intro h
    apply hi₀
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [hv, Prod.fst_zero, Prod.snd_zero, neg_eq_zero] at h1 h2
    exact Prod.ext h2 h1
  obtain ⟨i, hi⟩ := hw v hvne
  have : planeDot v (w i) = det (w i₀) (w i) := by
    simp only [hv, planeDot, det]; ring
  rw [this, hall i₀ i] at hi
  exact lt_irrefl _ hi

/-- Local step of SM lem:transport-lengths: around every parameter there is a neighbourhood
carrying continuous strictly positive closing lengths (Cramer correction of a pointwise
closing vector). -/
theorem exists_local_closing (u : ι → ℝ → Plane) (hu : ∀ i, Continuous (u i))
    (hns : ∀ t, NoClosedHalfPlane fun i => u i t) (t₀ : ℝ) :
    ∃ V ∈ 𝓝 t₀, ∃ l : ι → ℝ → ℝ, (∀ i, ContinuousOn (l i) V) ∧
      ∀ t ∈ V, (∀ i, 0 < l i t) ∧ ∑ i, l i t • u i t = 0 := by
  classical
  obtain ⟨l₀, hl₀pos, hl₀close⟩ := (hns t₀).exists_positive_closing
  obtain ⟨p, q, hD₀⟩ := (hns t₀).exists_det_ne_zero
  have hpq : p ≠ q := by
    rintro rfl
    exact hD₀ (det_self _)
  set E : ℝ → Plane := fun t => ∑ i, l₀ i • u i t with hE
  set D : ℝ → ℝ := fun t => det (u p t) (u q t) with hD
  set dp : ℝ → ℝ := fun t => -det (E t) (u q t) / D t with hdp
  set dq : ℝ → ℝ := fun t => -det (u p t) (E t) / D t with hdq
  set l : ι → ℝ → ℝ := fun i t =>
    l₀ i + ((if i = p then dp t else 0) + (if i = q then dq t else 0)) with hl
  have hEc : Continuous E := continuous_finsetSum _ fun i _ => (hu i).const_smul (l₀ i)
  have hDc : Continuous D := continuous_det (hu p) (hu q)
  have hE₀ : E t₀ = 0 := hl₀close
  set W : Set ℝ := {t | D t ≠ 0} with hW
  have hWo : IsOpen W := isOpen_ne_fun hDc continuous_const
  have hdpc : ContinuousOn dp W :=
    ((continuous_det hEc (hu q)).neg.continuousOn).div hDc.continuousOn fun t ht => ht
  have hdqc : ContinuousOn dq W :=
    ((continuous_det (hu p) hEc).neg.continuousOn).div hDc.continuousOn fun t ht => ht
  have hlc : ∀ i, ContinuousOn (l i) W := by
    intro i
    refine continuousOn_const.add (ContinuousOn.add ?_ ?_)
    · by_cases h : i = p
      · simp only [h, ↓reduceIte]; exact hdpc
      · simp only [h, ↓reduceIte]; exact continuousOn_const
    · by_cases h : i = q
      · simp only [h, ↓reduceIte]; exact hdqc
      · simp only [h, ↓reduceIte]; exact continuousOn_const
  have hlt₀ : ∀ i, l i t₀ = l₀ i := by
    intro i
    simp only [hl, hdp, hdq, hE₀, det_zero_left, det_zero_right, neg_zero, zero_div, ite_self,
      add_zero]
  have hV : ∀ᶠ t in 𝓝 t₀, D t ≠ 0 ∧ ∀ i, 0 < l i t := by
    refine (hDc.continuousAt.eventually_ne hD₀).and (eventually_all.mpr fun i => ?_)
    have hcont : ContinuousAt (l i) t₀ := (hlc i).continuousAt (hWo.mem_nhds hD₀)
    have hpos : 0 < l i t₀ := by rw [hlt₀ i]; exact hl₀pos i
    exact hcont.eventually (lt_mem_nhds hpos)
  refine ⟨{t | D t ≠ 0 ∧ ∀ i, 0 < l i t}, hV, l, fun i => (hlc i).mono fun t ht => ht.1,
    fun t ht => ⟨ht.2, ?_⟩⟩
  have hsplit : ∑ i, l i t • u i t = E t + dp t • u p t + dq t • u q t := by
    simp only [hl, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, hE, add_assoc]
  rw [hsplit]
  exact cramer_closing ht.1

end Local

/-! ### Gluing by a partition of unity -/

section Glue

variable {ι : Type*} [Fintype ι]

/-- Gluing step of SM lem:transport-lengths: continuous positive closing lengths on the
members of a finite open cover of a closed set are combined, through a continuous partition
of unity subordinate to the cover, into continuous positive closing lengths on the set. -/
theorem glue_closing {J : Type*} [Fintype J] (u : ι → ℝ → Plane) {s : Set ℝ} (hs : IsClosed s)
    (U : J → Set ℝ) (hUo : ∀ j, IsOpen (U j)) (hUs : s ⊆ ⋃ j, U j)
    (l : J → ι → ℝ → ℝ) (hlc : ∀ j i, ContinuousOn (l j i) (U j))
    (hl : ∀ j, ∀ t ∈ U j, (∀ i, 0 < l j i t) ∧ ∑ i, l j i t • u i t = 0) :
    ∃ L : ι → ℝ → ℝ, (∀ i, Continuous (L i)) ∧
      ∀ t ∈ s, (∀ i, 0 < L i t) ∧ ∑ i, L i t • u i t = 0 := by
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate hs U hUo hUs
  set g : J → ι → ℝ → ℝ := fun j i => (U j).indicator fun t => f j t * l j i t with hg
  have hg_cont : ∀ j i, Continuous (g j i) := by
    intro j i
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : t ∈ U j
    · have hnhds : U j ∈ 𝓝 t := (hUo j).mem_nhds ht
      have hc : ContinuousAt (fun t => f j t * l j i t) t :=
        (f j).continuous.continuousAt.mul ((hlc j i).continuousAt hnhds)
      refine hc.congr (eventually_of_mem hnhds fun t' ht' => ?_)
      exact (indicator_of_mem ht' (fun t : ℝ => (f j t : ℝ) * l j i t)).symm
    · have ht' : t ∉ tsupport (f j) := fun h => ht (hf j h)
      have hev := notMem_tsupport_iff_eventuallyEq.mp ht'
      refine Filter.EventuallyEq.continuousAt (y := (0 : ℝ)) ?_
      filter_upwards [hev] with t' ht'
      by_cases h : t' ∈ U j
      · simp [hg, indicator_of_mem h, ht']
      · simp [hg, indicator_of_notMem h]
  set L : ι → ℝ → ℝ := fun i t => ∑ j, g j i t with hL
  refine ⟨L, fun i => continuous_finsetSum _ fun j _ => hg_cont j i, fun t ht => ⟨fun i => ?_, ?_⟩⟩
  · obtain ⟨j₀, hj₀⟩ := f.exists_pos ht
    have hj₀U : t ∈ U j₀ := hf j₀ (subset_tsupport _ (Function.mem_support.mpr hj₀.ne'))
    have hnn : ∀ j, 0 ≤ g j i t := fun j => by
      by_cases h : t ∈ U j
      · simp only [hg, indicator_of_mem h]
        exact mul_nonneg (f.nonneg j t) ((hl j t h).1 i).le
      · simp only [hg, indicator_of_notMem h]
        exact le_rfl
    have hpos : 0 < g j₀ i t := by
      simp only [hg, indicator_of_mem hj₀U]
      exact mul_pos hj₀ ((hl j₀ t hj₀U).1 i)
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ j₀))
  · calc ∑ i, L i t • u i t = ∑ i, ∑ j, g j i t • u i t := by
          simp only [hL, Finset.sum_smul]
      _ = ∑ j, ∑ i, g j i t • u i t := Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero fun j _ => by
          by_cases h : t ∈ U j
          · simp only [hg, indicator_of_mem h, mul_smul, ← Finset.smul_sum, (hl j t h).2,
              smul_zero]
          · simp only [hg, indicator_of_notMem h, zero_smul, Finset.sum_const_zero]

end Glue

/-! ### Convexity of positive closing lengths at fixed directions -/

section Convexity

variable {ι : Type*} [Fintype ι]

/-- For fixed directions the set of strictly positive closing length vectors is convex
(last sentence of the proof of SM lem:transport-lengths). -/
theorem convex_positiveClosing (w : ι → Plane) :
    Convex ℝ {l : ι → ℝ | (∀ i, 0 < l i) ∧ ∑ i, l i • w i = 0} := by
  intro m hm l hl α β hα hβ hαβ
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hα0 : α = 0
    · rw [hα0, zero_add] at hαβ
      rw [hα0, hαβ, zero_mul, one_mul, zero_add]
      exact hl.1 i
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hα (Ne.symm hα0)) (hm.1 i))
        (mul_nonneg hβ (hl.1 i).le)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
      mul_smul, ← Finset.smul_sum, hm.2, hl.2, smul_zero, add_zero]

/-- The straight segment between two positive closing length vectors for the same directions
consists of positive closing length vectors. -/
theorem closing_segment {w : ι → Plane} {m l : ι → ℝ} (hm : ∀ i, 0 < m i) (hl : ∀ i, 0 < l i)
    (hmc : ∑ i, m i • w i = 0) (hlc : ∑ i, l i • w i = 0) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∀ i, 0 < (1 - s) * m i + s * l i) ∧ ∑ i, ((1 - s) * m i + s * l i) • w i = 0 := by
  have h := convex_positiveClosing w ⟨hm, hmc⟩ ⟨hl, hlc⟩ (sub_nonneg.mpr hs.2) hs.1
    (by ring)
  exact h

end Convexity

/-! ### The theorem -/

section Main

variable {ι : Type*} [Fintype ι]

/-- **SM lem:transport-lengths** (positive closing lengths along a direction path).
Let `u i`, `i : ι`, be continuous unit vectors on the compact interval `[a, b]` lying in no
closed semicircle at any parameter.  Then there are continuous strictly positive lengths
`l i` on `[a, b]` with `∑ i, l i t • u i t = 0`, and at either endpoint any prescribed positive
closing lengths `m` are joined to the selected lengths by the straight segment
`s ↦ (1 - s) m + s l`, which consists of positive closing lengths for the fixed directions. -/
theorem transport_lengths {a b : ℝ} (hab : a ≤ b) (u : ι → ℝ → Plane)
    (hu : ∀ i, ContinuousOn (u i) (Icc a b))
    (hunit : ∀ i, ∀ t ∈ Icc a b, euclideanLength (u i t) = 1)
    (hsemi : ∀ t ∈ Icc a b,
      ¬ ∃ v : Plane, euclideanLength v = 1 ∧ ∀ i, 0 ≤ planeDot v (u i t)) :
    ∃ l : ι → ℝ → ℝ,
      (∀ i, ContinuousOn (l i) (Icc a b)) ∧
      (∀ i, ∀ t ∈ Icc a b, 0 < l i t) ∧
      (∀ t ∈ Icc a b, ∑ i, l i t • u i t = 0) ∧
      (∀ m : ι → ℝ, (∀ i, 0 < m i) → ∑ i, m i • u i a = 0 →
        ∀ s ∈ Icc (0 : ℝ) 1,
          (∀ i, 0 < (1 - s) * m i + s * l i a) ∧
          ∑ i, ((1 - s) * m i + s * l i a) • u i a = 0) ∧
      (∀ m : ι → ℝ, (∀ i, 0 < m i) → ∑ i, m i • u i b = 0 →
        ∀ s ∈ Icc (0 : ℝ) 1,
          (∀ i, 0 < (1 - s) * m i + s * l i b) ∧
          ∑ i, ((1 - s) * m i + s * l i b) • u i b = 0) := by
  classical
  -- Step 0: extend the directions continuously to all of `ℝ` by the retraction onto `[a, b]`.
  set v : ι → ℝ → Plane := fun i t => u i (projIcc a b hab t) with hv
  have hvc : ∀ i, Continuous (v i) := fun i =>
    (hu i).comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun t => (projIcc a b hab t).2
  have hveq : ∀ i, ∀ t ∈ Icc a b, v i t = u i t := fun i t ht => by
    simp only [hv, projIcc_of_mem hab ht]
  have hns : ∀ t, NoClosedHalfPlane fun i => v i t := by
    intro t w hw
    by_contra hcon
    push Not at hcon
    apply hsemi (projIcc a b hab t) (projIcc a b hab t).2
    have hwpos : 0 < euclideanLength w := euclideanLength_pos hw
    refine ⟨(1 / euclideanLength w) • w, ?_, fun i => ?_⟩
    · rw [euclideanLength_smul, abs_of_pos (one_div_pos.mpr hwpos), one_div_mul_cancel hwpos.ne']
    · rw [tl_planeDot_smul_left]
      exact mul_nonneg (one_div_pos.mpr hwpos).le (hcon i)
  -- Step 1: local continuous positive closing lengths around every parameter.
  have hloc := fun t₀ => exists_local_closing v hvc hns t₀
  choose V hV l hlc hl using hloc
  -- Step 2: a finite subcover of the compact interval by the interiors.
  obtain ⟨T, -, hT⟩ := isCompact_Icc.elim_nhds_subcover (fun t₀ => interior (V t₀))
    fun t₀ _ => interior_mem_nhds.mpr (hV t₀)
  -- Step 3: glue.
  obtain ⟨L, hLc, hL⟩ := glue_closing (J := T) v isClosed_Icc (fun j => interior (V j))
    (fun j => isOpen_interior)
    (by
      intro t ht
      obtain ⟨t₀, ht₀T, ht₀⟩ := Set.mem_iUnion₂.mp (hT ht)
      exact Set.mem_iUnion.mpr ⟨⟨t₀, ht₀T⟩, ht₀⟩)
    (fun j => l j) (fun j i => (hlc j i).mono interior_subset)
    (fun j t ht => hl j t (interior_subset ht))
  have hLpos : ∀ i, ∀ t ∈ Icc a b, 0 < L i t := fun i t ht => (hL t ht).1 i
  have hLclose : ∀ t ∈ Icc a b, ∑ i, L i t • u i t = 0 := fun t ht => by
    rw [← (hL t ht).2]
    exact Finset.sum_congr rfl fun i _ => by rw [hveq i t ht]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  refine ⟨L, fun i => (hLc i).continuousOn, hLpos, hLclose, ?_, ?_⟩
  · intro m hm hmc s hs
    exact closing_segment hm (fun i => hLpos i a ha) hmc (hLclose a ha) hs
  · intro m hm hmc s hs
    exact closing_segment hm (fun i => hLpos i b hb) hmc (hLclose b hb) hs

/-- SM lem:transport-lengths with the source's indexing `u_1, …, u_n` read in `ZMod n`
(source label `n ≡ 0`). -/
theorem transport_lengths_zmod (n : ℕ) [NeZero n] {a b : ℝ} (hab : a ≤ b)
    (u : ZMod n → ℝ → Plane)
    (hu : ∀ i, ContinuousOn (u i) (Icc a b))
    (hunit : ∀ i, ∀ t ∈ Icc a b, euclideanLength (u i t) = 1)
    (hsemi : ∀ t ∈ Icc a b,
      ¬ ∃ v : Plane, euclideanLength v = 1 ∧ ∀ i, 0 ≤ planeDot v (u i t)) :
    ∃ l : ZMod n → ℝ → ℝ,
      (∀ i, ContinuousOn (l i) (Icc a b)) ∧
      (∀ i, ∀ t ∈ Icc a b, 0 < l i t) ∧
      (∀ t ∈ Icc a b, ∑ i, l i t • u i t = 0) ∧
      (∀ m : ZMod n → ℝ, (∀ i, 0 < m i) → ∑ i, m i • u i a = 0 →
        ∀ s ∈ Icc (0 : ℝ) 1,
          (∀ i, 0 < (1 - s) * m i + s * l i a) ∧
          ∑ i, ((1 - s) * m i + s * l i a) • u i a = 0) ∧
      (∀ m : ZMod n → ℝ, (∀ i, 0 < m i) → ∑ i, m i • u i b = 0 →
        ∀ s ∈ Icc (0 : ℝ) 1,
          (∀ i, 0 < (1 - s) * m i + s * l i b) ∧
          ∑ i, ((1 - s) * m i + s * l i b) • u i b = 0) :=
  transport_lengths hab u hu hunit hsemi

end Main

end SM
