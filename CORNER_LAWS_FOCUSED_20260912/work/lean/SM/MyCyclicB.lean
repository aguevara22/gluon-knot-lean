import SM.TransportLengths
import SM.TransportAngleInterval
import SM.RotationContinuity
import SM.CumulativeTurns
import SM.RotationBounds
import SM.UniformRotation
import SM.BowTie
import SM.Admissible
import SM.Fibres
import Mathlib.Topology.Instances.Sign

/-! Towards thm:mycyclic (sm-5-transport.tex:150), strategy B (JoinedIn). Written 2026-09-13 by a Claude Code prover subagent of the
pod executor (workflow prove-transport-lane-2 / prove:mycyclic-B), checked with `lake env lean` (placeholder-free, standard axioms) and ported
verbatim from work/drafts/MyCyclicB.lean (only this header added and #print lines removed). An independent Path-based proof of the same
theorem (work/drafts/MyCyclicA.lean) compiles as well and is kept as a cross-check; it is not part of the library. -/

/-! # SM15 `thm:mycyclic` (connectivity of the fibres), strategy B

Source: reference/SM/sm-5-transport.tex, lines 150–290. -/

open Real Set

namespace SM

/-! ### Unit directions and regular pairs -/

theorem mcB_unitDir_ne_zero (a : ℝ) : unitDir a ≠ 0 := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [unitDir, Prod.fst_zero, Prod.snd_zero] at h1 h2
  have := Real.cos_sq_add_sin_sq a
  rw [h1, h2] at this
  norm_num at this

theorem mcB_planeDot_unitDir_self (a : ℝ) : planeDot (unitDir a) (unitDir a) = 1 := by
  change Real.cos a * Real.cos a + Real.sin a * Real.sin a = 1
  nlinarith [Real.cos_sq_add_sin_sq a]

theorem mcB_euclideanLength_unitDir (a : ℝ) : euclideanLength (unitDir a) = 1 := by
  rw [euclideanLength_eq_sqrt, mcB_planeDot_unitDir_self, Real.sqrt_one]

theorem mcB_unitDir_eq_of_angle_eq {a b : ℝ} (h : (a : Real.Angle) = (b : Real.Angle)) :
    unitDir a = unitDir b := by
  have hc : Real.cos a = Real.cos b := by
    rw [← Real.Angle.cos_coe, ← Real.Angle.cos_coe, h]
  have hs : Real.sin a = Real.sin b := by
    rw [← Real.Angle.sin_coe, ← Real.Angle.sin_coe, h]
  simp only [unitDir, hc, hs]

theorem mcB_unitDir_add_int_mul_two_pi (a : ℝ) (k : ℤ) :
    unitDir (a + k * (2 * π)) = unitDir a := by
  simp only [unitDir, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem mcB_unitDir_add_two_pi_mul_int (a : ℝ) (k : ℤ) :
    unitDir (a + 2 * π * k) = unitDir a := by
  rw [show a + 2 * π * k = a + k * (2 * π) by ring]
  exact mcB_unitDir_add_int_mul_two_pi a k

/-- Every nonzero vector is its Euclidean length times the unit direction of its argument. -/
theorem mcB_eq_length_smul_unitDir_arg (v : Plane) :
    v = euclideanLength v • unitDir (planeComplex v).arg := by
  have hr := Complex.norm_mul_cos_arg (planeComplex v)
  have hi := Complex.norm_mul_sin_arg (planeComplex v)
  apply Prod.ext
  · change v.1 = euclideanLength v * Real.cos (planeComplex v).arg
    rw [euclideanLength, hr]; rfl
  · change v.2 = euclideanLength v * Real.sin (planeComplex v).arg
    rw [euclideanLength, hi]; rfl

theorem mcB_regularPair_smul {u v : Plane} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    RegularPair (a • u) (b • v) ↔ RegularPair u v := by
  constructor
  · rintro ⟨hu, hv, hn⟩
    refine ⟨fun h => hu (by rw [h, smul_zero]), fun h => hv (by rw [h, smul_zero]), ?_⟩
    rintro ⟨r, hr, hvu⟩
    apply hn
    refine ⟨r * b / a, by
      have : r * b < 0 := mul_neg_of_neg_of_pos hr hb
      exact div_neg_of_neg_of_pos this ha, ?_⟩
    rw [hvu, smul_smul, smul_smul]
    congr 1
    field_simp
  · rintro ⟨hu, hv, hn⟩
    refine ⟨smul_ne_zero ha.ne' hu, smul_ne_zero hb.ne' hv, ?_⟩
    rintro ⟨r, hr, hvu⟩
    apply hn
    refine ⟨r * a / b, by
      have : r * a < 0 := mul_neg_of_neg_of_pos hr ha
      exact div_neg_of_neg_of_pos this hb, ?_⟩
    have h1 : v = (1 / b) • (b • v) := by rw [smul_smul, one_div_mul_cancel hb.ne', one_smul]
    rw [h1, hvu, smul_smul, smul_smul]
    congr 1
    field_simp

/-- Two unit directions whose angle difference is within `π` of an integer multiple of `2π`
form a regular pair (they are not antiparallel). -/
theorem mcB_regularPair_unitDir {α β : ℝ} (m : ℤ) (h : |β - α - 2 * π * m| < π) :
    RegularPair (unitDir α) (unitDir β) := by
  refine ⟨mcB_unitDir_ne_zero α, mcB_unitDir_ne_zero β, ?_⟩
  rintro ⟨r, hr, hβ⟩
  have hlen := congrArg euclideanLength hβ
  rw [euclideanLength_smul, mcB_euclideanLength_unitDir, mcB_euclideanLength_unitDir,
    mul_one, abs_of_neg hr] at hlen
  have hr1 : r = -1 := by linarith
  rw [hr1] at hβ
  have hc : Real.cos β = -Real.cos α := by
    have := congrArg Prod.fst hβ
    simpa [unitDir] using this
  have hs : Real.sin β = -Real.sin α := by
    have := congrArg Prod.snd hβ
    simpa [unitDir] using this
  have hcos : Real.cos (β - (α + π)) = 1 := by
    rw [Real.cos_sub, Real.cos_add_pi, Real.sin_add_pi, hc, hs]
    nlinarith [Real.cos_sq_add_sin_sq α]
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hcos
  have he : β - α - 2 * π * m = π * (1 + 2 * (k - m)) := by
    have : (k : ℝ) * (2 * π) = β - (α + π) := hk
    linear_combination -this
  rw [he, abs_mul, abs_of_pos Real.pi_pos] at h
  have h2 : |(1 : ℝ) + 2 * (k - m)| < 1 := by
    have := Real.pi_pos
    nlinarith
  have h3 : |(1 : ℤ) + 2 * (k - m)| < 1 := by exact_mod_cast h2
  have h4 := Int.abs_lt_one_iff.mp h3
  omega

/-! ### A labelled tuple from its edge vectors -/

variable {n : ℕ}

/-- The tuple with base vertex `base` and prescribed edge vectors `e` (source: "successively
add the positive vectors `l_i(t) u_i(t)`"). -/
def mcB_tupleOfEdges (base : Plane) (e : ZMod n → Plane) : LabelledTuple n :=
  fun i => base + ∑ j ∈ Finset.range i.val, e (j : ZMod n)

theorem mcB_tupleOfEdges_zero [NeZero n] (base : Plane) (e : ZMod n → Plane) :
    mcB_tupleOfEdges base e 0 = base := by
  simp [mcB_tupleOfEdges]

theorem mcB_edge_tupleOfEdges [NeZero n] (base : Plane) (e : ZMod n → Plane)
    (hsum : ∑ i, e i = 0) (i : ZMod n) : edge (mcB_tupleOfEdges base e) i = e i := by
  have hi : ((i.val : ℕ) : ZMod n) = i := ZMod.natCast_zmod_val i
  have hlt : i.val < n := ZMod.val_lt i
  unfold edge mcB_tupleOfEdges
  rcases Nat.lt_or_ge (i.val + 1) n with hlt1 | hge
  · have h1 : i + 1 = ((i.val + 1 : ℕ) : ZMod n) := by push_cast; rw [hi]
    have hv : (i + 1).val = i.val + 1 := by rw [h1, ZMod.val_natCast_of_lt hlt1]
    rw [hv, Finset.sum_range_succ, hi]
    abel
  · have hn1 : i.val + 1 = n := by omega
    have h1 : i + 1 = 0 := by
      have : i + 1 = ((i.val + 1 : ℕ) : ZMod n) := by push_cast; rw [hi]
      rw [this, hn1, ZMod.natCast_self]
    have hsr : ∑ j ∈ Finset.range (i.val + 1), e (j : ZMod n) = 0 := by
      rw [hn1, ← sum_zmod_eq_sum_range]; exact hsum
    rw [Finset.sum_range_succ, hi] at hsr
    rw [h1, ZMod.val_zero, Finset.sum_range_zero]
    have : ∑ j ∈ Finset.range i.val, e (j : ZMod n) = -e i := by linear_combination hsr
    rw [this]
    abel

/-- Telescoping: a tuple is recovered from its base vertex and its edges. -/
theorem mcB_tupleOfEdges_edge [NeZero n] (P : LabelledTuple n) :
    mcB_tupleOfEdges (P 0) (edge P) = P := by
  funext i
  have hi : ((i.val : ℕ) : ZMod n) = i := ZMod.natCast_zmod_val i
  unfold mcB_tupleOfEdges
  have key : ∀ k : ℕ, P 0 + ∑ j ∈ Finset.range k, edge P (j : ZMod n) = P (k : ZMod n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ih]
      simp [edge]
  rw [key, hi]

theorem mcB_continuousOn_tupleOfEdges {base : ℝ → Plane} {e : ZMod n → ℝ → Plane} {s : Set ℝ}
    (hb : ContinuousOn base s) (he : ∀ i, ContinuousOn (e i) s) :
    ContinuousOn (fun t => mcB_tupleOfEdges (base t) (fun i => e i t)) s := by
  apply continuousOn_pi.mpr
  intro i
  apply hb.add
  exact continuousOn_finsetSum _ (fun j _ => he _)

/-! ### Paths from continuous families on `[0, 1]` -/

theorem mcB_joinedIn_of_continuousOn {X : Type*} [TopologicalSpace X] {F : Set X} {f : ℝ → X}
    (hf : ContinuousOn f (Icc 0 1)) (hF : ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ F) :
    JoinedIn F (f 0) (f 1) := by
  refine ⟨{ toFun := fun t => f t
            continuous_toFun := hf.comp_continuous continuous_subtype_val (fun t => t.2)
            source' := by simp
            target' := by simp }, ?_⟩
  intro t
  exact hF t t.2


/-! ### Index arithmetic in `ZMod n` -/

theorem mcB_neg_one_val [NeZero n] : ((0 : ZMod n) - 1).val = n - 1 := by
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel NeZero.one_le
  have h : (0 : ZMod n) - 1 = ((n - 1 : ℕ) : ZMod n) := by
    have h2 : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
      rw [← Nat.cast_add_one, hn, ZMod.natCast_self]
    linear_combination -h2
  rw [h, ZMod.val_natCast_of_lt (by omega)]

theorem mcB_pred_val [NeZero n] (i : ZMod n) (hi : i ≠ 0) : (i - 1).val + 1 = i.val := by
  have hv : i.val ≠ 0 := fun h => hi ((ZMod.val_eq_zero i).mp h)
  have hlt : i.val < n := ZMod.val_lt i
  have h : i - 1 = ((i.val - 1 : ℕ) : ZMod n) := by
    have h2 : ((i.val - 1 : ℕ) : ZMod n) + 1 = i := by
      rw [← Nat.cast_add_one, Nat.sub_add_cancel (Nat.pos_of_ne_zero hv), ZMod.natCast_zmod_val]
    linear_combination -h2
  rw [h, ZMod.val_natCast_of_lt (by omega)]
  omega

theorem mcB_succ_val_of_lt [NeZero n] (i : ZMod n) (h : i.val + 1 < n) :
    (i + 1).val = i.val + 1 := by
  have h1 : i + 1 = ((i.val + 1 : ℕ) : ZMod n) := by push_cast; rw [ZMod.natCast_zmod_val]
  rw [h1, ZMod.val_natCast_of_lt h]

theorem mcB_succ_eq_zero [NeZero n] (i : ZMod n) (h : i.val + 1 = n) : i + 1 = 0 := by
  have h1 : i + 1 = ((i.val + 1 : ℕ) : ZMod n) := by push_cast; rw [ZMod.natCast_zmod_val]
  rw [h1, h, ZMod.natCast_self]

theorem mcB_abs_convex_lt {a b t c : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ha : |a| < c) (hb : |b| < c) :
    |(1 - t) * a + t * b| < c := by
  obtain ⟨ht0, ht1⟩ := ht
  calc |(1 - t) * a + t * b| ≤ |(1 - t) * a| + |t * b| := abs_add_le _ _
    _ = (1 - t) * |a| + t * |b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg ht0]
    _ < c := by
        rcases lt_or_eq_of_le ht1 with h | h
        · nlinarith [mul_pos (sub_pos.mpr h) (sub_pos.mpr ha), mul_nonneg ht0 (sub_pos.mpr hb).le]
        · rw [h]; simpa using hb

/-! ### Layer 1: reconstructing a regular path from a lifted direction path

The lifted edge arguments `Θ t k`, `0 ≤ k ≤ n` (source `transport:prefix`), have consecutive
differences of absolute value `< π` and close up to `2πr`; the unit directions lie in no closed
semicircle; the endpoint polygons have edges pointing along the endpoint directions. Then a
continuous path of regular polygons joins the endpoints (source: "Reconstructing a polygon from
directions"). -/

theorem mcB_joinedIn_regular_of_liftedAngles [NeZero n] {P P' : LabelledTuple n} (r : ℤ)
    (Θ : ℝ → ℕ → ℝ) (hΘ : ∀ k, ContinuousOn (fun t => Θ t k) (Icc 0 1))
    (hstep : ∀ t ∈ Icc (0 : ℝ) 1, ∀ k, k < n → |Θ t (k + 1) - Θ t k| < π)
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1, Θ t n = Θ t 0 + 2 * π * r)
    (hsemi : ∀ t ∈ Icc (0 : ℝ) 1, ¬ InClosedSemicircle (fun i : ZMod n => Θ t i.val))
    (h0 : ∀ i : ZMod n, ∃ m : ℝ, 0 < m ∧ edge P i = m • unitDir (Θ 0 i.val))
    (h1 : ∀ i : ZMod n, ∃ m : ℝ, 0 < m ∧ edge P' i = m • unitDir (Θ 1 i.val)) :
    JoinedIn {Q : LabelledTuple n | Regular Q} P P' := by
  set u : ZMod n → ℝ → Plane := fun i t => unitDir (Θ t i.val) with hu
  have huc : ∀ i, ContinuousOn (u i) (Icc 0 1) := fun i =>
    (Real.continuous_cos.comp_continuousOn (hΘ _)).prodMk
      (Real.continuous_sin.comp_continuousOn (hΘ _))
  have hunit : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, euclideanLength (u i t) = 1 :=
    fun i t _ => mcB_euclideanLength_unitDir _
  have hsemi' : ∀ t ∈ Icc (0 : ℝ) 1,
      ¬ ∃ v : Plane, euclideanLength v = 1 ∧ ∀ i, 0 ≤ planeDot v (u i t) := by
    rintro t ht ⟨v, hv, hdot⟩
    apply hsemi t ht
    refine ⟨v, ?_, hdot⟩
    rw [← euclideanLength_mul_self, hv, one_mul]
  have hreg : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i, RegularPair (u (i - 1) t) (u i t) := by
    intro t ht i
    by_cases hi : i = 0
    · subst hi
      apply mcB_regularPair_unitDir (-r)
      rw [mcB_neg_one_val, ZMod.val_zero]
      have hs := hstep t ht (n - 1) (by have := NeZero.one_le (n := n); omega)
      rw [Nat.sub_add_cancel NeZero.one_le, hclose t ht] at hs
      convert hs using 2
      push_cast
      ring
    · obtain hk := mcB_pred_val i hi
      apply mcB_regularPair_unitDir 0
      simp only [Int.cast_zero, mul_zero, sub_zero]
      rw [← hk]
      exact hstep t ht _ (by have := ZMod.val_lt i; omega)
  obtain ⟨l, hlc, hlpos, hlsum, hjoin0, hjoin1⟩ :=
    transport_lengths zero_le_one u huc hunit hsemi'
  set base : ℝ → Plane := fun t => (1 - t) • P 0 + t • P' 0 with hbase
  have hbasec : ContinuousOn base (Icc 0 1) :=
    ((continuousOn_const.sub continuousOn_id).smul continuousOn_const).add
      (continuousOn_id.smul continuousOn_const)
  set Q : ℝ → LabelledTuple n := fun t => mcB_tupleOfEdges (base t) (fun i => l i t • u i t)
    with hQ
  have hQreg : ∀ t ∈ Icc (0 : ℝ) 1, Regular (Q t) := by
    intro t ht i
    simp only [hQ]
    rw [mcB_edge_tupleOfEdges _ _ (hlsum t ht), mcB_edge_tupleOfEdges _ _ (hlsum t ht)]
    exact (mcB_regularPair_smul (hlpos _ t ht) (hlpos _ t ht)).mpr (hreg t ht i)
  have hQc : ContinuousOn Q (Icc 0 1) :=
    mcB_continuousOn_tupleOfEdges hbasec (fun i => (hlc i).smul (huc i))
  have hmid : JoinedIn {Q : LabelledTuple n | Regular Q} (Q 0) (Q 1) :=
    mcB_joinedIn_of_continuousOn hQc hQreg
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hI1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- left endpoint join
  choose m hmpos hm using h0
  have hmsum : ∑ i, m i • u i 0 = 0 := by
    rw [← sum_edges P]
    exact Finset.sum_congr rfl (fun i _ => (hm i).symm)
  have hleft : JoinedIn {Q : LabelledTuple n | Regular Q} P (Q 0) := by
    set R : ℝ → LabelledTuple n :=
      fun s => mcB_tupleOfEdges (P 0) (fun i => ((1 - s) * m i + s * l i 0) • u i 0) with hR
    have hR0 : R 0 = P := by
      simp only [hR, sub_zero, one_mul, zero_mul, add_zero]
      have : (fun i => m i • u i 0) = edge P := funext (fun i => (hm i).symm)
      rw [this, mcB_tupleOfEdges_edge]
    have hR1 : R 1 = Q 0 := by
      simp only [hR, hQ, hbase, sub_self, zero_mul, zero_add, one_mul, zero_smul, one_smul,
        sub_zero, add_zero]
    have hRreg : ∀ s ∈ Icc (0 : ℝ) 1, Regular (R s) := by
      intro s hs i
      obtain ⟨hpos, hsum⟩ := hjoin0 m hmpos hmsum s hs
      simp only [hR]
      rw [mcB_edge_tupleOfEdges _ _ hsum, mcB_edge_tupleOfEdges _ _ hsum]
      exact (mcB_regularPair_smul (hpos _) (hpos _)).mpr (hreg 0 hI0 i)
    have hRc : ContinuousOn R (Icc 0 1) :=
      mcB_continuousOn_tupleOfEdges continuousOn_const (fun i =>
        (((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
          (continuousOn_id.mul continuousOn_const)).smul continuousOn_const)
    have := mcB_joinedIn_of_continuousOn (F := {Q : LabelledTuple n | Regular Q}) hRc hRreg
    rwa [hR0, hR1] at this
  -- right endpoint join
  choose m' hm'pos hm' using h1
  have hm'sum : ∑ i, m' i • u i 1 = 0 := by
    rw [← sum_edges P']
    exact Finset.sum_congr rfl (fun i _ => (hm' i).symm)
  have hright : JoinedIn {Q : LabelledTuple n | Regular Q} P' (Q 1) := by
    set R : ℝ → LabelledTuple n :=
      fun s => mcB_tupleOfEdges (P' 0) (fun i => ((1 - s) * m' i + s * l i 1) • u i 1) with hR
    have hR0 : R 0 = P' := by
      simp only [hR, sub_zero, one_mul, zero_mul, add_zero]
      have : (fun i => m' i • u i 1) = edge P' := funext (fun i => (hm' i).symm)
      rw [this, mcB_tupleOfEdges_edge]
    have hR1 : R 1 = Q 1 := by
      simp only [hR, hQ, hbase, sub_self, zero_mul, zero_add, one_mul, zero_smul, one_smul]
    have hRreg : ∀ s ∈ Icc (0 : ℝ) 1, Regular (R s) := by
      intro s hs i
      obtain ⟨hpos, hsum⟩ := hjoin1 m' hm'pos hm'sum s hs
      simp only [hR]
      rw [mcB_edge_tupleOfEdges _ _ hsum, mcB_edge_tupleOfEdges _ _ hsum]
      exact (mcB_regularPair_smul (hpos _) (hpos _)).mpr (hreg 1 hI1 i)
    have hRc : ContinuousOn R (Icc 0 1) :=
      mcB_continuousOn_tupleOfEdges continuousOn_const (fun i =>
        (((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
          (continuousOn_id.mul continuousOn_const)).smul continuousOn_const)
    have := mcB_joinedIn_of_continuousOn (F := {Q : LabelledTuple n | Regular Q}) hRc hRreg
    rwa [hR0, hR1] at this
  exact hleft.trans (hmid.trans hright.symm)

/-! ### Lifted edge arguments of a regular polygon (source `transport:prefix`) -/

/-- `θ_k = β + ∑_{m=1}^{k} ϑ_m`, with `β` the argument of the edge `E_0` (source label `n`). -/
noncomputable def mcB_liftArg [NeZero n] (P : LabelledTuple n) (k : ℕ) : ℝ :=
  (planeComplex (edge P 0)).arg + turnPrefix P k

theorem mcB_liftArg_succ [NeZero n] (P : LabelledTuple n) (k : ℕ) :
    mcB_liftArg P (k + 1) - mcB_liftArg P k = principalTurn P ((k + 1 : ℕ) : ZMod n) := by
  unfold mcB_liftArg turnPrefix
  rw [Finset.sum_range_succ]
  ring

theorem mcB_abs_liftArg_succ_lt [NeZero n] {P : LabelledTuple n} (hP : Regular P) (k : ℕ) :
    |mcB_liftArg P (k + 1) - mcB_liftArg P k| < π := by
  rw [mcB_liftArg_succ]
  exact principalTurn_abs_lt_pi hP _

theorem mcB_liftArg_coe_angle [NeZero n] {P : LabelledTuple n} (hP : Regular P) (k : ℕ) :
    (mcB_liftArg P k : Real.Angle) = ((planeComplex (edge P (k : ZMod n))).arg : Real.Angle) := by
  unfold mcB_liftArg
  rw [Real.Angle.coe_add, turnPrefix_coe_angle hP]
  unfold edgeDirectionAngle
  abel

theorem mcB_turnPrefix_n [NeZero n] (P : LabelledTuple n) :
    turnPrefix P n = ∑ i : ZMod n, principalTurn P i := by
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel NeZero.one_le
  have h := Finset.sum_range_succ (fun j : ℕ => principalTurn P ((j + 1 : ℕ) : ZMod n)) (n - 1)
  rw [hn] at h
  rw [sum_principalTurn_eq_prefix]
  unfold turnPrefix
  rw [h]
  simp only [ZMod.natCast_self]

theorem mcB_liftArg_n [NeZero n] {P : LabelledTuple n} (_hP : Regular P) :
    mcB_liftArg P n = mcB_liftArg P 0 + 2 * π * rotationNumber P := by
  unfold mcB_liftArg turnPrefix
  simp only [Finset.range_zero, Finset.sum_empty, add_zero]
  have h := mcB_turnPrefix_n P
  unfold turnPrefix at h
  rw [h]
  unfold rotationNumber
  field_simp

theorem mcB_edge_eq_smul_unitDir [NeZero n] {P : LabelledTuple n} (hP : Regular P) (i : ZMod n) :
    edge P i = euclideanLength (edge P i) • unitDir (mcB_liftArg P i.val) := by
  rw [mcB_unitDir_eq_of_angle_eq (mcB_liftArg_coe_angle hP i.val), ZMod.natCast_zmod_val]
  exact mcB_eq_length_smul_unitDir_arg _

/-! ### Nonzero rotation excludes closed semicircles (source: "Nonzero rotation") -/

theorem mcB_not_semicircle_of_rot_ne_zero [NeZero n] (Θ : ℕ → ℝ) (r : ℤ) (hr : r ≠ 0)
    (hstep : ∀ k, k < n → |Θ (k + 1) - Θ k| < π) (hclose : Θ n = Θ 0 + 2 * π * r) :
    ¬ InClosedSemicircle (fun i : ZMod n => Θ i.val) := by
  rintro ⟨v, hv, hdot⟩
  set Θ' : Fin (n + 1) → ℝ := fun k => Θ k.val with hΘ'
  have hstep' : ∀ k : Fin n, |Θ' k.succ - Θ' k.castSucc| < π := fun k => hstep k.val k.isLt
  have hsemi' : InClosedSemicircle Θ' := by
    refine ⟨v, hv, fun k => ?_⟩
    rcases Nat.lt_or_ge k.val n with hk | hk
    · have := hdot (k.val : ZMod n)
      simp only [ZMod.val_natCast_of_lt hk] at this
      exact this
    · have hk' : k.val = n := by omega
      show 0 ≤ planeDot v (unitDir (Θ k.val))
      rw [hk', hclose, mcB_unitDir_add_two_pi_mul_int]
      have := hdot 0
      simp only [ZMod.val_zero] at this
      exact this
  obtain ⟨c, hc⟩ := transport_angle_interval Θ' hstep' hsemi'
  have h0 := hc 0
  have hn := hc (Fin.last n)
  simp only [hΘ', Fin.val_zero, Fin.val_last] at h0 hn
  rw [hclose] at hn
  have h3 : |(r : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith [Real.pi_pos]
  have h4 : |r| < 1 := by exact_mod_cast h3
  exact hr (Int.abs_lt_one_iff.mp h4)

/-! ### Layer 2: nonzero rotation (source: "Nonzero rotation") -/

theorem mcB_joined_regular_nonzero_rotation [NeZero n] {P P' : LabelledTuple n}
    (hP : Regular P) (hP' : Regular P') (r : ℤ) (hr : r ≠ 0)
    (hrP : rotationNumber P = r) (hrP' : rotationNumber P' = r) :
    JoinedIn {Q : LabelledTuple n | Regular Q} P P' := by
  set Θ : ℝ → ℕ → ℝ := fun t k => (1 - t) * mcB_liftArg P k + t * mcB_liftArg P' k with hΘ
  have hstep : ∀ t ∈ Icc (0 : ℝ) 1, ∀ k, k < n → |Θ t (k + 1) - Θ t k| < π := by
    intro t ht k _
    have e : Θ t (k + 1) - Θ t k = (1 - t) * (mcB_liftArg P (k + 1) - mcB_liftArg P k) +
        t * (mcB_liftArg P' (k + 1) - mcB_liftArg P' k) := by
      simp only [hΘ]; ring
    rw [e]
    exact mcB_abs_convex_lt ht (mcB_abs_liftArg_succ_lt hP k) (mcB_abs_liftArg_succ_lt hP' k)
  have hclose : ∀ t ∈ Icc (0 : ℝ) 1, Θ t n = Θ t 0 + 2 * π * r := by
    intro t _
    simp only [hΘ]
    rw [mcB_liftArg_n hP, mcB_liftArg_n hP', hrP, hrP']
    ring
  refine mcB_joinedIn_regular_of_liftedAngles r Θ ?_ hstep hclose ?_ ?_ ?_
  · intro k
    exact ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
      (continuousOn_id.mul continuousOn_const)
  · intro t ht
    exact mcB_not_semicircle_of_rot_ne_zero (Θ t) r hr (hstep t ht) (hclose t ht)
  · intro i
    refine ⟨euclideanLength (edge P i), euclideanLength_pos (hP i).2.1, ?_⟩
    have e : Θ 0 i.val = mcB_liftArg P i.val := by simp only [hΘ]; ring
    rw [e]
    exact mcB_edge_eq_smul_unitDir hP i
  · intro i
    refine ⟨euclideanLength (edge P' i), euclideanLength_pos (hP' i).2.1, ?_⟩
    have e : Θ 1 i.val = mcB_liftArg P' i.val := by simp only [hΘ]; ring
    rw [e]
    exact mcB_edge_eq_smul_unitDir hP' i

/-! ### Rotation is constant along regular paths (lem:rot (ii)) -/

theorem mcB_joinedIn_fibre_of_regular [NeZero n] {P P' : LabelledTuple n} (r : ℝ)
    (hrP : rotationNumber P = r) (h : JoinedIn {Q : LabelledTuple n | Regular Q} P P') :
    JoinedIn {Q : LabelledTuple n | Regular Q ∧ rotationNumber Q = r} P P' := by
  obtain ⟨γ, hγ⟩ := h
  refine ⟨γ, fun t => ⟨hγ t, ?_⟩⟩
  have := rotationNumber_family_constant γ.continuous hγ t 0
  rw [this, γ.source, hrP]


/-! ### Layer 3: the zero-rotation angle domain (source: "The zero-rotation angle domain") -/

/-- `transport:zero-angle-domain`: `|θ_{i+1} − θ_i| < π` cyclically. -/
def mcB_CyclicSteps (θ : ZMod n → ℝ) : Prop := ∀ i, |θ (i + 1) - θ i| < π

/-- `transport:chart`: the chart `A(h, d)`. -/
def mcB_Chart (h : ZMod n) (d : ℕ) (θ : ZMod n → ℝ) : Prop :=
  mcB_CyclicSteps θ ∧ θ h - θ (h + d) > π

/-- The feasible zero-rotation angle vectors: cyclic steps `< π` and unit directions lying in
no closed semicircle. -/
def mcB_ZeroDomain (θ : ZMod n → ℝ) : Prop := mcB_CyclicSteps θ ∧ ¬ InClosedSemicircle θ

/-- Every chart point has directions lying in no closed semicircle
(Lemma transport-angle-interval applied to the cyclic sequence starting at `h`). -/
theorem mcB_chart_not_semicircle [NeZero n] {h : ZMod n} {d : ℕ} (hd : d ≤ n)
    {θ : ZMod n → ℝ} (hθ : mcB_Chart h d θ) : ¬ InClosedSemicircle θ := by
  rintro ⟨v, hv, hdot⟩
  set Θ' : Fin (n + 1) → ℝ := fun k => θ (h + (k.val : ZMod n)) with hΘ'
  have hstep' : ∀ k : Fin n, |Θ' k.succ - Θ' k.castSucc| < π := by
    intro k
    simp only [hΘ', Fin.val_succ, Fin.val_castSucc]
    push_cast
    rw [← add_assoc]
    exact hθ.1 _
  have hsemi' : InClosedSemicircle Θ' := ⟨v, hv, fun k => hdot _⟩
  obtain ⟨c, hc⟩ := transport_angle_interval Θ' hstep' hsemi'
  have h0 := hc 0
  have hdd := hc ⟨d, by omega⟩
  simp only [hΘ', Fin.val_zero, Nat.cast_zero, add_zero] at h0 hdd
  have := hθ.2
  linarith [h0.2, hdd.1]

theorem mcB_chart_mem_zeroDomain [NeZero n] {h : ZMod n} {d : ℕ} (hd : d ≤ n)
    {θ : ZMod n → ℝ} (hθ : mcB_Chart h d θ) : mcB_ZeroDomain θ :=
  ⟨hθ.1, mcB_chart_not_semicircle hd hθ⟩

theorem mcB_natCast_pred [NeZero n] : ((n - 1 : ℕ) : ZMod n) = -1 := by
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel NeZero.one_le
  have h2 : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
    rw [← Nat.cast_add_one, hn, ZMod.natCast_self]
  linear_combination h2

/-- The charts cover the zero-rotation domain: take a maximum `h` and a minimum `m`; they are
not cyclically adjacent, and `θ_h − θ_m > π`. -/
theorem mcB_exists_chart [NeZero n] {θ : ZMod n → ℝ} (hθ : mcB_ZeroDomain θ) :
    ∃ h : ZMod n, ∃ d : ℕ, 2 ≤ d ∧ d ≤ n - 2 ∧ mcB_Chart h d θ := by
  obtain ⟨hstep, hsemi⟩ := hθ
  obtain ⟨h, hmax⟩ := Finite.exists_max θ
  obtain ⟨m, hmin⟩ := Finite.exists_min θ
  have hgap : θ h - θ m > π := by
    by_contra hle
    push Not at hle
    apply hsemi
    apply transport_angle_interval_converse
    exact ⟨θ m, fun i => ⟨hmin i, by linarith [hmax i]⟩⟩
  have hcast : (((m - h).val : ℕ) : ZMod n) = m - h := ZMod.natCast_zmod_val _
  have hlt : (m - h).val < n := ZMod.val_lt _
  refine ⟨h, (m - h).val, ?_, ?_, hstep, ?_⟩
  · by_contra hlt2
    push Not at hlt2
    rcases Nat.lt_or_ge (m - h).val 1 with h0 | h1
    · have hv : (m - h).val = 0 := by omega
      have : m = h := by
        have := (ZMod.val_eq_zero (m - h)).mp hv
        linear_combination this
      rw [this] at hgap
      linarith [Real.pi_pos]
    · have hv : (m - h).val = 1 := by omega
      have hm : m = h + 1 := by
        rw [hv] at hcast
        push_cast at hcast
        linear_combination -hcast
      have := abs_lt.mp (hstep h)
      rw [hm] at hgap
      linarith
  · by_contra hgt
    push Not at hgt
    have hv : (m - h).val = n - 1 := by omega
    have hm : h = m + 1 := by
      rw [hv, mcB_natCast_pred] at hcast
      linear_combination hcast
    have := abs_lt.mp (hstep m)
    rw [hm] at hgap
    linarith
  · rw [hcast]
    simpa using hgap

theorem mcB_convex_gt {a b t c : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ha : a > c) (hb : b > c) :
    (1 - t) * a + t * b > c := by
  obtain ⟨ht0, ht1⟩ := ht
  rcases lt_or_eq_of_le ht1 with h | h
  · nlinarith [mul_pos (sub_pos.mpr h) (sub_pos.mpr ha), mul_nonneg ht0 (sub_pos.mpr hb).le]
  · rw [h]; simpa using hb

/-- The charts are convex. -/
theorem mcB_chart_convex_comb {h : ZMod n} {d : ℕ} {θ θ' : ZMod n → ℝ}
    (hθ : mcB_Chart h d θ) (hθ' : mcB_Chart h d θ') {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    mcB_Chart h d (fun i => (1 - s) * θ i + s * θ' i) := by
  refine ⟨fun i => ?_, ?_⟩
  · have e : (1 - s) * θ (i + 1) + s * θ' (i + 1) - ((1 - s) * θ i + s * θ' i) =
        (1 - s) * (θ (i + 1) - θ i) + s * (θ' (i + 1) - θ' i) := by ring
    simp only
    rw [e]
    exact mcB_abs_convex_lt hs (hθ.1 i) (hθ'.1 i)
  · have e : (1 - s) * θ h + s * θ' h - ((1 - s) * θ (h + d) + s * θ' (h + d)) =
        (1 - s) * (θ h - θ (h + d)) + s * (θ' h - θ' (h + d)) := by ring
    simp only
    rw [e]
    exact mcB_convex_gt hs hθ.2 hθ'.2

/-- Two points of one chart are joined by a straight segment inside the zero-rotation domain. -/
theorem mcB_joined_same_chart [NeZero n] {h : ZMod n} {d : ℕ} (hd : d ≤ n)
    {θ θ' : ZMod n → ℝ} (hθ : mcB_Chart h d θ) (hθ' : mcB_Chart h d θ') :
    JoinedIn {ψ : ZMod n → ℝ | mcB_ZeroDomain ψ} θ θ' := by
  have hc : ContinuousOn (fun s : ℝ => fun i => (1 - s) * θ i + s * θ' i) (Icc 0 1) :=
    continuousOn_pi.mpr (fun i =>
      ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
        (continuousOn_id.mul continuousOn_const))
  have := mcB_joinedIn_of_continuousOn (F := {ψ : ZMod n → ℝ | mcB_ZeroDomain ψ}) hc
    (fun s hs => mcB_chart_mem_zeroDomain hd (mcB_chart_convex_comb hθ hθ' hs))
  simpa using this

/-! ### Chart overlaps for `n ≥ 5` (source: "Connected chart overlaps for n ≥ 5")

The witnesses are three-valued, with the values `3π/2, 3π/4, 0`; the source uses linear
ramps, and only nonemptiness of the overlaps matters. -/

set_option linter.unusedSimpArgs false

/-- Witness for `A(h,d) ∩ A(h,d+1)`, as a function of the cyclic distance `s` from `h`. -/
noncomputable def mcB_w1 (n : ℕ) (s : ℕ) : ℝ :=
  if s = 0 then 3 * π / 2 else if s = 1 ∨ s = n - 1 then 3 * π / 4 else 0

/-- Witness for `A(h,d+1) ∩ A(h+1,d)`. -/
noncomputable def mcB_w2 (n : ℕ) (s : ℕ) : ℝ :=
  if s = 0 ∨ s = 1 then 3 * π / 2 else if s = 2 ∨ s = n - 1 then 3 * π / 4 else 0

/-- The cyclic angle vector reading `w` at the cyclic distance from `h`. -/
def mcB_cyc (h : ZMod n) (w : ℕ → ℝ) : ZMod n → ℝ := fun i => w (i - h).val

theorem mcB_cyc_apply_add [NeZero n] (h : ZMod n) (w : ℕ → ℝ) {d : ℕ} (hd : d < n) :
    mcB_cyc h w (h + d) = w d := by
  simp only [mcB_cyc, add_sub_cancel_left, ZMod.val_natCast_of_lt hd]

theorem mcB_cyc_apply_self (h : ZMod n) (w : ℕ → ℝ) : mcB_cyc h w h = w 0 := by
  simp [mcB_cyc]

theorem mcB_cyclicSteps_cyc [NeZero n] (h : ZMod n) (w : ℕ → ℝ)
    (hw : ∀ s, s + 1 < n → |w (s + 1) - w s| < π) (hwrap : |w 0 - w (n - 1)| < π) :
    mcB_CyclicSteps (mcB_cyc h w) := by
  intro i
  have e : i + 1 - h = (i - h) + 1 := by ring
  simp only [mcB_cyc]
  rw [e]
  rcases Nat.lt_or_ge ((i - h).val + 1) n with hlt | hge
  · rw [mcB_succ_val_of_lt _ hlt]
    exact hw _ hlt
  · have hn1 : 1 ≤ n := NeZero.one_le
    have hv : (i - h).val = n - 1 := by have := ZMod.val_lt (i - h); omega
    rw [mcB_succ_eq_zero (i - h) (by omega), ZMod.val_zero, hv]
    exact hwrap

theorem mcB_w1_charts [NeZero n] (hn : 5 ≤ n) (h : ZMod n) {d : ℕ} (hd2 : 2 ≤ d)
    (hdn : d ≤ n - 3) :
    mcB_Chart h d (mcB_cyc h (mcB_w1 n)) ∧ mcB_Chart h (d + 1) (mcB_cyc h (mcB_w1 n)) := by
  have hsteps : mcB_CyclicSteps (mcB_cyc h (mcB_w1 n)) := by
    apply mcB_cyclicSteps_cyc
    · intro s hs
      unfold mcB_w1
      split_ifs <;>
        (try simp only [false_or, or_false, or_true, true_or, not_true_eq_false,
          not_false_eq_true] at *) <;>
        first | omega | (rw [abs_lt]; constructor <;> linarith [Real.pi_pos])
    · unfold mcB_w1
      split_ifs <;>
        (try simp only [false_or, or_false, or_true, true_or, not_true_eq_false,
          not_false_eq_true] at *) <;>
        first | omega | (rw [abs_lt]; constructor <;> linarith [Real.pi_pos])
  have h0 : mcB_cyc h (mcB_w1 n) h = 3 * π / 2 := by
    rw [mcB_cyc_apply_self]; simp [mcB_w1]
  have hd0 : mcB_cyc h (mcB_w1 n) (h + d) = 0 := by
    rw [mcB_cyc_apply_add h _ (by omega)]
    unfold mcB_w1
    split_ifs <;>
      (try simp only [false_or, or_false, or_true, true_or, not_true_eq_false,
        not_false_eq_true] at *) <;>
      omega
  have hd1 : mcB_cyc h (mcB_w1 n) (h + ((d + 1 : ℕ) : ZMod n)) = 0 := by
    rw [mcB_cyc_apply_add h _ (by omega)]
    unfold mcB_w1
    split_ifs <;>
      (try simp only [false_or, or_false, or_true, true_or, not_true_eq_false,
        not_false_eq_true] at *) <;>
      omega
  refine ⟨⟨hsteps, ?_⟩, ⟨hsteps, ?_⟩⟩
  · rw [h0, hd0]; linarith [Real.pi_pos]
  · rw [h0, hd1]; linarith [Real.pi_pos]

theorem mcB_w2_charts [NeZero n] (hn : 5 ≤ n) (h : ZMod n) {d : ℕ} (hd2 : 2 ≤ d)
    (hdn : d ≤ n - 3) :
    mcB_Chart h (d + 1) (mcB_cyc h (mcB_w2 n)) ∧
      mcB_Chart (h + 1) d (mcB_cyc h (mcB_w2 n)) := by
  have hsteps : mcB_CyclicSteps (mcB_cyc h (mcB_w2 n)) := by
    apply mcB_cyclicSteps_cyc
    · intro s hs
      unfold mcB_w2
      split_ifs <;>
        (try simp only [false_or, or_false, or_true, true_or, not_true_eq_false,
          not_false_eq_true] at *) <;>
        first | omega | (rw [abs_lt]; constructor <;> linarith [Real.pi_pos])
    · unfold mcB_w2
      split_ifs <;>
        (try simp only [false_or, or_false, or_true, true_or, not_true_eq_false,
          not_false_eq_true] at *) <;>
        first | omega | (rw [abs_lt]; constructor <;> linarith [Real.pi_pos])
  have h0 : mcB_cyc h (mcB_w2 n) h = 3 * π / 2 := by
    rw [mcB_cyc_apply_self]; simp [mcB_w2]
  have h1 : mcB_cyc h (mcB_w2 n) (h + 1) = 3 * π / 2 := by
    have := mcB_cyc_apply_add h (mcB_w2 n) (d := 1) (by omega)
    push_cast at this
    rw [this]; simp [mcB_w2]
  have hd1 : mcB_cyc h (mcB_w2 n) (h + ((d + 1 : ℕ) : ZMod n)) = 0 := by
    rw [mcB_cyc_apply_add h _ (by omega)]
    unfold mcB_w2
    split_ifs <;>
      (try simp only [false_or, or_false, or_true, true_or, not_true_eq_false,
        not_false_eq_true] at *) <;>
      omega
  have hd1' : mcB_cyc h (mcB_w2 n) (h + 1 + d) = 0 := by
    have e : h + 1 + (d : ZMod n) = h + ((d + 1 : ℕ) : ZMod n) := by push_cast; ring
    rw [e, hd1]
  refine ⟨⟨hsteps, ?_⟩, ⟨hsteps, ?_⟩⟩
  · rw [h0, hd1]; linarith [Real.pi_pos]
  · rw [h1, hd1']; linarith [Real.pi_pos]

set_option linter.unusedSimpArgs true

/-! ### The chart graph is connected (`n ≥ 5`) -/

theorem mcB_joined_to_two [NeZero n] (hn : 5 ≤ n) (h : ZMod n) :
    ∀ d : ℕ, 2 ≤ d → d ≤ n - 2 → ∀ θ θ₂ : ZMod n → ℝ, mcB_Chart h d θ → mcB_Chart h 2 θ₂ →
      JoinedIn {ψ : ZMod n → ℝ | mcB_ZeroDomain ψ} θ θ₂ := by
  intro d hd2
  induction d, hd2 using Nat.le_induction with
  | base =>
    intro _ θ θ₂ hθ hθ₂
    exact mcB_joined_same_chart (by omega) hθ hθ₂
  | succ d hd ih =>
    intro hdn θ θ₂ hθ hθ₂
    have hw := mcB_w1_charts hn h hd (by omega)
    exact (mcB_joined_same_chart (by omega) hθ hw.2).trans (ih (by omega) _ _ hw.1 hθ₂)

theorem mcB_joined_to_base [NeZero n] (hn : 5 ≤ n) :
    ∀ k : ℕ, ∀ θ θ₀ : ZMod n → ℝ, mcB_Chart (k : ZMod n) 2 θ → mcB_Chart 0 2 θ₀ →
      JoinedIn {ψ : ZMod n → ℝ | mcB_ZeroDomain ψ} θ θ₀ := by
  intro k
  induction k with
  | zero =>
    intro θ θ₀ hθ hθ₀
    rw [Nat.cast_zero] at hθ
    exact mcB_joined_same_chart (by omega) hθ hθ₀
  | succ k ih =>
    intro θ θ₀ hθ hθ₀
    have hw2 := mcB_w2_charts hn (k : ZMod n) (le_refl 2) (by omega)
    have hw1 := mcB_w1_charts hn (k : ZMod n) (le_refl 2) (by omega)
    rw [Nat.cast_succ] at hθ
    have h1 := mcB_joined_same_chart (by omega) hθ hw2.2
    have h2 := mcB_joined_to_two hn (k : ZMod n) 3 (by omega) (by omega) _ _ hw2.1 hw1.1
    have h3 := ih _ θ₀ hw1.1 hθ₀
    exact h1.trans (h2.trans h3)

/-- For `n ≥ 5` the zero-rotation angle domain is path connected. -/
theorem mcB_zeroDomain_joined [NeZero n] (hn : 5 ≤ n) {θ θ' : ZMod n → ℝ}
    (hθ : mcB_ZeroDomain θ) (hθ' : mcB_ZeroDomain θ') :
    JoinedIn {ψ : ZMod n → ℝ | mcB_ZeroDomain ψ} θ θ' := by
  have hbase : mcB_Chart (0 : ZMod n) 2 (mcB_cyc 0 (mcB_w1 n)) :=
    (mcB_w1_charts hn 0 le_rfl (by omega)).1
  have key : ∀ ψ : ZMod n → ℝ, mcB_ZeroDomain ψ →
      JoinedIn {ψ : ZMod n → ℝ | mcB_ZeroDomain ψ} ψ (mcB_cyc 0 (mcB_w1 n)) := by
    intro ψ hψ
    obtain ⟨h, d, hd2, hdn, hch⟩ := mcB_exists_chart hψ
    have hw1 := mcB_w1_charts hn h le_rfl (by omega)
    have h1 := mcB_joined_to_two hn h d hd2 hdn ψ _ hch hw1.1
    have h2 := mcB_joined_to_base hn h.val _ _ (by rw [ZMod.natCast_zmod_val]; exact hw1.1) hbase
    exact h1.trans h2
  exact (key θ hθ).trans (key θ' hθ').symm

/-! ### The angle vector of a zero-rotation regular polygon lies in the domain -/

/-- The cyclic vector of lifted edge arguments `(θ_1, …, θ_n)` (source label `n ≡ 0`). -/
noncomputable def mcB_angleVec [NeZero n] (P : LabelledTuple n) : ZMod n → ℝ :=
  fun i => mcB_liftArg P i.val

theorem mcB_angleVec_step [NeZero n] {P : LabelledTuple n} (hP : Regular P)
    (hr : rotationNumber P = 0) (i : ZMod n) :
    mcB_angleVec P (i + 1) - mcB_angleVec P i = principalTurn P (i + 1) := by
  unfold mcB_angleVec
  rcases Nat.lt_or_ge (i.val + 1) n with hlt | hge
  · rw [mcB_succ_val_of_lt i hlt, mcB_liftArg_succ]
    congr 1
    push_cast
    rw [ZMod.natCast_zmod_val]
  · have hn1 : 1 ≤ n := NeZero.one_le
    have hv : i.val = n - 1 := by have := ZMod.val_lt i; omega
    rw [mcB_succ_eq_zero i (by omega), ZMod.val_zero, hv]
    have h1 := mcB_liftArg_succ P (n - 1)
    rw [Nat.sub_add_cancel NeZero.one_le, mcB_liftArg_n hP, hr, ZMod.natCast_self] at h1
    simp only [mul_zero, add_zero] at h1
    exact h1

theorem mcB_angleVec_cyclicSteps [NeZero n] {P : LabelledTuple n} (hP : Regular P)
    (hr : rotationNumber P = 0) : mcB_CyclicSteps (mcB_angleVec P) := by
  intro i
  rw [mcB_angleVec_step hP hr]
  exact principalTurn_abs_lt_pi hP _

/-- The directions of a regular closed polygon lie in no closed half-plane through the origin
(source: "The directions of any regular closed polygon lie in no closed semicircle"). -/
theorem mcB_regular_not_halfplane [NeZero n] {P : LabelledTuple n} (hP : Regular P) :
    ¬ ∃ v : Plane, v ≠ 0 ∧ ∀ i, 0 ≤ planeDot v (edge P i) := by
  rintro ⟨v, hv, hdot⟩
  have hsum : ∑ i, planeDot v (edge P i) = 0 := by
    rw [← planeDot_sum, sum_edges]; simp [planeDot]
  have hzero : ∀ i, planeDot v (edge P i) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hdot i)).mp hsum i (Finset.mem_univ i)
  have hdet : ∀ i, det (edge P (i - 1)) (edge P i) = 0 := by
    intro i
    have h1 := hzero (i - 1)
    have h2 := hzero i
    simp only [planeDot] at h1 h2
    have e1 : v.1 * det (edge P (i - 1)) (edge P i) = 0 := by
      simp only [det]
      linear_combination (edge P i).2 * h1 - (edge P (i - 1)).2 * h2
    have e2 : v.2 * det (edge P (i - 1)) (edge P i) = 0 := by
      simp only [det]
      linear_combination -(edge P i).1 * h1 + (edge P (i - 1)).1 * h2
    by_cases hv1 : v.1 = 0
    · have hv2 : v.2 ≠ 0 := fun h2' => hv (Prod.ext hv1 h2')
      exact (mul_eq_zero.mp e2).resolve_left hv2
    · exact (mul_eq_zero.mp e1).resolve_left hv1
  have hpos : ∀ i, ∃ r : ℝ, 0 < r ∧ edge P i = r • edge P (i - 1) := fun i =>
    (principalTurn_eq_zero_iff (hP i)).mp
      ((principalAngle_zero_iff_det_zero (hP i)).mpr (hdet i))
  have hmult : ∀ k : ℕ, ∃ c : ℝ, 0 < c ∧ edge P (k : ZMod n) = c • edge P 0 := by
    intro k
    induction k with
    | zero => exact ⟨1, one_pos, by simp⟩
    | succ k ih =>
      obtain ⟨c, hc, hck⟩ := ih
      obtain ⟨r, hr, hrk⟩ := hpos ((k + 1 : ℕ) : ZMod n)
      refine ⟨r * c, mul_pos hr hc, ?_⟩
      rw [hrk]
      have e : ((k + 1 : ℕ) : ZMod n) - 1 = (k : ZMod n) := by push_cast; ring
      rw [e, hck, smul_smul]
  choose c hcpos hc using hmult
  have hsum' : ∑ i, edge P i = (∑ k ∈ Finset.range n, c k) • edge P 0 := by
    rw [sum_zmod_eq_sum_range, Finset.sum_smul]
    exact Finset.sum_congr rfl (fun k _ => hc k)
  rw [sum_edges] at hsum'
  have hcs : 0 < ∑ k ∈ Finset.range n, c k :=
    Finset.sum_pos (fun k _ => hcpos k) (Finset.nonempty_range_iff.mpr (NeZero.ne n))
  exact smul_ne_zero hcs.ne' (hP 0).2.1 hsum'.symm

theorem mcB_angleVec_not_semicircle [NeZero n] {P : LabelledTuple n} (hP : Regular P) :
    ¬ InClosedSemicircle (mcB_angleVec P) := by
  rintro ⟨v, hv, hdot⟩
  apply mcB_regular_not_halfplane hP
  refine ⟨v, ?_, fun i => ?_⟩
  · rintro rfl
    simp [planeDot] at hv
  · rw [mcB_edge_eq_smul_unitDir hP i, planeDot_smul_right]
    exact mul_nonneg (euclideanLength_nonneg _) (hdot i)

theorem mcB_angleVec_zeroDomain [NeZero n] {P : LabelledTuple n} (hP : Regular P)
    (hr : rotationNumber P = 0) : mcB_ZeroDomain (mcB_angleVec P) :=
  ⟨mcB_angleVec_cyclicSteps hP hr, mcB_angleVec_not_semicircle hP⟩

/-- A path of feasible zero-rotation angle vectors reconstructs a regular path
(source: "Every continuous angle path inside the union can thus be reconstructed as above"). -/
theorem mcB_joined_regular_of_zeroDomain_path [NeZero n] {P P' : LabelledTuple n}
    {θ θ' : ZMod n → ℝ}
    (hθP : ∀ i, ∃ m : ℝ, 0 < m ∧ edge P i = m • unitDir (θ i))
    (hθP' : ∀ i, ∃ m : ℝ, 0 < m ∧ edge P' i = m • unitDir (θ' i))
    (hj : JoinedIn {ψ : ZMod n → ℝ | mcB_ZeroDomain ψ} θ θ') :
    JoinedIn {Q : LabelledTuple n | Regular Q} P P' := by
  obtain ⟨γ, hγ⟩ := hj
  set Θ : ℝ → ℕ → ℝ := fun t k => γ.extend t (k : ZMod n) with hΘ
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, mcB_ZeroDomain (γ.extend t) := by
    intro t ht
    have e : γ.extend t = γ ⟨t, ht⟩ := Path.extend_extends' γ ⟨t, ht⟩
    rw [e]
    exact hγ ⟨t, ht⟩
  refine mcB_joinedIn_regular_of_liftedAngles 0 Θ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k
    exact ((continuous_apply ((k : ℕ) : ZMod n)).comp γ.continuous_extend).continuousOn
  · intro t ht k _
    simp only [hΘ]
    push_cast
    exact (hmem t ht).1 _
  · intro t _
    simp only [hΘ, ZMod.natCast_self, Nat.cast_zero, Int.cast_zero, mul_zero, add_zero]
  · intro t ht
    simp only [hΘ, ZMod.natCast_zmod_val]
    exact (hmem t ht).2
  · intro i
    simp only [hΘ, ZMod.natCast_zmod_val, Path.extend_zero]
    exact hθP i
  · intro i
    simp only [hΘ, ZMod.natCast_zmod_val, Path.extend_one]
    exact hθP' i

/-- Zero rotation, `n ≥ 5` (source: "Connected chart overlaps for n ≥ 5"). -/
theorem mcB_joined_regular_zero_rotation [NeZero n] (hn : 5 ≤ n) {P P' : LabelledTuple n}
    (hP : Regular P) (hP' : Regular P') (hrP : rotationNumber P = 0)
    (hrP' : rotationNumber P' = 0) : JoinedIn {Q : LabelledTuple n | Regular Q} P P' :=
  mcB_joined_regular_of_zeroDomain_path
    (fun i => ⟨_, euclideanLength_pos (hP i).2.1, mcB_edge_eq_smul_unitDir hP i⟩)
    (fun i => ⟨_, euclideanLength_pos (hP' i).2.1, mcB_edge_eq_smul_unitDir hP' i⟩)
    (mcB_zeroDomain_joined hn (mcB_angleVec_zeroDomain hP hrP) (mcB_angleVec_zeroDomain hP' hrP'))

/-! ### Layer 4: the exceptional four-vertex fibre (source: "The exceptional four-vertex fibre") -/

theorem mcB_chart_shift {h : ZMod n} {d : ℕ} {θ : ZMod n → ℝ} (hθ : mcB_Chart h d θ)
    (k : ZMod n) : mcB_Chart (h - k) d (fun i => θ (i + k)) := by
  refine ⟨fun i => ?_, ?_⟩
  · simp only
    rw [show i + 1 + k = (i + k) + 1 by ring]
    exact hθ.1 _
  · simp only
    rw [sub_add_cancel, show h - k + d + k = h + d by ring]
    exact hθ.2

/-- At `(4, 0)`: after a cyclic shift of `P'`, both angle vectors lie in one chart `A(h, 2)`. -/
theorem mcB_joined_four_zero {P P' : LabelledTuple 4} (hP : Regular P) (hP' : Regular P')
    (hrP : rotationNumber P = 0) (hrP' : rotationNumber P' = 0) :
    ∃ k : ZMod 4, JoinedIn {Q : LabelledTuple 4 | Regular Q} P (shift k P') := by
  obtain ⟨h, d, hd2, hdn, hch⟩ := mcB_exists_chart (mcB_angleVec_zeroDomain hP hrP)
  obtain ⟨h', d', hd2', hdn', hch'⟩ := mcB_exists_chart (mcB_angleVec_zeroDomain hP' hrP')
  have hd : d = 2 := by omega
  have hd' : d' = 2 := by omega
  subst hd hd'
  refine ⟨h' - h, ?_⟩
  have hsh := mcB_chart_shift hch' (h' - h)
  rw [sub_sub_cancel] at hsh
  refine mcB_joined_regular_of_zeroDomain_path (θ := mcB_angleVec P)
    (θ' := fun i => mcB_angleVec P' (i + (h' - h))) ?_ ?_ ?_
  · intro i
    exact ⟨_, euclideanLength_pos (hP i).2.1, mcB_edge_eq_smul_unitDir hP i⟩
  · intro i
    rw [edge_shift]
    exact ⟨_, euclideanLength_pos (hP' _).2.1, mcB_edge_eq_smul_unitDir hP' _⟩
  · exact mcB_joined_same_chart (by norm_num) hch hsh

/-- `transport:four-orders`: no zero-rotation regular four-tuple has a zero turn. -/
theorem mcB_four_zero_turn_ne_zero {Q : LabelledTuple 4} (hQ : Regular Q)
    (hr : rotationNumber Q = 0) (i : ZMod 4) : principalTurn Q i ≠ 0 := by
  obtain ⟨h, d, hd2, hdn, hch⟩ := mcB_exists_chart (mcB_angleVec_zeroDomain hQ hr)
  have hd : d = 2 := by omega
  subst hd
  obtain ⟨hsteps, hgap⟩ := hch
  have key : ∀ j : ZMod 4, principalTurn Q (j + 1) =
      mcB_angleVec Q (j + 1) - mcB_angleVec Q j := fun j => (mcB_angleVec_step hQ hr j).symm
  have s0 := abs_lt.mp (hsteps h)
  have s1 := abs_lt.mp (hsteps (h + 1))
  have s2 := abs_lt.mp (hsteps (h + 2))
  have s3 := abs_lt.mp (hsteps (h + 3))
  have e1 : h + 1 + 1 = h + 2 := by ring
  have e2 : h + 2 + 1 = h + 3 := by ring
  have e3 : h + 3 + 1 = h := by
    have : (4 : ZMod 4) = 0 := by decide
    linear_combination this
  rw [e1] at s1
  rw [e2] at s2
  rw [e3] at s3
  have hgap' : mcB_angleVec Q h - mcB_angleVec Q (h + ((2 : ℕ) : ZMod 4)) > π := hgap
  push_cast at hgap'
  obtain ⟨e, rfl⟩ : ∃ e, i = h + e + 1 := ⟨i - h - 1, by ring⟩
  have hcases : ∀ e : ZMod 4, e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by decide
  rcases hcases e with rfl | rfl | rfl | rfl
  · rw [add_zero, key]
    intro heq
    linarith
  · rw [key, e1]
    intro heq
    linarith
  · rw [key, e2]
    intro heq
    linarith
  · rw [key, e3]
    intro heq
    linarith

/-- The fibre of regular labelled `n`-tuples with rotation `r` (the set
`𝓡_n ∩ rot⁻¹(r)` of the source). -/
def mcB_fibre (n : ℕ) [NeZero n] (r : ℤ) : Set (LabelledTuple n) :=
  {Q | Regular Q ∧ rotationNumber Q = r}

/-- Along a regular zero-rotation path of four-tuples all four turn signs are fixed. -/
theorem mcB_four_turn_word_constant {Q Q' : LabelledTuple 4}
    (h : JoinedIn (mcB_fibre 4 0) Q Q') (i : ZMod 4) : turn Q i = turn Q' i := by
  obtain ⟨γ, hγ⟩ := h
  have hreg : ∀ t, Regular (γ t) := fun t => (hγ t).1
  have hrot : ∀ t, rotationNumber (γ t) = 0 := fun t => by
    have := (hγ t).2; simpa using this
  have hc : Continuous (fun t => principalTurn (γ t) i) :=
    continuous_principalTurn_family γ.continuous hreg i
  have hne : ∀ t, principalTurn (γ t) i ≠ 0 := fun t =>
    mcB_four_zero_turn_ne_zero (hreg t) (hrot t) i
  have hsc : Continuous (fun t => SignType.sign (principalTurn (γ t) i)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (continuousAt_sign_of_ne_zero (hne t)).comp (f := fun t => principalTurn (γ t) i)
      hc.continuousAt
  have hQ : Regular Q := by have := hreg 0; rwa [γ.source] at this
  have hQ' : Regular Q' := by have := hreg 1; rwa [γ.target] at this
  rw [← principalTurn_sign hQ i, ← principalTurn_sign hQ' i]
  have := PreconnectedSpace.constant inferInstance hsc (x := 0) (y := 1)
  simpa [γ.source, γ.target] using this

theorem mcB_bowTie_turn_explicit (j : ZMod 4) :
    turn bowTie j = if j = 2 ∨ j = 3 then 1 else -1 := by
  have hcases : ∀ e : ZMod 4, e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by decide
  rcases hcases j with rfl | rfl | rfl | rfl
  · rw [bowTie_turn_zero]; decide
  · rw [bowTie_turn_one]; decide
  · rw [bowTie_turn_two]; decide
  · rw [bowTie_turn_three]; decide

/-- The four shifts of `K_0` have four distinct turn words. -/
theorem mcB_bowTie_turn_word_injective (k k' : ZMod 4)
    (h : ∀ i, turn (shift k bowTie) i = turn (shift k' bowTie) i) : k = k' := by
  simp only [turn_shift, mcB_bowTie_turn_explicit] at h
  revert h
  revert k k'
  decide

theorem mcB_shift_bowTie_mem_fibre (k : ZMod 4) : shift k bowTie ∈ mcB_fibre 4 0 :=
  ⟨regular_shift_forward k bowTie_regular, by rw [rotationNumber_shift, bowTie_rotation]; simp⟩


/-! ### The four labelled components at `(4, 0)` -/

/-- The bow-tie clause of thm:mycyclic: the four shifts of `K_0` lie in the fibre, in four
distinct labelled path components, distinguished by their turn words (which are constant along
paths in the fibre); every point of the fibre is joined to one of them. -/
theorem mcB_four_components :
    (∀ k : ZMod 4, shift k bowTie ∈ mcB_fibre 4 0) ∧
    (∀ k k' : ZMod 4, JoinedIn (mcB_fibre 4 0) (shift k bowTie) (shift k' bowTie) ↔ k = k') ∧
    (∀ Q Q' : LabelledTuple 4, JoinedIn (mcB_fibre 4 0) Q Q' → ∀ i, turn Q i = turn Q' i) ∧
    (∀ k k' : ZMod 4, (∀ i, turn (shift k bowTie) i = turn (shift k' bowTie) i) → k = k') ∧
    (∀ Q ∈ mcB_fibre 4 0, ∃ k : ZMod 4, JoinedIn (mcB_fibre 4 0) Q (shift k bowTie)) := by
  refine ⟨mcB_shift_bowTie_mem_fibre, fun k k' => ⟨fun h => ?_, fun h => ?_⟩,
    fun Q Q' h i => mcB_four_turn_word_constant h i, mcB_bowTie_turn_word_injective, ?_⟩
  · exact mcB_bowTie_turn_word_injective k k' (fun i => mcB_four_turn_word_constant h i)
  · subst h
    exact JoinedIn.refl (mcB_shift_bowTie_mem_fibre k)
  · rintro Q ⟨hQ, hr⟩
    have hr' : rotationNumber Q = 0 := by simpa using hr
    obtain ⟨k, hk⟩ := mcB_joined_four_zero hQ bowTie_regular hr' bowTie_rotation
    exact ⟨k, mcB_joinedIn_fibre_of_regular _ hr hk⟩

/-! ### Assembly (source thm:mycyclic) -/

theorem mcB_joined_fibre [NeZero n] {r : ℤ} (ha : Admissible (n : ℤ) r)
    {P P' : LabelledTuple n} (hP : Regular P) (hP' : Regular P')
    (hrP : rotationNumber P = r) (hrP' : rotationNumber P' = r)
    (hne : ((n : ℤ), r) ≠ (4, 0)) : JoinedIn (mcB_fibre n r) P P' := by
  apply mcB_joinedIn_fibre_of_regular _ hrP
  by_cases hr : r = 0
  · subst hr
    have hn5 : 5 ≤ n := by
      obtain ⟨hn3, -, hne3⟩ := ha
      have h3 : n ≠ 3 := fun h => hne3 (by simp [h])
      have h4 : n ≠ 4 := fun h => hne (by simp [h])
      have hn3' : 3 ≤ n := by exact_mod_cast hn3
      omega
    exact mcB_joined_regular_zero_rotation hn5 hP hP' (by simpa using hrP) (by simpa using hrP')
  · exact mcB_joined_regular_nonzero_rotation hP hP' r hr hrP hrP'

theorem mcB_joined_fibre_shift [NeZero n] {r : ℤ} (ha : Admissible (n : ℤ) r)
    {P P' : LabelledTuple n} (hP : Regular P) (hP' : Regular P')
    (hrP : rotationNumber P = r) (hrP' : rotationNumber P' = r) :
    ∃ k : ZMod n, JoinedIn (mcB_fibre n r) P (shift k P') := by
  by_cases hne : ((n : ℤ), r) ≠ (4, 0)
  · exact ⟨0, by rw [shift_zero]; exact mcB_joined_fibre ha hP hP' hrP hrP' hne⟩
  · push Not at hne
    have hn : n = 4 := by
      have h1 : (n : ℤ) = 4 := congrArg Prod.fst hne
      exact_mod_cast h1
    have hr : r = 0 := congrArg Prod.snd hne
    subst hn hr
    obtain ⟨k, hk⟩ := mcB_joined_four_zero hP hP' (by simpa using hrP) (by simpa using hrP')
    exact ⟨k, mcB_joinedIn_fibre_of_regular _ hrP hk⟩

/-- The fibre of cyclic polygon orbits: the orbits `[P]` of regular labelled tuples with
rotation `r` in the orbit space `(ℝ²)^n / (ℤ/n)` (= `SM.Polygon n hn` by definition). -/
def mcB_orbitFibre (n : ℕ) [NeZero n] (r : ℤ) : Set (Quotient (cyclicSetoid n)) :=
  {Q | ∃ P : LabelledTuple n, Regular P ∧ rotationNumber P = r ∧ Q = Quotient.mk (cyclicSetoid n) P}

theorem mcB_orbitFibre_pathConnected [NeZero n] {r : ℤ} (ha : Admissible (n : ℤ) r) :
    IsPathConnected (mcB_orbitFibre n r) := by
  rw [isPathConnected_iff]
  constructor
  · obtain ⟨P, hP, hr⟩ := exists_generic_of_admissible ha
    have hn : 3 ≤ n := by exact_mod_cast ha.1
    exact ⟨Quotient.mk (cyclicSetoid n) P, P, generic_regular hn hP, hr, rfl⟩
  · rintro _ ⟨P, hP, hrP, rfl⟩ _ ⟨P', hP', hrP', rfl⟩
    obtain ⟨k, γ, hγ⟩ := mcB_joined_fibre_shift ha hP hP' hrP hrP'
    have hmk : Quotient.mk (cyclicSetoid n) P' = Quotient.mk (cyclicSetoid n) (shift k P') :=
      Quotient.sound ⟨k, rfl⟩
    rw [hmk]
    have hcont : Continuous (Quotient.mk (cyclicSetoid n)) := continuous_quotient_mk'
    refine ⟨γ.map hcont, fun t => ?_⟩
    refine ⟨γ t, (hγ t).1, ?_, ?_⟩
    · exact (hγ t).2
    · simp [Path.map_coe]

/-- **SM15 thm:mycyclic** (connectivity of the fibres), strategy B. Let `(n, r)` be admissible
and let `P, P' ∈ 𝓡_n` be labelled tuples with `rot P = rot P' = r`. If `(n, r) ≠ (4, 0)`, a
continuous path in `𝓡_n ∩ rot⁻¹(r)` joins `P` to `P'`. If `(n, r) = (4, 0)`, there is
`k ∈ ℤ/4` and such a path from `P` to `σ^k P'`. Every fibre of cyclic polygon orbits is path
connected. (The bow-tie clause is `mcB_four_components`.) -/
theorem mycyclic_B [NeZero n] {r : ℤ} (ha : Admissible (n : ℤ) r) :
    (∀ P P' : LabelledTuple n, Regular P → Regular P' →
      rotationNumber P = r → rotationNumber P' = r → ((n : ℤ), r) ≠ (4, 0) →
      JoinedIn (mcB_fibre n r) P P') ∧
    (∀ P P' : LabelledTuple n, Regular P → Regular P' →
      rotationNumber P = r → rotationNumber P' = r → ((n : ℤ), r) = (4, 0) →
      ∃ k : ZMod n, JoinedIn (mcB_fibre n r) P (shift k P')) ∧
    IsPathConnected (mcB_orbitFibre n r) :=
  ⟨fun _ _ hP hP' hrP hrP' hne => mcB_joined_fibre ha hP hP' hrP hrP' hne,
    fun _ _ hP hP' hrP hrP' _ => mcB_joined_fibre_shift ha hP hP' hrP hrP',
    mcB_orbitFibre_pathConnected ha⟩

/-- The orbit clause read on the source's polygon space `SM.Polygon n hn`
(definitionally `Quotient (cyclicSetoid n)`, with the quotient topology). -/
theorem mycyclic_B_orbit_polygon [NeZero n] (hn : 3 ≤ n) {r : ℤ} (ha : Admissible (n : ℤ) r) :
    @IsPathConnected (Polygon n hn) instTopologicalSpaceQuotient (mcB_orbitFibre n r) :=
  mcB_orbitFibre_pathConnected ha

end SM

