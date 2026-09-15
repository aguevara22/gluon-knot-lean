import SM.TransportLengths
import SM.TransportAngleInterval
import SM.CumulativeTurns
import SM.RotationContinuity
import SM.UniformRotation
import SM.BowTie
import SM.Admissible
import SM.FibreExistence
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc

/-! # SM15 `thm:mycyclic` (connectivity of the fibres), strategy A (direction paths)

Source: `reference/SM/sm-5-transport.tex`, lines 150–290.

All new names carry the prefix `mycyc`/`Mycyc` to avoid clashes with `work/lean/SM`. -/

namespace SM

open Real Set

variable {n : ℕ}

/-! ### Joinedness inside the regular locus -/

/-- Two labelled tuples are joined by a continuous path inside the regular locus `ℛ_n`. -/
def MycycJoined (P Q : LabelledTuple n) : Prop :=
  ∃ γ : Path P Q, ∀ t, Regular (γ t)

theorem MycycJoined.refl {P : LabelledTuple n} (h : Regular P) : MycycJoined P P :=
  ⟨Path.refl P, fun _ => h⟩

theorem MycycJoined.symm {P Q : LabelledTuple n} (h : MycycJoined P Q) : MycycJoined Q P := by
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ.symm, fun t => hγ _⟩

theorem MycycJoined.trans {P Q R : LabelledTuple n} (h₁ : MycycJoined P Q)
    (h₂ : MycycJoined Q R) : MycycJoined P R := by
  obtain ⟨γ, hγ⟩ := h₁
  obtain ⟨γ', hγ'⟩ := h₂
  refine ⟨γ.trans γ', fun t => ?_⟩
  rw [Path.trans_apply]
  split_ifs
  · exact hγ _
  · exact hγ' _

theorem MycycJoined.regular_left {P Q : LabelledTuple n} (h : MycycJoined P Q) : Regular P := by
  obtain ⟨γ, hγ⟩ := h
  simpa using hγ 0

theorem MycycJoined.regular_right {P Q : LabelledTuple n} (h : MycycJoined P Q) : Regular Q := by
  obtain ⟨γ, hγ⟩ := h
  simpa using hγ 1

/-- Along a regular path the rotation number is constant, so a regular path from a tuple of
rotation `r` stays in the fibre `rot⁻¹(r)`. -/
theorem MycycJoined.exists_path_fibre [NeZero n] {P Q : LabelledTuple n} (h : MycycJoined P Q)
    {r : ℝ} (hr : rotationNumber P = r) :
    ∃ γ : Path P Q, ∀ t, Regular (γ t) ∧ rotationNumber (γ t) = r := by
  obtain ⟨γ, hγ⟩ := h
  refine ⟨γ, fun t => ⟨hγ t, ?_⟩⟩
  have hc := rotationNumber_family_constant γ.continuous hγ t 0
  rw [hc, Path.source, hr]

theorem MycycJoined.rotationNumber_eq [NeZero n] {P Q : LabelledTuple n} (h : MycycJoined P Q) :
    rotationNumber P = rotationNumber Q := by
  obtain ⟨γ, hγ⟩ := h
  exact rotationNumber_path_constant γ hγ

/-- A path from a map that is continuous on `[0, 1] ⊆ ℝ`. -/
def mycycPath {X : Type*} [TopologicalSpace X] (F : ℝ → X) (hF : ContinuousOn F (Icc 0 1))
    {x y : X} (h0 : F 0 = x) (h1 : F 1 = y) : Path x y where
  toFun t := F t
  continuous_toFun := hF.comp_continuous continuous_subtype_val (fun t => t.2)
  source' := by simpa using h0
  target' := by simpa using h1

theorem mycycPath_apply {X : Type*} [TopologicalSpace X] (F : ℝ → X)
    (hF : ContinuousOn F (Icc 0 1)) {x y : X} (h0 : F 0 = x) (h1 : F 1 = y) (t : unitInterval) :
    mycycPath F hF h0 h1 t = F t := rfl

theorem mycycJoined_of_continuousOn {P Q : LabelledTuple n} (F : ℝ → LabelledTuple n)
    (hF : ContinuousOn F (Icc 0 1)) (h0 : F 0 = P) (h1 : F 1 = Q)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, Regular (F t)) : MycycJoined P Q :=
  ⟨mycycPath F hF h0 h1, fun t => hreg t t.2⟩

/-! ### Elementary facts about unit directions and principal angles -/

theorem mycyc_euclideanLength_unitDir (θ : ℝ) : euclideanLength (unitDir θ) = 1 := by
  rw [euclideanLength_formula]
  simp only [unitDir]
  rw [← sq, ← sq, Real.cos_sq_add_sin_sq, Real.sqrt_one]

theorem mycyc_planeDot_eq_one_of_length {v : Plane} (hv : euclideanLength v = 1) :
    planeDot v v = 1 := by
  rw [← euclideanLength_mul_self, hv, one_mul]

theorem mycyc_unitDir_ne_zero (θ : ℝ) : unitDir θ ≠ 0 := by
  intro h
  have := mycyc_euclideanLength_unitDir θ
  rw [h] at this
  simp [euclideanLength, planeComplex_zero] at this

theorem mycyc_unitDir_eq_of_coe_eq {a b : ℝ} (h : (a : Real.Angle) = b) : unitDir a = unitDir b := by
  simp only [unitDir]
  rw [← Real.Angle.cos_coe a, ← Real.Angle.sin_coe a, h, Real.Angle.cos_coe, Real.Angle.sin_coe]

theorem mycyc_unitDir_add_two_pi_int (a : ℝ) (k : ℤ) : unitDir (a + 2 * π * k) = unitDir a := by
  apply mycyc_unitDir_eq_of_coe_eq
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
  exact ⟨k, by ring⟩

/-- The corner rotor of two scaled unit directions. -/
theorem mycyc_cornerRotor_unitDir (a b p q : ℝ) :
    cornerRotor (p • unitDir a) (q • unitDir b) =
      ((p * q : ℝ) : ℂ) * (Real.cos (b - a) + Real.sin (b - a) * Complex.I) := by
  apply Complex.ext
  · simp only [cornerRotor, planeComplex, unitDir, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Real.cos_sub, Real.sin_sub]
    ring
  · simp only [cornerRotor, planeComplex, unitDir, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Real.cos_sub, Real.sin_sub]
    ring

/-- The principal angle from `p • (cos a, sin a)` to `q • (cos b, sin b)` is `b - a` when
`p, q > 0` and `|b - a| < π`. -/
theorem mycyc_principalAngle_unitDir {a b p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hab : |b - a| < π) :
    principalAngle (p • unitDir a) (q • unitDir b) = b - a := by
  rw [principalAngle, mycyc_cornerRotor_unitDir, Complex.arg_real_mul _ (mul_pos hp hq),
    Complex.ofReal_cos, Complex.ofReal_sin]
  exact Complex.arg_cos_add_sin_mul_I ⟨(abs_lt.mp hab).1, (abs_lt.mp hab).2.le⟩

theorem mycyc_regularPair_unitDir {a b p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hab : |b - a| < π) : RegularPair (p • unitDir a) (q • unitDir b) := by
  rw [regularPair_iff_slitPlane]
  refine ⟨smul_ne_zero hp.ne' (mycyc_unitDir_ne_zero a),
    smul_ne_zero hq.ne' (mycyc_unitDir_ne_zero b), ?_⟩
  rw [Complex.mem_slitPlane_iff_arg]
  refine ⟨?_, cornerRotor_ne_zero (smul_ne_zero hp.ne' (mycyc_unitDir_ne_zero a))
    (smul_ne_zero hq.ne' (mycyc_unitDir_ne_zero b))⟩
  have h := mycyc_principalAngle_unitDir hp hq hab
  rw [principalAngle] at h
  rw [h]
  exact (abs_lt.mp hab).2.ne

theorem mycyc_regularPair_unitDir' {a b : ℝ} (hab : |b - a| < π) :
    RegularPair (unitDir a) (unitDir b) := by
  have h := mycyc_regularPair_unitDir one_pos one_pos hab
  simpa only [one_smul] using h

/-- A nonzero plane vector is its length times the unit direction of its argument. -/
theorem mycyc_eq_length_smul_unitDir_arg {e : Plane} (he : e ≠ 0) :
    e = euclideanLength e • unitDir (planeComplex e).arg := by
  have hz : planeComplex e ≠ 0 := planeComplex_ne_zero he
  have hn : euclideanLength e ≠ 0 := (euclideanLength_pos he).ne'
  have hc := Complex.cos_arg hz
  have hs := Complex.sin_arg (planeComplex e)
  apply Prod.ext
  · simp only [unitDir, Prod.smul_fst, smul_eq_mul]
    rw [hc]
    change e.1 = euclideanLength e * (e.1 / euclideanLength e)
    field_simp
  · simp only [unitDir, Prod.smul_snd, smul_eq_mul]
    rw [hs]
    change e.2 = euclideanLength e * (e.2 / euclideanLength e)
    field_simp

/-- Positive rescaling of both vectors preserves a regular pair. -/
theorem mycyc_regularPair_smul {u v : Plane} (h : RegularPair u v) {p q : ℝ} (hp : 0 < p)
    (hq : 0 < q) : RegularPair (p • u) (q • v) := by
  refine ⟨smul_ne_zero hp.ne' h.1, smul_ne_zero hq.ne' h.2.1, ?_⟩
  rintro ⟨r, hr, hqv⟩
  apply h.2.2
  refine ⟨r * p / q, div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hr hp) hq, ?_⟩
  have hq' : q ≠ 0 := hq.ne'
  calc v = q⁻¹ • (q • v) := by rw [smul_smul, inv_mul_cancel₀ hq', one_smul]
    _ = q⁻¹ • (r • p • u) := by rw [hqv]
    _ = (r * p / q) • u := by rw [smul_smul, smul_smul]; congr 1; field_simp

/-! ### Index bookkeeping in `ZMod n` -/

theorem mycyc_val_succ_cases [NeZero n] (i : ZMod n) :
    (i + 1 = 0 ∧ i.val = n - 1) ∨ (i + 1 ≠ 0 ∧ (i + 1).val = i.val + 1) := by
  have hi : i = (i.val : ZMod n) := (ZMod.natCast_zmod_val i).symm
  have hlt : i.val < n := ZMod.val_lt i
  by_cases h : i.val + 1 = n
  · left
    refine ⟨?_, by omega⟩
    have he : i + 1 = ((i.val + 1 : ℕ) : ZMod n) := by push_cast; rw [ZMod.natCast_zmod_val]
    rw [he, h, ZMod.natCast_self]
  · right
    have hlt' : i.val + 1 < n := by omega
    have he : i + 1 = ((i.val + 1 : ℕ) : ZMod n) := by push_cast; rw [ZMod.natCast_zmod_val]
    refine ⟨?_, ?_⟩
    · rw [he]
      exact natIndex_ne_zero (by omega) hlt'
    · rw [he, ZMod.val_natCast_of_lt hlt']

theorem mycyc_val_pred_cases [NeZero n] (i : ZMod n) :
    (i = 0 ∧ (i - 1).val = n - 1) ∨ (i ≠ 0 ∧ i.val = (i - 1).val + 1) := by
  rcases mycyc_val_succ_cases (i - 1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨by simpa using h1, h2⟩
  · right
    exact ⟨by simpa using h1, by simpa using h2⟩

theorem mycyc_val_zero [NeZero n] : (0 : ZMod n).val = 0 := ZMod.val_zero

theorem mycyc_natCast_pred [NeZero n] : (((n - 1 : ℕ) : ZMod n)) = -1 := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have : ((n - 1 : ℕ) : ZMod n) + 1 = ((n - 1 + 1 : ℕ) : ZMod n) := by push_cast; ring
  have h2 : ((n - 1 + 1 : ℕ) : ZMod n) = 0 := by rw [Nat.sub_add_cancel hn, ZMod.natCast_self]
  linear_combination this + h2

/-! ### Building a polygon from a base point, lengths and directions -/

/-- The labelled tuple with vertex `0` at `b` and edge `i` equal to `l i • u i` (once the
weighted directions close up). -/
noncomputable def mycycBuild [NeZero n] (b : Plane) (l : ZMod n → ℝ) (u : ZMod n → Plane) :
    LabelledTuple n :=
  fun i => b + ∑ k ∈ Finset.range i.val, l (k : ZMod n) • u (k : ZMod n)

theorem mycycBuild_zero [NeZero n] (b : Plane) (l : ZMod n → ℝ) (u : ZMod n → Plane) :
    mycycBuild b l u 0 = b := by
  simp [mycycBuild, ZMod.val_zero]

theorem mycycBuild_edge [NeZero n] (b : Plane) (l : ZMod n → ℝ) (u : ZMod n → Plane)
    (hclose : ∑ i, l i • u i = 0) (i : ZMod n) :
    edge (mycycBuild b l u) i = l i • u i := by
  unfold edge
  rcases mycyc_val_succ_cases i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, mycycBuild_zero]
    simp only [mycycBuild, h2]
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    have hi : i = ((n - 1 : ℕ) : ZMod n) := by
      rw [← h2, ZMod.natCast_zmod_val]
    have hsum : (∑ k ∈ Finset.range (n - 1), l (k : ZMod n) • u (k : ZMod n)) =
        -(l ((n - 1 : ℕ) : ZMod n) • u ((n - 1 : ℕ) : ZMod n)) := by
      apply eq_neg_of_add_eq_zero_left
      rw [← Finset.sum_range_succ, Nat.sub_add_cancel hn]
      exact (sum_zmod_eq_sum_range (fun i : ZMod n => l i • u i)).symm.trans hclose
    rw [hsum, hi]
    abel
  · simp only [mycycBuild, h2, Finset.sum_range_succ, ZMod.natCast_zmod_val]
    abel

theorem mycycBuild_regular [NeZero n] (b : Plane) (l : ZMod n → ℝ) (u : ZMod n → Plane)
    (hpos : ∀ i, 0 < l i) (hclose : ∑ i, l i • u i = 0)
    (hreg : ∀ i, RegularPair (u (i - 1)) (u i)) : Regular (mycycBuild b l u) := by
  intro i
  rw [mycycBuild_edge b l u hclose, mycycBuild_edge b l u hclose]
  exact mycyc_regularPair_smul (hreg i) (hpos _) (hpos _)

/-- The tuple with the given edge decomposition is rebuilt from its vertex `0`. -/
theorem mycycBuild_of_edges [NeZero n] (P : LabelledTuple n) (l : ZMod n → ℝ)
    (u : ZMod n → Plane) (hP : ∀ i, edge P i = l i • u i) :
    mycycBuild (P 0) l u = P := by
  funext i
  simp only [mycycBuild]
  have hsum : (∑ k ∈ Finset.range i.val, l (k : ZMod n) • u (k : ZMod n)) =
      ∑ k ∈ Finset.range i.val, (P ((k + 1 : ℕ) : ZMod n) - P (k : ZMod n)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [← hP]
    simp only [edge, Nat.cast_add, Nat.cast_one]
  rw [hsum, Finset.sum_range_sub (fun k : ℕ => P (k : ZMod n)), ZMod.natCast_zmod_val,
    Nat.cast_zero]
  abel

theorem mycycBuild_continuousOn [NeZero n] (b : ℝ → Plane) (l : ZMod n → ℝ → ℝ)
    (u : ZMod n → ℝ → Plane) {s : Set ℝ} (hb : ContinuousOn b s)
    (hl : ∀ i, ContinuousOn (l i) s) (hu : ∀ i, ContinuousOn (u i) s) :
    ContinuousOn (fun t => mycycBuild (b t) (fun i => l i t) (fun i => u i t)) s := by
  apply continuousOn_pi.mpr
  intro i
  simp only [mycycBuild]
  exact hb.add (continuousOn_finsetSum _ fun k _ => (hl _).smul (hu _))

/-! ### Reconstruction of a regular path from a direction path (transport:prefix step) -/

/-- **Reconstructing a polygon from directions.** A continuous family of unit directions on
`[0, 1]`, forming regular pairs consecutively and lying in no closed semicircle, joins any two
regular tuples having these directions at the endpoints by a path in the regular locus. -/
theorem mycyc_reconstruct [NeZero n] (u : ZMod n → ℝ → Plane)
    (hu : ∀ i, ContinuousOn (u i) (Icc 0 1))
    (hunit : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, euclideanLength (u i t) = 1)
    (hreg : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, RegularPair (u (i - 1) t) (u i t))
    (hsemi : ∀ t ∈ Icc (0 : ℝ) 1,
      ¬ ∃ v : Plane, euclideanLength v = 1 ∧ ∀ i, 0 ≤ planeDot v (u i t))
    {P P' : LabelledTuple n} (hP : Regular P) (hP' : Regular P')
    (hPu : ∀ i, edge P i = euclideanLength (edge P i) • u i 0)
    (hP'u : ∀ i, edge P' i = euclideanLength (edge P' i) • u i 1) :
    MycycJoined P P' := by
  obtain ⟨l, hlc, hlpos, hlclose, hjoin0, hjoin1⟩ :=
    transport_lengths_zmod n zero_le_one u hu hunit hsemi
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  set m : ZMod n → ℝ := fun i => euclideanLength (edge P i) with hm
  set m' : ZMod n → ℝ := fun i => euclideanLength (edge P' i) with hm'
  have hmpos : ∀ i, 0 < m i := fun i => euclideanLength_pos (hP i).2.1
  have hm'pos : ∀ i, 0 < m' i := fun i => euclideanLength_pos (hP' i).2.1
  have hmclose : ∑ i, m i • u i 0 = 0 := by
    rw [← sum_edges P]
    exact Finset.sum_congr rfl fun i _ => (hPu i).symm
  have hm'close : ∑ i, m' i • u i 1 = 0 := by
    rw [← sum_edges P']
    exact Finset.sum_congr rfl fun i _ => (hP'u i).symm
  have hreg0 := fun i => hreg i 0 h0
  have hreg1 := fun i => hreg i 1 h1
  -- Piece A: from `P` to the reconstructed tuple with lengths `l · 0` at fixed directions.
  have hA : MycycJoined P (mycycBuild (P 0) (fun i => l i 0) (fun i => u i 0)) := by
    refine mycycJoined_of_continuousOn
      (fun s => mycycBuild (P 0) (fun i => (1 - s) * m i + s * l i 0) (fun i => u i 0))
      ?_ ?_ ?_ ?_
    · exact mycycBuild_continuousOn (fun _ => P 0) _ _ continuousOn_const
        (fun i => ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
          (continuousOn_id.mul continuousOn_const)) (fun i => continuousOn_const)
    · simp only [sub_zero, one_mul, zero_mul, add_zero]
      exact mycycBuild_of_edges P m (fun i => u i 0) hPu
    · simp only [sub_self, zero_mul, one_mul, zero_add]
    · intro s hs
      obtain ⟨hpos, hclose⟩ := hjoin0 m hmpos hmclose s hs
      exact mycycBuild_regular _ _ _ hpos hclose hreg0
  -- Piece B: the direction path.
  have hB : MycycJoined (mycycBuild (P 0) (fun i => l i 0) (fun i => u i 0))
      (mycycBuild (P' 0) (fun i => l i 1) (fun i => u i 1)) := by
    refine mycycJoined_of_continuousOn
      (fun t => mycycBuild (P 0 + t • (P' 0 - P 0)) (fun i => l i t) (fun i => u i t))
      ?_ ?_ ?_ ?_
    · exact mycycBuild_continuousOn _ _ _
        (continuousOn_const.add (continuousOn_id.smul continuousOn_const)) hlc hu
    · simp only [zero_smul, add_zero]
    · simp only [one_smul, add_sub_cancel]
    · intro t ht
      exact mycycBuild_regular _ _ _ (fun i => hlpos i t ht) (hlclose t ht) (fun i => hreg i t ht)
  -- Piece C: from `P'` to the reconstructed tuple with lengths `l · 1`.
  have hC : MycycJoined P' (mycycBuild (P' 0) (fun i => l i 1) (fun i => u i 1)) := by
    refine mycycJoined_of_continuousOn
      (fun s => mycycBuild (P' 0) (fun i => (1 - s) * m' i + s * l i 1) (fun i => u i 1))
      ?_ ?_ ?_ ?_
    · exact mycycBuild_continuousOn (fun _ => P' 0) _ _ continuousOn_const
        (fun i => ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
          (continuousOn_id.mul continuousOn_const)) (fun i => continuousOn_const)
    · simp only [sub_zero, one_mul, zero_mul, add_zero]
      exact mycycBuild_of_edges P' m' (fun i => u i 1) hP'u
    · simp only [sub_self, zero_mul, one_mul, zero_add]
    · intro s hs
      obtain ⟨hpos, hclose⟩ := hjoin1 m' hm'pos hm'close s hs
      exact mycycBuild_regular _ _ _ hpos hclose hreg1
  exact (hA.trans hB).trans hC.symm

/-! ### The lifted edge arguments of a regular polygon (transport:prefix) -/

/-- The lifted edge arguments `θ_k = β + ∑_{m=1}^{k} ϑ_m`, with `β` the argument of the first
edge `E_0` (source label `n ≡ 0`). -/
noncomputable def mycycLift [NeZero n] (P : LabelledTuple n) (k : ℕ) : ℝ :=
  (planeComplex (edge P 0)).arg + turnPrefix P k

theorem mycycLift_zero [NeZero n] (P : LabelledTuple n) :
    mycycLift P 0 = (planeComplex (edge P 0)).arg := by
  simp [mycycLift, turnPrefix]

theorem mycycLift_succ_sub [NeZero n] (P : LabelledTuple n) (k : ℕ) :
    mycycLift P (k + 1) - mycycLift P k = principalTurn P ((k + 1 : ℕ) : ZMod n) := by
  simp only [mycycLift, turnPrefix, Finset.sum_range_succ]
  ring

theorem mycycLift_step_lt [NeZero n] {P : LabelledTuple n} (hP : Regular P) (k : ℕ) :
    |mycycLift P (k + 1) - mycycLift P k| < π := by
  rw [mycycLift_succ_sub]
  exact principalTurn_abs_lt_pi hP _

theorem mycycLift_coe_angle [NeZero n] {P : LabelledTuple n} (hP : Regular P) (k : ℕ) :
    (mycycLift P k : Real.Angle) = ((planeComplex (edge P (k : ZMod n))).arg : Real.Angle) := by
  simp only [mycycLift, Real.Angle.coe_add]
  rw [turnPrefix_coe_angle hP k]
  simp only [edgeDirectionAngle]
  abel

/-- Every edge is its length times the unit direction of its lifted argument. -/
theorem mycycLift_unitDir [NeZero n] {P : LabelledTuple n} (hP : Regular P) (k : ℕ) :
    edge P (k : ZMod n) = euclideanLength (edge P (k : ZMod n)) • unitDir (mycycLift P k) := by
  rw [mycyc_unitDir_eq_of_coe_eq (mycycLift_coe_angle hP k)]
  exact mycyc_eq_length_smul_unitDir_arg (hP _).2.1

/-- `θ_n − θ_0 = 2π · rot(P)`. -/
theorem mycycLift_last [NeZero n] (P : LabelledTuple n) :
    mycycLift P n = mycycLift P 0 + 2 * π * rotationNumber P := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have h1 : turnPrefix P n = ∑ i : ZMod n, principalTurn P i := by
    rw [sum_principalTurn_eq_prefix]
    have hsucc : turnPrefix P (n - 1 + 1) =
        turnPrefix P (n - 1) + principalTurn P ((n - 1 + 1 : ℕ) : ZMod n) := by
      simp only [turnPrefix, Finset.sum_range_succ]
    rw [Nat.sub_add_cancel hn, ZMod.natCast_self] at hsucc
    exact hsucc
  have h2 : 2 * π * rotationNumber P = ∑ i : ZMod n, principalTurn P i := by
    unfold rotationNumber
    field_simp
  have h0 : turnPrefix P 0 = 0 := by simp [turnPrefix]
  simp only [mycycLift]
  rw [h0, h1, h2]
  ring

/-- The cyclic angle vector `θ = (θ_1, …, θ_n)` of a regular polygon, read on `ZMod n`. -/
noncomputable def mycycCyc [NeZero n] (P : LabelledTuple n) : ZMod n → ℝ :=
  fun i => mycycLift P i.val

theorem mycycCyc_unitDir [NeZero n] {P : LabelledTuple n} (hP : Regular P) (i : ZMod n) :
    edge P i = euclideanLength (edge P i) • unitDir (mycycCyc P i) := by
  have h := mycycLift_unitDir hP i.val
  rwa [ZMod.natCast_zmod_val] at h

/-- The principal turn at vertex `i ≠ 0` is the difference of consecutive lifted arguments. -/
theorem mycyc_principalTurn_eq_cyc_sub [NeZero n] (P : LabelledTuple n) {i : ZMod n}
    (hi : i ≠ 0) : principalTurn P i = mycycCyc P i - mycycCyc P (i - 1) := by
  rcases mycyc_val_pred_cases i with ⟨h, _⟩ | ⟨_, h⟩
  · exact absurd h hi
  · simp only [mycycCyc, h, mycycLift_succ_sub]
    congr 1
    push_cast
    rw [ZMod.natCast_zmod_val, sub_add_cancel]

/-- The principal turn at vertex `0` closes the cycle up to `2π · rot(P)`. -/
theorem mycyc_principalTurn_zero_eq [NeZero n] (P : LabelledTuple n) :
    principalTurn P 0 = mycycCyc P 0 + 2 * π * rotationNumber P - mycycCyc P (0 - 1) := by
  rcases mycyc_val_pred_cases (0 : ZMod n) with ⟨_, h⟩ | ⟨h, _⟩
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    simp only [mycycCyc, h, ZMod.val_zero]
    rw [← mycycLift_last]
    have := mycycLift_succ_sub P (n - 1)
    rw [Nat.sub_add_cancel hn, ZMod.natCast_self] at this
    linarith
  · exact absurd rfl h

theorem mycycCyc_sub [NeZero n] {P : LabelledTuple n} (h0 : rotationNumber P = 0) (i : ZMod n) :
    mycycCyc P i - mycycCyc P (i - 1) = principalTurn P i := by
  by_cases hi : i = 0
  · subst hi
    rw [mycyc_principalTurn_zero_eq, h0]
    ring
  · exact (mycyc_principalTurn_eq_cyc_sub P hi).symm

theorem mycycCyc_step [NeZero n] {P : LabelledTuple n} (hP : Regular P)
    (h0 : rotationNumber P = 0) (i : ZMod n) :
    |mycycCyc P (i + 1) - mycycCyc P i| < π := by
  have := mycycCyc_sub h0 (i + 1)
  rw [add_sub_cancel_right] at this
  rw [this]
  exact principalTurn_abs_lt_pi hP _

/-! ### The directions of a regular closed polygon lie in no closed semicircle -/

theorem mycyc_planeDot_sum (v : Plane) {ι : Type*} (s : Finset ι) (f : ι → Plane) :
    planeDot v (∑ i ∈ s, f i) = ∑ i ∈ s, planeDot v (f i) := by
  simp only [planeDot, Prod.fst_sum, Prod.snd_sum, Finset.mul_sum, Finset.sum_add_distrib]

theorem mycyc_regular_noClosedSemicircle [NeZero n] {P : LabelledTuple n} (hP : Regular P) :
    ¬ ∃ v : Plane, euclideanLength v = 1 ∧ ∀ i, 0 ≤ planeDot v (edge P i) := by
  rintro ⟨v, hv1, hv⟩
  have hvv : planeDot v v = 1 := mycyc_planeDot_eq_one_of_length hv1
  have hvv' : v.1 * v.1 + v.2 * v.2 = 1 := hvv
  have hsum : ∑ i, planeDot v (edge P i) = 0 := by
    rw [← mycyc_planeDot_sum, sum_edges]
    simp [planeDot]
  have hzero : ∀ i, planeDot v (edge P i) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hv i)).mp hsum i (Finset.mem_univ i)
  set w : Plane := (-v.2, v.1) with hw
  have hwne : w ≠ 0 := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [hw, Prod.fst_zero, Prod.snd_zero, neg_eq_zero] at h1 h2
    rw [h1, h2] at hvv'
    norm_num at hvv'
  set c : ZMod n → ℝ := fun i => det v (edge P i) with hc
  have hedge : ∀ i, edge P i = c i • w := by
    intro i
    have hd : v.1 * (edge P i).1 + v.2 * (edge P i).2 = 0 := hzero i
    apply Prod.ext
    · simp only [hc, hw, det, Prod.smul_fst, smul_eq_mul]
      linear_combination v.1 * hd - (edge P i).1 * hvv'
    · simp only [hc, hw, det, Prod.smul_snd, smul_eq_mul]
      linear_combination v.2 * hd - (edge P i).2 * hvv'
  have hcne : ∀ i, c i ≠ 0 := by
    intro i hci
    apply (hP i).2.1
    rw [hedge i, hci, zero_smul]
  have hadj : ∀ i, 0 < c i * c (i - 1) := by
    intro i
    have hreg := hP i
    rw [hedge i, hedge (i - 1)] at hreg
    have hne := mul_ne_zero (hcne i) (hcne (i - 1))
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exfalso
      apply hreg.2.2
      refine ⟨c i / c (i - 1), ?_, ?_⟩
      · have hsq : 0 < c (i - 1) * c (i - 1) := mul_self_pos.mpr (hcne (i - 1))
        have : c i / c (i - 1) = (c i * c (i - 1)) / (c (i - 1) * c (i - 1)) := by
          field_simp
        rw [this]
        exact div_neg_of_neg_of_pos hneg hsq
      · rw [smul_smul, div_mul_cancel₀ _ (hcne (i - 1))]
    · exact hpos
  have hsame : ∀ k : ℕ, 0 < c (k : ZMod n) * c 0 := by
    intro k
    induction k with
    | zero => simpa using mul_self_pos.mpr (hcne 0)
    | succ k ih =>
      have h1 := hadj ((k + 1 : ℕ) : ZMod n)
      rw [show (((k + 1 : ℕ) : ZMod n) - 1) = (k : ZMod n) by push_cast; ring] at h1
      have hsq : 0 < c (k : ZMod n) * c (k : ZMod n) := mul_self_pos.mpr (hcne _)
      have : 0 < (c ((k + 1 : ℕ) : ZMod n) * c 0) * (c (k : ZMod n) * c (k : ZMod n)) := by
        have := mul_pos h1 ih
        linarith [this, show (c ((k + 1 : ℕ) : ZMod n) * c 0) * (c (k : ZMod n) * c (k : ZMod n)) =
          (c ((k + 1 : ℕ) : ZMod n) * c (k : ZMod n)) * (c (k : ZMod n) * c 0) by ring]
      exact (mul_pos_iff_of_pos_right hsq).mp this
  have hsame' : ∀ i : ZMod n, 0 < c i * c 0 := fun i => by
    have := hsame i.val
    rwa [ZMod.natCast_zmod_val] at this
  have hclose : (∑ i, c i) • w = 0 := by
    rw [Finset.sum_smul]
    simp_rw [← hedge]
    exact sum_edges P
  have hsum0 : ∑ i, c i = 0 := by
    rcases smul_eq_zero.mp hclose with h | h
    · exact h
    · exact absurd h hwne
  have hpos : 0 < (∑ i, c i) * c 0 := by
    rw [Finset.sum_mul]
    exact Finset.sum_pos (fun i _ => hsame' i) Finset.univ_nonempty
  rw [hsum0, zero_mul] at hpos
  exact lt_irrefl _ hpos

theorem mycyc_length_eq_one_of_planeDot {v : Plane} (hv : planeDot v v = 1) :
    euclideanLength v = 1 := by
  rw [euclideanLength_eq_sqrt, hv, Real.sqrt_one]

/-- The cyclic angle vector of a regular polygon lies in no closed semicircle. -/
theorem mycycCyc_not_inClosedSemicircle [NeZero n] {P : LabelledTuple n} (hP : Regular P) :
    ¬ InClosedSemicircle (mycycCyc P) := by
  rintro ⟨v, hv, h⟩
  apply mycyc_regular_noClosedSemicircle hP
  refine ⟨v, mycyc_length_eq_one_of_planeDot hv, fun i => ?_⟩
  rw [mycycCyc_unitDir hP i, planeDot_smul_right]
  exact mul_nonneg (euclideanLength_nonneg _) (h i)

/-! ### Reconstruction from a cyclic angle path -/

theorem mycyc_continuous_unitDir : Continuous unitDir :=
  Real.continuous_cos.prodMk Real.continuous_sin

/-- A convex combination of two numbers of absolute value `< π` has absolute value `< π`. -/
theorem mycyc_abs_combo_lt {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : |x| < π) (hy : |y| < π) : |a * x + b * y| < π := by
  have h1 := abs_add_le (a * x) (b * y)
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at h1
  rcases eq_or_lt_of_le ha with h | h
  · subst h
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hy
  · have h2 : a * |x| < a * π := mul_lt_mul_of_pos_left hx h
    have h3 : b * |y| ≤ b * π := mul_le_mul_of_nonneg_left hy.le hb
    have h4 : a * π + b * π = π := by rw [← add_mul, hab, one_mul]
    linarith

/-- Reconstruction from a continuous cyclic angle path `Θ i t` with `|Θ_{i+1} − Θ_i| < π` and
directions in no closed semicircle: the regular tuples with these edge directions at the two
endpoints are joined inside the regular locus. -/
theorem mycyc_reconstruct_angles [NeZero n] (Θ : ZMod n → ℝ → ℝ)
    (hΘ : ∀ i, ContinuousOn (Θ i) (Icc 0 1))
    (hstep : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i, |Θ (i + 1) t - Θ i t| < π)
    (hsemi : ∀ t ∈ Icc (0 : ℝ) 1, ¬ InClosedSemicircle (fun i => Θ i t))
    {P P' : LabelledTuple n} (hP : Regular P) (hP' : Regular P')
    (hPu : ∀ i, edge P i = euclideanLength (edge P i) • unitDir (Θ i 0))
    (hP'u : ∀ i, edge P' i = euclideanLength (edge P' i) • unitDir (Θ i 1)) :
    MycycJoined P P' := by
  refine mycyc_reconstruct (fun i t => unitDir (Θ i t)) ?_ ?_ ?_ ?_ hP hP' hPu hP'u
  · intro i
    exact mycyc_continuous_unitDir.comp_continuousOn (hΘ i)
  · intro i t _
    exact mycyc_euclideanLength_unitDir _
  · intro i t ht
    apply mycyc_regularPair_unitDir'
    have := hstep t ht (i - 1)
    rwa [sub_add_cancel] at this
  · intro t ht
    rintro ⟨v, hv, h⟩
    exact hsemi t ht ⟨v, mycyc_planeDot_eq_one_of_length hv, h⟩

/-! ### The zero-rotation angle domain and its convex charts (transport:chart) -/

/-- The cyclic angle domain: `|θ_{i+1} − θ_i| < π` cyclically (transport:zero-angle-domain). -/
def mycycDomain (n : ℕ) : Set (ZMod n → ℝ) := {θ | ∀ i, |θ (i + 1) - θ i| < π}

/-- The chart `𝓐(h, d) = {θ : domain, θ_h − θ_{h+d} > π}`. -/
def mycycChart (h : ZMod n) (d : ℕ) : Set (ZMod n → ℝ) :=
  {θ | θ ∈ mycycDomain n ∧ π < θ h - θ (h + d)}

/-- The union of the charts with `2 ≤ d ≤ n − 2`. -/
def mycycCharts (n : ℕ) : Set (ZMod n → ℝ) :=
  {θ | ∃ h : ZMod n, ∃ d : ℕ, 2 ≤ d ∧ d ≤ n - 2 ∧ θ ∈ mycycChart h d}

theorem mycycChart_subset_charts {h : ZMod n} {d : ℕ} (hd : 2 ≤ d) (hdn : d ≤ n - 2) :
    mycycChart h d ⊆ mycycCharts n := fun _ hθ => ⟨h, d, hd, hdn, hθ⟩

theorem mycycCharts_subset_domain : mycycCharts n ⊆ mycycDomain n := by
  rintro θ ⟨h, d, _, _, hθ⟩
  exact hθ.1

theorem mycycDomain_convex (n : ℕ) : Convex ℝ (mycycDomain n) := by
  intro x hx y hy a b ha hb hab i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have he : a * x (i + 1) + b * y (i + 1) - (a * x i + b * y i) =
      a * (x (i + 1) - x i) + b * (y (i + 1) - y i) := by ring
  rw [he]
  exact mycyc_abs_combo_lt ha hb hab (hx i) (hy i)

theorem mycycChart_convex (h : ZMod n) (d : ℕ) : Convex ℝ (mycycChart h d) := by
  intro x hx y hy a b ha hb hab
  refine ⟨mycycDomain_convex n hx.1 hy.1 ha hb hab, ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have he : a * x h + b * y h - (a * x (h + d) + b * y (h + d)) =
      a * (x h - x (h + d)) + b * (y h - y (h + d)) := by ring
  rw [he]
  rcases eq_or_lt_of_le ha with h0 | hpos
  · subst h0
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hy.2
  · have h1 : a * π < a * (x h - x (h + d)) := mul_lt_mul_of_pos_left hx.2 hpos
    have h2 : b * π ≤ b * (y h - y (h + d)) := mul_le_mul_of_nonneg_left hy.2.le hb
    have h4 : a * π + b * π = π := by rw [← add_mul, hab, one_mul]
    linarith

/-- Every chart point has directions lying in no closed semicircle
(lem:transport-angle-interval). -/
theorem mycycChart_not_inClosedSemicircle [NeZero n] {h : ZMod n} {d : ℕ} (hd : d ≤ n)
    {θ : ZMod n → ℝ} (hθ : θ ∈ mycycChart h d) : ¬ InClosedSemicircle θ := by
  rintro ⟨v, hv, hsemi⟩
  obtain ⟨hdom, hgap⟩ := hθ
  set φ : Fin (n + 1) → ℝ := fun j => θ (h + ((j : ℕ) : ZMod n)) with hφ
  have hstep : ∀ j : Fin n, |φ j.succ - φ j.castSucc| < π := by
    intro j
    simp only [hφ, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    have := hdom (h + ((j : ℕ) : ZMod n))
    rwa [add_assoc] at this
  have hsc : InClosedSemicircle φ := ⟨v, hv, fun j => hsemi _⟩
  obtain ⟨c, hc⟩ := transport_angle_interval φ hstep hsc
  have h0 := hc 0
  have hd' := hc ⟨d, Nat.lt_succ_of_le hd⟩
  simp only [hφ, Fin.val_zero, Nat.cast_zero, add_zero] at h0
  simp only [hφ] at hd'
  linarith [h0.1, h0.2, hd'.1, hd'.2, hgap]

theorem mycycCharts_not_inClosedSemicircle [NeZero n] {θ : ZMod n → ℝ}
    (hθ : θ ∈ mycycCharts n) : ¬ InClosedSemicircle θ := by
  obtain ⟨h, d, _, hdn, hθ⟩ := hθ
  exact mycycChart_not_inClosedSemicircle (by omega) hθ

theorem mycycCyc_mem_domain [NeZero n] {P : LabelledTuple n} (hP : Regular P)
    (h0 : rotationNumber P = 0) : mycycCyc P ∈ mycycDomain n :=
  fun i => mycycCyc_step hP h0 i

/-- The charts cover all zero-rotation endpoints: the cyclic angle vector of a regular
zero-rotation polygon lies in some chart `𝓐(h, d)` with `2 ≤ d ≤ n − 2`. -/
theorem mycycCyc_mem_charts [NeZero n] {P : LabelledTuple n} (hP : Regular P)
    (h0 : rotationNumber P = 0) : mycycCyc P ∈ mycycCharts n := by
  set θ := mycycCyc P with hθ
  have hdom : θ ∈ mycycDomain n := mycycCyc_mem_domain hP h0
  have hns := mycycCyc_not_inClosedSemicircle hP
  obtain ⟨hmax, hmax_spec⟩ := Finite.exists_max θ
  obtain ⟨hmin, hmin_spec⟩ := Finite.exists_min θ
  have hgap : π < θ hmax - θ hmin := by
    by_contra hle
    push Not at hle
    apply hns
    apply transport_angle_interval_converse
    exact ⟨θ hmin, fun i => ⟨hmin_spec i, by linarith [hmax_spec i]⟩⟩
  set d := (hmin - hmax).val with hd
  have hhd : hmax + (d : ZMod n) = hmin := by rw [hd, ZMod.natCast_zmod_val]; ring
  have hdlt : d < n := ZMod.val_lt _
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero, add_zero] at hhd
    rw [hhd] at hgap
    linarith [Real.pi_pos]
  have hd1 : d ≠ 1 := by
    intro h
    rw [h, Nat.cast_one] at hhd
    have := hdom hmax
    rw [hhd] at this
    linarith [(abs_lt.mp this).1]
  have hdn : d ≠ n - 1 := by
    intro h
    rw [h, mycyc_natCast_pred] at hhd
    have e : hmin + 1 = hmax := by rw [← hhd]; ring
    have := hdom hmin
    rw [e] at this
    linarith [(abs_lt.mp this).2]
  refine ⟨hmax, d, by omega, by omega, hdom, ?_⟩
  rw [hhd]
  exact hgap

/-! ### Explicit chart-overlap witnesses (transport:chart-moves) -/

/-- A plateau profile on `ℕ`: `3π/2` before `a − 1`, `3π/4` at `a − 1`, `0` on `[a, b]`,
`3π/4` at `b + 1`, `3π/2` afterwards. -/
noncomputable def mycycPlateauFun (a b s : ℕ) : ℝ :=
  if s + 1 < a then 3 * π / 2 else if s + 1 = a then 3 * π / 4
  else if s ≤ b then 0 else if s = b + 1 then 3 * π / 4 else 3 * π / 2

theorem mycycPlateauFun_step (a b s : ℕ) :
    |mycycPlateauFun a b (s + 1) - mycycPlateauFun a b s| ≤ 3 * π / 4 := by
  have hπ := Real.pi_pos
  unfold mycycPlateauFun
  split_ifs <;> first | omega | (rw [abs_le]; constructor <;> linarith)

theorem mycycPlateauFun_high (a b s : ℕ) (hs : s + 1 < a) : mycycPlateauFun a b s = 3 * π / 2 := by
  unfold mycycPlateauFun
  rw [ite_eq_left hs]

theorem mycycPlateauFun_low (a b s : ℕ) (ha : a ≤ s) (hb : s ≤ b) : mycycPlateauFun a b s = 0 := by
  unfold mycycPlateauFun
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hb]

theorem mycycPlateauFun_wrap (a b m : ℕ) (ha : 2 ≤ a) (hb : b + 1 ≤ m) :
    |mycycPlateauFun a b 0 - mycycPlateauFun a b m| ≤ 3 * π / 4 := by
  have hπ := Real.pi_pos
  rw [mycycPlateauFun_high a b 0 (by omega)]
  unfold mycycPlateauFun
  split_ifs <;> first | omega | (rw [abs_le]; constructor <;> linarith)

/-- The plateau witness read cyclically from `h`. -/
noncomputable def mycycPlateau (h : ZMod n) (a b : ℕ) : ZMod n → ℝ :=
  fun i => mycycPlateauFun a b (i - h).val

theorem mycycPlateau_mem_domain [NeZero n] (h : ZMod n) {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hb : b ≤ n - 2) : mycycPlateau h a b ∈ mycycDomain n := by
  intro i
  have hπ := Real.pi_pos
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  simp only [mycycPlateau]
  have e : i + 1 - h = (i - h) + 1 := by ring
  rw [e]
  rcases mycyc_val_succ_cases (i - h) with ⟨h1, h2⟩ | ⟨_, h2⟩
  · rw [h1, ZMod.val_zero, h2]
    have := mycycPlateauFun_wrap a b (n - 1) ha (by omega)
    linarith
  · rw [h2]
    have := mycycPlateauFun_step a b (i - h).val
    linarith

theorem mycycPlateau_mem_chart [NeZero n] (h : ZMod n) {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hb : b ≤ n - 2) {h' : ZMod n} {d : ℕ} (hs : (h' - h).val + 1 < a)
    (hlo1 : a ≤ (h' + d - h).val) (hlo2 : (h' + d - h).val ≤ b) :
    mycycPlateau h a b ∈ mycycChart h' d := by
  refine ⟨mycycPlateau_mem_domain h ha hab hb, ?_⟩
  simp only [mycycPlateau]
  rw [mycycPlateauFun_high a b _ hs, mycycPlateauFun_low a b _ hlo1 hlo2]
  linarith [Real.pi_pos]

/-! ### Connectivity of the chart overlap graph for `n ≥ 5` -/

theorem mycyc_chart_joinedIn [NeZero n] {h : ZMod n} {d : ℕ} (hd : 2 ≤ d) (hdn : d ≤ n - 2)
    {x y : ZMod n → ℝ} (hx : x ∈ mycycChart h d) (hy : y ∈ mycycChart h d) :
    JoinedIn (mycycCharts n) x y :=
  (((mycycChart_convex h d).isPathConnected ⟨x, hx⟩).joinedIn x hx y hy).mono
    (mycycChart_subset_charts hd hdn)

theorem mycyc_val_natCast_sub_self [NeZero n] (h : ZMod n) (d : ℕ) (hd : d < n) :
    (h + (d : ZMod n) - h).val = d := by
  rw [add_sub_cancel_left, ZMod.val_natCast_of_lt hd]

/-- The first move `𝓐(h, d) ∩ 𝓐(h, d+1) ≠ ∅` for `2 ≤ d ≤ n − 3`. -/
theorem mycyc_witness_first [NeZero n] (h : ZMod n) {d : ℕ} (hd : 2 ≤ d) (hdn : d ≤ n - 3) :
    mycycPlateau h 2 (d + 1) ∈ mycycChart h d ∧ mycycPlateau h 2 (d + 1) ∈ mycycChart h (d + 1) := by
  have hn : 5 ≤ n := by omega
  have e0 : (h - h).val = 0 := by rw [sub_self, ZMod.val_zero]
  have e1 := mycyc_val_natCast_sub_self h d (by omega)
  have e2 := mycyc_val_natCast_sub_self h (d + 1) (by omega)
  constructor
  · exact mycycPlateau_mem_chart h le_rfl (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact mycycPlateau_mem_chart h le_rfl (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The second move `𝓐(h, d+1) ∩ 𝓐(h+1, d) ≠ ∅` for `2 ≤ d ≤ n − 3`. -/
theorem mycyc_witness_second [NeZero n] (h : ZMod n) {d : ℕ} (hd : 2 ≤ d) (hdn : d ≤ n - 3) :
    mycycPlateau h 3 (d + 1) ∈ mycycChart h (d + 1) ∧
      mycycPlateau h 3 (d + 1) ∈ mycycChart (h + 1) d := by
  have hn : 5 ≤ n := by omega
  have h1 : (h + 1 - h).val = 1 := by
    have := mycyc_val_natCast_sub_self h 1 (by omega)
    simpa using this
  have h2 : (h + 1 + (d : ZMod n) - h).val = d + 1 := by
    have := mycyc_val_natCast_sub_self h (d + 1) (by omega)
    rw [← this]
    congr 1
    push_cast
    ring
  have e0 : (h - h).val = 0 := by rw [sub_self, ZMod.val_zero]
  have e2 := mycyc_val_natCast_sub_self h (d + 1) (by omega)
  constructor
  · exact mycycPlateau_mem_chart h (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact mycycPlateau_mem_chart h (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- Descending the distance: every point of `𝓐(h, d)` is joined to a point of `𝓐(h, 2)`. -/
theorem mycyc_descend [NeZero n] (h : ZMod n) :
    ∀ d : ℕ, 2 ≤ d → d ≤ n - 2 → ∀ x ∈ mycycChart h d,
      ∃ y ∈ mycycChart h 2, JoinedIn (mycycCharts n) x y := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base =>
    intro hdn x hx
    exact ⟨x, hx, JoinedIn.refl (mycycChart_subset_charts le_rfl hdn hx)⟩
  | succ d hd ih =>
    intro hdn x hx
    obtain ⟨hw1, hw2⟩ := mycyc_witness_first h hd (by omega)
    obtain ⟨y, hy, hjy⟩ := ih (by omega) _ hw1
    exact ⟨y, hy, (mycyc_chart_joinedIn (d := d + 1) (by omega) (by omega) hx hw2).trans hjy⟩

/-- Advancing the high index: every point of `𝓐(h, 2)` is joined to a point of `𝓐(h+1, 2)`
(valid for `n ≥ 5`). -/
theorem mycyc_advance [NeZero n] (hn : 5 ≤ n) (h : ZMod n) {x : ZMod n → ℝ}
    (hx : x ∈ mycycChart h 2) : ∃ y ∈ mycycChart (h + 1) 2, JoinedIn (mycycCharts n) x y := by
  obtain ⟨hw1, hw2⟩ := mycyc_witness_first h le_rfl (by omega)
  obtain ⟨hv1, hv2⟩ := mycyc_witness_second h le_rfl (by omega)
  refine ⟨mycycPlateau h 3 (2 + 1), hv2, ?_⟩
  exact (mycyc_chart_joinedIn le_rfl (by omega) hx hw1).trans
    (mycyc_chart_joinedIn (by omega) (by omega) hw2 hv1)

theorem mycyc_advance_iter [NeZero n] (hn : 5 ≤ n) (h : ZMod n) :
    ∀ k : ℕ, ∀ x ∈ mycycChart h 2,
      ∃ y ∈ mycycChart (h + (k : ZMod n)) 2, JoinedIn (mycycCharts n) x y := by
  intro k
  induction k with
  | zero =>
    intro x hx
    exact ⟨x, by simpa using hx, JoinedIn.refl (mycycChart_subset_charts le_rfl (by omega) hx)⟩
  | succ k ih =>
    intro x hx
    obtain ⟨y, hy, hjy⟩ := ih x hx
    obtain ⟨z, hz, hjz⟩ := mycyc_advance hn _ hy
    refine ⟨z, ?_, hjy.trans hjz⟩
    rwa [Nat.cast_add, Nat.cast_one, ← add_assoc]

/-- The base point `𝓦(0; 2, 3) ∈ 𝓐(0, 2)`. -/
theorem mycyc_base_mem [NeZero n] (hn : 5 ≤ n) :
    mycycPlateau (0 : ZMod n) 2 3 ∈ mycycChart (0 : ZMod n) 2 :=
  (mycyc_witness_first (0 : ZMod n) le_rfl (by omega)).1

/-- For `n ≥ 5` the union of the charts is path connected: every point is joined to the base. -/
theorem mycyc_charts_joinedIn_base [NeZero n] (hn : 5 ≤ n) {x : ZMod n → ℝ}
    (hx : x ∈ mycycCharts n) : JoinedIn (mycycCharts n) x (mycycPlateau (0 : ZMod n) 2 3) := by
  obtain ⟨h, d, hd, hdn, hxd⟩ := hx
  obtain ⟨y, hy, hjy⟩ := mycyc_descend h d hd hdn x hxd
  obtain ⟨z, hz, hjz⟩ := mycyc_advance_iter hn h (-h).val y hy
  rw [ZMod.natCast_zmod_val, add_neg_cancel] at hz
  exact (hjy.trans hjz).trans (mycyc_chart_joinedIn le_rfl (by omega) hz (mycyc_base_mem hn))

theorem mycyc_charts_joinedIn [NeZero n] (hn : 5 ≤ n) {x y : ZMod n → ℝ}
    (hx : x ∈ mycycCharts n) (hy : y ∈ mycycCharts n) : JoinedIn (mycycCharts n) x y :=
  (mycyc_charts_joinedIn_base hn hx).trans (mycyc_charts_joinedIn_base hn hy).symm

theorem mycyc_charts_isPathConnected [NeZero n] (hn : 5 ≤ n) :
    IsPathConnected (mycycCharts n) :=
  ⟨mycycPlateau (0 : ZMod n) 2 3, mycycChart_subset_charts le_rfl (by omega) (mycyc_base_mem hn),
    fun _ hy => (mycyc_charts_joinedIn_base hn hy).symm⟩

/-! ### Nonzero rotation: linear interpolation of the lifted arguments -/

/-- **Nonzero rotation.** Two regular tuples with the same nonzero rotation number are joined
inside the regular locus, with no cyclic shift. -/
theorem mycyc_nonzero_rotation [NeZero n] {P P' : LabelledTuple n} (hP : Regular P)
    (hP' : Regular P') {r : ℤ} (hr : rotationNumber P = r) (hr' : rotationNumber P' = r)
    (hr0 : r ≠ 0) : MycycJoined P P' := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  set θ : ℕ → ℝ → ℝ := fun k t => (1 - t) * mycycLift P k + t * mycycLift P' k with hθ
  have hθ0 : ∀ k, θ k 0 = mycycLift P k := by intro k; simp [hθ]
  have hθ1 : ∀ k, θ k 1 = mycycLift P' k := by intro k; simp [hθ]
  have hstep : ∀ t ∈ Icc (0 : ℝ) 1, ∀ k, |θ (k + 1) t - θ k t| < π := by
    intro t ht k
    have e : θ (k + 1) t - θ k t = (1 - t) * (mycycLift P (k + 1) - mycycLift P k) +
        t * (mycycLift P' (k + 1) - mycycLift P' k) := by simp only [hθ]; ring
    rw [e]
    exact mycyc_abs_combo_lt (by linarith [ht.2]) ht.1 (by ring) (mycycLift_step_lt hP k)
      (mycycLift_step_lt hP' k)
  have hlast : ∀ t, θ n t = θ 0 t + 2 * π * r := by
    intro t
    simp only [hθ, mycycLift_last, hr, hr']
    ring
  have hcont : ∀ k, Continuous (θ k) := by
    intro k
    simp only [hθ]
    fun_prop
  refine mycyc_reconstruct (fun i t => unitDir (θ i.val t)) ?_ ?_ ?_ ?_ hP hP' ?_ ?_
  · intro i
    exact (mycyc_continuous_unitDir.comp (hcont _)).continuousOn
  · intro i t _
    exact mycyc_euclideanLength_unitDir _
  · intro i t ht
    rcases mycyc_val_pred_cases i with ⟨hi, hv⟩ | ⟨_, hv⟩
    · subst hi
      rw [hv, ZMod.val_zero]
      have e : unitDir (θ 0 t) = unitDir (θ n t) := by
        rw [hlast t, mycyc_unitDir_add_two_pi_int]
      rw [e]
      apply mycyc_regularPair_unitDir'
      have := hstep t ht (n - 1)
      rwa [Nat.sub_add_cancel hn] at this
    · rw [hv]
      exact mycyc_regularPair_unitDir' (hstep t ht _)
  · intro t ht
    rintro ⟨v, hv1, hsemi⟩
    set φ : Fin (n + 1) → ℝ := fun j => θ j.val t with hφ
    have hstepφ : ∀ j : Fin n, |φ j.succ - φ j.castSucc| < π := fun j => by
      simpa [hφ] using hstep t ht j.val
    have hsc : InClosedSemicircle φ := by
      refine ⟨v, mycyc_planeDot_eq_one_of_length hv1, fun j => ?_⟩
      by_cases hj : j.val < n
      · have := hsemi (j.val : ZMod n)
        simp only [ZMod.val_natCast_of_lt hj] at this
        exact this
      · have hjn : j.val = n := by have := j.isLt; omega
        simp only [hφ, hjn]
        rw [hlast t, mycyc_unitDir_add_two_pi_int]
        have := hsemi 0
        simpa only [ZMod.val_zero] using this
    obtain ⟨c, hc⟩ := transport_angle_interval φ hstepφ hsc
    have h0 := hc 0
    have hn' := hc (Fin.last n)
    simp only [hφ, Fin.val_zero, Fin.val_last] at h0 hn'
    have hle : |θ n t - θ 0 t| ≤ π := by
      rw [abs_le]
      constructor <;> linarith [h0.1, h0.2, hn'.1, hn'.2]
    rw [hlast t, add_sub_cancel_left, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos] at hle
    have hr1 : (1 : ℝ) ≤ |(r : ℝ)| := by
      have : (1 : ℤ) ≤ |r| := Int.one_le_abs hr0
      exact_mod_cast this
    nlinarith [Real.pi_pos]
  · intro i
    rw [hθ0]
    exact mycycCyc_unitDir hP i
  · intro i
    rw [hθ1]
    exact mycycCyc_unitDir hP' i

/-! ### Zero rotation, `n ≥ 5`: paths in the union of the charts -/

/-- **Zero rotation for `n ≥ 5`.** Two regular tuples of rotation `0` are joined inside the
regular locus, with no relabelling. -/
theorem mycyc_zero_rotation_five [NeZero n] (hn : 5 ≤ n) {P P' : LabelledTuple n}
    (hP : Regular P) (hP' : Regular P') (h0 : rotationNumber P = 0)
    (h0' : rotationNumber P' = 0) : MycycJoined P P' := by
  obtain ⟨γ, hγ⟩ := mycyc_charts_joinedIn hn (mycycCyc_mem_charts hP h0)
    (mycycCyc_mem_charts hP' h0')
  set Θ : ZMod n → ℝ → ℝ := fun i t => γ (projIcc 0 1 zero_le_one t) i with hΘ
  have hΘc : ∀ i, Continuous (Θ i) := fun i =>
    (continuous_apply i).comp (γ.continuous.comp continuous_projIcc)
  have hmem : ∀ t, (fun i => Θ i t) ∈ mycycCharts n := fun t => hγ _
  refine mycyc_reconstruct_angles Θ (fun i => (hΘc i).continuousOn) ?_ ?_ hP hP' ?_ ?_
  · intro t _ i
    exact mycycCharts_subset_domain (hmem t) i
  · intro t _
    exact mycycCharts_not_inClosedSemicircle (hmem t)
  · intro i
    have e : Θ i 0 = mycycCyc P i := by
      simp only [hΘ]
      rw [projIcc_left]
      exact congrFun γ.source i
    rw [e]
    exact mycycCyc_unitDir hP i
  · intro i
    have e : Θ i 1 = mycycCyc P' i := by
      simp only [hΘ]
      rw [projIcc_right]
      exact congrFun γ.target i
    rw [e]
    exact mycycCyc_unitDir hP' i

/-! ### The exceptional four-vertex fibre -/

section Four

theorem mycyc_four_eq_zero : (4 : ZMod 4) = 0 := by decide

theorem mycyc_four_exists_chart (P : LabelledTuple 4) (hP : Regular P)
    (h0 : rotationNumber P = 0) : ∃ h : ZMod 4, mycycCyc P ∈ mycycChart h 2 := by
  obtain ⟨h, d, hd, hdn, hθ⟩ := mycycCyc_mem_charts hP h0
  have hd2 : d = 2 := by omega
  subst hd2
  exact ⟨h, hθ⟩

/-- The turn word of a zero-rotation four-tuple with angle vector in `𝓐(h, 2)`
(transport:four-orders): beginning at vertex `h` it reads `(+, −, −, +)`. -/
theorem mycyc_four_chart_turns (P : LabelledTuple 4) (hP : Regular P) (h0 : rotationNumber P = 0)
    (h : ZMod 4) (hθ : mycycCyc P ∈ mycycChart h 2) :
    turn P h = 1 ∧ turn P (h + 1) = -1 ∧ turn P (h + 2) = -1 ∧ turn P (h + 3) = 1 := by
  obtain ⟨hdom, hgap⟩ := hθ
  have h4 := mycyc_four_eq_zero
  simp only [Nat.cast_ofNat] at hgap
  have s0 := hdom h
  have s1 := hdom (h + 1)
  have s2 := hdom (h + 2)
  have s3 := hdom (h + 3)
  have e1 : h + 1 + 1 = h + 2 := by ring
  have e2 : h + 2 + 1 = h + 3 := by ring
  have e3 : h + 3 + 1 = h := by linear_combination h4
  rw [e1] at s1
  rw [e2] at s2
  rw [e3] at s3
  have ht : ∀ i, turn P i = SignType.sign (mycycCyc P i - mycycCyc P (i - 1)) := by
    intro i
    rw [← principalTurn_sign hP, mycycCyc_sub h0]
  have f1 : h + 1 - 1 = h := by ring
  have f2 : h + 2 - 1 = h + 1 := by ring
  have f3 : h + 3 - 1 = h + 2 := by ring
  have f0 : h - 1 = h + 3 := by linear_combination -h4
  obtain ⟨a0, b0⟩ := abs_lt.mp s0
  obtain ⟨a1, b1⟩ := abs_lt.mp s1
  obtain ⟨a2, b2⟩ := abs_lt.mp s2
  obtain ⟨a3, b3⟩ := abs_lt.mp s3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht, f0]
    exact sign_eq_one_iff.mpr (by linarith)
  · rw [ht, f1]
    exact sign_eq_neg_one_iff.mpr (by linarith)
  · rw [ht, f2]
    exact sign_eq_neg_one_iff.mpr (by linarith)
  · rw [ht, f3]
    exact sign_eq_one_iff.mpr (by linarith)

/-- The turn word determines the chart: the four charts are disjoint. -/
theorem mycyc_four_chart_unique (P : LabelledTuple 4) (hP : Regular P)
    (h0 : rotationNumber P = 0) {h h' : ZMod 4} (hθ : mycycCyc P ∈ mycycChart h 2)
    (t1 : turn P h' = 1) (t2 : turn P (h' + 1) = -1) : h' = h := by
  obtain ⟨w0, w1, w2, _⟩ := mycyc_four_chart_turns P hP h0 h hθ
  have h4 := mycyc_four_eq_zero
  obtain ⟨m, hm, hj⟩ : ∃ m : ℕ, m < 4 ∧ h' = h + (m : ZMod 4) :=
    ⟨(h' - h).val, ZMod.val_lt _, by rw [ZMod.natCast_zmod_val]; ring⟩
  subst hj
  interval_cases m
  · simp
  · exfalso
    simp only [Nat.cast_one] at t1
    rw [w1] at t1
    exact absurd t1 (by decide)
  · exfalso
    simp only [Nat.cast_ofNat] at t1
    rw [w2] at t1
    exact absurd t1 (by decide)
  · exfalso
    simp only [Nat.cast_ofNat] at t2
    have e : h + 3 + 1 = h := by linear_combination h4
    rw [e, w0] at t2
    exact absurd t2 (by decide)

/-- No regular zero-rotation four-tuple has a zero turn. -/
theorem mycyc_four_turn_ne_zero (P : LabelledTuple 4) (hP : Regular P)
    (h0 : rotationNumber P = 0) (i : ZMod 4) : turn P i ≠ 0 := by
  obtain ⟨h, hθ⟩ := mycyc_four_exists_chart P hP h0
  obtain ⟨w0, w1, w2, w3⟩ := mycyc_four_chart_turns P hP h0 h hθ
  obtain ⟨m, hm, hj⟩ : ∃ m : ℕ, m < 4 ∧ i = h + (m : ZMod 4) :=
    ⟨(i - h).val, ZMod.val_lt _, by rw [ZMod.natCast_zmod_val]; ring⟩
  subst hj
  interval_cases m
  · simp only [Nat.cast_zero, add_zero]; rw [w0]; decide
  · simp only [Nat.cast_one]; rw [w1]; decide
  · simp only [Nat.cast_ofNat]; rw [w2]; decide
  · simp only [Nat.cast_ofNat]; rw [w3]; decide

/-- A continuous nowhere-vanishing real function on `[0, 1]` has constant sign. -/
theorem mycyc_sign_constant {f : unitInterval → ℝ} (hf : Continuous f) (hne : ∀ t, f t ≠ 0) :
    SignType.sign (f 0) = SignType.sign (f 1) := by
  rcases lt_or_gt_of_ne (hne 0) with h0 | h0 <;> rcases lt_or_gt_of_ne (hne 1) with h1 | h1
  · rw [sign_eq_neg_one_iff.mpr h0, sign_eq_neg_one_iff.mpr h1]
  · exfalso
    obtain ⟨t, ht⟩ := intermediate_value_univ 0 1 hf ⟨h0.le, h1.le⟩
    exact hne t ht
  · exfalso
    obtain ⟨t, ht⟩ := intermediate_value_univ 1 0 hf ⟨h1.le, h0.le⟩
    exact hne t ht
  · rw [sign_eq_one_iff.mpr h0, sign_eq_one_iff.mpr h1]

/-- Along a regular zero-rotation path of four-tuples all four turn signs stay fixed. -/
theorem mycyc_four_joined_turn_eq {P Q : LabelledTuple 4} (hJ : MycycJoined P Q)
    (h0 : rotationNumber P = 0) (i : ZMod 4) : turn P i = turn Q i := by
  obtain ⟨γ, hγ⟩ := hJ
  have hrot : ∀ t, rotationNumber (γ t) = 0 := fun t => by
    rw [rotationNumber_family_constant γ.continuous hγ t 0, Path.source, h0]
  have hne : ∀ t, principalTurn (γ t) i ≠ 0 := by
    intro t ht
    apply mycyc_four_turn_ne_zero (γ t) (hγ t) (hrot t) i
    rw [← principalTurn_sign (hγ t), ht, sign_zero]
  have := mycyc_sign_constant (continuous_principalTurn_family γ.continuous hγ i) hne
  rw [principalTurn_sign (hγ 0), principalTurn_sign (hγ 1), Path.source, Path.target] at this
  exact this

/-- Two regular zero-rotation four-tuples with the same turn word are joined inside the
regular locus (interpolation inside the common convex chart). -/
theorem mycyc_four_same_word_joined {P Q : LabelledTuple 4} (hP : Regular P) (hQ : Regular Q)
    (h0 : rotationNumber P = 0) (h0' : rotationNumber Q = 0) (hw : ∀ i, turn P i = turn Q i) :
    MycycJoined P Q := by
  obtain ⟨h, hθ⟩ := mycyc_four_exists_chart P hP h0
  obtain ⟨h', hθ'⟩ := mycyc_four_exists_chart Q hQ h0'
  obtain ⟨w0, w1, _, _⟩ := mycyc_four_chart_turns P hP h0 h hθ
  have hh : h = h' := mycyc_four_chart_unique Q hQ h0' hθ' (by rw [← hw, w0]) (by rw [← hw, w1])
  subst hh
  have hconv := mycycChart_convex h 2
  set Θ : ZMod 4 → ℝ → ℝ := fun i t => (1 - t) * mycycCyc P i + t * mycycCyc Q i with hΘ
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, (fun i => Θ i t) ∈ mycycChart h 2 := by
    intro t ht
    have := hconv hθ hθ' (by linarith [ht.2] : 0 ≤ 1 - t) ht.1 (by ring)
    have e : (fun i => Θ i t) = (1 - t) • mycycCyc P + t • mycycCyc Q := by
      funext i
      simp [hΘ]
    rw [e]
    exact this
  refine mycyc_reconstruct_angles Θ ?_ ?_ ?_ hP hQ ?_ ?_
  · intro i
    simp only [hΘ]
    fun_prop
  · intro t ht i
    exact (hmem t ht).1 i
  · intro t ht
    exact mycycChart_not_inClosedSemicircle (by norm_num) (hmem t ht)
  · intro i
    simp only [hΘ, sub_zero, one_mul, zero_mul, add_zero]
    exact mycycCyc_unitDir hP i
  · intro i
    simp only [hΘ, sub_self, zero_mul, one_mul, zero_add]
    exact mycycCyc_unitDir hQ i

/-- **The exceptional fibre `(4, 0)`.** Two regular zero-rotation four-tuples are joined after
a cyclic shift of the target. -/
theorem mycyc_four_exceptional {P P' : LabelledTuple 4} (hP : Regular P) (hP' : Regular P')
    (h0 : rotationNumber P = 0) (h0' : rotationNumber P' = 0) :
    ∃ k : ZMod 4, MycycJoined P (shift k P') := by
  obtain ⟨h, hθ⟩ := mycyc_four_exists_chart P hP h0
  obtain ⟨h', hθ'⟩ := mycyc_four_exists_chart P' hP' h0'
  obtain ⟨w0, w1, w2, w3⟩ := mycyc_four_chart_turns P hP h0 h hθ
  obtain ⟨v0, v1, v2, v3⟩ := mycyc_four_chart_turns P' hP' h0' h' hθ'
  refine ⟨h' - h, mycyc_four_same_word_joined hP ((regular_shift _ _).mpr hP') h0
    (by rw [rotationNumber_shift, h0']) ?_⟩
  intro i
  rw [turn_shift]
  obtain ⟨m, hm, hj⟩ : ∃ m : ℕ, m < 4 ∧ i = h + (m : ZMod 4) :=
    ⟨(i - h).val, ZMod.val_lt _, by rw [ZMod.natCast_zmod_val]; ring⟩
  subst hj
  interval_cases m
  · simp only [Nat.cast_zero, add_zero]
    rw [w0, show h + (h' - h) = h' by ring, v0]
  · simp only [Nat.cast_one]
    rw [w1, show h + 1 + (h' - h) = h' + 1 by ring, v1]
  · simp only [Nat.cast_ofNat]
    rw [w2, show h + 2 + (h' - h) = h' + 2 by ring, v2]
  · simp only [Nat.cast_ofNat]
    rw [w3, show h + 3 + (h' - h) = h' + 3 by ring, v3]

/-- The turn word of `σ^k K_0` at the vertex `3 − k` reads `(+, −)`: this is where its chart
index lies. -/
theorem mycyc_bowTie_shift_word (k : ZMod 4) :
    turn (shift k bowTie) (3 - k) = 1 ∧ turn (shift k bowTie) (3 - k + 1) = -1 := by
  have h4 := mycyc_four_eq_zero
  rw [turn_shift, turn_shift]
  have e1 : 3 - k + k = 3 := by ring
  have e2 : 3 - k + 1 + k = 0 := by linear_combination h4
  rw [e1, e2]
  exact ⟨bowTie_turn_three, bowTie_turn_zero⟩

theorem mycyc_bowTie_shift_regular (k : ZMod 4) : Regular (shift k bowTie) :=
  (regular_shift k bowTie).mpr bowTie_regular

theorem mycyc_bowTie_shift_rotation (k : ZMod 4) : rotationNumber (shift k bowTie) = 0 := by
  rw [rotationNumber_shift, bowTie_rotation]

/-- Distinct shifts of the bow-tie are not joined inside `ℛ₄ ∩ rot⁻¹(0)`. -/
theorem mycyc_bowTie_shift_joined_inj {k k' : ZMod 4}
    (hJ : MycycJoined (shift k bowTie) (shift k' bowTie)) : k = k' := by
  have hw : ∀ i, turn (shift k bowTie) i = turn (shift k' bowTie) i :=
    mycyc_four_joined_turn_eq hJ (mycyc_bowTie_shift_rotation k)
  obtain ⟨h, hθ⟩ := mycyc_four_exists_chart _ (mycyc_bowTie_shift_regular k')
    (mycyc_bowTie_shift_rotation k')
  obtain ⟨a1, a2⟩ := mycyc_bowTie_shift_word k
  obtain ⟨b1, b2⟩ := mycyc_bowTie_shift_word k'
  have e1 : 3 - k = h := mycyc_four_chart_unique _ (mycyc_bowTie_shift_regular k')
    (mycyc_bowTie_shift_rotation k') hθ (by rw [← hw, a1]) (by rw [← hw, a2])
  have e2 : 3 - k' = h := mycyc_four_chart_unique _ (mycyc_bowTie_shift_regular k')
    (mycyc_bowTie_shift_rotation k') hθ b1 b2
  linear_combination e2 - e1

/-- **The four labelled components of `ℛ₄ ∩ rot⁻¹(0)`.** Every regular zero-rotation
four-tuple is joined to exactly one shift `σ^k K_0` of the bow-tie; the shifts of `K_0` lie in
four distinct labelled path components, and the components are distinguished by the turn
words: two regular zero-rotation four-tuples are joined iff their turn words coincide. The turn
word of `σ^k K_0` is the `k`-th cyclic shift of that of `K_0`, namely
`(τ_1, τ_2, τ_3, τ_4) = (−1, +1, +1, −1)` (labels `1, 2, 3, 4 ≡ 0`). -/
theorem mycyc_four_components :
    (∀ k : ZMod 4, Regular (shift k bowTie) ∧ rotationNumber (shift k bowTie) = 0) ∧
    (∀ k k' : ZMod 4, MycycJoined (shift k bowTie) (shift k' bowTie) → k = k') ∧
    (∀ k i : ZMod 4, turn (shift k bowTie) i = turn bowTie (i + k)) ∧
    (turn bowTie 1 = -1 ∧ turn bowTie 2 = 1 ∧ turn bowTie 3 = 1 ∧ turn bowTie 0 = -1) ∧
    (∀ P : LabelledTuple 4, Regular P → rotationNumber P = 0 →
      ∃! k : ZMod 4, MycycJoined P (shift k bowTie)) ∧
    (∀ P Q : LabelledTuple 4, Regular P → Regular Q → rotationNumber P = 0 →
      rotationNumber Q = 0 → (MycycJoined P Q ↔ ∀ i, turn P i = turn Q i)) := by
  refine ⟨fun k => ⟨mycyc_bowTie_shift_regular k, mycyc_bowTie_shift_rotation k⟩,
    fun _ _ hJ => mycyc_bowTie_shift_joined_inj hJ, fun k i => turn_shift k bowTie i,
    ⟨bowTie_turn_one, bowTie_turn_two, bowTie_turn_three, bowTie_turn_zero⟩, ?_, ?_⟩
  · intro P hP h0
    obtain ⟨k, hk⟩ := mycyc_four_exceptional hP bowTie_regular h0 bowTie_rotation
    refine ⟨k, hk, fun k' hk' => ?_⟩
    exact mycyc_bowTie_shift_joined_inj (hk'.symm.trans hk)
  · intro P Q hP hQ h0 h0'
    exact ⟨fun hJ i => mycyc_four_joined_turn_eq hJ h0 i,
      mycyc_four_same_word_joined hP hQ h0 h0'⟩

end Four

/-! ### Regular triangles (the last paragraph of the proof) -/

/-- A regular triangle has rotation `+1` or `−1`; there is no zero-rotation case at `n = 3`. -/
theorem mycyc_triangle_rotation {P : LabelledTuple 3} (hP : Regular P) :
    rotationNumber P = 1 ∨ rotationNumber P = -1 := by
  have hne : rotationNumber P ≠ 0 := by
    intro h0
    obtain ⟨_, d, hd, hdn, _⟩ := mycycCyc_mem_charts hP h0
    omega
  obtain ⟨k, hk⟩ := rotationNumber_integer hP
  have hb := rotationNumber_strict_bound hP
  rw [hk] at hb hne ⊢
  have hk0 : k ≠ 0 := by exact_mod_cast hne
  have hkb : 2 * |k| < 3 := by
    have : (2 : ℝ) * |(k : ℝ)| < 3 := by simpa using hb
    exact_mod_cast this
  have hk1 : |k| ≤ 1 := by omega
  have hk2 := abs_le.mp hk1
  have : k = 1 ∨ k = -1 := by omega
  rcases this with h | h <;> simp [h]

/-! ### The theorem -/

/-- **SM15 `thm:mycyclic` (connectivity of the fibres).** Let `(n, r)` be admissible and let
`P, P' ∈ ℛ_n` be labelled tuples with `rot(P) = rot(P') = r`. If `(n, r) ≠ (4, 0)`, a continuous
path in `ℛ_n ∩ rot⁻¹(r)` joins `P` to `P'`. If `(n, r) = (4, 0)`, there is `k ∈ ℤ/4` and such a
path from `P` to `σ^k P'`. (The four components at `(4, 0)` are `mycyc_four_components`; the
orbit statement is `mycyclic_orbits` / `mycyclic_polygon_fibre`.) -/
theorem mycyclicA [NeZero n] {r : ℤ} (hadm : Admissible (n : ℤ) r) {P P' : LabelledTuple n}
    (hP : Regular P) (hP' : Regular P') (hr : rotationNumber P = r)
    (hr' : rotationNumber P' = r) :
    (((n : ℤ), r) ≠ (4, 0) →
      ∃ γ : Path P P', ∀ t, Regular (γ t) ∧ rotationNumber (γ t) = r) ∧
    (((n : ℤ), r) = (4, 0) →
      ∃ k : ZMod n, ∃ γ : Path P (shift k P'), ∀ t, Regular (γ t) ∧ rotationNumber (γ t) = r) := by
  obtain ⟨hn3, hbound, hne3⟩ := hadm
  by_cases hr0 : r = 0
  · subst hr0
    have hn4 : 4 ≤ n := by
      have : (n : ℤ) ≠ 3 := fun h => hne3 (by rw [h])
      omega
    simp only [Int.cast_zero] at hr hr'
    by_cases hn4' : n = 4
    · subst hn4'
      refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
      obtain ⟨k, hk⟩ := mycyc_four_exceptional hP hP' hr hr'
      obtain ⟨γ, hγ⟩ := hk.exists_path_fibre hr
      exact ⟨k, γ, fun t => by simpa using hγ t⟩
    · have hn5 : 5 ≤ n := by omega
      refine ⟨fun _ => ?_, fun h => absurd (by exact_mod_cast (Prod.mk.inj h).1) hn4'⟩
      obtain ⟨γ, hγ⟩ := (mycyc_zero_rotation_five hn5 hP hP' hr hr').exists_path_fibre hr
      exact ⟨γ, fun t => by simpa using hγ t⟩
  · refine ⟨fun _ => (mycyc_nonzero_rotation hP hP' hr hr' hr0).exists_path_fibre hr,
      fun h => absurd (Prod.mk.inj h).2 hr0⟩

/-- **Orbit form of `thm:mycyclic`.** For admissible `(n, r)`, any two regular tuples of rotation
`r` are joined, up to a cyclic shift of the target, by a path in `ℛ_n ∩ rot⁻¹(r)`. -/
theorem mycyclic_orbits [NeZero n] {r : ℤ} (hadm : Admissible (n : ℤ) r) {P P' : LabelledTuple n}
    (hP : Regular P) (hP' : Regular P') (hr : rotationNumber P = r)
    (hr' : rotationNumber P' = r) :
    ∃ k : ZMod n, ∃ γ : Path P (shift k P'), ∀ t, Regular (γ t) ∧ rotationNumber (γ t) = r := by
  obtain ⟨h1, h2⟩ := mycyclicA hadm hP hP' hr hr'
  by_cases h : ((n : ℤ), r) = (4, 0)
  · exact h2 h
  · obtain ⟨γ, hγ⟩ := h1 h
    exact ⟨0, γ.cast rfl (shift_zero P'), fun t => by rw [Path.cast_coe]; exact hγ t⟩

/-- The fibre of rotation `r` in the cyclic quotient (the actual polygon orbits of regular
labelled tuples), as a subset of `Quotient (cyclicSetoid n)` (`= Polygon n hn`). -/
def mycycOrbitFibre (n : ℕ) [NeZero n] (r : ℤ) : Set (Quotient (cyclicSetoid n)) :=
  {Q | ∃ P : LabelledTuple n, Regular P ∧ rotationNumber P = r ∧ Quotient.mk _ P = Q}

/-- **Every fibre of cyclic polygon orbits is path connected** (quotient topology). -/
theorem mycyclic_polygon_fibre [NeZero n] {r : ℤ} (hadm : Admissible (n : ℤ) r) :
    IsPathConnected (mycycOrbitFibre n r) := by
  have hn3 : 3 ≤ n := by have := hadm.1; omega
  obtain ⟨P₀, hP₀, hr₀⟩ := exists_generic_of_admissible hadm
  have hreg₀ : Regular P₀ := generic_regular hn3 hP₀
  refine ⟨Quotient.mk _ P₀, ⟨P₀, hreg₀, hr₀, rfl⟩, ?_⟩
  rintro Q ⟨P, hP, hr, rfl⟩
  obtain ⟨k, γ, hγ⟩ := mycyclic_orbits hadm hreg₀ hP hr₀ hr
  have hmk : Quotient.mk (cyclicSetoid n) (shift k P) = Quotient.mk (cyclicSetoid n) P :=
    Quotient.sound ((cyclicSetoid n).iseqv.symm ⟨k, rfl⟩)
  have hc : Continuous (Quotient.mk (cyclicSetoid n)) := by
    let _ : Setoid (LabelledTuple n) := cyclicSetoid n
    exact continuous_quotient_mk'
  refine ⟨(γ.map hc).cast rfl hmk.symm, fun t => ?_⟩
  rw [Path.cast_coe, Path.map_coe]
  exact ⟨γ t, (hγ t).1, (hγ t).2, rfl⟩

end SM

#print axioms SM.mycyclicA
#print axioms SM.mycyc_four_components
#print axioms SM.mycyclic_orbits
#print axioms SM.mycyclic_polygon_fibre
#print axioms SM.mycyc_triangle_rotation
