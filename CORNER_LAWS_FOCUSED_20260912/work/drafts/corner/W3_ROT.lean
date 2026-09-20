-- W3_Skeleton.lean — corner wave 3 (row 110 thm:C-S7), 2026-09-15: the four open declarations of Corner_Assembled.lean
-- (s7_sliding_law_at 8656-8668, s7_bigon_law_at 9816-9834, thm_C_S7_of / thm_C_S7_of_floor 10008-10039) VERBATIM on top of the
-- ported library (SM.CornerChainUnits = waves 1-2a, SM.CS7Sliding = wave 2b, SM.BigonDeletion = the moves toolkit,
-- SM.CarrierFloorRows = thm_floor), plus the row theorem. Units APPEND prefixed material and may replace ONLY the two `sorry`
-- bodies; statements, names and docstrings are frozen (audit A-110-1, AUTHOR_NOTES 20:46Z).
import SM.CornerChainUnits
import SM.CS7Sliding
import SM.BigonDeletion
import SM.CarrierFloorRows

namespace SM

open Link Carrier

attribute [local instance] Classical.propDecidable

noncomputable section

section VertexEdge

variable {n : ℕ} [NeZero n]

/-! ### Unit ROT (wave 3, prefix `s7q_`; serves the leaf `s7_sliding_law_at`).  PLAN_FINAL §3.3 sliding (2)-(3)
at the level of U110-E's contact sector (W2_S7E_REPORT §2): (a) the rotation equality `hr` of the two relocated
contact carriers by principal-angle addition in one open half-plane (eqs. s7c:turn-short-a/b, sm-4:343-357),
(b) the ordered corner correspondence packaged as `s7q_CornerMerge` (one extra corner) / `s7q_CornerPerturb`
(two perturbed turns), (c) the per-row bookkeeping: coefficient products along the carrier correspondence,
the one refined selector (eq. s7c:short-selector via `s7c_carrierWeight_refine`'s multiset form) and
`s7c_sliding_selector_difference`, giving the termwise identity `hterm` of `s7e_contactSector_of_pivotSplit`.
The geometric inputs (SPLIT = `s7b_PivotSplit`, RET = `s7b_SlidingTransport.ret`, the corner correspondences
and the direction data) are stated as `s7q_`-prefixed black boxes with `sorry` (§S7QBoxes). -/

section S7QAngles

/-! #### (a) Principal-angle addition in one open half-plane (eqs. s7c:turn-short-a/b).  "The two incident
tangents lie in one open angular half-plane bounded by `r`.  Thus their principal turns satisfy the real
equalities `ϑ(r,u_in) + ϑ(u_in,u_out) = ϑ(r,u_out)`, `ϑ(u_in,u_out) + ϑ(u_out,r) = ϑ(u_in,r)`.  There is no hidden
multiple of `2π`" (sm-4:343-352).  The sign hypothesis is eq. s7c:sliding-signs `sgn det(r,u_in) = sgn det(r,u_out) ≠ 0`. -/

omit [NeZero n] in
theorem s7q_det_swap (u v : Plane) : det v u = -det u v := by
  simp only [det]; ring

omit [NeZero n] in
/-- eq. s7c:turn-short-a: `u`, `w` on one side of the line `ℝr` ⇒ `∠(r,u) + ∠(u,w) = ∠(r,w)` exactly. -/
theorem s7q_principalAngle_add_of_side {r u w : Plane} {τ : SignType} (hτ : τ ≠ 0)
    (h1 : SignType.sign (det r u) = τ) (h2 : SignType.sign (det r w) = τ) :
    principalAngle r u + principalAngle u w = principalAngle r w := by
  have d1 := sftc_det_ne_zero_of_sign hτ h1
  have d2 := sftc_det_ne_zero_of_sign hτ h2
  have hr := sftc_ne_zero_of_det_ne_zero_left d1
  have hu := sftc_ne_zero_of_det_ne_zero_right d1
  have hw := sftc_ne_zero_of_det_ne_zero_right d2
  have r1 := sftc_regularPair_of_det_ne_zero d1
  have r2 := sftc_regularPair_of_det_ne_zero d2
  have hang : ((principalAngle r u + principalAngle u w : ℝ) : Real.Angle) =
      (principalAngle r w : Real.Angle) := by
    rw [Real.Angle.coe_add, principalAngle_coe_angle hr hu, principalAngle_coe_angle hu hw,
      principalAngle_coe_angle hr hw]
    abel
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
  have b1 := principalAngle_bounds r1
  have b2 := principalAngle_bounds r2
  have b3 : -Real.pi < principalAngle u w ∧ principalAngle u w ≤ Real.pi :=
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  have s1 := principalAngle_sign r1
  have s2 := principalAngle_sign r2
  rw [h1] at s1
  rw [h2] at s2
  have hpi := Real.pi_pos
  have hk0 : k = 0 := by
    rcases sftc_signType_cases hτ with rfl | rfl
    · rw [sign_eq_one_iff] at s1 s2
      have hk1 : (k : ℝ) < 1 := by
        by_contra hc
        have : (1 : ℝ) ≤ k := not_lt.mp hc
        nlinarith
      have hk2 : (-1 : ℝ) < k := by
        by_contra hc
        have : (k : ℝ) ≤ -1 := not_lt.mp hc
        nlinarith
      have hk1' : k < 1 := by exact_mod_cast hk1
      have hk2' : -1 < k := by exact_mod_cast hk2
      omega
    · rw [sign_eq_neg_one_iff] at s1 s2
      have hk1 : (k : ℝ) < 1 := by
        by_contra hc
        have : (1 : ℝ) ≤ k := not_lt.mp hc
        nlinarith
      have hk2 : (-1 : ℝ) < k := by
        by_contra hc
        have : (k : ℝ) ≤ -1 := not_lt.mp hc
        nlinarith
      have hk1' : k < 1 := by exact_mod_cast hk1
      have hk2' : -1 < k := by exact_mod_cast hk2
      omega
  rw [hk0] at hk
  simp only [Int.cast_zero, mul_zero] at hk
  linarith

omit [NeZero n] in
/-- Antisymmetry of the principal angle on a regular pair (`∠(v,u) = −∠(u,v)`; both in `(−π, π)`, sum `≡ 0`). -/
theorem s7q_principalAngle_swap {u v : Plane} (h : RegularPair u v) :
    principalAngle v u = -principalAngle u v := by
  have hu : u ≠ 0 := h.1
  have hv : v ≠ 0 := h.2.1
  have hvu : RegularPair v u := by
    refine ⟨hv, hu, ?_⟩
    rintro ⟨c, hc, hcu⟩
    apply h.2.2
    refine ⟨c⁻¹, inv_lt_zero.mpr hc, ?_⟩
    rw [hcu, smul_smul, inv_mul_cancel₀ hc.ne, one_smul]
  have hang : ((principalAngle v u + principalAngle u v : ℝ) : Real.Angle) = ((0 : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add, principalAngle_coe_angle hv hu, principalAngle_coe_angle hu hv, Real.Angle.coe_zero]
    abel
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
  have b1 := principalAngle_bounds h
  have b2 := principalAngle_bounds hvu
  have hpi := Real.pi_pos
  have hk0 : k = 0 := by
    have hk1 : (k : ℝ) < 1 := by
      by_contra hc
      have : (1 : ℝ) ≤ k := not_lt.mp hc
      nlinarith
    have hk2 : (-1 : ℝ) < k := by
      by_contra hc
      have : (k : ℝ) ≤ -1 := not_lt.mp hc
      nlinarith
    have hk1' : k < 1 := by exact_mod_cast hk1
    have hk2' : -1 < k := by exact_mod_cast hk2
    omega
  rw [hk0] at hk
  simp only [Int.cast_zero, mul_zero, sub_zero] at hk
  linarith

omit [NeZero n] in
/-- eq. s7c:turn-short-b: `u`, `w` on one side of the line `ℝr` ⇒ `∠(u,w) + ∠(w,r) = ∠(u,r)` exactly. -/
theorem s7q_principalAngle_add_of_side' {r u w : Plane} {τ : SignType} (hτ : τ ≠ 0)
    (h1 : SignType.sign (det r u) = τ) (h2 : SignType.sign (det r w) = τ) :
    principalAngle u w + principalAngle w r = principalAngle u r := by
  have d1 := sftc_det_ne_zero_of_sign hτ h1
  have d2 := sftc_det_ne_zero_of_sign hτ h2
  have hr := sftc_ne_zero_of_det_ne_zero_left d1
  have hu := sftc_ne_zero_of_det_ne_zero_right d1
  have hw := sftc_ne_zero_of_det_ne_zero_right d2
  have r1 := sftc_regularPair_of_det_ne_zero d1
  have r2 := sftc_regularPair_of_det_ne_zero d2
  -- swap the reference: `∠(w,r) = −∠(r,w)`, `∠(u,r) = −∠(r,u)`
  have hwr : principalAngle w r = -principalAngle r w := s7q_principalAngle_swap r2
  have hur : principalAngle u r = -principalAngle r u := s7q_principalAngle_swap r1
  -- and `∠(u,w) = −∠(w,u)` once `(u,w)` is regular: `w` is no negative multiple of `u` (same side of `r`)
  have ruw : RegularPair u w := by
    refine ⟨hu, hw, ?_⟩
    rintro ⟨c, hc, hcw⟩
    have hdet : det r w = c * det r u := by
      rw [hcw]; simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [hdet, sign_mul, sign_neg hc, h1] at h2
    rcases sftc_signType_cases hτ with rfl | rfl <;> exact absurd h2 (by decide)
  have huw : principalAngle w u = -principalAngle u w := s7q_principalAngle_swap ruw
  have := s7q_principalAngle_add_of_side hτ h2 h1
  linarith

omit [NeZero n] in
/-- The two-turn perturbation identity (the pivot carrier / the carrier through `μ_M` on the side where it has
no extra corner): replacing the middle direction `u` by `u'` on the same side of both neighbours `w`, `r`
keeps the SUM of the two adjacent principal turns.  (Both additions are the half-plane lemma.) -/
theorem s7q_two_turn_perturb {w u u' r : Plane} {σ τ : SignType} (hσ : σ ≠ 0) (hτ : τ ≠ 0)
    (h1 : SignType.sign (det w u) = σ) (h2 : SignType.sign (det w u') = σ)
    (h3 : SignType.sign (det r u) = τ) (h4 : SignType.sign (det r u') = τ) :
    principalAngle w u + principalAngle u r = principalAngle w u' + principalAngle u' r := by
  have A := s7q_principalAngle_add_of_side hσ h1 h2
  have B := s7q_principalAngle_add_of_side' hτ h3 h4
  linarith

omit [NeZero n] in
/-- Deleting a vertex whose two edges `r`, `u` lie in one open half-plane: with `d = α r + β u` (`α, β > 0`) the
merged direction, `∠(e,r) + ∠(r,u) + ∠(u,w) = ∠(e,d) + ∠(d,w)` exactly, PROVIDED the neighbours see `d` on the
same side as `r` (`H1`) and `u` on the same side as `d` (`H2`) — the two "smallness" conditions (both hold for
`β` small, i.e. a short edge `u`).  This is the EXACT step of the corrected route for `hr` (see the defect note
of §S7QMerge): within the side polygon `Q(t)` the extra corner is deleted exactly; the perturbation of the
resulting `(k−1)`-gon to the half's carrier polygon is `rotationNumber_locally_constant`. -/
theorem s7q_principal_delete {e r u w d : Plane} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hd : d = α • r + β • u)
    {η σ : SignType} (hη : η ≠ 0) (hσ : σ ≠ 0)
    (hru : SignType.sign (det r u) = η) (H2 : SignType.sign (det d w) = η)
    (H1e : SignType.sign (det e r) = σ) (H1d : SignType.sign (det e d) = σ) :
    principalAngle e r + principalAngle r u + principalAngle u w = principalAngle e d + principalAngle d w := by
  have hrd : SignType.sign (det r d) = η := by
    have : det r d = β * det r u := by
      rw [hd]; simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [this, sign_mul, sign_pos hβ, one_mul, hru]
  have hdu : SignType.sign (det d u) = η := by
    have : det d u = α * det r u := by
      rw [hd]; simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [this, sign_mul, sign_pos hα, one_mul, hru]
  -- `∠(r,d) + ∠(d,u) = ∠(r,u)`: `d`, `u` on one side of `r`
  have A := s7q_principalAngle_add_of_side hη hrd hru
  -- `∠(e,r) + ∠(r,d) = ∠(e,d)`: `r`, `d` on one side of `e`
  have B := s7q_principalAngle_add_of_side hσ H1e H1d
  -- `∠(d,u) + ∠(u,w) = ∠(d,w)`: `u`, `w` on one side of `d`
  have C := s7q_principalAngle_add_of_side hη hdu H2
  linarith

end S7QAngles

section S7QMerge

/-! #### (a)+(b) at the polygon level.  DEFECT NOTE (rule 4): the printed/report form "the side carrier has ONE
extra corner whose two adjacent turns add to the half's single contact turn" (eqs. s7c:turn-short-a/b) holds
with the directions `u_in, u_out` taken AT THE CENTRE; on the side polygon the vertex `μ_M` is displaced, so the
side's `u_out` (resp. `u_in`) differs from the half's by a small perturbation and the corner AFTER `μ_M`
(resp. BEFORE) also changes its principal turn.  The true identity is a THREE-turn ↔ TWO-turn sum:
`ϑ(r,u_in^Q) + ϑ(u_in^Q,u_out^Q) + ϑ(u_out^Q,w) = ϑ(r,u_out^c) + ϑ(u_out^c,w)` — turn-short-a at the side
followed by the two-turn perturbation `s7q_two_turn_perturb` (both are the half-plane lemma).  Likewise the
OTHER contact carrier (the pivot carrier on `P₋`, the `v_a`-carrier on `P₊`) has the same corners but TWO
perturbed adjacent turns of equal sum.  Both preserve `rotationNumber = Σ principalTurn / 2π` exactly, and the
merge refines the turn multiset by the one turn at `μ_M` — the inputs `hr` of `s7d_cornerCoefficient_eq_of_cut`
and the multiset form of `s7c_carrierWeight_refine`.  SECOND DEFECT NOTE (W3_ROT_REPORT §3.2): `WallGerm.curve`
moves EVERY vertex, so the exact fields `principal_eq`/`principal_three`/`principal_two` hold between polygons read
on the SAME side polygon `Q(t)` (e.g. `Q(t)`'s carrier vs the `(k−1)`-gon through the half's marks at `Q(t)`'s
positions, `s7q_principal_delete`), not between `Q(t)`'s carrier and the half's carrier on the centre; that last
comparison is the perturbation step `rotationNumber_locally_constant`.  The sign-level fields (`turn_eq`,
`turns_eq`) are the ones that transfer across the wall. -/

omit [NeZero n] in
/-- Summation bookkeeping: `g ∘ e = f` off a finite set `T` of corners other than `j`, and on `T` the sums
differ by `f j`. -/
theorem s7q_sum_eq_of_merge {k k₁ : ℕ} [NeZero k] [NeZero k₁] (f : ZMod k → ℝ) (g : ZMod k₁ → ℝ)
    (j : ZMod k) (e : {i : ZMod k // i ≠ j} ≃ ZMod k₁) (T : Finset {i : ZMod k // i ≠ j})
    (he : ∀ x : {i : ZMod k // i ≠ j}, x ∉ T → g (e x) = f x.1)
    (hT : ∑ x ∈ T, g (e x) = f j + ∑ x ∈ T, f x.1) : ∑ i, f i = ∑ i, g i := by
  classical
  have h1 : ∑ i, f i = f j + ∑ x : {i : ZMod k // i ≠ j}, f x.1 := by
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ j)]
    congr 1
    exact Finset.sum_subtype (Finset.univ.erase j) (fun x => by simp [Finset.mem_erase]) f
  have h2 : ∑ y : ZMod k₁, g y = ∑ x : {i : ZMod k // i ≠ j}, g (e x) :=
    (Fintype.sum_equiv e _ _ (fun x => rfl)).symm
  rw [h1, h2, ← Finset.sum_add_sum_compl T, ← Finset.sum_add_sum_compl T (fun x => g (e x)), hT,
    Finset.sum_congr rfl (fun x hx => he x (Finset.mem_compl.mp hx))]
  ring

omit [NeZero n] in
/-- Summation bookkeeping for the perturbation: `g ∘ e = f` off `T`, equal sums on `T`. -/
theorem s7q_sum_eq_of_perturb {k k₁ : ℕ} [NeZero k] [NeZero k₁] (f : ZMod k → ℝ) (g : ZMod k₁ → ℝ)
    (e : ZMod k ≃ ZMod k₁) (T : Finset (ZMod k)) (he : ∀ i, i ∉ T → g (e i) = f i)
    (hT : ∑ i ∈ T, g (e i) = ∑ i ∈ T, f i) : ∑ i, f i = ∑ i, g i := by
  classical
  have h1 : ∑ i, g i = ∑ i, g (e i) := (Fintype.sum_equiv e _ _ (fun i => rfl)).symm
  rw [h1, ← Finset.sum_add_sum_compl T, ← Finset.sum_add_sum_compl T (fun i => g (e i)), hT,
    Finset.sum_congr rfl (fun i hi => he i (Finset.mem_compl.mp hi))]

/-- **The ordered corner correspondence with one extra corner** (eq. s7c:short-direction-lists, corrected):
the corners of `Q` other than `j` (the corner at `μ_M`, turn `τ`) correspond in order to ALL corners of `Q₁`;
turn signs agree; principal turns agree off the two neighbours `j − 1`, `j + 1` of `j`, and the three turns at
`j − 1, j, j + 1` sum to the two turns at their images (`s7q_principal_three_a/_b`). -/
structure s7q_CornerMerge {k k₁ : ℕ} [NeZero k] [NeZero k₁] (Q : LabelledTuple k) (Q₁ : LabelledTuple k₁)
    (j : ZMod k) where
  ne₁ : j - 1 ≠ j
  ne₂ : j + 1 ≠ j
  ne₃ : j - 1 ≠ j + 1
  e : {i : ZMod k // i ≠ j} ≃ ZMod k₁
  turn_eq : ∀ x : {i : ZMod k // i ≠ j}, turn Q₁ (e x) = turn Q x.1
  principal_eq : ∀ x : {i : ZMod k // i ≠ j}, x.1 ≠ j - 1 → x.1 ≠ j + 1 →
    principalTurn Q₁ (e x) = principalTurn Q x.1
  principal_three : principalTurn Q₁ (e ⟨j - 1, ne₁⟩) + principalTurn Q₁ (e ⟨j + 1, ne₂⟩) =
    principalTurn Q (j - 1) + principalTurn Q j + principalTurn Q (j + 1)

omit [NeZero n] in
/-- "The chamber and half carriers have equal signed, and hence absolute, rotations." -/
theorem s7q_CornerMerge.rotationNumber_eq {k k₁ : ℕ} [NeZero k] [NeZero k₁] {Q : LabelledTuple k}
    {Q₁ : LabelledTuple k₁} {j : ZMod k} (hM : s7q_CornerMerge Q Q₁ j) :
    rotationNumber Q = rotationNumber Q₁ := by
  classical
  unfold rotationNumber
  have hne : (⟨j - 1, hM.ne₁⟩ : {i : ZMod k // i ≠ j}) ≠ ⟨j + 1, hM.ne₂⟩ := by
    intro h
    exact hM.ne₃ (congrArg Subtype.val h)
  have hT : ∑ x ∈ ({⟨j - 1, hM.ne₁⟩, ⟨j + 1, hM.ne₂⟩} : Finset {i : ZMod k // i ≠ j}),
      principalTurn Q₁ (hM.e x) =
      principalTurn Q j + ∑ x ∈ ({⟨j - 1, hM.ne₁⟩, ⟨j + 1, hM.ne₂⟩} : Finset {i : ZMod k // i ≠ j}),
        principalTurn Q x.1 := by
    rw [Finset.sum_pair hne, Finset.sum_pair hne, hM.principal_three]
    ring
  have he : ∀ x : {i : ZMod k // i ≠ j},
      x ∉ ({⟨j - 1, hM.ne₁⟩, ⟨j + 1, hM.ne₂⟩} : Finset {i : ZMod k // i ≠ j}) →
      principalTurn Q₁ (hM.e x) = principalTurn Q x.1 := by
    intro x hx
    refine hM.principal_eq x (fun h => hx ?_) (fun h => hx ?_)
    · simp [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, h]
    · simp [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff, h]
  rw [s7q_sum_eq_of_merge (principalTurn Q) (principalTurn Q₁) j hM.e _ he hT]

omit [NeZero n] in
/-- The turn multiset of `Q` is that of `Q₁` refined by the turn at `j` (the multiset form of
`s7c_carrierWeight_refine`'s hypotheses). -/
theorem s7q_CornerMerge.turns_eq {k k₁ : ℕ} [NeZero k] [NeZero k₁] {Q : LabelledTuple k}
    {Q₁ : LabelledTuple k₁} {j : ZMod k} (hM : s7q_CornerMerge Q Q₁ j) :
    s7c_turns Q = s7c_turns Q₁ + {turn Q j} := by
  classical
  rw [s7c_turns_eq_erase_add Q j, s7c_map_erase_eq_map_subtype,
    s7c_map_univ_eq_of_equiv (fun x : {i : ZMod k // i ≠ j} => turn Q x.1) (turn Q₁) hM.e hM.turn_eq]
  rfl

omit [NeZero n] in
/-- The three-turn identity from direction data, orientation of eq. s7c:turn-short-a (`P₋`, leg `M−1`: the
corner polygon runs `r` (edge `a`) → `u_in^Q` (the short edge `v_a → μ_M`) → `u_out^Q` (edge `M`) → `w`; the
half runs `r → u_out^c → w`): corners `j − 1 = v_a`, `j = μ_M`, `j + 1` ↦ `i₁ = μ_M(λ₁)`, `i₁ + 1`. -/
theorem s7q_principal_three_a {k k₁ : ℕ} [NeZero k] [NeZero k₁] (Q : LabelledTuple k) (Q₁ : LabelledTuple k₁)
    (j : ZMod k) (i₁ : ZMod k₁) {r uinQ uoutQ uoutC w : Plane} {η σ : SignType} (hη : η ≠ 0) (hσ : σ ≠ 0)
    (h1 : SignType.sign (det r uinQ) = η) (h2 : SignType.sign (det r uoutQ) = η)
    (h3 : SignType.sign (det r uoutC) = η)
    (h4 : SignType.sign (det w uoutQ) = σ) (h5 : SignType.sign (det w uoutC) = σ)
    {c₀ c₁ c₂ c₃ d₁ d₂ d₃ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (e₀ : edge Q (j - 1 - 1) = c₀ • r) (e₁ : edge Q (j - 1) = c₁ • uinQ) (e₂ : edge Q j = c₂ • uoutQ)
    (e₃ : edge Q (j + 1) = c₃ • w)
    (f₁ : edge Q₁ (i₁ - 1) = d₁ • r) (f₂ : edge Q₁ i₁ = d₂ • uoutC) (f₃ : edge Q₁ (i₁ + 1) = d₃ • w) :
    principalTurn Q₁ i₁ + principalTurn Q₁ (i₁ + 1) =
      principalTurn Q (j - 1) + principalTurn Q j + principalTurn Q (j + 1) := by
  have e₂' : edge Q (j + 1 - 1) = c₂ • uoutQ := by rw [add_sub_cancel_right]; exact e₂
  have f₂' : edge Q₁ (i₁ + 1 - 1) = d₂ • uoutC := by rw [add_sub_cancel_right]; exact f₂
  rw [s7i_principalTurn_eq_of_pos_smul Q₁ i₁ hd₁ hd₂ f₁ f₂,
    s7i_principalTurn_eq_of_pos_smul Q₁ (i₁ + 1) hd₂ hd₃ f₂' f₃,
    s7i_principalTurn_eq_of_pos_smul Q (j - 1) hc₀ hc₁ e₀ e₁,
    s7i_principalTurn_eq_of_pos_smul Q j hc₁ hc₂ e₁ e₂,
    s7i_principalTurn_eq_of_pos_smul Q (j + 1) hc₂ hc₃ e₂' e₃]
  have A := s7q_principalAngle_add_of_side hη h1 h2
  have B := s7q_two_turn_perturb hη hσ h2 h3 h4 h5
  linarith

omit [NeZero n] in
/-- The three-turn identity, orientation of eq. s7c:turn-short-b (`P₊`, leg `M`: the corner polygon runs
`w → u_in^Q` (edge `M−1`) → `u_out^Q` (the short edge `μ_M → v_ℓ`) → `r` (edge `a`); the half runs
`w → u_in^c → r`): corners `j − 1`, `j = μ_M`, `j + 1 = v_ℓ` ↦ `i₁`, `i₁ + 1 = μ_M(λ₂)`. -/
theorem s7q_principal_three_b {k k₁ : ℕ} [NeZero k] [NeZero k₁] (Q : LabelledTuple k) (Q₁ : LabelledTuple k₁)
    (j : ZMod k) (i₁ : ZMod k₁) {r uinQ uoutQ uinC w : Plane} {η σ : SignType} (hη : η ≠ 0) (hσ : σ ≠ 0)
    (h1 : SignType.sign (det r uinQ) = η) (h2 : SignType.sign (det r uoutQ) = η)
    (h3 : SignType.sign (det r uinC) = η)
    (h4 : SignType.sign (det w uinQ) = σ) (h5 : SignType.sign (det w uinC) = σ)
    {c₀ c₁ c₂ c₃ d₁ d₂ d₃ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (e₀ : edge Q (j - 1 - 1) = c₀ • w) (e₁ : edge Q (j - 1) = c₁ • uinQ) (e₂ : edge Q j = c₂ • uoutQ)
    (e₃ : edge Q (j + 1) = c₃ • r)
    (f₁ : edge Q₁ (i₁ - 1) = d₁ • w) (f₂ : edge Q₁ i₁ = d₂ • uinC) (f₃ : edge Q₁ (i₁ + 1) = d₃ • r) :
    principalTurn Q₁ i₁ + principalTurn Q₁ (i₁ + 1) =
      principalTurn Q (j - 1) + principalTurn Q j + principalTurn Q (j + 1) := by
  have e₂' : edge Q (j + 1 - 1) = c₂ • uoutQ := by rw [add_sub_cancel_right]; exact e₂
  have f₂' : edge Q₁ (i₁ + 1 - 1) = d₂ • uinC := by rw [add_sub_cancel_right]; exact f₂
  rw [s7i_principalTurn_eq_of_pos_smul Q₁ i₁ hd₁ hd₂ f₁ f₂,
    s7i_principalTurn_eq_of_pos_smul Q₁ (i₁ + 1) hd₂ hd₃ f₂' f₃,
    s7i_principalTurn_eq_of_pos_smul Q (j - 1) hc₀ hc₁ e₀ e₁,
    s7i_principalTurn_eq_of_pos_smul Q j hc₁ hc₂ e₁ e₂,
    s7i_principalTurn_eq_of_pos_smul Q (j + 1) hc₂ hc₃ e₂' e₃]
  have A := s7q_principalAngle_add_of_side' hη h1 h2
  have B := s7q_two_turn_perturb hσ hη h4 h5 h1 h3
  linarith

/-- **The ordered corner correspondence with the same corners and two perturbed turns** (the pivot carrier on
`P₋`, the `v_a`-carrier on `P₊`): turn signs agree everywhere, principal turns agree off `{p − 1, p}`, and the
two turns at `p − 1`, `p` have the same sum (`s7q_two_turn_perturb`, `s7q_principal_two`). -/
structure s7q_CornerPerturb {k k₁ : ℕ} [NeZero k] [NeZero k₁] (Q : LabelledTuple k) (Q₁ : LabelledTuple k₁)
    (p : ZMod k) where
  e : ZMod k ≃ ZMod k₁
  turn_eq : ∀ i, turn Q₁ (e i) = turn Q i
  principal_eq : ∀ i, i ≠ p - 1 → i ≠ p → principalTurn Q₁ (e i) = principalTurn Q i
  principal_two : principalTurn Q₁ (e (p - 1)) + principalTurn Q₁ (e p) =
    principalTurn Q (p - 1) + principalTurn Q p

omit [NeZero n] in
theorem s7q_CornerPerturb.rotationNumber_eq {k k₁ : ℕ} [NeZero k] [NeZero k₁] {Q : LabelledTuple k}
    {Q₁ : LabelledTuple k₁} {p : ZMod k} (hM : s7q_CornerPerturb Q Q₁ p) :
    rotationNumber Q = rotationNumber Q₁ := by
  classical
  unfold rotationNumber
  have he : ∀ i, i ∉ ({p - 1, p} : Finset (ZMod k)) → principalTurn Q₁ (hM.e i) = principalTurn Q i := by
    intro i hi
    refine hM.principal_eq i (fun h => hi ?_) (fun h => hi ?_)
    · simp [Finset.mem_insert, Finset.mem_singleton, h]
    · simp [Finset.mem_insert, Finset.mem_singleton, h]
  have hT : ∑ i ∈ ({p - 1, p} : Finset (ZMod k)), principalTurn Q₁ (hM.e i) =
      ∑ i ∈ ({p - 1, p} : Finset (ZMod k)), principalTurn Q i := by
    by_cases hp : p - 1 = p
    · have h2 := hM.principal_two
      rw [hp] at h2
      rw [hp, Finset.insert_eq_of_mem (Finset.mem_singleton_self p), Finset.sum_singleton,
        Finset.sum_singleton]
      linarith
    · rw [Finset.sum_pair hp, Finset.sum_pair hp, hM.principal_two]
  rw [s7q_sum_eq_of_perturb (principalTurn Q) (principalTurn Q₁) hM.e _ he hT]

omit [NeZero n] in
theorem s7q_CornerPerturb.turns_eq {k k₁ : ℕ} [NeZero k] [NeZero k₁] {Q : LabelledTuple k}
    {Q₁ : LabelledTuple k₁} {p : ZMod k} (hM : s7q_CornerPerturb Q Q₁ p) :
    s7c_turns Q = s7c_turns Q₁ := by
  unfold s7c_turns
  exact s7c_map_univ_eq_of_equiv (turn Q) (turn Q₁) hM.e hM.turn_eq

omit [NeZero n] in
/-- The two-turn identity from direction data (the middle direction `u^Q` of the side vs `u^c` of the half, on
one side of both neighbouring directions `w`, `r`): corners `p − 1, p` ↦ `i₁, i₁ + 1`. -/
theorem s7q_principal_two {k k₁ : ℕ} [NeZero k] [NeZero k₁] (Q : LabelledTuple k) (Q₁ : LabelledTuple k₁)
    (p : ZMod k) (i₁ : ZMod k₁) {w uQ uC r : Plane} {σ τ : SignType} (hσ : σ ≠ 0) (hτ : τ ≠ 0)
    (h1 : SignType.sign (det w uQ) = σ) (h2 : SignType.sign (det w uC) = σ)
    (h3 : SignType.sign (det r uQ) = τ) (h4 : SignType.sign (det r uC) = τ)
    {c₀ c₁ c₂ d₀ d₁ d₂ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (e₀ : edge Q (p - 1 - 1) = c₀ • w) (e₁ : edge Q (p - 1) = c₁ • uQ) (e₂ : edge Q p = c₂ • r)
    (f₀ : edge Q₁ (i₁ - 1) = d₀ • w) (f₁ : edge Q₁ i₁ = d₁ • uC) (f₂ : edge Q₁ (i₁ + 1) = d₂ • r) :
    principalTurn Q₁ i₁ + principalTurn Q₁ (i₁ + 1) = principalTurn Q (p - 1) + principalTurn Q p := by
  have e₁' : edge Q (p - 1) = c₁ • uQ := e₁
  have f₁' : edge Q₁ (i₁ + 1 - 1) = d₁ • uC := by rw [add_sub_cancel_right]; exact f₁
  rw [s7i_principalTurn_eq_of_pos_smul Q₁ i₁ hd₀ hd₁ f₀ f₁,
    s7i_principalTurn_eq_of_pos_smul Q₁ (i₁ + 1) hd₁ hd₂ f₁' f₂,
    s7i_principalTurn_eq_of_pos_smul Q (p - 1) hc₀ hc₁ e₀ e₁,
    s7i_principalTurn_eq_of_pos_smul Q p hc₁ hc₂ e₁' e₂]
  exact (s7q_two_turn_perturb hσ hτ h1 h2 h3 h4).symm

/-- Carrier-level reading of the merge: rotation equality (`hr` of `s7d_cornerCoefficient_eq_of_cut`). -/
theorem s7q_carrierRotation_eq_of_merge (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁)
    {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁) (S₁ : Finset (Crossing P₁)) (q₁ : Component hn₁ hP₁ S₁)
    {j : ZMod (ccpCornerCount hn hP S q)}
    (hM : s7q_CornerMerge (ccpCornerPolygon hn hP S q) (ccpCornerPolygon hn₁ hP₁ S₁ q₁) j) :
    carrierRotation hn hP S q = carrierRotation hn₁ hP₁ S₁ q₁ :=
  hM.rotationNumber_eq

/-- … and the refined weight `wt(q) = sel(turns(q₁) + {τ})`, `τ` the turn at `j` (eq. s7c:short-selector). -/
theorem s7q_carrierWeight_eq_of_merge (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁)
    {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁) (S₁ : Finset (Crossing P₁)) (q₁ : Component hn₁ hP₁ S₁)
    {j : ZMod (ccpCornerCount hn hP S q)}
    (hM : s7q_CornerMerge (ccpCornerPolygon hn hP S q) (ccpCornerPolygon hn₁ hP₁ S₁ q₁) j) :
    carrierWeight hn hP S q =
      s7c_sel (s7c_turns (ccpCornerPolygon hn₁ hP₁ S₁ q₁) + {turn (ccpCornerPolygon hn hP S q) j}) := by
  rw [s7c_carrierWeight_eq_sel, hM.turns_eq]

theorem s7q_carrierRotation_eq_of_perturb (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁)
    {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁) (S₁ : Finset (Crossing P₁)) (q₁ : Component hn₁ hP₁ S₁)
    {p : ZMod (ccpCornerCount hn hP S q)}
    (hM : s7q_CornerPerturb (ccpCornerPolygon hn hP S q) (ccpCornerPolygon hn₁ hP₁ S₁ q₁) p) :
    carrierRotation hn hP S q = carrierRotation hn₁ hP₁ S₁ q₁ :=
  hM.rotationNumber_eq

theorem s7q_carrierWeight_eq_of_perturb (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) {n₁ : ℕ} [NeZero n₁] (hn₁ : 3 ≤ n₁)
    {P₁ : LabelledTuple n₁} (hP₁ : Generic P₁) (S₁ : Finset (Crossing P₁)) (q₁ : Component hn₁ hP₁ S₁)
    {p : ZMod (ccpCornerCount hn hP S q)}
    (hM : s7q_CornerPerturb (ccpCornerPolygon hn hP S q) (ccpCornerPolygon hn₁ hP₁ S₁ q₁) p) :
    carrierWeight hn hP S q = carrierWeight hn₁ hP₁ S₁ q₁ := by
  rw [s7c_carrierWeight_eq_sel, s7c_carrierWeight_eq_sel, hM.turns_eq]

end S7QMerge

section S7QAlgebra

/-! #### (c) The per-row bookkeeping (eqs. s7c:sliding-coefficients, s7c:sliding-selector-factors,
s7c:sliding-selector-difference): products over the carriers along `Component S ≃ Component S₁ ⊕ Component S₂`
(U110-B's `componentEquiv`), one refined carrier per side, `s7c_sliding_selector_difference`. -/

omit [NeZero n] in
/-- A product over `B` read through `e : B ≃ D` with one exceptional value at `e.symm a₀`. -/
theorem s7q_prod_eq_of_except {D B : Type*} [Fintype D] [Fintype B] [DecidableEq D] (e : B ≃ D)
    (f : B → ℤ) (w : D → ℤ) (a₀ : D) (v : ℤ) (hf : ∀ b, e b ≠ a₀ → f b = w (e b))
    (hv : f (e.symm a₀) = v) : ∏ b, f b = v * ∏ d ∈ Finset.univ.erase a₀, w d := by
  have h1 : ∏ b, f b = ∏ d, Function.update w a₀ v d := by
    refine Fintype.prod_equiv e _ _ (fun b => ?_)
    by_cases hb : e b = a₀
    · have hb' : b = e.symm a₀ := by rw [← hb, Equiv.symm_apply_apply]
      rw [hb, Function.update_self, hb', hv]
    · rw [Function.update_of_ne hb, hf b hb]
  rw [h1, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a₀), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl (fun d hd => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hd)]

omit [NeZero n] in
/-- **The termwise identity of a sliding row, abstractly** (sm-4:358-377).  Carriers of `P₋` (`B`) and of `P₊`
(`C`) both correspond to the half carriers `D = Component S₁ ⊕ Component S₂`; coefficients are transported
(eq. s7c:sliding-coefficients); the weights are transported except at ONE carrier per side (`a₀` on `P₋`, `a₀'`
on `P₊` — the two half contact carriers, of contact signs `s`, `−s`), whose weight is the refined selector
`sel(m + {τ})`.  Then `W₊C₊ − W₋C₋ = s (W₁C₁)(W₂C₂)` with `Q_sp` the product of the other weights, "without
assuming it nonzero". -/
theorem s7q_term_difference {D B C : Type*} [Fintype D] [Fintype B] [Fintype C] [DecidableEq D]
    (em : B ≃ D) (ep : C ≃ D) (cm : B → ℤ) (cp : C → ℤ) (c : D → ℤ) (wm : B → ℤ) (wp : C → ℤ)
    (w : D → ℤ) (a₀ a₀' : D) (hne : a₀ ≠ a₀') (m₀ m₀' : Multiset SignType) {s τ : SignType}
    (hs : s ≠ 0) (hτ : τ ≠ 0) (hm₀ : s ∈ m₀) (hm₀' : -s ∈ m₀')
    (hw₀ : w a₀ = s7c_sel m₀) (hw₀' : w a₀' = s7c_sel m₀')
    (hcm : ∀ b, cm b = c (em b)) (hcp : ∀ x, cp x = c (ep x))
    (hwm : ∀ b, em b ≠ a₀ → wm b = w (em b)) (hwp : ∀ x, ep x ≠ a₀' → wp x = w (ep x))
    (hwm₀ : wm (em.symm a₀) = s7c_sel (m₀ + {τ})) (hwp₀ : wp (ep.symm a₀') = s7c_sel (m₀' + {τ})) :
    (∏ x, wp x) * (∏ x, cp x) - (∏ b, wm b) * (∏ b, cm b) =
      (s : ℤ) * ((∏ d, w d) * ∏ d, c d) := by
  have hCm : ∏ b, cm b = ∏ d, c d := Fintype.prod_equiv em _ _ hcm
  have hCp : ∏ x, cp x = ∏ d, c d := Fintype.prod_equiv ep _ _ hcp
  have hWm := s7q_prod_eq_of_except em wm w a₀ _ hwm hwm₀
  have hWp := s7q_prod_eq_of_except ep wp w a₀' _ hwp hwp₀
  have hmem : a₀' ∈ Finset.univ.erase a₀ := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
  have hmem' : a₀ ∈ Finset.univ.erase a₀' := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
  have hE : ∏ d ∈ Finset.univ.erase a₀, w d =
      w a₀' * ∏ d ∈ (Finset.univ.erase a₀).erase a₀', w d :=
    (Finset.mul_prod_erase _ _ hmem).symm
  have hE' : ∏ d ∈ Finset.univ.erase a₀', w d =
      w a₀ * ∏ d ∈ (Finset.univ.erase a₀).erase a₀', w d := by
    rw [Finset.erase_right_comm]
    exact (Finset.mul_prod_erase _ _ hmem').symm
  have hW : ∏ d, w d = w a₀ * ∏ d ∈ Finset.univ.erase a₀, w d :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ a₀)).symm
  set Qsp := ∏ d ∈ (Finset.univ.erase a₀).erase a₀', w d with hQsp
  have key := s7c_sliding_selector_difference Qsp m₀ m₀' hs hτ hm₀ hm₀'
  rw [hCm, hCp, hWm, hWp, hE, hE', hW, hE, hw₀, hw₀']
  linear_combination (∏ d, c d) * key

/-- **Per-row data of a sliding row on one side** (the consumer shape of `s7q_term_difference`): a carrier
correspondence `e` (U110-B's `componentEquiv`), transported coefficients (U110-D's `s7d_cornerCoefficient_eq_of_cut`
with `hr` from §S7QMerge), transported weights off the ONE carrier `e.symm a₀` (the relocated contact carrier of
eq. s7c:short-direction-lists), whose weight is the refined selector `sel(m₀ + {τ})` (`s7q_carrierWeight_eq_of_merge`). -/
structure s7q_RowData (hn : 3 ≤ n) {Q : LabelledTuple n} (hQ : Generic Q) {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]
    (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁)
    (hP₂ : Generic P₂) {S : Finset (Crossing Q)} (hS : IsDecomposition hn hQ S)
    {S₁ : Finset (Crossing P₁)} (hS₁ : IsDecomposition hn₁ hP₁ S₁)
    {S₂ : Finset (Crossing P₂)} (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (a₀ : Component hn₁ hP₁ S₁ ⊕ Component hn₂ hP₂ S₂) (m₀ : Multiset SignType) (τ : SignType) : Prop where
  data : ∃ e : Component hn hQ S ≃ Component hn₁ hP₁ S₁ ⊕ Component hn₂ hP₂ S₂,
    (∀ q, cornerCoefficient hn hQ S q hS =
      Sum.elim (fun r => cornerCoefficient hn₁ hP₁ S₁ r hS₁) (fun r => cornerCoefficient hn₂ hP₂ S₂ r hS₂)
        (e q)) ∧
    (∀ q, e q ≠ a₀ → carrierWeight hn hQ S q =
      Sum.elim (carrierWeight hn₁ hP₁ S₁) (carrierWeight hn₂ hP₂ S₂) (e q)) ∧
    carrierWeight hn hQ S (e.symm a₀) = s7c_sel (m₀ + {τ})

/-- **The termwise identity of a sliding row on the actual state-sum terms**: from the row data of both sides
(refined at the two DIFFERENT half contact carriers `a₀ ≠ a₀'`, of turn multisets `m₀ ∋ s`, `m₀' ∋ −s`),
`term₊ − term₋ = s · term₁ · term₂`. -/
theorem s7q_term_eq_of_rowData (hn : 3 ≤ n) {Qm Qp : LabelledTuple n} (hQm : Generic Qm) (hQp : Generic Qp)
    {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂] (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂)
    {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂)
    {Sm : Finset (Crossing Qm)} (hSm : IsDecomposition hn hQm Sm)
    {Sp : Finset (Crossing Qp)} (hSp : IsDecomposition hn hQp Sp)
    {S₁ : Finset (Crossing P₁)} (hS₁ : IsDecomposition hn₁ hP₁ S₁)
    {S₂ : Finset (Crossing P₂)} (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    {a₀ a₀' : Component hn₁ hP₁ S₁ ⊕ Component hn₂ hP₂ S₂} (hne : a₀ ≠ a₀')
    {m₀ m₀' : Multiset SignType} {s τ : SignType} (hs : s ≠ 0) (hτ : τ ≠ 0)
    (hm₀ : s ∈ m₀) (hm₀' : -s ∈ m₀')
    (hw₀ : Sum.elim (carrierWeight hn₁ hP₁ S₁) (carrierWeight hn₂ hP₂ S₂) a₀ = s7c_sel m₀)
    (hw₀' : Sum.elim (carrierWeight hn₁ hP₁ S₁) (carrierWeight hn₂ hP₂ S₂) a₀' = s7c_sel m₀')
    (hrm : s7q_RowData hn hQm hn₁ hn₂ hP₁ hP₂ hSm hS₁ hS₂ a₀ m₀ τ)
    (hrp : s7q_RowData hn hQp hn₁ hn₂ hP₁ hP₂ hSp hS₁ hS₂ a₀' m₀' τ) :
    s7e_term hn hQp Sp - s7e_term hn hQm Sm =
      (s : ℤ) * (s7e_term hn₁ hP₁ S₁ * s7e_term hn₂ hP₂ S₂) := by
  classical
  obtain ⟨em, hcm, hwm, hwm₀⟩ := hrm.data
  obtain ⟨ep, hcp, hwp, hwp₀⟩ := hrp.data
  rw [s7e_term_of_decomposition hn hQp hSp, s7e_term_of_decomposition hn hQm hSm,
    s7e_term_of_decomposition hn₁ hP₁ hS₁, s7e_term_of_decomposition hn₂ hP₂ hS₂]
  unfold wind cornerProduct
  have key := s7q_term_difference em ep _ _
    (Sum.elim (fun r => cornerCoefficient hn₁ hP₁ S₁ r hS₁) (fun r => cornerCoefficient hn₂ hP₂ S₂ r hS₂))
    _ _ (Sum.elim (carrierWeight hn₁ hP₁ S₁) (carrierWeight hn₂ hP₂ S₂)) a₀ a₀' hne m₀ m₀' hs hτ hm₀ hm₀'
    hw₀ hw₀' hcm hcp hwm hwp hwm₀ hwp₀
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type] at key
  simp only [Sum.elim_inl, Sum.elim_inr] at key
  rw [key]
  ring

end S7QAlgebra

section S7QTransport

/-! #### The row data from U110-B's transport (RET) and pivot split (SPLIT): the coefficient clause is
`s7d_cornerCoefficient_eq_of_cut` carrier by carrier along `componentEquiv`, with `hmem` from
`carrierCrossings_eq_img_first/_second` + `s7b_visit_of_*CrossingQ` and `htwin` from `s7b_*VisitQ_visitTwin`
(PROVED here); the remaining per-carrier inputs (`hmono`/`hcut`: the key decoding of the half labelling with the
cut `c`; `hbit`: the over bits; `hr`: the rotation equality, §S7QMerge) and the weight clause are hypotheses. -/

variable {hn : 3 ≤ n} {M a : ZMod n} {hsep : ContactSeparated M a} {P Q : LabelledTuple n}
  {hm : P M ∈ edgeInterior P a}
  {hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)}
  {hQ : Generic Q} {h₁ : Generic (firstHalf P M a)} {h₂ : Generic (secondHalf P M a)}
  {S : Finset (Crossing Q)} {S₁ : Finset (Crossing (firstHalf P M a))}
  {S₂ : Finset (Crossing (secondHalf P M a))} {vm : Visit Q}

/-- The cut-form inputs of `s7d_cornerCoefficient_eq_of_cut` for a carrier `q` of `Q` corresponding to the
carrier `q₁` of `λ₁` under `φ := s7b_firstVisitQ` and the cut `c` (the wrap of `Q`'s edge labels inside the
half's labelling): key monotonicity off the cut, reversal across it, equal over bits, equal rotations. -/
def s7q_CutFirst (hn : 3 ≤ n) (hsep : ContactSeparated M a) (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)) (hQ : Generic Q)
    (h₁ : Generic (firstHalf P M a)) (S : Finset (Crossing Q)) (S₁ : Finset (Crossing (firstHalf P M a)))
    (q : Component hn hQ S) (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁) : Prop :=
  ∃ c : ℝ,
    (∀ v w : Visit (firstHalf P M a),
      v.1 ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ →
      w.1 ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ →
      geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).1.1 h₁) v <
        geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).1.1 h₁) w →
      (geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).1.1 h₁) w < c ∨
        c ≤ geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).1.1 h₁) v) →
      geometricVisitKey (CB.cg hn hQ) (s7b_firstVisitQ hn hsep hm hQC v) <
        geometricVisitKey (CB.cg hn hQ) (s7b_firstVisitQ hn hsep hm hQC w)) ∧
    (∀ v w : Visit (firstHalf P M a),
      v.1 ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ →
      w.1 ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ →
      geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).1.1 h₁) v < c →
      c ≤ geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).1.1 h₁) w →
      geometricVisitKey (CB.cg hn hQ) (s7b_firstVisitQ hn hsep hm hQC w) <
        geometricVisitKey (CB.cg hn hQ) (s7b_firstVisitQ hn hsep hm hQC v)) ∧
    (∀ v : Visit (firstHalf P M a),
      v.1 ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ →
      CB.positiveOverBit (s7b_firstVisitQ hn hsep hm hQC v) = CB.positiveOverBit v) ∧
    carrierRotation (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ = carrierRotation hn hQ S q

/-- The same for a carrier corresponding to a carrier `q₂` of `λ₂` under `s7b_secondVisitQ`. -/
def s7q_CutSecond (hn : 3 ≤ n) (hsep : ContactSeparated M a) (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)) (hQ : Generic Q)
    (h₂ : Generic (secondHalf P M a)) (S : Finset (Crossing Q))
    (S₂ : Finset (Crossing (secondHalf P M a)))
    (q : Component hn hQ S) (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂) : Prop :=
  ∃ c : ℝ,
    (∀ v w : Visit (secondHalf P M a),
      v.1 ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ →
      w.1 ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ →
      geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).2.1 h₂) v <
        geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).2.1 h₂) w →
      (geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).2.1 h₂) w < c ∨
        c ≤ geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).2.1 h₂) v) →
      geometricVisitKey (CB.cg hn hQ) (s7b_secondVisitQ hn hsep hm hQC v) <
        geometricVisitKey (CB.cg hn hQ) (s7b_secondVisitQ hn hsep hm hQC w)) ∧
    (∀ v w : Visit (secondHalf P M a),
      v.1 ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ →
      w.1 ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ →
      geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).2.1 h₂) v < c →
      c ≤ geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).2.1 h₂) w →
      geometricVisitKey (CB.cg hn hQ) (s7b_secondVisitQ hn hsep hm hQC w) <
        geometricVisitKey (CB.cg hn hQ) (s7b_secondVisitQ hn hsep hm hQC v)) ∧
    (∀ v : Visit (secondHalf P M a),
      v.1 ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ →
      CB.positiveOverBit (s7b_secondVisitQ hn hsep hm hQC v) = CB.positiveOverBit v) ∧
    carrierRotation (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ = carrierRotation hn hQ S q

/-! ##### The key decoding of the half labelling (the `hmono`/`hcut` clauses of `s7q_CutFirst`/`_Second`).
`λ₁`'s edge `i` is `Q`'s edge `M + i`; `Q`'s traversal key of the image is `((M.val + i.val) % n) + p'`, the
half's is `i.val + p`.  Off the wrap of `Q`'s labels (`M.val + i.val < n`) the image key is the half key shifted
by `M.val`; across the wrap it drops by `n`: so the image order is the half order cut at `c = n − M.val`, PROVIDED
the same-edge order of parameters agrees (`hord`: the only geometric input — `ContactOrderAgrees` of
lem:wall-sides (V) on `Q` composed with U110-B's parameter laws at the centre, monotone on the cut edge). -/

omit [NeZero n] in
/-- A traversal key as `edge.val + parameter`. -/
theorem s7q_key_eq {k : ℕ} [NeZero k] (hk : 3 ≤ k) {R : LabelledTuple k} (hR : Generic R) (v : Visit R) :
    geometricVisitKey (CB.cg hk hR) v = ((v.2.val.val : ℕ) : ℝ) + visitParameter v := by
  rw [s7e_gkey hk hR v, s7e_markKey_eq hk hR (Sum.inr v)]
  rfl

omit [NeZero n] in
/-- Keys `e + p`, `e' + p'` with `p, p' ∈ [0, 1)` compare by the edge index first. -/
theorem s7q_key_lt_of_edge_lt {e e' : ℕ} {p p' : ℝ} (hp : p < 1) (hp' : 0 ≤ p') (h : e < e') :
    (e : ℝ) + p < e' + p' := by
  have : (e : ℝ) + 1 ≤ e' := by exact_mod_cast h
  linarith

omit [NeZero n] in
theorem s7q_edge_lt_of_key_lt {e e' : ℕ} {p p' : ℝ} (hp : 0 ≤ p) (hp' : p' < 1) (h : (e : ℝ) + p < e' + p') :
    e ≤ e' := by
  by_contra hc
  have : (e' : ℝ) + 1 ≤ e := by exact_mod_cast not_le.mp hc
  linarith

/-- The edge label of the image of `λ₁`'s edge `i` on `Q`, as a natural number: `(M.val + i.val) % n`. -/
theorem s7q_firstHalfIndex_val {M a : ZMod n} (i : ZMod (firstHalfSize M a)) :
    (firstHalfIndex M a i).val = (M.val + i.val) % n := by
  unfold firstHalfIndex cyclicRangeIndex
  rw [ZMod.val_add, ZMod.val_natCast_of_lt (lt_of_lt_of_le i.val_lt (firstHalfSize_le M a))]

theorem s7q_secondHalfEdgeIndex_val {M a : ZMod n} (j : ZMod (secondHalfSize M a)) :
    (secondHalfEdgeIndex M a j).val = (a.val + j.val) % n := by
  unfold secondHalfEdgeIndex cyclicRangeIndex
  rw [ZMod.val_add, ZMod.val_natCast_of_lt (lt_of_lt_of_le j.val_lt (secondHalfSize_le M a))]

omit [NeZero n] in
/-- The wrap arithmetic: `(m + i) % n` is `m + i` below `n` and `m + i − n` from `n` on (`m, i < n`). -/
theorem s7q_mod_cases {m i : ℕ} (hm : m < n) (hi : i < n) :
    (((m + i) % n : ℕ) : ℝ) = if m + i < n then (m : ℝ) + i else (m : ℝ) + i - n := by
  split_ifs with h
  · rw [Nat.mod_eq_of_lt h]; push_cast; ring
  · have h' : n ≤ m + i := not_lt.mp h
    rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)]
    rw [Nat.cast_sub h']; push_cast; ring

omit [NeZero n] in
/-- **The abstract key decoding**: half keys `i + p` (`i < k ≤ n`, `p ∈ [0,1)`), image keys
`((m + i) % n) + p'` with the same-edge order of `p'` that of `p`; then the image order is the half order
cut at `c = n − m`: monotone on each side of the cut, reversed across it. -/
theorem s7q_key_decoding {ι : Type*} (m k : ℕ) (hk : k ≤ n) (hm : m < n) (ed : ι → ℕ) (hed : ∀ v, ed v < k)
    (p p' : ι → ℝ) (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v < 1) (hp0' : ∀ v, 0 ≤ p' v) (hp1' : ∀ v, p' v < 1)
    (hord : ∀ v w, ed v = ed w → (p v < p w ↔ p' v < p' w)) :
    (∀ v w, (ed v : ℝ) + p v < ed w + p w →
      ((ed w : ℝ) + p w < (n : ℝ) - m ∨ (n : ℝ) - m ≤ ed v + p v) →
      (((m + ed v) % n : ℕ) : ℝ) + p' v < (((m + ed w) % n : ℕ) : ℝ) + p' w) ∧
    (∀ v w, (ed v : ℝ) + p v < (n : ℝ) - m → (n : ℝ) - m ≤ ed w + p w →
      (((m + ed w) % n : ℕ) : ℝ) + p' w < (((m + ed v) % n : ℕ) : ℝ) + p' v) := by
  have hedn : ∀ v, ed v < n := fun v => lt_of_lt_of_le (hed v) hk
  -- the wrap test in terms of the cut
  have hwrap : ∀ v, ((n : ℝ) - m ≤ ed v + p v ↔ n ≤ m + ed v) := by
    intro v
    constructor
    · intro h
      by_contra hc
      have : m + ed v + 1 ≤ n := not_le.mp hc
      have : (m : ℝ) + ed v + 1 ≤ n := by exact_mod_cast this
      linarith [hp1 v]
    · intro h
      have : (n : ℝ) ≤ m + ed v := by exact_mod_cast h
      linarith [hp0 v]
  constructor
  · intro v w hlt hside
    rw [s7q_mod_cases hm (hedn v), s7q_mod_cases hm (hedn w)]
    have hle : ed v ≤ ed w := s7q_edge_lt_of_key_lt (hp0 v) (hp1 w) hlt
    rcases lt_or_eq_of_le hle with hvw | hvw
    · -- different edges: both on one side of the wrap
      rcases hside with hside | hside
      · have h1 : ¬ n ≤ m + ed w := fun h => by
          have := (hwrap w).mpr h
          linarith
        have h2 : ¬ n ≤ m + ed v := fun h => h1 (by omega)
        rw [ite_eq_left (not_le.mp h2), ite_eq_left (not_le.mp h1)]
        have : (ed v : ℝ) + 1 ≤ ed w := by exact_mod_cast hvw
        linarith [hp1' v, hp0' w]
      · have h1 : n ≤ m + ed v := (hwrap v).mp hside
        have h2 : n ≤ m + ed w := by omega
        rw [ite_eq_right (not_lt.mpr h1), ite_eq_right (not_lt.mpr h2)]
        have : (ed v : ℝ) + 1 ≤ ed w := by exact_mod_cast hvw
        linarith [hp1' v, hp0' w]
    · -- the same edge: the parameters decide, and `hord` transports their order
      have hp : p v < p w := by
        have : (ed v : ℝ) = ed w := by exact_mod_cast hvw
        linarith
      have hp' : p' v < p' w := (hord v w hvw).mp hp
      rw [hvw]
      linarith
  · intro v w hv hw
    rw [s7q_mod_cases hm (hedn v), s7q_mod_cases hm (hedn w)]
    have h1 : ¬ n ≤ m + ed v := fun h => by
      have := (hwrap v).mpr h
      linarith
    have h2 : n ≤ m + ed w := (hwrap w).mp hw
    rw [ite_eq_left (not_le.mp h1), ite_eq_right (not_lt.mpr h2)]
    have : (ed w : ℝ) + 1 ≤ n := by exact_mod_cast hedn w
    linarith [hp0' v, hp1' w]

/-- **The `hmono`/`hcut` clauses of `s7q_CutFirst` from the same-edge order agreement** `hord` (the visits of
`λ₁` on one edge map to `Q`'s visits on the image edge in the same parameter order), with the cut
`c = n − M.val` (the wrap of `Q`'s labels inside `λ₁`'s labelling `M, M+1, …, a`). -/
theorem s7q_keys_first (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a) {P Q : LabelledTuple n}
    (hm : P M ∈ edgeInterior P a) (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hQ : Generic Q) (h₁ : Generic (firstHalf P M a))
    (hord : ∀ v w : Visit (firstHalf P M a), v.2.val = w.2.val →
      (visitParameter v < visitParameter w ↔
        visitParameter (s7b_firstVisitQ hn hsep hm hQC v) < visitParameter (s7b_firstVisitQ hn hsep hm hQC w))) :
    (∀ v w : Visit (firstHalf P M a),
      geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).1.1 h₁) v <
        geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).1.1 h₁) w →
      (geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).1.1 h₁) w < (n : ℝ) - M.val ∨
        (n : ℝ) - M.val ≤ geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).1.1 h₁) v) →
      geometricVisitKey (CB.cg hn hQ) (s7b_firstVisitQ hn hsep hm hQC v) <
        geometricVisitKey (CB.cg hn hQ) (s7b_firstVisitQ hn hsep hm hQC w)) ∧
    (∀ v w : Visit (firstHalf P M a),
      geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).1.1 h₁) v < (n : ℝ) - M.val →
      (n : ℝ) - M.val ≤ geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).1.1 h₁) w →
      geometricVisitKey (CB.cg hn hQ) (s7b_firstVisitQ hn hsep hm hQC w) <
        geometricVisitKey (CB.cg hn hQ) (s7b_firstVisitQ hn hsep hm hQC v)) := by
  have hn₁ := (contactHalfSizes_bounds hn hsep).1.1
  have hk1 : ∀ v : Visit (firstHalf P M a),
      geometricVisitKey (CB.cg hn₁ h₁) v = ((v.2.val.val : ℕ) : ℝ) + visitParameter v :=
    fun v => s7q_key_eq hn₁ h₁ v
  have hk2 : ∀ v : Visit (firstHalf P M a),
      geometricVisitKey (CB.cg hn hQ) (s7b_firstVisitQ hn hsep hm hQC v) =
        (((M.val + v.2.val.val) % n : ℕ) : ℝ) + visitParameter (s7b_firstVisitQ hn hsep hm hQC v) := by
    intro v
    rw [s7q_key_eq hn hQ, s7b_firstVisitQ_edge, s7q_firstHalfIndex_val]
  have key := s7q_key_decoding (n := n) M.val (firstHalfSize M a) (firstHalfSize_le M a) (ZMod.val_lt M)
    (fun v : Visit (firstHalf P M a) => v.2.val.val) (fun v => ZMod.val_lt _)
    visitParameter (fun v => visitParameter (s7b_firstVisitQ hn hsep hm hQC v))
    (fun v => (s7e_visitParameter_pos hn₁ h₁ v).le) (fun v => s7e_visitParameter_lt_one hn₁ h₁ v)
    (fun v => (s7e_visitParameter_pos hn hQ _).le) (fun v => s7e_visitParameter_lt_one hn hQ _)
    (fun v w hvw => hord v w (ZMod.val_injective _ hvw))
  refine ⟨fun v w h1 h2 => ?_, fun v w h1 h2 => ?_⟩
  · rw [hk1, hk1] at h1 h2
    rw [hk2, hk2]
    exact key.1 v w h1 h2
  · rw [hk1] at h1 h2
    rw [hk2, hk2]
    exact key.2 v w h1 h2

/-- The same for `λ₂` under `s7b_secondVisitQ` (edge `j` ↦ `a + j`; cut `c = n − a.val`). -/
theorem s7q_keys_second (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a) {P Q : LabelledTuple n}
    (hm : P M ∈ edgeInterior P a) (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hQ : Generic Q) (h₂ : Generic (secondHalf P M a))
    (hord : ∀ v w : Visit (secondHalf P M a), v.2.val = w.2.val →
      (visitParameter v < visitParameter w ↔
        visitParameter (s7b_secondVisitQ hn hsep hm hQC v) <
          visitParameter (s7b_secondVisitQ hn hsep hm hQC w))) :
    (∀ v w : Visit (secondHalf P M a),
      geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).2.1 h₂) v <
        geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).2.1 h₂) w →
      (geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).2.1 h₂) w < (n : ℝ) - a.val ∨
        (n : ℝ) - a.val ≤ geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).2.1 h₂) v) →
      geometricVisitKey (CB.cg hn hQ) (s7b_secondVisitQ hn hsep hm hQC v) <
        geometricVisitKey (CB.cg hn hQ) (s7b_secondVisitQ hn hsep hm hQC w)) ∧
    (∀ v w : Visit (secondHalf P M a),
      geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).2.1 h₂) v < (n : ℝ) - a.val →
      (n : ℝ) - a.val ≤ geometricVisitKey (CB.cg (contactHalfSizes_bounds hn hsep).2.1 h₂) w →
      geometricVisitKey (CB.cg hn hQ) (s7b_secondVisitQ hn hsep hm hQC w) <
        geometricVisitKey (CB.cg hn hQ) (s7b_secondVisitQ hn hsep hm hQC v)) := by
  have hn₂ := (contactHalfSizes_bounds hn hsep).2.1
  have hk1 : ∀ v : Visit (secondHalf P M a),
      geometricVisitKey (CB.cg hn₂ h₂) v = ((v.2.val.val : ℕ) : ℝ) + visitParameter v :=
    fun v => s7q_key_eq hn₂ h₂ v
  have hk2 : ∀ v : Visit (secondHalf P M a),
      geometricVisitKey (CB.cg hn hQ) (s7b_secondVisitQ hn hsep hm hQC v) =
        (((a.val + v.2.val.val) % n : ℕ) : ℝ) + visitParameter (s7b_secondVisitQ hn hsep hm hQC v) := by
    intro v
    rw [s7q_key_eq hn hQ, s7b_secondVisitQ_edge, s7q_secondHalfEdgeIndex_val]
  have key := s7q_key_decoding (n := n) a.val (secondHalfSize M a) (secondHalfSize_le M a) (ZMod.val_lt a)
    (fun v : Visit (secondHalf P M a) => v.2.val.val) (fun v => ZMod.val_lt _)
    visitParameter (fun v => visitParameter (s7b_secondVisitQ hn hsep hm hQC v))
    (fun v => (s7e_visitParameter_pos hn₂ h₂ v).le) (fun v => s7e_visitParameter_lt_one hn₂ h₂ v)
    (fun v => (s7e_visitParameter_pos hn hQ _).le) (fun v => s7e_visitParameter_lt_one hn hQ _)
    (fun v w hvw => hord v w (ZMod.val_injective _ hvw))
  refine ⟨fun v w h1 h2 => ?_, fun v w h1 h2 => ?_⟩
  · rw [hk1, hk1] at h1 h2
    rw [hk2, hk2]
    exact key.1 v w h1 h2
  · rw [hk1] at h1 h2
    rw [hk2, hk2]
    exact key.2 v w h1 h2

/-- `s7q_CutFirst` from the order agreement, the over bits and the rotation equality. -/
theorem s7q_cutFirst_of (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a) {P Q : LabelledTuple n}
    (hm : P M ∈ edgeInterior P a) (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hQ : Generic Q) (h₁ : Generic (firstHalf P M a)) (S : Finset (Crossing Q))
    (S₁ : Finset (Crossing (firstHalf P M a))) (q : Component hn hQ S)
    (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
    (hord : ∀ v w : Visit (firstHalf P M a), v.2.val = w.2.val →
      (visitParameter v < visitParameter w ↔
        visitParameter (s7b_firstVisitQ hn hsep hm hQC v) < visitParameter (s7b_firstVisitQ hn hsep hm hQC w)))
    (hbit : ∀ v : Visit (firstHalf P M a),
      v.1 ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ →
      CB.positiveOverBit (s7b_firstVisitQ hn hsep hm hQC v) = CB.positiveOverBit v)
    (hr : carrierRotation (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ = carrierRotation hn hQ S q) :
    s7q_CutFirst hn hsep hm hQC hQ h₁ S S₁ q q₁ :=
  ⟨(n : ℝ) - M.val, fun v w _ _ h1 h2 => (s7q_keys_first hn hsep hm hQC hQ h₁ hord).1 v w h1 h2,
    fun v w _ _ h1 h2 => (s7q_keys_first hn hsep hm hQC hQ h₁ hord).2 v w h1 h2, hbit, hr⟩

theorem s7q_cutSecond_of (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a) {P Q : LabelledTuple n}
    (hm : P M ∈ edgeInterior P a) (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hQ : Generic Q) (h₂ : Generic (secondHalf P M a)) (S : Finset (Crossing Q))
    (S₂ : Finset (Crossing (secondHalf P M a))) (q : Component hn hQ S)
    (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂)
    (hord : ∀ v w : Visit (secondHalf P M a), v.2.val = w.2.val →
      (visitParameter v < visitParameter w ↔
        visitParameter (s7b_secondVisitQ hn hsep hm hQC v) <
          visitParameter (s7b_secondVisitQ hn hsep hm hQC w)))
    (hbit : ∀ v : Visit (secondHalf P M a),
      v.1 ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ →
      CB.positiveOverBit (s7b_secondVisitQ hn hsep hm hQC v) = CB.positiveOverBit v)
    (hr : carrierRotation (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ = carrierRotation hn hQ S q) :
    s7q_CutSecond hn hsep hm hQC hQ h₂ S S₂ q q₂ :=
  ⟨(n : ℝ) - a.val, fun v w _ _ h1 h2 => (s7q_keys_second hn hsep hm hQC hQ h₂ hord).1 v w h1 h2,
    fun v w _ _ h1 h2 => (s7q_keys_second hn hsep hm hQC hQ h₂ hord).2 v w h1 h2, hbit, hr⟩

/-- **Coefficient transport to `λ₁`** (eq. s7c:sliding-coefficients, one carrier): `hmem` from
`carrierCrossings_eq_img_first`, `htwin` from `s7b_firstVisitQ_visitTwin`, the rest from `s7q_CutFirst`. -/
theorem s7q_coef_first (hT : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) vm.1)
    (hS : IsDecomposition hn hQ S) (hS₁ : IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
    (q : Component hn hQ S) (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
    (hq : hT.componentEquiv q = Sum.inl q₁)
    (hcut : s7q_CutFirst hn hsep hm hQC hQ h₁ S S₁ q q₁) :
    cornerCoefficient hn hQ S q hS = cornerCoefficient (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ hS₁ := by
  obtain ⟨c, hmono, hcut', hbit, hr⟩ := hcut
  symm
  refine s7d_cornerCoefficient_eq_of_cut (contactHalfSizes_bounds hn hsep).1.1 hn h₁ hQ hS₁ q₁ hS q
    (s7b_firstVisitQ hn hsep hm hQC) c ?_ hmono hcut' (fun v _ => s7b_firstVisitQ_visitTwin hn hsep hm hQC v)
    hbit hr
  intro w
  rw [hT.carrierCrossings_eq_img_first hsplit hS q q₁ hq, s7b_mem_img]
  constructor
  · rintro ⟨c', hc', hcw⟩
    obtain ⟨v, hv, rfl⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC w c' hcw.symm
    exact ⟨v, by rw [hv]; exact hc', rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.1, hv, (s7b_firstVisitQ_fst hn hsep hm hQC v).symm⟩

/-- **Coefficient transport to `λ₂`**. -/
theorem s7q_coef_second (hT : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) vm.1)
    (hS : IsDecomposition hn hQ S) (hS₂ : IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂)
    (q : Component hn hQ S) (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂)
    (hq : hT.componentEquiv q = Sum.inr q₂)
    (hcut : s7q_CutSecond hn hsep hm hQC hQ h₂ S S₂ q q₂) :
    cornerCoefficient hn hQ S q hS = cornerCoefficient (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ hS₂ := by
  obtain ⟨c, hmono, hcut', hbit, hr⟩ := hcut
  symm
  refine s7d_cornerCoefficient_eq_of_cut (contactHalfSizes_bounds hn hsep).2.1 hn h₂ hQ hS₂ q₂ hS q
    (s7b_secondVisitQ hn hsep hm hQC) c ?_ hmono hcut' (fun v _ => s7b_secondVisitQ_visitTwin hn hsep hm hQC v)
    hbit hr
  intro w
  rw [hT.carrierCrossings_eq_img_second hsplit hS q q₂ hq, s7b_mem_img]
  constructor
  · rintro ⟨c', hc', hcw⟩
    obtain ⟨v, hv, rfl⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC w c' hcw.symm
    exact ⟨v, by rw [hv]; exact hc', rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.1, hv, (s7b_secondVisitQ_fst hn hsep hm hQC v).symm⟩

/-- **The row data from RET + SPLIT + the per-carrier inputs**: `e := componentEquiv`; the coefficient clause
by `s7q_coef_first/_second`; the weight clause and the refined weight as given (from `s7q_carrierWeight_eq_of_merge`
/ `_of_perturb` / turn-sign equalities). -/
theorem s7q_rowData_of_transport (hT : s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S S₁ S₂ vm)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) vm.1)
    (hS : IsDecomposition hn hQ S) (hS₁ : IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
    (hS₂ : IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂)
    (a₀ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ ⊕
      Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂) (m₀ : Multiset SignType) (τ : SignType)
    (hc₁ : ∀ q q₁, hT.componentEquiv q = Sum.inl q₁ → s7q_CutFirst hn hsep hm hQC hQ h₁ S S₁ q q₁)
    (hc₂ : ∀ q q₂, hT.componentEquiv q = Sum.inr q₂ → s7q_CutSecond hn hsep hm hQC hQ h₂ S S₂ q q₂)
    (hw : ∀ q, hT.componentEquiv q ≠ a₀ → carrierWeight hn hQ S q =
      Sum.elim (carrierWeight (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
        (carrierWeight (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂) (hT.componentEquiv q))
    (hw₀ : carrierWeight hn hQ S (hT.componentEquiv.symm a₀) = s7c_sel (m₀ + {τ})) :
    s7q_RowData hn hQ (contactHalfSizes_bounds hn hsep).1.1 (contactHalfSizes_bounds hn hsep).2.1 h₁ h₂
      hS hS₁ hS₂ a₀ m₀ τ := by
  refine ⟨hT.componentEquiv, fun q => ?_, hw, hw₀⟩
  rcases hx : hT.componentEquiv q with q₁ | q₂
  · rw [Sum.elim_inl]
    exact s7q_coef_first hT hsplit hS hS₁ q q₁ hx (hc₁ q q₁ hx)
  · rw [Sum.elim_inr]
    exact s7q_coef_second hT hsplit hS hS₂ q q₂ hx (hc₂ q q₂ hx)

end S7QTransport

section S7QBoxes

/-! #### The geometric inputs as black boxes, and the assembly to the leaf statement.
Notation of `s7e_contactSector_of_pivotSplit` (W2_S7E_REPORT §3): side `b`, `hQ := s7a_sideGeneric g b`,
`hsep := h.1.1`, `hm := h.1.2.2.2.1`, `hQC := s7e_hQC hn g h t b`, `x := s7e_xm hn h t` / `s7e_xp hn h t`. -/

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.SlidingAt M a)

/-- The interlacement transfer of side `b` at `x` (U_S7B_REPORT §2.2; SPLIT). -/
def s7q_Split (t : g.SideParameter) (b : Bool) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (x : Crossing (g.curve (g.sideTime b t))) : Prop :=
  s7b_PivotSplit (Interlaces hn (s7a_sideGeneric g b))
    (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
    (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
    (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b))
    (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b)) x

/-- **BLACK BOX (SPLIT, unit SPLIT of wave 3)**: the two interlacement transfers below a radius. -/
theorem s7q_box_split (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      s7q_Split hn g h t false h₁ h₂ (s7e_xm hn h t) ∧ s7q_Split hn g h t true h₁ h₂ (s7e_xp hn h t) := by
  sorry

/-- The two half contact carriers of a row `(S₁, S₂)`: `λ₁`'s carrier through its vertex `0 = μ_M` and `λ₂`'s
through its vertex `0 = μ_M` (`componentEquiv_owner_vertexM` / `_pivot`), as the two points of
`Component S₁ ⊕ Component S₂`, in the order fixed by `first` (which half carries the extra corner on `P₋`:
`λ₁` when the leg of `x₋` is `M−1`, `λ₂` when it is `M`). -/
def s7q_contactPoint (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (S₁ : Finset (Crossing (firstHalf g.center M a))) (S₂ : Finset (Crossing (secondHalf g.center M a)))
    (first : Bool) :
    Component (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ ⊕ Component (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ :=
  if first then Sum.inl (owner (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ (Sum.inl 0))
  else Sum.inr (owner (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ (Sum.inl 0))

/-- The turn multiset of the half contact carrier selected by `first`. -/
def s7q_contactTurns (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (S₁ : Finset (Crossing (firstHalf g.center M a))) (S₂ : Finset (Crossing (secondHalf g.center M a)))
    (first : Bool) : Multiset SignType :=
  if first then
    s7c_turns (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁
      (owner (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ (Sum.inl 0)))
  else
    s7c_turns (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂
      (owner (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ (Sum.inl 0)))

theorem s7q_contactPoint_ne (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (S₁ : Finset (Crossing (firstHalf g.center M a))) (S₂ : Finset (Crossing (secondHalf g.center M a)))
    (first : Bool) :
    s7q_contactPoint hn g h h₁ h₂ S₁ S₂ first ≠ s7q_contactPoint hn g h h₁ h₂ S₁ S₂ (!first) := by
  cases first <;> simp [s7q_contactPoint]

theorem s7q_contactPoint_weight (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a))
    (S₁ : Finset (Crossing (firstHalf g.center M a))) (S₂ : Finset (Crossing (secondHalf g.center M a)))
    (first : Bool) :
    Sum.elim (carrierWeight (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁)
        (carrierWeight (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂)
        (s7q_contactPoint hn g h h₁ h₂ S₁ S₂ first) =
      s7c_sel (s7q_contactTurns hn g h h₁ h₂ S₁ S₂ first) := by
  cases first <;> simp [s7q_contactPoint, s7q_contactTurns, s7c_carrierWeight_eq_sel]

/-- The half supports of a row are the preimages of its side support (for the RET unit: the fields
`first_pre`/`second_pre` of `s7b_SlidingTransport` on the row `((E).symm q).1`). -/
theorem s7q_pre_of_symm {M a : ZMod n} (hsep : ContactSeparated M a) {P Q : LabelledTuple n}
    (hm : P M ∈ edgeInterior P a) (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hQ : Generic Q) (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a)) (x : Crossing Q)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) x)
    (q : {S₁ : Finset (Crossing (firstHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂}) :
    q.1.1 = s7b_pre (s7b_firstCrossingQ hn hsep hm hQC)
        ((s7b_slidingDecompositionEquiv hn hsep hm hQC hQ h₁ h₂ x hsplit).symm q).1 ∧
      q.2.1 = s7b_pre (s7b_secondCrossingQ hn hsep hm hQC)
        ((s7b_slidingDecompositionEquiv hn hsep hm hQC hQ h₁ h₂ x hsplit).symm q).1 := by
  have h := (s7b_slidingDecompositionEquiv hn hsep hm hQC hQ h₁ h₂ x hsplit).apply_symm_apply q
  constructor
  · conv_lhs => rw [← h]
    rfl
  · conv_lhs => rw [← h]
    rfl

/-- **BLACK BOX (RET, unit RET of wave 3)**: below a radius, every row of either side carries a
`s7b_SlidingTransport` instance (the first-return law `ret`) with pivot visit `vm` the contact visit of the
side's contact crossing (`vm.1 = x₋`, resp. `x₊`; the leg visit) and half supports the row's. -/
theorem s7q_box_ret (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      ∀ (hsplitm : s7q_Split hn g h t false h₁ h₂ (s7e_xm hn h t))
        (hsplitp : s7q_Split hn g h t true h₁ h₂ (s7e_xp hn h t))
        (q : {S₁ : Finset (Crossing (firstHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
            {S₂ : Finset (Crossing (secondHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}),
        (∃ vm : Visit (g.curve (g.sideTime false t)), vm.1 = s7e_xm hn h t ∧
          s7b_SlidingTransport hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false) (s7a_sideGeneric g false) h₁ h₂
            ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false)
              (s7a_sideGeneric g false) h₁ h₂ (s7e_xm hn h t) hsplitm).symm q).1 q.1.1 q.2.1 vm) ∧
        (∃ vm : Visit (g.curve (g.sideTime true t)), vm.1 = s7e_xp hn h t ∧
          s7b_SlidingTransport hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true) (s7a_sideGeneric g true) h₁ h₂
            ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true)
              (s7a_sideGeneric g true) h₁ h₂ (s7e_xp hn h t) hsplitp).symm q).1 q.1.1 q.2.1 vm) := by
  sorry

/-- The same-edge order agreement of side `b` at `t` for both halves (the `hord` input of `s7q_keys_first/_second`:
the visits of a half on one edge map to `Q`'s visits on the image edge in the same parameter order —
`ContactOrderAgrees` of lem:wall-sides (V) composed with U110-B's parameter laws at the centre). -/
def s7q_OrderAgrees (t : g.SideParameter) (b : Bool) : Prop :=
  (∀ v w : Visit (firstHalf g.center M a), v.2.val = w.2.val →
    (visitParameter v < visitParameter w ↔
      visitParameter (s7b_firstVisitQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b) v) <
        visitParameter (s7b_firstVisitQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b) w))) ∧
  (∀ v w : Visit (secondHalf g.center M a), v.2.val = w.2.val →
    (visitParameter v < visitParameter w ↔
      visitParameter (s7b_secondVisitQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b) v) <
        visitParameter (s7b_secondVisitQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b) w)))

/-- **BLACK BOX (ORDER; SPLIT-adjacent)**: the same-edge order agreement on both sides below a radius. -/
theorem s7q_box_order :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → ∀ b : Bool, s7q_OrderAgrees hn g h t b := by
  sorry

/-- The per-carrier inputs of one side's row data, given its transport instance: for every carrier, the
over bits of its visits (`hbit`) and the rotation equality (`hr`, §S7QMerge) with the corresponding half
carrier; the transported weights off the refined carrier `a₀`; the refined weight `sel(m₀ + {τ})`. -/
def s7q_CarrierData {Q : LabelledTuple n} (hQ : Generic Q)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing g.center s))
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    {S : Finset (Crossing Q)} {S₁ : Finset (Crossing (firstHalf g.center M a))}
    {S₂ : Finset (Crossing (secondHalf g.center M a))} {vm : Visit Q}
    (hT : s7b_SlidingTransport hn h.1.1 h.1.2.2.2.1 hQC hQ h₁ h₂ S S₁ S₂ vm)
    (a₀ : Component (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ ⊕
      Component (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂) (m₀ : Multiset SignType) (τ : SignType) :
    Prop :=
  (∀ q q₁, hT.componentEquiv q = Sum.inl q₁ →
    (∀ v : Visit (firstHalf g.center M a),
      v.1 ∈ carrierCrossings (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ q₁ →
      CB.positiveOverBit (s7b_firstVisitQ hn h.1.1 h.1.2.2.2.1 hQC v) = CB.positiveOverBit v) ∧
    carrierRotation (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ q₁ = carrierRotation hn hQ S q) ∧
  (∀ q q₂, hT.componentEquiv q = Sum.inr q₂ →
    (∀ v : Visit (secondHalf g.center M a),
      v.1 ∈ carrierCrossings (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ q₂ →
      CB.positiveOverBit (s7b_secondVisitQ hn h.1.1 h.1.2.2.2.1 hQC v) = CB.positiveOverBit v) ∧
    carrierRotation (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ q₂ = carrierRotation hn hQ S q) ∧
  (∀ q, hT.componentEquiv q ≠ a₀ → carrierWeight hn hQ S q =
    Sum.elim (carrierWeight (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁)
      (carrierWeight (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂) (hT.componentEquiv q)) ∧
  carrierWeight hn hQ S (hT.componentEquiv.symm a₀) = s7c_sel (m₀ + {τ})

/-- **BLACK BOX (ROT (a)-(c) geometry, given RET + SPLIT)**: below a radius, for every row and every
transport instance of either side, the per-carrier data — `P₋` refined at the half contact carrier `first`
(turns containing `s = χ(P₋)`), `P₊` at the other (containing `−s`), common turn `τ ≠ 0` at `μ_M`.  Contents
per carrier: `s7q_CutFirst/_Second` = the key decoding of the half labelling (`hmono`/`hcut`, cut `c` at the
wrap of `Q`'s edge labels inside the half's), the over bits (`s7d_positiveOverBit_eq_of_smul` +
`HalvesData.cut_segments` off the contact edges, sign constancy on them), and `hr` by
`s7q_carrierRotation_eq_of_merge` (the extra-corner carrier: `s7q_principal_three_a/_b` on the direction data
`r, u_in, u_out` of eq. s7c:short-direction-lists), `s7q_carrierRotation_eq_of_perturb` (the other contact
carrier: `s7q_two_turn_perturb`) and `s7i_principalTurn_eq_of_edges_pos_smul` (all others); the weights by
`s7q_carrierWeight_eq_of_merge` / `_of_perturb` and `s7c_carrierWeight_eq_sel` with the turn-sign equalities.
The ORDERED corner correspondences (`s7q_CornerMerge`/`s7q_CornerPerturb`) are U_S7B_REPORT §2.3. -/
theorem s7q_box_carriers (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ (first : Bool) (τ : SignType) (δ : ℝ), τ ≠ 0 ∧ 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      ∀ (hsplitm : s7q_Split hn g h t false h₁ h₂ (s7e_xm hn h t))
        (hsplitp : s7q_Split hn g h t true h₁ h₂ (s7e_xp hn h t))
        (q : {S₁ : Finset (Crossing (firstHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
            {S₂ : Finset (Crossing (secondHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}),
        (g.contactSign M a ∈ s7q_contactTurns hn g h h₁ h₂ q.1.1 q.2.1 first) ∧
        (-g.contactSign M a ∈ s7q_contactTurns hn g h h₁ h₂ q.1.1 q.2.1 (!first)) ∧
        (∀ (vm : Visit (g.curve (g.sideTime false t)))
          (hT : s7b_SlidingTransport hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false) (s7a_sideGeneric g false)
            h₁ h₂ ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false)
              (s7a_sideGeneric g false) h₁ h₂ (s7e_xm hn h t) hsplitm).symm q).1 q.1.1 q.2.1 vm),
          vm.1 = s7e_xm hn h t →
          s7q_CarrierData hn g h (s7a_sideGeneric g false) (s7e_hQC hn g h t false) h₁ h₂ hT
            (s7q_contactPoint hn g h h₁ h₂ q.1.1 q.2.1 first)
            (s7q_contactTurns hn g h h₁ h₂ q.1.1 q.2.1 first) τ) ∧
        (∀ (vm : Visit (g.curve (g.sideTime true t)))
          (hT : s7b_SlidingTransport hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true) (s7a_sideGeneric g true)
            h₁ h₂ ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true)
              (s7a_sideGeneric g true) h₁ h₂ (s7e_xp hn h t) hsplitp).symm q).1 q.1.1 q.2.1 vm),
          vm.1 = s7e_xp hn h t →
          s7q_CarrierData hn g h (s7a_sideGeneric g true) (s7e_hQC hn g h t true) h₁ h₂ hT
            (s7q_contactPoint hn g h h₁ h₂ q.1.1 q.2.1 (!first))
            (s7q_contactTurns hn g h h₁ h₂ q.1.1 q.2.1 (!first)) τ) := by
  sorry

/-- One side's row data from its transport instance, the order agreement and the carrier data
(`s7q_rowData_of_transport` with `s7q_cutFirst_of`/`s7q_cutSecond_of`). -/
theorem s7q_rowData_of_carrierData (t : g.SideParameter) (b : Bool)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    {S : Finset (Crossing (g.curve (g.sideTime b t)))} {S₁ : Finset (Crossing (firstHalf g.center M a))}
    {S₂ : Finset (Crossing (secondHalf g.center M a))} {vm : Visit (g.curve (g.sideTime b t))}
    (hT : s7b_SlidingTransport hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b) (s7a_sideGeneric g b) h₁ h₂ S S₁ S₂ vm)
    (hsplit : s7b_PivotSplit (Interlaces hn (s7a_sideGeneric g b))
      (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
      (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b))
      (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b)) vm.1)
    (hS : IsDecomposition hn (s7a_sideGeneric g b) S)
    (hS₁ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁)
    (hS₂ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂)
    {a₀ : Component (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ ⊕
      Component (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂} {m₀ : Multiset SignType} {τ : SignType}
    (hord : s7q_OrderAgrees hn g h t b)
    (hd : s7q_CarrierData hn g h (s7a_sideGeneric g b) (s7e_hQC hn g h t b) h₁ h₂ hT a₀ m₀ τ) :
    s7q_RowData hn (s7a_sideGeneric g b) (contactHalfSizes_bounds hn h.1.1).1.1
      (contactHalfSizes_bounds hn h.1.1).2.1 h₁ h₂ hS hS₁ hS₂ a₀ m₀ τ :=
  s7q_rowData_of_transport hT hsplit hS hS₁ hS₂ a₀ m₀ τ
    (fun q q₁ hq => s7q_cutFirst_of hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b) (s7a_sideGeneric g b) h₁ S S₁ q q₁
      hord.1 (hd.1 q q₁ hq).1 (hd.1 q q₁ hq).2)
    (fun q q₂ hq => s7q_cutSecond_of hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b) (s7a_sideGeneric g b) h₂ S S₂ q q₂
      hord.2 (hd.2.1 q q₂ hq).1 (hd.2.1 q q₂ hq).2)
    hd.2.2.1 hd.2.2.2

/-- **The row data of both sides from the three boxes `s7q_box_ret`, `s7q_box_order`, `s7q_box_carriers`** (PROVED): below a radius,
for every row `q = (S₁, S₂)` of the contact sector, the row data of both sides — `P₋` refined at the half contact carrier `first` (turn multiset
containing the contact sign `s = χ(P₋)`), `P₊` refined at the other one (containing `−s`), with one common
turn `τ ≠ 0` (the turn at `μ_M`, `τ = sgn det(u_in, u_out)`).  Contents: `e := componentEquiv` (RET);
coefficients by `s7d_cornerCoefficient_eq_of_cut` with `hmem` from `carrierCrossings_eq_img_*`, `hmono/hcut` from
the key decoding of the half labelling, `htwin` from `s7b_*VisitQ_visitTwin`, `hbit` from
`s7d_positiveOverBit_eq_of_smul` + `HalvesData.cut_segments`, and `hr` from `s7q_carrierRotation_eq_of_merge`
(the extra-corner carrier, `s7q_principal_three_a/_b`), `s7q_carrierRotation_eq_of_perturb` (the other contact
carrier, `s7q_two_turn_perturb`) and `s7i_principalTurn_eq_of_edges_pos_smul` (all others); weights by
`s7q_carrierWeight_eq_of_merge` / `_of_perturb` / `s7c_carrierWeight_eq_sel` with the turn-sign equalities. -/
theorem s7q_box_rows (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ (first : Bool) (τ : SignType) (δ : ℝ), τ ≠ 0 ∧ 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      ∀ (hsplitm : s7q_Split hn g h t false h₁ h₂ (s7e_xm hn h t))
        (hsplitp : s7q_Split hn g h t true h₁ h₂ (s7e_xp hn h t))
        (q : {S₁ : Finset (Crossing (firstHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
            {S₂ : Finset (Crossing (secondHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}),
        (g.contactSign M a ∈ s7q_contactTurns hn g h h₁ h₂ q.1.1 q.2.1 first) ∧
        (-g.contactSign M a ∈ s7q_contactTurns hn g h h₁ h₂ q.1.1 q.2.1 (!first)) ∧
        s7q_RowData hn (s7a_sideGeneric g false) (contactHalfSizes_bounds hn h.1.1).1.1
          (contactHalfSizes_bounds hn h.1.1).2.1 h₁ h₂
          ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false)
            (s7a_sideGeneric g false) h₁ h₂ (s7e_xm hn h t) hsplitm).symm q).2.1 q.1.2 q.2.2
          (s7q_contactPoint hn g h h₁ h₂ q.1.1 q.2.1 first)
          (s7q_contactTurns hn g h h₁ h₂ q.1.1 q.2.1 first) τ ∧
        s7q_RowData hn (s7a_sideGeneric g true) (contactHalfSizes_bounds hn h.1.1).1.1
          (contactHalfSizes_bounds hn h.1.1).2.1 h₁ h₂
          ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true)
            (s7a_sideGeneric g true) h₁ h₂ (s7e_xp hn h t) hsplitp).symm q).2.1 q.1.2 q.2.2
          (s7q_contactPoint hn g h h₁ h₂ q.1.1 q.2.1 (!first))
          (s7q_contactTurns hn g h h₁ h₂ q.1.1 q.2.1 (!first)) τ := by
  obtain ⟨δ₁, hδ₁, hret⟩ := s7q_box_ret hn g h h₁ h₂
  obtain ⟨first, τ, δ₂, hτ, hδ₂, hcar⟩ := s7q_box_carriers hn g h h₁ h₂
  obtain ⟨δ₃, hδ₃, hord⟩ := s7q_box_order hn g h
  refine ⟨first, τ, min (min δ₁ δ₂) δ₃, hτ, lt_min (lt_min hδ₁ hδ₂) hδ₃,
    fun t ht hsplitm hsplitp q => ?_⟩
  have ht₁ : t.val < δ₁ := lt_of_lt_of_le ht (le_trans (min_le_left _ _) (min_le_left _ _))
  have ht₂ : t.val < δ₂ := lt_of_lt_of_le ht (le_trans (min_le_left _ _) (min_le_right _ _))
  have ht₃ : t.val < δ₃ := lt_of_lt_of_le ht (min_le_right _ _)
  obtain ⟨⟨vm, hvm, hTm⟩, ⟨vp, hvp, hTp⟩⟩ := hret t ht₁ hsplitm hsplitp q
  obtain ⟨hs₁, hs₂, hdm, hdp⟩ := hcar t ht₂ hsplitm hsplitp q
  refine ⟨hs₁, hs₂, ?_, ?_⟩
  · exact s7q_rowData_of_carrierData hn g h t false h₁ h₂ hTm (by rw [hvm]; exact hsplitm) _ q.1.2 q.2.2
      (hord t ht₃ false) (hdm vm hTm hvm)
  · exact s7q_rowData_of_carrierData hn g h t true h₁ h₂ hTp (by rw [hvp]; exact hsplitp) _ q.1.2 q.2.2
      (hord t ht₃ true) (hdp vp hTp hvp)

/-- The termwise identity `hterm` of `s7e_contactSector_of_pivotSplit` from the row data of both sides. -/
theorem s7q_hterm_of_rows (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (t : g.SideParameter) (first : Bool) {τ : SignType} (hτ : τ ≠ 0)
    (hsplitm : s7q_Split hn g h t false h₁ h₂ (s7e_xm hn h t))
    (hsplitp : s7q_Split hn g h t true h₁ h₂ (s7e_xp hn h t))
    (q : {S₁ : Finset (Crossing (firstHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂})
    (hs₁ : g.contactSign M a ∈ s7q_contactTurns hn g h h₁ h₂ q.1.1 q.2.1 first)
    (hs₂ : -g.contactSign M a ∈ s7q_contactTurns hn g h h₁ h₂ q.1.1 q.2.1 (!first))
    (hrm : s7q_RowData hn (s7a_sideGeneric g false) (contactHalfSizes_bounds hn h.1.1).1.1
      (contactHalfSizes_bounds hn h.1.1).2.1 h₁ h₂
      ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false)
        (s7a_sideGeneric g false) h₁ h₂ (s7e_xm hn h t) hsplitm).symm q).2.1 q.1.2 q.2.2
      (s7q_contactPoint hn g h h₁ h₂ q.1.1 q.2.1 first)
      (s7q_contactTurns hn g h h₁ h₂ q.1.1 q.2.1 first) τ)
    (hrp : s7q_RowData hn (s7a_sideGeneric g true) (contactHalfSizes_bounds hn h.1.1).1.1
      (contactHalfSizes_bounds hn h.1.1).2.1 h₁ h₂
      ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true)
        (s7a_sideGeneric g true) h₁ h₂ (s7e_xp hn h t) hsplitp).symm q).2.1 q.1.2 q.2.2
      (s7q_contactPoint hn g h h₁ h₂ q.1.1 q.2.1 (!first))
      (s7q_contactTurns hn g h h₁ h₂ q.1.1 q.2.1 (!first)) τ) :
    s7e_term hn (s7a_sideGeneric g true)
        ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true)
          (s7a_sideGeneric g true) h₁ h₂ (s7e_xp hn h t) hsplitp).symm q).1 -
      s7e_term hn (s7a_sideGeneric g false)
        ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false)
          (s7a_sideGeneric g false) h₁ h₂ (s7e_xm hn h t) hsplitm).symm q).1 =
      (g.contactSign M a : ℤ) *
        (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ q.1.1 *
          s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ q.2.1) :=
  s7q_term_eq_of_rowData hn (s7a_sideGeneric g false) (s7a_sideGeneric g true)
    (contactHalfSizes_bounds hn h.1.1).1.1 (contactHalfSizes_bounds hn h.1.1).2.1 h₁ h₂ _ _ q.1.2 q.2.2
    (s7q_contactPoint_ne hn g h h₁ h₂ q.1.1 q.2.1 first) (g.vertex_contact_signs h.1 t t).1 hτ hs₁ hs₂
    (s7q_contactPoint_weight hn g h h₁ h₂ q.1.1 q.2.1 first)
    (s7q_contactPoint_weight hn g h h₁ h₂ q.1.1 q.2.1 (!first)) hrm hrp

/-- The contact sector below a radius, from the two black boxes (SPLIT + the row data). -/
theorem s7q_exists_contactSector (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → s7e_ContactSector hn h h₁ h₂ t := by
  obtain ⟨δ₁, hδ₁, hsplit⟩ := s7q_box_split hn g h h₁ h₂
  obtain ⟨first, τ, δ₂, hτ, hδ₂, hrows⟩ := s7q_box_rows hn g h h₁ h₂
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht => ?_⟩
  obtain ⟨hsplitm, hsplitp⟩ := hsplit t (lt_of_lt_of_le ht (min_le_left _ _))
  have hr := hrows t (lt_of_lt_of_le ht (min_le_right _ _)) hsplitm hsplitp
  exact s7e_contactSector_of_pivotSplit hn g h t h₁ h₂ hsplitm hsplitp fun q =>
    s7q_hterm_of_rows hn g h h₁ h₂ t first hτ hsplitm hsplitp q (hr q).1 (hr q).2.1 (hr q).2.2.1
      (hr q).2.2.2

/-- **The leaf statement from the black boxes** (the one-liner of W2_S7E_REPORT §2 with the boxes explicit):
`s7_sliding_law_at`'s conclusion follows from `s7q_box_split` and `s7q_box_rows`. -/
theorem s7q_sliding_law_at_of_boxes (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) :=
  s7e_sliding_law_at_of_contact hn g h h₁ h₂ (s7q_exists_contactSector hn g h h₁ h₂)

end S7QBoxes

/-- The sliding branch (sm-4:300-406): relocation bijection `φ(x₋) = x₊`, the support bijection
eq. s7c:sliding-bijection with the halves, equal coefficient products eq. s7c:sliding-coefficients, and
the exact selector difference eq. s7c:sliding-selector-difference.  NO floor, NO singleton. -/
theorem s7_sliding_law_at (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (h : g.SlidingAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  sorry


/-- The bigon branch (sm-4:407-874): two-newborn sector `B = (1−ε)J` (contact triangle: a crossing-free
uniform carrier, `corner_values_i`), universal skein extraction eq. s7c:universal-extraction (lp:core
skein, R-II deletion, oriented smoothing), lem:homflyrows two-component row, the rotation ledger, and the
two floor-dependent branches (interlacing: `Ω_H − Ω_L = −ω₁ω₂`; noninterlacing: every returned row zero,
the one-newborn rows by cb:singleton).  `a_floor` enters at the two half contact carriers (uniform for
`ε = 1`, one-dissent for `ε = 0`), read as carriers of the decompositions `T_i` of the generic halves
`λ_i` (sm-4:800-835); cb:singleton enters at the one-newborn rows (sm-4:777-783) — both printed
dependencies are explicit parameters. -/
theorem s7_bigon_law_at (hF : FloorTheoremData) (hsing : CbSingletonData) (hn : 3 ≤ n)
    (g : WallGerm n) (M a : ZMod n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  sorry


end VertexEdge

/-- **Row 110, conditional on thm:floor AND cb:singleton** (the printed dependency list of
tools/claims.py; library material).  PROVED from the two branch leaves: the wall is of bigon or sliding
type (`vertexEdge_bigon_or_sliding`); both side parameters are moved below the branch radius by chamber
constancy along each side (`cornerStateSum_side_eq`). -/
theorem thm_C_S7_of (hF : FloorTheoremData) (hsing : CbSingletonData) : CS7Data := by
  refine ⟨?_⟩
  intro n _ hn g M a h h₁ h₂ tp tm
  obtain ⟨δ, hδ, hlaw⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1).2.1 h₂) := by
    rcases g.vertexEdge_bigon_or_sliding h with hb | hs
    · exact s7_bigon_law_at hF hsing hn g M a hb h₁ h₂
    · exact s7_sliding_law_at hn g M a hs h₁ h₂
  have hr := g.radius_pos
  let t : g.SideParameter := ⟨min δ g.radius / 2, by
    constructor
    · have := lt_min hδ hr; linarith
    · have := min_le_right δ g.radius; linarith⟩
  have ht : t.val < δ := by
    show min δ g.radius / 2 < δ
    have := min_le_left δ g.radius; linarith
  rw [cornerStateSum_side_eq hn g true tp t, cornerStateSum_side_eq hn g false tm t]
  exact hlaw t ht

/-- **Row 110, conditional on the floor alone** (the row theorem `SM.thm_C_S7 := thm_C_S7_of_floor
SM.thm_floor` once row 100 lands). -/
theorem thm_C_S7_of_floor (hF : FloorTheoremData) : CS7Data :=
  thm_C_S7_of hF (cb_singleton_of_floor hF)


/-- Row 110 thm:C-S7 (FIXED target name, axiom-policy.json): the assembly on thm:floor (row 100). -/
theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor

end

end SM
