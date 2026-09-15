import SM.LinkDiagramRecord

/-! Chapter-3 representation layer, module LinkRecordExtension: the piecewise-linear extension clause of def:gauss-record
(sm-3:365-369) — every named record isomorphism of diagram records extends to orientation-preserving bijections of the parametrizing
circles which carry each occurrence to its image and are the positive affine map between successive marks in oriented key
coordinates (a linear rescaling on a mark-free circle): `RecordIso.ExtendsPiecewiseAffine`, `rexB_recordIso_extend_pl`, and the weaker
`recordIso_extend_statement` (`rexB_recordIso_extend`). Written 2026-09-13 by Claude Code prover subagents of the pod executor
(workflows prove-record-extension / prove-record-extension-pl), checked with `lake env lean` (sorry-free, standard axioms) and ported
verbatim from work/drafts/RecordExtensionPL.lean (only this header added and #print lines removed); the independent attempt
work/drafts/RecordExtensionA.lean is kept as a cross-check. -/

/-! # RecordExtensionPL: the piecewise-linear extension `Φ̄` of def:gauss-record, with the affine clause

Sections 1-6 are RecordExtensionB.lean verbatim (nothing renamed).  Sections 7-9 add the predicate
`RecordIso.ExtendsPiecewiseAffine` (the printed affine clause of sm-3:365-369 in oriented key
coordinates: `Diagram.cyclicOffset` distances scaled by the ratio of arc lengths `rexPL_arcLen`, and
the linear rescaling `k'/k` on mark-free circles), the theorem `rexB_recordIso_extend_pl` proving it
for the witness below, and `ExtendsPiecewiseAffine.toExtendsToCircleMaps`.  New helpers carry the
prefix `rexPL_`.

Proof of `SM.Link.recordIso_extend_statement` (work/lean/SM/LinkDiagramRecord.lean, section H):
every named record isomorphism `ι` between the records of two diagrams `D`, `D'` extends to
orientation-preserving circle maps of the parameter circles carrying occurrences to occurrences
(sm-3:365-369, "After a finite subdivision we choose an orientation-preserving piecewise-linear
circle map Φ̄ : C → C' extending Φ: on each interval between successive marked points use the
positive affine map in oriented interval coordinates. If M is empty, choose any positive circle
parametrization.").

The witness is the printed construction, in traversal-key coordinates `[0, k)` of the component:
1. rotate the circle so that the first occurrence `v₀ = ent 0` of the component sits at `0`
   (`rexB_rot`); the occurrences `ent 0, ent 1, …, ent (m-1)` then have increasing coordinates
   `0 = a 0 < a 1 < … < a (m-1) < a m := k`;
2. do the same on `D'` with base `ι.Φ v₀`; by cyclic-order preservation
   (`RecordIso.visitBetween_iff`) the images `ι.Φ (ent j)` have increasing rotated coordinates
   `0 = b 0 < b 1 < … < b (m-1) < b m := k'`;
3. interpolate piecewise affinely (`rexB_pl`): on `[a j, a (j+1)]` the positive affine map onto
   `[b j, b (j+1)]` (written as a sum of clamped affine pieces, `rexB_pl_eq_affine_on_piece`);
4. rotate back (`rexB_unrot`).  If the component has no occurrence use `m = 1`, `a = (0, k)`,
   `b = (0, k')`: the linear rescaling `x ↦ (k'/k) x`, a positive parametrization.
The resulting real map is a strictly increasing (in rotated coordinates) continuous bijection
`[0,k) → [0,k')`, hence preserves `cycBetween`; it is lifted to `TraversalPoint` through
`traversalKey` and its inverse `rexB_unkey`.  Helper names carry the prefix `rexB_`. -/

namespace SM.Link

open SM Equiv

noncomputable section

/-! ## 1. Rotations of the cut circle `[0, k)` -/

/-- Rotation of the oriented circle `[0, k)` carrying the point `c` to `0`: `x ↦ x - c (mod k)`. -/
def rexB_rot (k c x : ℝ) : ℝ := if x < c then x - c + k else x - c

/-- The inverse rotation, carrying `0` to `c`: `y ↦ y + c (mod k)`. -/
def rexB_unrot (k c y : ℝ) : ℝ := if y + c < k then y + c else y + c - k

theorem rexB_rot_self (k c : ℝ) : rexB_rot k c c = 0 := by
  simp [rexB_rot]

theorem rexB_rot_mem (k c x : ℝ) (hc : 0 ≤ c ∧ c < k) (hx : 0 ≤ x ∧ x < k) :
    0 ≤ rexB_rot k c x ∧ rexB_rot k c x < k := by
  unfold rexB_rot
  split_ifs with h <;> constructor <;> linarith [hc.1, hc.2, hx.1, hx.2]

theorem rexB_unrot_mem (k c y : ℝ) (hc : 0 ≤ c ∧ c < k) (hy : 0 ≤ y ∧ y < k) :
    0 ≤ rexB_unrot k c y ∧ rexB_unrot k c y < k := by
  unfold rexB_unrot
  split_ifs with h <;> constructor <;> linarith [hc.1, hc.2, hy.1, hy.2]

theorem rexB_unrot_rot (k c x : ℝ) (hx : 0 ≤ x ∧ x < k) :
    rexB_unrot k c (rexB_rot k c x) = x := by
  unfold rexB_unrot rexB_rot
  split_ifs <;> linarith [hx.1, hx.2]

theorem rexB_rot_unrot (k c y : ℝ) (hy : 0 ≤ y ∧ y < k) :
    rexB_rot k c (rexB_unrot k c y) = y := by
  unfold rexB_rot rexB_unrot
  split_ifs <;> linarith [hy.1, hy.2]

/-- Rotation preserves the oriented cyclic order of the circle. -/
theorem rexB_cycBetween_rot (k c x y z : ℝ) (hc : 0 ≤ c ∧ c < k) (hx : 0 ≤ x ∧ x < k)
    (hy : 0 ≤ y ∧ y < k) (hz : 0 ≤ z ∧ z < k) :
    cycBetween (rexB_rot k c x) (rexB_rot k c y) (rexB_rot k c z) ↔ cycBetween x y z := by
  have hc1 := hc.1; have hc2 := hc.2; have hx1 := hx.1; have hx2 := hx.2
  have hy1 := hy.1; have hy2 := hy.2; have hz1 := hz.1; have hz2 := hz.2
  unfold cycBetween rexB_rot
  split_ifs <;> constructor <;> rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

theorem rexB_cycBetween_unrot (k c x y z : ℝ) (hc : 0 ≤ c ∧ c < k) (hx : 0 ≤ x ∧ x < k)
    (hy : 0 ≤ y ∧ y < k) (hz : 0 ≤ z ∧ z < k) :
    cycBetween (rexB_unrot k c x) (rexB_unrot k c y) (rexB_unrot k c z) ↔ cycBetween x y z := by
  rw [← rexB_cycBetween_rot k c _ _ _ hc (rexB_unrot_mem k c x hc hx) (rexB_unrot_mem k c y hc hy)
    (rexB_unrot_mem k c z hc hz), rexB_rot_unrot k c x hx, rexB_rot_unrot k c y hy,
    rexB_rot_unrot k c z hz]

/-- A strictly increasing map preserves the cyclic order. -/
theorem rexB_cycBetween_of_strictMonoOn {F : ℝ → ℝ} {s : Set ℝ} (hF : StrictMonoOn F s)
    {x y z : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (h : cycBetween x y z) :
    cycBetween (F x) (F y) (F z) := by
  unfold cycBetween at h ⊢
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨hF hx hy h₁, hF hy hz h₂⟩
  · exact Or.inr (Or.inl ⟨hF hy hz h₁, hF hz hx h₂⟩)
  · exact Or.inr (Or.inr ⟨hF hz hx h₁, hF hx hy h₂⟩)

/-- Cyclic betweenness from the cut point `0` is the linear order. -/
theorem rexB_cycBetween_zero (y z : ℝ) (hz : 0 ≤ z) :
    cycBetween 0 y z ↔ 0 < y ∧ y < z := by
  unfold cycBetween
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨h₁, h₂⟩
    · exact absurd h₂ (not_lt.mpr hz)
    · exact absurd h₁ (not_lt.mpr hz)
  · intro h
    exact Or.inl h

theorem rexB_rot_lt_of_cycBetween (k c x y : ℝ) (hc : 0 ≤ c ∧ c < k) (hx : 0 ≤ x ∧ x < k)
    (hy : 0 ≤ y ∧ y < k) (h : cycBetween c x y) : rexB_rot k c x < rexB_rot k c y := by
  have h' := (rexB_cycBetween_rot k c c x y hc hc hx hy).mpr h
  rw [rexB_rot_self] at h'
  exact ((rexB_cycBetween_zero _ _ (rexB_rot_mem k c y hc hy).1).mp h').2

theorem rexB_rot_pos_of_ne (k c x : ℝ) (hc : 0 ≤ c ∧ c < k) (hx : 0 ≤ x ∧ x < k) (hne : x ≠ c) :
    0 < rexB_rot k c x := by
  unfold rexB_rot
  split_ifs with h
  · linarith [hc.2, hx.1]
  · exact sub_pos.mpr (lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne))

/-! ## 2. Piecewise-affine interpolation between two increasing finite sequences -/

/-- Clamp `x` to the interval `[lo, hi]`. -/
def rexB_clamp (lo hi x : ℝ) : ℝ := max lo (min hi x)

theorem rexB_clamp_of_le (lo hi x : ℝ) (h : x ≤ lo) (_hlh : lo ≤ hi) : rexB_clamp lo hi x = lo := by
  unfold rexB_clamp
  exact max_eq_left ((min_le_right hi x).trans h)

theorem rexB_clamp_of_ge (lo hi x : ℝ) (h : hi ≤ x) (hlh : lo ≤ hi) : rexB_clamp lo hi x = hi := by
  unfold rexB_clamp
  rw [min_eq_left h, max_eq_right hlh]

theorem rexB_clamp_of_mem (lo hi x : ℝ) (h1 : lo ≤ x) (h2 : x ≤ hi) : rexB_clamp lo hi x = x := by
  unfold rexB_clamp
  rw [min_eq_right h2, max_eq_right h1]

theorem rexB_clamp_mono (lo hi : ℝ) : Monotone (rexB_clamp lo hi) := by
  intro x y hxy
  unfold rexB_clamp
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

theorem rexB_clamp_continuous (lo hi : ℝ) : Continuous (rexB_clamp lo hi) := by
  show Continuous (fun x => max lo (min hi x))
  exact continuous_const.max (continuous_const.min continuous_id)

/-- Slope of the affine piece carrying `[a j, a (j+1)]` onto `[b j, b (j+1)]`. -/
def rexB_slope (a b : ℕ → ℝ) (j : ℕ) : ℝ := (b (j + 1) - b j) / (a (j + 1) - a j)

/-- The piecewise-affine interpolation: on `[a j, a (j+1)]` (for `j < m`) it is the positive affine
map onto `[b j, b (j+1)]` shifted by `-b 0` (so `a j ↦ b j - b 0`), written as a sum of clamped
affine pieces.  With `a 0 = 0 = b 0` this is the printed "positive affine map in oriented interval
coordinates" on each interval between successive marks. -/
def rexB_pl (m : ℕ) (a b : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, rexB_slope a b j * (rexB_clamp (a j) (a (j + 1)) x - a j)

theorem rexB_slope_pos (a b : ℕ → ℝ) (j : ℕ) (ha : a j < a (j + 1)) (hb : b j < b (j + 1)) :
    0 < rexB_slope a b j :=
  div_pos (sub_pos.mpr hb) (sub_pos.mpr ha)

theorem rexB_slope_mul (a b : ℕ → ℝ) (j : ℕ) (ha : a j < a (j + 1)) :
    rexB_slope a b j * (a (j + 1) - a j) = b (j + 1) - b j := by
  unfold rexB_slope
  exact div_mul_cancel₀ _ (sub_pos.mpr ha).ne'

/-- A sequence increasing at consecutive indices below `m` is monotone on `{0, …, m}`. -/
theorem rexB_mono_of_succ {a : ℕ → ℝ} {m : ℕ} (ha : ∀ j < m, a j < a (j + 1)) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ m) : a i ≤ a j := by
  revert hj
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih => intro hj; exact (ih (by omega)).trans (ha j (by omega)).le

theorem rexB_strictMono_of_succ {a : ℕ → ℝ} {m : ℕ} (ha : ∀ j < m, a j < a (j + 1)) {i j : ℕ}
    (hij : i < j) (hj : j ≤ m) : a i < a j :=
  (ha i (by omega)).trans_le (rexB_mono_of_succ ha hij hj)

/-- Values at the marks: `rexB_pl` carries `a i` to `b i - b 0` (telescoping). -/
theorem rexB_pl_mark {m : ℕ} {a b : ℕ → ℝ} (ha : ∀ j < m, a j < a (j + 1)) (i : ℕ) (hi : i ≤ m) :
    rexB_pl m a b (a i) = b i - b 0 := by
  unfold rexB_pl
  rw [← Finset.sum_range_add_sum_Ico _ hi]
  have h1 : ∀ j ∈ Finset.range i,
      rexB_slope a b j * (rexB_clamp (a j) (a (j + 1)) (a i) - a j) = b (j + 1) - b j := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [rexB_clamp_of_ge _ _ _ (rexB_mono_of_succ ha hj hi) (ha j (by omega)).le]
    exact rexB_slope_mul a b j (ha j (by omega))
  have h2 : ∀ j ∈ Finset.Ico i m,
      rexB_slope a b j * (rexB_clamp (a j) (a (j + 1)) (a i) - a j) = 0 := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [rexB_clamp_of_le _ _ _ (rexB_mono_of_succ ha hj.1 hj.2.le) (ha j hj.2).le, sub_self,
      mul_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_range_sub, Finset.sum_eq_zero h2, add_zero]

/-- On the piece `[a j, a (j+1)]` the interpolation is the affine map of slope `rexB_slope a b j`
through `(a j, b j - b 0)`: "on each interval between successive marked points use the positive
affine map in oriented interval coordinates". -/
theorem rexB_pl_eq_affine_on_piece {m : ℕ} {a b : ℕ → ℝ} (ha : ∀ j < m, a j < a (j + 1)) (j : ℕ)
    (hj : j < m) (x : ℝ) (h1 : a j ≤ x) (h2 : x ≤ a (j + 1)) :
    rexB_pl m a b x = b j - b 0 + rexB_slope a b j * (x - a j) := by
  unfold rexB_pl
  rw [← Finset.sum_range_add_sum_Ico _ hj.le, Finset.sum_eq_sum_Ico_succ_bot hj]
  have hA : ∀ i ∈ Finset.range j,
      rexB_slope a b i * (rexB_clamp (a i) (a (i + 1)) x - a i) = b (i + 1) - b i := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [rexB_clamp_of_ge _ _ _ ((rexB_mono_of_succ ha hi hj.le).trans h1) (ha i (by omega)).le]
    exact rexB_slope_mul a b i (ha i (by omega))
  have hB : ∀ i ∈ Finset.Ico (j + 1) m,
      rexB_slope a b i * (rexB_clamp (a i) (a (i + 1)) x - a i) = 0 := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [rexB_clamp_of_le _ _ _ (h2.trans (rexB_mono_of_succ ha hi.1 hi.2.le)) (ha i hi.2).le,
      sub_self, mul_zero]
  rw [Finset.sum_congr rfl hA, Finset.sum_range_sub, Finset.sum_eq_zero hB, add_zero,
    rexB_clamp_of_mem _ _ _ h1 h2]

theorem rexB_pl_mono {m : ℕ} {a b : ℕ → ℝ} (ha : ∀ j < m, a j < a (j + 1))
    (hb : ∀ j < m, b j < b (j + 1)) : Monotone (rexB_pl m a b) := by
  intro x y hxy
  unfold rexB_pl
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mem_range] at hj
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right (rexB_clamp_mono _ _ hxy) _)
    (rexB_slope_pos a b j (ha j hj) (hb j hj)).le

/-- Every point of `[a 0, a m)` lies on a piece `[a j, a (j+1))`, `j < m`. -/
theorem rexB_exists_piece (a : ℕ → ℝ) (m : ℕ) (x : ℝ) (h0 : a 0 ≤ x) (hm : x < a m) :
    ∃ j, j < m ∧ a j ≤ x ∧ x < a (j + 1) := by
  induction m with
  | zero => exact absurd (h0.trans_lt hm) (lt_irrefl _)
  | succ m ih =>
    by_cases h : x < a m
    · obtain ⟨j, hj, h1, h2⟩ := ih h
      exact ⟨j, by omega, h1, h2⟩
    · exact ⟨m, by omega, not_lt.mp h, hm⟩

/-- Strict increase from a point of `[a 0, a m)`. -/
theorem rexB_pl_lt {m : ℕ} {a b : ℕ → ℝ} (ha : ∀ j < m, a j < a (j + 1))
    (hb : ∀ j < m, b j < b (j + 1)) {x y : ℝ} (hx : a 0 ≤ x ∧ x < a m) (hxy : x < y) :
    rexB_pl m a b x < rexB_pl m a b y := by
  obtain ⟨j, hj, h1, h2⟩ := rexB_exists_piece a m x hx.1 hx.2
  unfold rexB_pl
  apply Finset.sum_lt_sum
  · intro i hi
    rw [Finset.mem_range] at hi
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (rexB_clamp_mono _ _ hxy.le) _)
      (rexB_slope_pos a b i (ha i hi) (hb i hi)).le
  · refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
    apply mul_lt_mul_of_pos_left _ (rexB_slope_pos a b j (ha j hj) (hb j hj))
    apply sub_lt_sub_right _ _
    rw [rexB_clamp_of_mem _ _ _ h1 h2.le]
    show x < max (a j) (min (a (j + 1)) y)
    exact lt_max_of_lt_right (lt_min h2 hxy)

theorem rexB_pl_strictMonoOn {m : ℕ} {a b : ℕ → ℝ} (ha : ∀ j < m, a j < a (j + 1))
    (hb : ∀ j < m, b j < b (j + 1)) : StrictMonoOn (rexB_pl m a b) (Set.Ico (a 0) (a m)) :=
  fun _ hx _ _ hxy => rexB_pl_lt ha hb hx hxy

theorem rexB_pl_continuous (m : ℕ) (a b : ℕ → ℝ) : Continuous (rexB_pl m a b) := by
  show Continuous (fun x => ∑ j ∈ Finset.range m,
    rexB_slope a b j * (rexB_clamp (a j) (a (j + 1)) x - a j))
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((rexB_clamp_continuous _ _).sub continuous_const)

/-- The interpolation maps `[a 0, a m)` into `[0, b m - b 0)`. -/
theorem rexB_pl_mem {m : ℕ} {a b : ℕ → ℝ} (ha : ∀ j < m, a j < a (j + 1))
    (hb : ∀ j < m, b j < b (j + 1)) (x : ℝ) (hx : a 0 ≤ x ∧ x < a m) :
    0 ≤ rexB_pl m a b x ∧ rexB_pl m a b x < b m - b 0 := by
  constructor
  · have h := rexB_pl_mono ha hb hx.1
    rwa [rexB_pl_mark ha 0 (Nat.zero_le m), sub_self] at h
  · have h := rexB_pl_lt ha hb hx hx.2
    rwa [rexB_pl_mark ha m le_rfl] at h

/-- The interpolation maps `[a 0, a m)` onto `[0, b m - b 0)` (intermediate value theorem). -/
theorem rexB_pl_surj {m : ℕ} {a : ℕ → ℝ} (ha : ∀ j < m, a j < a (j + 1)) (b : ℕ → ℝ) (y : ℝ)
    (hy : 0 ≤ y ∧ y < b m - b 0) : ∃ x, (a 0 ≤ x ∧ x < a m) ∧ rexB_pl m a b x = y := by
  have h0m : a 0 ≤ a m := rexB_mono_of_succ ha (Nat.zero_le m) le_rfl
  have hmem : y ∈ Set.Icc (rexB_pl m a b (a 0)) (rexB_pl m a b (a m)) := by
    rw [rexB_pl_mark ha 0 (Nat.zero_le m), rexB_pl_mark ha m le_rfl, sub_self]
    exact ⟨hy.1, hy.2.le⟩
  obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc h0m (rexB_pl_continuous m a b).continuousOn hmem
  refine ⟨x, ⟨hx.1, lt_of_le_of_ne hx.2 ?_⟩, hxy⟩
  intro hxm
  rw [hxm, rexB_pl_mark ha m le_rfl] at hxy
  exact hy.2.ne' hxy

/-! ## 3. The circle map in `[0, k)` coordinates: rotate, interpolate, rotate back -/

/-- The full circle map on `[0, k)`-coordinates: rotate the base mark `c` to `0`, interpolate
piecewise affinely, rotate `0` to the image base mark `c'`. -/
def rexB_F (k k' c c' : ℝ) (m : ℕ) (a b : ℕ → ℝ) (x : ℝ) : ℝ :=
  rexB_unrot k' c' (rexB_pl m a b (rexB_rot k c x))

/-- The data of a piecewise-affine circle map `[0,k) → [0,k')`: base points `c`, `c'`, and
increasing mark sequences `0 = a 0 < … < a m = k`, `0 = b 0 < … < b m = k'` in rotated coordinates. -/
structure rexB_Good (k k' c c' : ℝ) (m : ℕ) (a b : ℕ → ℝ) : Prop where
  hc : 0 ≤ c ∧ c < k
  hc' : 0 ≤ c' ∧ c' < k'
  a0 : a 0 = 0
  am : a m = k
  b0 : b 0 = 0
  bm : b m = k'
  ha : ∀ j < m, a j < a (j + 1)
  hb : ∀ j < m, b j < b (j + 1)

namespace rexB_Good

variable {k k' c c' : ℝ} {m : ℕ} {a b : ℕ → ℝ} (G : rexB_Good k k' c c' m a b)
include G

theorem rot_mem (x : ℝ) (hx : 0 ≤ x ∧ x < k) : rexB_rot k c x ∈ Set.Ico (a 0) (a m) := by
  rw [G.a0, G.am]
  exact rexB_rot_mem k c x G.hc hx

theorem pl_mem (x : ℝ) (hx : 0 ≤ x ∧ x < k) :
    0 ≤ rexB_pl m a b (rexB_rot k c x) ∧ rexB_pl m a b (rexB_rot k c x) < k' := by
  have h := rexB_pl_mem G.ha G.hb (rexB_rot k c x) (G.rot_mem x hx)
  rwa [G.bm, G.b0, sub_zero] at h

theorem F_mem (x : ℝ) (hx : 0 ≤ x ∧ x < k) :
    0 ≤ rexB_F k k' c c' m a b x ∧ rexB_F k k' c c' m a b x < k' :=
  rexB_unrot_mem k' c' _ G.hc' (G.pl_mem x hx)

theorem F_injOn : Set.InjOn (rexB_F k k' c c' m a b) (Set.Ico 0 k) := by
  intro x hx y hy hxy
  unfold rexB_F at hxy
  have h := congrArg (rexB_rot k' c') hxy
  rw [rexB_rot_unrot k' c' _ (G.pl_mem x hx), rexB_rot_unrot k' c' _ (G.pl_mem y hy)]
    at h
  have h' := (rexB_pl_strictMonoOn G.ha G.hb).injOn (G.rot_mem x hx) (G.rot_mem y hy) h
  have h'' := congrArg (rexB_unrot k c) h'
  rwa [rexB_unrot_rot k c x hx, rexB_unrot_rot k c y hy] at h''

theorem F_surj (y : ℝ) (hy : 0 ≤ y ∧ y < k') :
    ∃ x, (0 ≤ x ∧ x < k) ∧ rexB_F k k' c c' m a b x = y := by
  have hy' := rexB_rot_mem k' c' y G.hc' hy
  obtain ⟨z, hz, hzy⟩ := rexB_pl_surj G.ha b (rexB_rot k' c' y) (by rw [G.bm, G.b0, sub_zero]; exact hy')
  rw [G.a0, G.am] at hz
  refine ⟨rexB_unrot k c z, rexB_unrot_mem k c z G.hc hz, ?_⟩
  unfold rexB_F
  rw [rexB_rot_unrot k c z hz, hzy, rexB_unrot_rot k' c' y hy]

theorem F_cycBetween (x y z : ℝ) (hx : 0 ≤ x ∧ x < k) (hy : 0 ≤ y ∧ y < k) (hz : 0 ≤ z ∧ z < k)
    (h : cycBetween x y z) :
    cycBetween (rexB_F k k' c c' m a b x) (rexB_F k k' c c' m a b y) (rexB_F k k' c c' m a b z) := by
  unfold rexB_F
  rw [rexB_cycBetween_unrot k' c' _ _ _ G.hc' (G.pl_mem x hx) (G.pl_mem y hy) (G.pl_mem z hz)]
  apply rexB_cycBetween_of_strictMonoOn (rexB_pl_strictMonoOn G.ha G.hb) (G.rot_mem x hx)
    (G.rot_mem y hy) (G.rot_mem z hz)
  exact (rexB_cycBetween_rot k c x y z G.hc hx hy hz).mpr h

/-- The mark clause: the `j`-th mark (at coordinate `unrot (a j)`) goes to the `j`-th image mark. -/
theorem F_mark (j : ℕ) (hj : j < m) :
    rexB_F k k' c c' m a b (rexB_unrot k c (a j)) = rexB_unrot k' c' (b j) := by
  have haj : 0 ≤ a j ∧ a j < k := by
    rw [← G.a0, ← G.am]
    exact ⟨rexB_mono_of_succ G.ha (Nat.zero_le j) hj.le, rexB_strictMono_of_succ G.ha hj le_rfl⟩
  unfold rexB_F
  rw [rexB_rot_unrot k c _ haj, rexB_pl_mark G.ha j hj.le, G.b0, sub_zero]

end rexB_Good

/-! ## 4. Lifting a real circle map to `TraversalPoint` -/

/-- The inverse of `traversalKey` on `[0, n)`: integer part as edge label, fractional part as
edge parameter. -/
def rexB_unkey (n : ℕ) (x : ℝ) : TraversalPoint n :=
  (((⌊x⌋ : ℤ) : ZMod n), ⟨Int.fract x, Int.fract_nonneg x, Int.fract_lt_one x⟩)

theorem rexB_key_unkey (n : ℕ) [NeZero n] (x : ℝ) (hx : 0 ≤ x ∧ x < n) :
    traversalKey (rexB_unkey n x) = x := by
  have h1 : (0 : ℤ) ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx.1
  have h2 : ⌊x⌋ < (n : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hx.2)
  have h3 : (((⌊x⌋ : ℤ) : ZMod n).val : ℤ) = ⌊x⌋ := by
    rw [ZMod.val_intCast, Int.emod_eq_of_lt h1 h2]
  have h4 : ((((⌊x⌋ : ℤ) : ZMod n).val : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
    exact_mod_cast h3
  show ((((⌊x⌋ : ℤ) : ZMod n).val : ℕ) : ℝ) + Int.fract x = x
  rw [h4, Int.floor_add_fract]

/-- A bijection `[0,k) → [0,k')` of real coordinates lifts to an equivalence of parameter circles. -/
def rexB_circleEquiv (k k' : ℕ) [NeZero k] [NeZero k'] (F : ℝ → ℝ)
    (hmem : ∀ x : ℝ, 0 ≤ x ∧ x < (k : ℝ) → 0 ≤ F x ∧ F x < (k' : ℝ))
    (hinj : Set.InjOn F (Set.Ico 0 (k : ℝ)))
    (hsurj : ∀ y : ℝ, 0 ≤ y ∧ y < (k' : ℝ) → ∃ x : ℝ, (0 ≤ x ∧ x < (k : ℝ)) ∧ F x = y) :
    TraversalPoint k ≃ TraversalPoint k' :=
  Equiv.ofBijective (fun p => rexB_unkey k' (F (traversalKey p))) (by
    constructor
    · intro p q hpq
      have hp : 0 ≤ traversalKey p ∧ traversalKey p < k :=
        ⟨traversalKey_nonneg p, Diagram.traversalKey_lt_card p⟩
      have hq : 0 ≤ traversalKey q ∧ traversalKey q < k :=
        ⟨traversalKey_nonneg q, Diagram.traversalKey_lt_card q⟩
      have h : traversalKey (rexB_unkey k' (F (traversalKey p))) =
          traversalKey (rexB_unkey k' (F (traversalKey q))) := congrArg traversalKey hpq
      rw [rexB_key_unkey k' _ (hmem _ hp), rexB_key_unkey k' _ (hmem _ hq)] at h
      exact traversalKey_injective (hinj hp hq h)
    · intro q
      have hq : 0 ≤ traversalKey q ∧ traversalKey q < k' :=
        ⟨traversalKey_nonneg q, Diagram.traversalKey_lt_card q⟩
      obtain ⟨x, hx, hxq⟩ := hsurj _ hq
      refine ⟨rexB_unkey k x, traversalKey_injective ?_⟩
      show traversalKey (rexB_unkey k' (F (traversalKey (rexB_unkey k x)))) = traversalKey q
      rw [rexB_key_unkey k x hx, rexB_key_unkey k' _ (hmem x hx), hxq])

theorem rexB_circleEquiv_key (k k' : ℕ) [NeZero k] [NeZero k'] (F : ℝ → ℝ)
    (hmem : ∀ x : ℝ, 0 ≤ x ∧ x < (k : ℝ) → 0 ≤ F x ∧ F x < (k' : ℝ))
    (hinj : Set.InjOn F (Set.Ico 0 (k : ℝ)))
    (hsurj : ∀ y : ℝ, 0 ≤ y ∧ y < (k' : ℝ) → ∃ x : ℝ, (0 ≤ x ∧ x < (k : ℝ)) ∧ F x = y) (p : TraversalPoint k) :
    traversalKey (rexB_circleEquiv k k' F hmem hinj hsurj p) = F (traversalKey p) :=
  rexB_key_unkey k' _ (hmem _ ⟨traversalKey_nonneg p, Diagram.traversalKey_lt_card p⟩)

theorem rexB_circleEquiv_between (k k' : ℕ) [NeZero k] [NeZero k'] (F : ℝ → ℝ)
    (hmem : ∀ x : ℝ, 0 ≤ x ∧ x < (k : ℝ) → 0 ≤ F x ∧ F x < (k' : ℝ))
    (hinj : Set.InjOn F (Set.Ico 0 (k : ℝ)))
    (hsurj : ∀ y : ℝ, 0 ≤ y ∧ y < (k' : ℝ) → ∃ x : ℝ, (0 ≤ x ∧ x < (k : ℝ)) ∧ F x = y)
    (hcyc : ∀ x y z : ℝ, 0 ≤ x ∧ x < (k : ℝ) → 0 ≤ y ∧ y < (k : ℝ) → 0 ≤ z ∧ z < (k : ℝ) →
      cycBetween x y z → cycBetween (F x) (F y) (F z))
    (p q r : TraversalPoint k) (h : traversalBetween p q r) :
    traversalBetween (rexB_circleEquiv k k' F hmem hinj hsurj p)
      (rexB_circleEquiv k k' F hmem hinj hsurj q) (rexB_circleEquiv k k' F hmem hinj hsurj r) := by
  rw [traversalBetween_iff_cycBetween] at h ⊢
  rw [rexB_circleEquiv_key, rexB_circleEquiv_key, rexB_circleEquiv_key]
  exact hcyc _ _ _ ⟨traversalKey_nonneg p, Diagram.traversalKey_lt_card p⟩
    ⟨traversalKey_nonneg q, Diagram.traversalKey_lt_card q⟩ ⟨traversalKey_nonneg r, Diagram.traversalKey_lt_card r⟩ h

/-! ## 5. The per-component data of a record isomorphism -/

section Component

variable {D D' : Diagram} (ι : RecordIso D.record D'.record) (i : Fin D.Γ.c)

theorem rexB_coord_mem (v : D.Γ.Visit) (hv : D.compOf v = i) :
    0 ≤ D.visitCoord v ∧ D.visitCoord v < (D.Γ.comp i).k := by
  refine ⟨D.visitCoord_nonneg v, ?_⟩
  have h := D.visitCoord_lt v
  rwa [hv] at h

theorem rexB_compOf_image (v : D.Γ.Visit) (hv : D.compOf v = i) : D'.compOf (ι.Φ v) = ι.e i := by
  rw [← hv]
  exact ι.comp_eq v

theorem rexB_coord'_mem (v : D.Γ.Visit) (hv : D.compOf v = i) :
    0 ≤ D'.visitCoord (ι.Φ v) ∧ D'.visitCoord (ι.Φ v) < (D'.Γ.comp (ι.e i)).k := by
  refine ⟨D'.visitCoord_nonneg _, ?_⟩
  have h := D'.visitCoord_lt (ι.Φ v)
  rwa [rexB_compOf_image ι i v hv] at h

/-- The occurrences of component `i` in coordinates rotated so that the first occurrence `ent 0`
sits at `0`; the terminal entry `a m = k` closes the circle. -/
def rexB_aSeq (hi : 0 < (D.compList i).length) (j : ℕ) : ℝ :=
  if j < (D.compList i).length then
    rexB_rot (D.Γ.comp i).k (D.visitCoord (D.ent i hi 0)) (D.visitCoord (D.ent i hi j))
  else (D.Γ.comp i).k

/-- The images `ι.Φ (ent j)` on component `ι.e i` of `D'`, in coordinates rotated so that
`ι.Φ (ent 0)` sits at `0`; the terminal entry `b m = k'` closes the circle. -/
def rexB_bSeq (hi : 0 < (D.compList i).length) (j : ℕ) : ℝ :=
  if j < (D.compList i).length then
    rexB_rot (D'.Γ.comp (ι.e i)).k (D'.visitCoord (ι.Φ (D.ent i hi 0)))
      (D'.visitCoord (ι.Φ (D.ent i hi j)))
  else (D'.Γ.comp (ι.e i)).k

theorem rexB_coord_ent_le (hi : 0 < (D.compList i).length) (j : ℕ) (hj : j < (D.compList i).length) :
    D.visitCoord (D.ent i hi 0) ≤ D.visitCoord (D.ent i hi j) := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; exact le_rfl
  · exact ((D.visitCoord_ent_lt_iff i hi 0 j).mpr
      (by rw [Nat.zero_mod, Nat.mod_eq_of_lt hj]; exact h)).le

/-- The mark data of a component with occurrences is good: on `D` the rotated coordinates increase
because the component list is sorted; on `D'` they increase because `ι` preserves the oriented
cyclic order (`RecordIso.visitBetween_iff`) and is injective. -/
theorem rexB_good_marks (hi : 0 < (D.compList i).length) :
    rexB_Good (D.Γ.comp i).k (D'.Γ.comp (ι.e i)).k (D.visitCoord (D.ent i hi 0))
      (D'.visitCoord (ι.Φ (D.ent i hi 0))) (D.compList i).length (rexB_aSeq i hi)
      (rexB_bSeq ι i hi) := by
  have hc := rexB_coord_mem i _ (D.compOf_ent i hi 0)
  have hc' := rexB_coord'_mem ι i _ (D.compOf_ent i hi 0)
  refine ⟨hc, hc', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold rexB_aSeq; rw [ite_eq_left hi, rexB_rot_self]
  · unfold rexB_aSeq; rw [ite_eq_right (lt_irrefl _)]
  · unfold rexB_bSeq; rw [ite_eq_left hi, rexB_rot_self]
  · unfold rexB_bSeq; rw [ite_eq_right (lt_irrefl _)]
  · intro j hj
    unfold rexB_aSeq
    rw [ite_eq_left hj]
    by_cases hj1 : j + 1 < (D.compList i).length
    · rw [ite_eq_left hj1]
      have h0j := rexB_coord_ent_le i hi j hj
      have h0j1 := rexB_coord_ent_le i hi (j + 1) hj1
      have hjj1 : D.visitCoord (D.ent i hi j) < D.visitCoord (D.ent i hi (j + 1)) :=
        (D.visitCoord_ent_lt_iff i hi j (j + 1)).mpr
          (by rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj1]; omega)
      unfold rexB_rot
      rw [ite_eq_right (not_lt.mpr h0j), ite_eq_right (not_lt.mpr h0j1)]
      linarith
    · rw [ite_eq_right hj1]
      exact (rexB_rot_mem _ _ _ hc (rexB_coord_mem i _ (D.compOf_ent i hi j))).2
  · intro j hj
    unfold rexB_bSeq
    rw [ite_eq_left hj]
    by_cases hj1 : j + 1 < (D.compList i).length
    · rw [ite_eq_left hj1]
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h
        rw [rexB_rot_self]
        apply rexB_rot_pos_of_ne _ _ _ hc' (rexB_coord'_mem ι i _ (D.compOf_ent i hi _))
        intro heq
        have h1 : ι.Φ (D.ent i hi (0 + 1)) = ι.Φ (D.ent i hi 0) :=
          D'.visitCoord_injOn ((ι.compOf_iff _ _).mpr (by rw [D.compOf_ent, D.compOf_ent])) heq
        have h2 := (D.ent_inj_iff i hi _ _).mp (ι.Φ.injective h1)
        rw [Nat.mod_eq_of_lt hj1, Nat.zero_mod] at h2
        omega
      · apply rexB_rot_lt_of_cycBetween _ _ _ _ hc' (rexB_coord'_mem ι i _ (D.compOf_ent i hi _))
          (rexB_coord'_mem ι i _ (D.compOf_ent i hi _))
        have hb := (D.visitBetween_ent_iff i hi 0 j (j + 1) h (Nat.succ_pos j) hj hj1).mpr
          (Nat.lt_succ_self j)
        rw [Nat.zero_add, Nat.zero_add] at hb
        exact (ι.visitBetween_iff (D.ent i hi 0) (D.ent i hi j) (D.ent i hi (j + 1))
          (by rw [D.compOf_ent, D.compOf_ent]) (by rw [D.compOf_ent, D.compOf_ent])).mpr hb
    · rw [ite_eq_right hj1]
      exact (rexB_rot_mem _ _ _ hc' (rexB_coord'_mem ι i _ (D.compOf_ent i hi j))).2

/-- Trivial mark data for a circle without occurrences: the two ends `0` and `k`. -/
def rexB_aTriv (k : ℝ) (j : ℕ) : ℝ := if j = 0 then 0 else k

/-- With no occurrences the interpolation is the linear rescaling `x ↦ (k'/k) x`, "any positive
circle parametrization". -/
theorem rexB_good_triv (k k' : ℝ) (hk : 0 < k) (hk' : 0 < k') :
    rexB_Good k k' 0 0 1 (rexB_aTriv k) (rexB_aTriv k') := by
  refine ⟨⟨le_rfl, hk⟩, ⟨le_rfl, hk'⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [rexB_aTriv]
  · simp [rexB_aTriv]
  · simp [rexB_aTriv]
  · simp [rexB_aTriv]
  · intro j hj
    have : j = 0 := by omega
    subst this
    simp [rexB_aTriv, hk]
  · intro j hj
    have : j = 0 := by omega
    subst this
    simp [rexB_aTriv, hk']

theorem rexB_k_pos (C : PolyComp) : (0 : ℝ) < C.k := by
  have := C.hk
  exact_mod_cast (show 0 < C.k by omega)

/-- The real circle map of component `i`: the piecewise-affine interpolation between the
occurrences and their images if there are occurrences, the linear rescaling otherwise. -/
def rexB_compF : ℝ → ℝ :=
  if hi : 0 < (D.compList i).length then
    rexB_F (D.Γ.comp i).k (D'.Γ.comp (ι.e i)).k (D.visitCoord (D.ent i hi 0))
      (D'.visitCoord (ι.Φ (D.ent i hi 0))) (D.compList i).length (rexB_aSeq i hi) (rexB_bSeq ι i hi)
  else
    rexB_F (D.Γ.comp i).k (D'.Γ.comp (ι.e i)).k 0 0 1 (rexB_aTriv (D.Γ.comp i).k)
      (rexB_aTriv (D'.Γ.comp (ι.e i)).k)

theorem rexB_compF_good : ∃ (c c' : ℝ) (m : ℕ) (a b : ℕ → ℝ),
    rexB_Good (D.Γ.comp i).k (D'.Γ.comp (ι.e i)).k c c' m a b ∧
      rexB_compF ι i = rexB_F (D.Γ.comp i).k (D'.Γ.comp (ι.e i)).k c c' m a b := by
  unfold rexB_compF
  split_ifs with hi
  · exact ⟨_, _, _, _, _, rexB_good_marks ι i hi, rfl⟩
  · exact ⟨_, _, _, _, _, rexB_good_triv _ _ (rexB_k_pos _) (rexB_k_pos _), rfl⟩

theorem rexB_compF_mem (x : ℝ) (hx : 0 ≤ x ∧ x < ((D.Γ.comp i).k : ℝ)) :
    0 ≤ rexB_compF ι i x ∧ rexB_compF ι i x < ((D'.Γ.comp (ι.e i)).k : ℝ) := by
  obtain ⟨c, c', m, a, b, G, hF⟩ := rexB_compF_good ι i
  rw [hF]
  exact G.F_mem x hx

theorem rexB_compF_injOn : Set.InjOn (rexB_compF ι i) (Set.Ico 0 ((D.Γ.comp i).k : ℝ)) := by
  obtain ⟨c, c', m, a, b, G, hF⟩ := rexB_compF_good ι i
  rw [hF]
  exact G.F_injOn

theorem rexB_compF_surj (y : ℝ) (hy : 0 ≤ y ∧ y < ((D'.Γ.comp (ι.e i)).k : ℝ)) :
    ∃ x : ℝ, (0 ≤ x ∧ x < ((D.Γ.comp i).k : ℝ)) ∧ rexB_compF ι i x = y := by
  obtain ⟨c, c', m, a, b, G, hF⟩ := rexB_compF_good ι i
  rw [hF]
  exact G.F_surj y hy

theorem rexB_compF_cycBetween (x y z : ℝ) (hx : 0 ≤ x ∧ x < ((D.Γ.comp i).k : ℝ))
    (hy : 0 ≤ y ∧ y < ((D.Γ.comp i).k : ℝ)) (hz : 0 ≤ z ∧ z < ((D.Γ.comp i).k : ℝ))
    (h : cycBetween x y z) :
    cycBetween (rexB_compF ι i x) (rexB_compF ι i y) (rexB_compF ι i z) := by
  obtain ⟨c, c', m, a, b, G, hF⟩ := rexB_compF_good ι i
  rw [hF]
  exact G.F_cycBetween x y z hx hy hz h

/-- The mark clause in coordinates: every occurrence of component `i` goes to the coordinate of
its image under `ι.Φ`. -/
theorem rexB_compF_mark (v : D.Γ.Visit) (hv : D.compOf v = i) :
    rexB_compF ι i (D.visitCoord v) = D'.visitCoord (ι.Φ v) := by
  have hi : 0 < (D.compList i).length := List.length_pos_of_mem ((D.mem_compList i v).mpr hv)
  unfold rexB_compF
  rw [dite_eq_left hi]
  obtain ⟨j, hj, rfl⟩ := D.exists_ent i hi v hv
  have G := rexB_good_marks ι i hi
  have h1 : D.visitCoord (D.ent i hi j) =
      rexB_unrot (D.Γ.comp i).k (D.visitCoord (D.ent i hi 0)) (rexB_aSeq i hi j) := by
    unfold rexB_aSeq
    rw [ite_eq_left hj, rexB_unrot_rot _ _ _ (rexB_coord_mem i _ (D.compOf_ent i hi j))]
  have h2 : D'.visitCoord (ι.Φ (D.ent i hi j)) =
      rexB_unrot (D'.Γ.comp (ι.e i)).k (D'.visitCoord (ι.Φ (D.ent i hi 0))) (rexB_bSeq ι i hi j) := by
    unfold rexB_bSeq
    rw [ite_eq_left hj, rexB_unrot_rot _ _ _ (rexB_coord'_mem ι i _ (D.compOf_ent i hi j))]
  rw [h1, h2]
  exact G.F_mark j hj

/-- The circle map of component `i`, lifted to the parameter circles. -/
def rexB_compEquiv : TraversalPoint (D.Γ.comp i).k ≃ TraversalPoint (D'.Γ.comp (ι.e i)).k :=
  rexB_circleEquiv _ _ (rexB_compF ι i) (rexB_compF_mem ι i) (rexB_compF_injOn ι i)
    (rexB_compF_surj ι i)

theorem rexB_compEquiv_key (p : TraversalPoint (D.Γ.comp i).k) :
    traversalKey (rexB_compEquiv ι i p) = rexB_compF ι i (traversalKey p) :=
  rexB_circleEquiv_key _ _ _ _ _ _ p

theorem rexB_compEquiv_between (p q r : TraversalPoint (D.Γ.comp i).k) (h : traversalBetween p q r) :
    traversalBetween (rexB_compEquiv ι i p) (rexB_compEquiv ι i q) (rexB_compEquiv ι i r) :=
  rexB_circleEquiv_between _ _ _ _ _ _ (rexB_compF_cycBetween ι i) p q r h

end Component

/-! ## 6. The extension theorem -/

/-- `RecordIso.extend` (def:gauss-record, sm-3:365-369): every named record isomorphism between
the records of two diagrams extends to orientation-preserving piecewise-linear circle maps of the
parameter circles carrying each occurrence to its image. -/
theorem rexB_extendsToCircleMaps {D D' : Diagram} (ι : RecordIso D.record D'.record) :
    ι.ExtendsToCircleMaps := by
  refine ⟨fun i => rexB_compEquiv ι i, ?_, ?_⟩
  · intro i p q r h
    exact rexB_compEquiv_between ι i p q r h
  · intro v
    have hc : (D'.visitPt (ι.Φ v)).1 = ι.e (D.visitPt v).1 := ι.comp_eq v
    have hk : traversalKey (rexB_compEquiv ι (D.visitPt v).1 (D.visitPt v).2) =
        traversalKey (D'.visitPt (ι.Φ v)).2 := by
      rw [rexB_compEquiv_key]
      exact rexB_compF_mark ι (D.visitPt v).1 v rfl
    show (⟨ι.e (D.visitPt v).1, rexB_compEquiv ι (D.visitPt v).1 (D.visitPt v).2⟩ : D'.Γ.Pt) =
      D'.visitPt (ι.Φ v)
    generalize D'.visitPt (ι.Φ v) = p' at hc hk ⊢
    obtain ⟨i', q'⟩ := p'
    dsimp only at hc hk
    subst hc
    rw [traversalKey_injective hk]

/-- The extension theorem of def:gauss-record, in the packaging of `LinkDiagramRecord` section H. -/
theorem rexB_recordIso_extend : recordIso_extend_statement :=
  fun _ _ ι => rexB_extendsToCircleMaps ι


/-! ## 7. The piecewise-affine clause as a predicate: `RecordIso.ExtendsPiecewiseAffine`

`ExtendsToCircleMaps` (LinkDiagramRecord, section H) records of the circle maps only that they are
orientation preserving and extend `Φ`.  The printed clause (sm-3:365-369) is more specific:

"After a finite subdivision we choose an orientation-preserving piecewise-linear circle map
Φ̄ : C → C' extending Φ: on each interval between successive marked points use the positive affine
map in oriented interval coordinates. If M is empty, choose any positive circle parametrization."

The predicate below adds the two missing clauses in traversal-key coordinates.  The "interval
between successive marked points" is the closed arc from an occurrence `v` to its forward successor
`nextVisit v` (def:gauss-record's `s`); "oriented interval coordinates" on that arc are the forward
traversal distance from `v` (the accepted `Diagram.cyclicOffset`), running from `0` to the arc length
`rexPL_arcLen`; the "positive affine map" between the two arcs is then multiplication by the ratio of
the arc lengths.  A circle carrying a single mark has `nextVisit v = v`, and its one "interval
between successive marked points" is the whole circle, of length `k`.  For a circle without marks
("If M is empty") the predicate fixes one definite positive parametrization: the linear rescaling
`traversalKey ↦ traversalKey · (k'/k)` of the key coordinate. -/

/-- The length of the oriented arc from the mark `a` to the mark `b` of the circle `[0, k)`: the
forward traversal distance `Diagram.cyclicOffset k a b`, except that the arc from a mark to itself
(a circle carrying a single occurrence, `nextVisit v = v`) is the whole circle, of length `k`. -/
def rexPL_arcLen (k : ℕ) (a b : ℝ) : ℝ := if a = b then (k : ℝ) else Diagram.cyclicOffset k a b

namespace RecordIso

variable {D D' : Diagram}

/-- `ι.ExtendsPiecewiseAffine` (def:gauss-record, sm-3:365-369: "After a finite subdivision we
choose an orientation-preserving piecewise-linear circle map Φ̄ : C → C' extending Φ: on each
interval between successive marked points use the positive affine map in oriented interval
coordinates. If M is empty, choose any positive circle parametrization."):
there are bijections `φ i` of the parameter circle of component `i` of `D` onto that of component
`ι.e i` of `D'` such that
1. ("orientation-preserving ... circle map") each `φ i` preserves the oriented cyclic order
   `traversalBetween`;
2. ("extending Φ") the traversal point of every occurrence `v` goes to that of `ι.Φ v`;
3. ("on each interval between successive marked points use the positive affine map in oriented
   interval coordinates") for every occurrence `v` on component `i` and every traversal point `p`
   of that component on the closed arc from `v` to its forward successor `nextVisit v` — its
   forward distance from `v` (`Diagram.cyclicOffset`) is at most the arc length `rexPL_arcLen`,
   which for the single-mark case `nextVisit v = v` is the whole circle `k` — the forward distance
   of `φ i p` from `ι.Φ v` equals the forward distance of `p` from `v` times the ratio (length of
   the image arc from `ι.Φ v` to `nextVisit (ι.Φ v)`) / (length of the arc from `v` to `nextVisit v`);
4. ("If M is empty, choose any positive circle parametrization") on every component `i` without
   occurrences the chosen parametrization is the linear rescaling
   `traversalKey (φ i p) = traversalKey p · (k'/k)` of the key coordinate.
Clauses 1-2 are `ExtendsToCircleMaps` (`ExtendsPiecewiseAffine.toExtendsToCircleMaps`). -/
def ExtendsPiecewiseAffine (ι : RecordIso D.record D'.record) : Prop :=
  ∃ φ : ∀ i : Fin D.Γ.c, TraversalPoint (D.Γ.comp i).k ≃ TraversalPoint (D'.Γ.comp (ι.e i)).k,
    (∀ i p q r, traversalBetween p q r → traversalBetween (φ i p) (φ i q) (φ i r)) ∧
    (∀ v : D.Γ.Visit, (⟨ι.e (D.visitPt v).1, φ _ (D.visitPt v).2⟩ : D'.Γ.Pt) = D'.visitPt (ι.Φ v)) ∧
    (∀ (i : Fin D.Γ.c) (v : D.Γ.Visit), D.compOf v = i → ∀ p : TraversalPoint (D.Γ.comp i).k,
      Diagram.cyclicOffset (D.Γ.comp i).k (D.visitCoord v) (traversalKey p) ≤
        rexPL_arcLen (D.Γ.comp i).k (D.visitCoord v) (D.visitCoord (D.nextVisit v)) →
      Diagram.cyclicOffset (D'.Γ.comp (ι.e i)).k (D'.visitCoord (ι.Φ v)) (traversalKey (φ i p)) =
        Diagram.cyclicOffset (D.Γ.comp i).k (D.visitCoord v) (traversalKey p) *
          (rexPL_arcLen (D'.Γ.comp (ι.e i)).k (D'.visitCoord (ι.Φ v))
              (D'.visitCoord (D'.nextVisit (ι.Φ v))) /
            rexPL_arcLen (D.Γ.comp i).k (D.visitCoord v) (D.visitCoord (D.nextVisit v)))) ∧
    (∀ i : Fin D.Γ.c, (∀ v : D.Γ.Visit, D.compOf v ≠ i) → ∀ p : TraversalPoint (D.Γ.comp i).k,
      traversalKey (φ i p) = traversalKey p * (((D'.Γ.comp (ι.e i)).k : ℝ) / ((D.Γ.comp i).k : ℝ)))

/-- The affine clause implies the extension clause of section H. -/
theorem ExtendsPiecewiseAffine.toExtendsToCircleMaps {ι : RecordIso D.record D'.record}
    (h : ι.ExtendsPiecewiseAffine) : ι.ExtendsToCircleMaps := by
  obtain ⟨φ, h1, h2, -, -⟩ := h
  exact ⟨φ, h1, h2⟩

end RecordIso

/-! ## 8. The affine clause for the printed witness

In rotated coordinates (`rexB_rot`) the forward distance from a mark is the accepted
`Diagram.cyclicOffset`; on the piece `[a j, a (j+1)]` the interpolation `rexB_pl` is the affine map
of slope `rexB_slope a b j` through `(a j, b j)` (`rexB_pl_eq_affine_on_piece`), so the forward
distance of the image from `b j` is the slope times the forward distance from `a j`.  The closed arc
from the last mark `a (m-1)` back to the base mark `a 0 = 0` wraps around the cut point: its far
endpoint is the base point `c = unrot 0 = unrot k`, handled separately. -/

/-- `rexB_rot k c x` is the accepted forward traversal distance from `c` to `x`. -/
theorem rexPL_rot_eq_cyclicOffset (k : ℕ) (c x : ℝ) :
    rexB_rot (k : ℝ) c x = Diagram.cyclicOffset k c x := by
  unfold rexB_rot Diagram.cyclicOffset
  by_cases h : c ≤ x
  · rw [ite_eq_left h, ite_eq_right (not_lt.mpr h)]
  · rw [ite_eq_right h, ite_eq_left (not_le.mp h)]

/-- Rotating both points by the same base leaves the forward distance unchanged. -/
theorem rexPL_rot_unrot_unrot (k c s t : ℝ) (hc : 0 ≤ c ∧ c < k) (hs : 0 ≤ s ∧ s < k)
    (ht : 0 ≤ t ∧ t < k) :
    rexB_rot k (rexB_unrot k c s) (rexB_unrot k c t) = rexB_rot k s t := by
  have hc1 := hc.1; have hc2 := hc.2; have hs1 := hs.1; have hs2 := hs.2
  have ht1 := ht.1; have ht2 := ht.2
  unfold rexB_rot rexB_unrot
  split_ifs <;> linarith

/-- The far end `k` of the cut circle rotates back to the base point. -/
theorem rexPL_unrot_k (k c : ℝ) (hc : 0 ≤ c ∧ c < k) : rexB_unrot k c k = c := by
  unfold rexB_unrot
  rw [ite_eq_right (not_lt.mpr (by linarith [hc.1]))]
  ring

theorem rexPL_unrot_zero (k c : ℝ) (hc : 0 ≤ c ∧ c < k) : rexB_unrot k c 0 = c := by
  unfold rexB_unrot
  rw [ite_eq_left (by linarith [hc.2])]
  ring

/-- On the piece `[a j, a (j+1)]` the forward distance of `rexB_pl x` from the image mark `b j` is
the slope times the forward distance of `x` from `a j` ("the positive affine map in oriented
interval coordinates"). -/
theorem rexPL_rot_pl_piece {m : ℕ} {a b : ℕ → ℝ} (ha : ∀ j < m, a j < a (j + 1))
    (hb : ∀ j < m, b j < b (j + 1)) (hb0 : b 0 = 0) (k' : ℝ) (j : ℕ) (hj : j < m) (x : ℝ)
    (h1 : a j ≤ x) (h2 : x ≤ a (j + 1)) :
    rexB_rot k' (b j) (rexB_pl m a b x) = rexB_slope a b j * (x - a j) := by
  rw [rexB_pl_eq_affine_on_piece ha j hj x h1 h2, hb0, sub_zero]
  have hpos : 0 ≤ rexB_slope a b j * (x - a j) :=
    mul_nonneg (rexB_slope_pos a b j (ha j hj) (hb j hj)).le (sub_nonneg.mpr h1)
  unfold rexB_rot
  rw [ite_eq_right (not_lt.mpr (by linarith))]
  ring

section GoodPL

variable {k k' c c' : ℝ} {m : ℕ} {a b : ℕ → ℝ} (G : rexB_Good k k' c c' m a b)
include G

theorem rexPL_a_mem (j : ℕ) (hj : j < m) : 0 ≤ a j ∧ a j < k := by
  rw [← G.a0, ← G.am]
  exact ⟨rexB_mono_of_succ G.ha (Nat.zero_le j) hj.le, rexB_strictMono_of_succ G.ha hj le_rfl⟩

theorem rexPL_b_mem (j : ℕ) (hj : j < m) : 0 ≤ b j ∧ b j < k' := by
  rw [← G.b0, ← G.bm]
  exact ⟨rexB_mono_of_succ G.hb (Nat.zero_le j) hj.le, rexB_strictMono_of_succ G.hb hj le_rfl⟩

theorem rexPL_a_succ_le (j : ℕ) (hj : j < m) : a (j + 1) ≤ k := by
  rw [← G.am]
  exact rexB_mono_of_succ G.ha (by omega) le_rfl

/-- The mark data read backwards (`D'` to `D`) is good as well. -/
theorem rexPL_good_swap : rexB_Good k' k c' c m b a :=
  ⟨G.hc', G.hc, G.b0, G.bm, G.a0, G.am, G.hb, G.ha⟩

/-- The affine clause for `rexB_F` in `[0,k)` coordinates: if the forward distance of `x` from the
`j`-th mark `unrot (a j)` is at most the arc length `a (j+1) - a j` to the next mark, the forward
distance of `F x` from the image mark `unrot (b j)` is that distance times the slope of the piece.
The wrap-around case (distance measured across the cut point) forces `x` to be the base point and
`j + 1 = m`. -/
theorem rexPL_F_offset (j : ℕ) (hj : j < m) (x : ℝ) (hx : 0 ≤ x ∧ x < k)
    (hle : rexB_rot k (rexB_unrot k c (a j)) x ≤ a (j + 1) - a j) :
    rexB_rot k' (rexB_unrot k' c' (b j)) (rexB_F k k' c c' m a b x) =
      rexB_rot k (rexB_unrot k c (a j)) x * rexB_slope a b j := by
  have haj := rexPL_a_mem G j hj
  have hbj := rexPL_b_mem G j hj
  have hrmem : 0 ≤ rexB_rot k c x ∧ rexB_rot k c x < k := rexB_rot_mem k c x G.hc hx
  have hpl := G.pl_mem x hx
  have hoff : rexB_rot k (rexB_unrot k c (a j)) x = rexB_rot k (a j) (rexB_rot k c x) := by
    conv_lhs => rw [← rexB_unrot_rot k c x hx]
    exact rexPL_rot_unrot_unrot k c (a j) _ G.hc haj hrmem
  have hF : rexB_F k k' c c' m a b x = rexB_unrot k' c' (rexB_pl m a b (rexB_rot k c x)) := rfl
  rw [hF, rexPL_rot_unrot_unrot k' c' (b j) _ G.hc' hbj hpl, hoff]
  rw [hoff] at hle
  generalize hr : rexB_rot k c x = r at hle hrmem hpl ⊢
  by_cases hcase : a j ≤ r
  · have hr2 : r ≤ a (j + 1) := by
      have := hle
      unfold rexB_rot at this
      rw [ite_eq_right (not_lt.mpr hcase)] at this
      linarith
    rw [rexPL_rot_pl_piece G.ha G.hb G.b0 k' j hj r hcase hr2]
    unfold rexB_rot
    rw [ite_eq_right (not_lt.mpr hcase)]
    ring
  · have hlt : r < a j := not_le.mp hcase
    have hle' : r - a j + k ≤ a (j + 1) - a j := by
      have := hle
      unfold rexB_rot at this
      rwa [ite_eq_left hlt] at this
    have hak : a (j + 1) ≤ k := rexPL_a_succ_le G j hj
    have hr0 : r = 0 := le_antisymm (by linarith) hrmem.1
    have hajk : a (j + 1) = k := by linarith
    have hjm : j + 1 = m := by
      by_contra hne
      have : a (j + 1) < a m := rexB_strictMono_of_succ G.ha (by omega) le_rfl
      rw [G.am] at this
      linarith
    have h0aj : 0 < a j := hrmem.1.trans_lt hlt
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h
        rw [G.a0] at h0aj
        exact absurd h0aj (lt_irrefl _)
      · exact h
    have hbjpos : 0 < b j := by
      have := rexB_strictMono_of_succ G.hb hj0 hj.le
      rwa [G.b0] at this
    have hbk : b (j + 1) = k' := by rw [hjm, G.bm]
    have hpl0 : rexB_pl m a b 0 = 0 := by
      have := rexB_pl_mark (b := b) G.ha 0 (Nat.zero_le m)
      rwa [G.a0, sub_self] at this
    have hne : k - a j ≠ 0 := sub_ne_zero.mpr haj.2.ne'
    rw [hr0, hpl0]
    unfold rexB_rot rexB_slope
    rw [ite_eq_left hbjpos, ite_eq_left h0aj, hbk, hajk]
    rw [show (0 : ℝ) - a j + k = k - a j by ring, mul_comm, div_mul_cancel₀ _ hne]
    ring

end GoodPL

/-- The arc from the `j`-th mark to the `(j+1)`-st (both in circle coordinates) has length
`a (j+1) - a j`; for the last mark the far end is the base point `c = unrot k = unrot 0`, and for a
single mark (`m = 1`) the arc from the mark to itself is the whole circle. -/
theorem rexPL_arcLen_marks {kn : ℕ} {k' c c' : ℝ} {m : ℕ} {a b : ℕ → ℝ}
    (G : rexB_Good (kn : ℝ) k' c c' m a b) (j : ℕ) (hj : j < m) :
    rexPL_arcLen kn (rexB_unrot kn c (a j)) (rexB_unrot kn c (a (j + 1))) = a (j + 1) - a j := by
  have haj := rexPL_a_mem G j hj
  have hak : a (j + 1) ≤ kn := rexPL_a_succ_le G j hj
  have hlt : a j < a (j + 1) := G.ha j hj
  have hkpos : (0 : ℝ) < kn := G.hc.1.trans_lt G.hc.2
  unfold rexPL_arcLen
  rcases lt_or_eq_of_le hak with hak | hak
  · have haj1 : 0 ≤ a (j + 1) ∧ a (j + 1) < kn := ⟨haj.1.trans hlt.le, hak⟩
    have hne : rexB_unrot kn c (a j) ≠ rexB_unrot kn c (a (j + 1)) := by
      intro heq
      have := congrArg (rexB_rot kn c) heq
      rw [rexB_rot_unrot _ _ _ haj, rexB_rot_unrot _ _ _ haj1] at this
      exact hlt.ne this
    rw [ite_eq_right hne, ← rexPL_rot_eq_cyclicOffset, rexPL_rot_unrot_unrot _ c _ _ G.hc haj haj1]
    unfold rexB_rot
    rw [ite_eq_right (not_lt.mpr hlt.le)]
  · rw [hak, rexPL_unrot_k _ _ G.hc]
    by_cases h0 : a j = 0
    · rw [h0, rexPL_unrot_zero _ _ G.hc, ite_eq_left rfl, sub_zero]
    · have hpos : 0 < a j := lt_of_le_of_ne haj.1 (Ne.symm h0)
      have hne : rexB_unrot kn c (a j) ≠ c := by
        intro heq
        have := congrArg (rexB_rot kn c) heq
        rw [rexB_rot_unrot _ _ _ haj, rexB_rot_self] at this
        exact h0 this
      have hoff : Diagram.cyclicOffset kn (rexB_unrot kn c (a j)) (rexB_unrot kn c 0) =
          kn - a j := by
        rw [← rexPL_rot_eq_cyclicOffset, rexPL_rot_unrot_unrot _ c _ _ G.hc haj ⟨le_rfl, hkpos⟩]
        unfold rexB_rot
        rw [ite_eq_left hpos]
        ring
      rw [rexPL_unrot_zero _ _ G.hc] at hoff
      rw [ite_eq_right hne, hoff]

section ComponentPL

variable {D D' : Diagram} (ι : RecordIso D.record D'.record) (i : Fin D.Γ.c)

/-- Coordinates of the enumerated occurrences through the rotation, including the wrap-around
index `m` (which returns to `ent 0`, at coordinate `c = unrot k`). -/
theorem rexPL_coord_ent (hi : 0 < (D.compList i).length) (j : ℕ) (hj : j ≤ (D.compList i).length) :
    D.visitCoord (D.ent i hi j) =
      rexB_unrot (D.Γ.comp i).k (D.visitCoord (D.ent i hi 0)) (rexB_aSeq i hi j) := by
  rcases lt_or_eq_of_le hj with hj | rfl
  · unfold rexB_aSeq
    rw [ite_eq_left hj, rexB_unrot_rot _ _ _ (rexB_coord_mem i _ (D.compOf_ent i hi j))]
  · have hent : D.ent i hi (D.compList i).length = D.ent i hi 0 := by
      rw [D.ent_inj_iff, Nat.mod_self, Nat.zero_mod]
    unfold rexB_aSeq
    rw [ite_eq_right (lt_irrefl _), hent,
      rexPL_unrot_k _ _ (rexB_coord_mem i _ (D.compOf_ent i hi 0))]

theorem rexPL_coord'_ent (hi : 0 < (D.compList i).length) (j : ℕ) (hj : j ≤ (D.compList i).length) :
    D'.visitCoord (ι.Φ (D.ent i hi j)) =
      rexB_unrot (D'.Γ.comp (ι.e i)).k (D'.visitCoord (ι.Φ (D.ent i hi 0))) (rexB_bSeq ι i hi j) := by
  rcases lt_or_eq_of_le hj with hj | rfl
  · unfold rexB_bSeq
    rw [ite_eq_left hj, rexB_unrot_rot _ _ _ (rexB_coord'_mem ι i _ (D.compOf_ent i hi j))]
  · have hent : D.ent i hi (D.compList i).length = D.ent i hi 0 := by
      rw [D.ent_inj_iff, Nat.mod_self, Nat.zero_mod]
    unfold rexB_bSeq
    rw [ite_eq_right (lt_irrefl _), hent,
      rexPL_unrot_k _ _ (rexB_coord'_mem ι i _ (D.compOf_ent i hi 0))]

/-- The affine clause in coordinates: on the closed arc from an occurrence `v` of component `i` to
its successor, the real circle map `rexB_compF` scales forward distances by the ratio of the arc
lengths. -/
theorem rexPL_compF_offset (v : D.Γ.Visit) (hv : D.compOf v = i) (x : ℝ)
    (hx : 0 ≤ x ∧ x < ((D.Γ.comp i).k : ℝ))
    (hle : Diagram.cyclicOffset (D.Γ.comp i).k (D.visitCoord v) x ≤
      rexPL_arcLen (D.Γ.comp i).k (D.visitCoord v) (D.visitCoord (D.nextVisit v))) :
    Diagram.cyclicOffset (D'.Γ.comp (ι.e i)).k (D'.visitCoord (ι.Φ v)) (rexB_compF ι i x) =
      Diagram.cyclicOffset (D.Γ.comp i).k (D.visitCoord v) x *
        (rexPL_arcLen (D'.Γ.comp (ι.e i)).k (D'.visitCoord (ι.Φ v))
            (D'.visitCoord (D'.nextVisit (ι.Φ v))) /
          rexPL_arcLen (D.Γ.comp i).k (D.visitCoord v) (D.visitCoord (D.nextVisit v))) := by
  have hi : 0 < (D.compList i).length := List.length_pos_of_mem ((D.mem_compList i v).mpr hv)
  unfold rexB_compF
  rw [dite_eq_left hi]
  obtain ⟨j, hj, rfl⟩ := D.exists_ent i hi v hv
  have G := rexB_good_marks ι i hi
  have hnext : D'.nextVisit (ι.Φ (D.ent i hi j)) = ι.Φ (D.ent i hi (j + 1)) := by
    rw [← D.nextVisit_ent i hi j]
    exact (ι.succ_eq _).symm
  rw [hnext, D.nextVisit_ent, rexPL_coord_ent i hi (j + 1) hj, rexPL_coord'_ent ι i hi (j + 1) hj,
    rexPL_coord_ent i hi j hj.le, rexPL_coord'_ent ι i hi j hj.le, rexPL_arcLen_marks G j hj,
    rexPL_arcLen_marks (rexPL_good_swap G) j hj]
  rw [D.nextVisit_ent, rexPL_coord_ent i hi (j + 1) hj, rexPL_coord_ent i hi j hj.le,
    rexPL_arcLen_marks G j hj] at hle
  simp only [← rexPL_rot_eq_cyclicOffset] at hle ⊢
  rw [rexPL_F_offset G j hj x hx hle]
  rfl

/-- "If M is empty, choose any positive circle parametrization": on a component without
occurrences the real circle map is the linear rescaling `x ↦ x · (k'/k)`. -/
theorem rexPL_compF_noOcc (hno : ∀ v : D.Γ.Visit, D.compOf v ≠ i) (x : ℝ)
    (hx : 0 ≤ x ∧ x < ((D.Γ.comp i).k : ℝ)) :
    rexB_compF ι i x = x * (((D'.Γ.comp (ι.e i)).k : ℝ) / ((D.Γ.comp i).k : ℝ)) := by
  have hi : ¬ 0 < (D.compList i).length := by
    intro h
    obtain ⟨v, hv⟩ := List.exists_mem_of_length_pos h
    exact hno v ((D.mem_compList i v).mp hv)
  unfold rexB_compF
  rw [dite_eq_right hi]
  have hk := rexB_k_pos (D.Γ.comp i)
  have hk' := rexB_k_pos (D'.Γ.comp (ι.e i))
  have G := rexB_good_triv _ _ hk hk'
  unfold rexB_F
  have hrot : rexB_rot ((D.Γ.comp i).k : ℝ) 0 x = x := by
    unfold rexB_rot
    rw [ite_eq_right (not_lt.mpr hx.1)]
    ring
  rw [hrot]
  have hpl : rexB_pl 1 (rexB_aTriv ((D.Γ.comp i).k : ℝ)) (rexB_aTriv ((D'.Γ.comp (ι.e i)).k : ℝ)) x =
      x * (((D'.Γ.comp (ι.e i)).k : ℝ) / ((D.Γ.comp i).k : ℝ)) := by
    rw [rexB_pl_eq_affine_on_piece G.ha 0 Nat.one_pos x (by rw [G.a0]; exact hx.1)
      (by rw [G.am]; exact hx.2.le)]
    unfold rexB_slope
    rw [G.a0, G.am, G.b0, G.bm]
    ring
  rw [hpl]
  have hlt : x * (((D'.Γ.comp (ι.e i)).k : ℝ) / ((D.Γ.comp i).k : ℝ)) < (D'.Γ.comp (ι.e i)).k := by
    calc x * (((D'.Γ.comp (ι.e i)).k : ℝ) / ((D.Γ.comp i).k : ℝ))
        < ((D.Γ.comp i).k : ℝ) * (((D'.Γ.comp (ι.e i)).k : ℝ) / ((D.Γ.comp i).k : ℝ)) :=
          mul_lt_mul_of_pos_right hx.2 (div_pos hk' hk)
      _ = (D'.Γ.comp (ι.e i)).k := by rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hk.ne', mul_one]
  unfold rexB_unrot
  rw [ite_eq_left (by linarith)]
  ring

/-- The mark clause on traversal points (the second clause of `ExtendsToCircleMaps`, isolated). -/
theorem rexPL_compEquiv_visitPt (v : D.Γ.Visit) :
    (⟨ι.e (D.visitPt v).1, rexB_compEquiv ι (D.visitPt v).1 (D.visitPt v).2⟩ : D'.Γ.Pt) =
      D'.visitPt (ι.Φ v) := by
  have hc : (D'.visitPt (ι.Φ v)).1 = ι.e (D.visitPt v).1 := ι.comp_eq v
  have hk : traversalKey (rexB_compEquiv ι (D.visitPt v).1 (D.visitPt v).2) =
      traversalKey (D'.visitPt (ι.Φ v)).2 := by
    rw [rexB_compEquiv_key]
    exact rexB_compF_mark ι (D.visitPt v).1 v rfl
  generalize D'.visitPt (ι.Φ v) = p' at hc hk ⊢
  obtain ⟨i', q'⟩ := p'
  dsimp only at hc hk
  subst hc
  rw [traversalKey_injective hk]

end ComponentPL

/-! ## 9. The extension theorem with the affine clause -/

/-- The printed witness satisfies the full clause of sm-3:365-369: orientation preserving, extending
`Φ`, affine in oriented interval coordinates on each arc between successive marks, and the linear
rescaling on mark-free circles. -/
theorem rexPL_extendsPiecewiseAffine {D D' : Diagram} (ι : RecordIso D.record D'.record) :
    ι.ExtendsPiecewiseAffine := by
  refine ⟨fun i => rexB_compEquiv ι i, ?_, ?_, ?_, ?_⟩
  · intro i p q r h
    exact rexB_compEquiv_between ι i p q r h
  · intro v
    exact rexPL_compEquiv_visitPt ι v
  · intro i v hv p hle
    rw [rexB_compEquiv_key]
    exact rexPL_compF_offset ι i v hv (traversalKey p)
      ⟨traversalKey_nonneg p, Diagram.traversalKey_lt_card p⟩ hle
  · intro i hno p
    rw [rexB_compEquiv_key]
    exact rexPL_compF_noOcc ι i hno (traversalKey p)
      ⟨traversalKey_nonneg p, Diagram.traversalKey_lt_card p⟩

/-- The extension theorem of def:gauss-record with the piecewise-affine clause (sm-3:365-369). -/
theorem rexB_recordIso_extend_pl :
    ∀ (D D' : Diagram) (ι : RecordIso D.record D'.record), ι.ExtendsPiecewiseAffine :=
  fun _ _ ι => rexPL_extendsPiecewiseAffine ι

/-- Sanity: the affine version recovers `recordIso_extend_statement`. -/
theorem rexPL_recordIso_extend_of_pl : recordIso_extend_statement :=
  fun D D' ι => (rexB_recordIso_extend_pl D D' ι).toExtendsToCircleMaps

end

end SM.Link

