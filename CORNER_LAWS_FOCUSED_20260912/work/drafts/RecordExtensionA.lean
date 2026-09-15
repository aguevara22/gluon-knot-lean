import SM.LinkDiagramRecord

/-! # The piecewise-linear extension Φ̄ of a named record isomorphism (`recordIso_extend_statement`)

Proof of the PL-extension clause of def:gauss-record (reference/SM/sm-3-statesum.tex 365-369):

"After a finite subdivision we choose an orientation-preserving piecewise-linear circle map
Φ̄ : C → C' extending Φ: on each interval between successive marked points use the positive affine
map in oriented interval coordinates. If M is empty, choose any positive circle parametrization."

Model (SM/LinkDiagramRecord, section H): the parameter circle of component `i` is
`TraversalPoint (D.Γ.comp i).k`, identified with the key circle `[0, k)` by `traversalKey`
(`rexA_keyEquiv`); its oriented cyclic order is `traversalBetween` = `cycBetween` of the keys; the
marks of component `i` are the occurrences `v` with `D.compOf v = i`, sitting at the key
`D.visitCoord v`, enumerated in key order by `D.ent i hi`.

Construction, for one component `i` with occurrence list of length `n`:
* `n = 0` ("If M is empty"): the positive linear rescaling `[0, k) → [0, k')`, `x ↦ x k'/k`
  (the piecewise-affine map with the single knot pair `(0, 0), (k, k')`).
* `n ≥ 1`: rotate `[0, k)` so that the first mark `a₀` goes to `0` (`rexA_rotTo k a₀`), rotate
  `[0, k')` so that its image mark `b₀ = visitCoord (Φ v₀)` goes to `0`; in these coordinates the
  marks are `0 = ã₀ < ã₁ < … < ã_{n-1}` and, because `ι` preserves the oriented cyclic order on the
  component (`RecordIso.visitBetween_iff`), their images are `0 = b̃₀ < b̃₁ < … < b̃_{n-1}` in the
  same order.  The strictly increasing piecewise-affine map `rexA_pl` with knots
  `(ã_j, b̃_j)_{j<n}, (k, k')` ("on each interval between successive marked points use the positive
  affine map in oriented interval coordinates") is a bijection `[0, k) → [0, k')` (strictly
  monotone, continuous, so onto by the intermediate value theorem); undoing the second rotation
  gives the circle map, which is orientation preserving (a composite of rotations and a strictly
  increasing map, each of which preserves `cycBetween`) and carries every mark to its `Φ`-image.

Main results: `RecordIso.rexA_component_key_map` (the key-level circle map of one component),
`RecordIso.rexA_extendsToCircleMaps` (`ι.ExtendsToCircleMaps` for every `ι`) and
`rexA_recordIso_extend : recordIso_extend_statement`.  Helper names are prefixed `rexA_`. -/

namespace SM.Link

open SM Equiv Finset

noncomputable section

/-! ## A. Real-level toolkit: the cyclic order on `[0, k)` -/

theorem rexA_cycBetween_zero {y z : ℝ} (hz : 0 ≤ z) (h : cycBetween 0 y z) :
    0 < y ∧ y < z := by
  unfold cycBetween at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · exact absurd (lt_of_le_of_lt hz h2) (lt_irrefl 0)
  · exact absurd (lt_of_le_of_lt hz h1) (lt_irrefl 0)

theorem rexA_cycBetween_of_lt {a b c : ℝ} (h1 : a < b) (h2 : b < c) : cycBetween a b c :=
  Or.inl ⟨h1, h2⟩

/-- A strictly monotone map on a set preserves the strict cyclic order of its points. -/
theorem rexA_cycBetween_of_strictMonoOn {g : ℝ → ℝ} {S : Set ℝ} (hg : StrictMonoOn g S)
    {a b c : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (h : cycBetween a b c) :
    cycBetween (g a) (g b) (g c) := by
  unfold cycBetween at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hg ha hb h1, hg hb hc h2⟩
  · exact Or.inr (Or.inl ⟨hg hb hc h1, hg hc ha h2⟩)
  · exact Or.inr (Or.inr ⟨hg hc ha h1, hg ha hb h2⟩)

/-! ### Rotations of the parameter circle `[0, k)` -/

/-- The rotation of the circle `[0, k)` carrying the point `a` to `0` (forward traversal distance
from `a`): `x ↦ x - a` for `a ≤ x`, `x ↦ x - a + k` for `x < a`. -/
def rexA_rotFun (k a x : ℝ) : ℝ := if x < a then x - a + k else x - a

theorem rexA_rotFun_self (k a : ℝ) : rexA_rotFun k a a = 0 := by
  simp [rexA_rotFun]

theorem rexA_rotFun_mem {k a x : ℝ} (ha : 0 ≤ a) (hak : a ≤ k) (hx : x ∈ Set.Ico (0 : ℝ) k) :
    rexA_rotFun k a x ∈ Set.Ico (0 : ℝ) k := by
  obtain ⟨hx0, hxk⟩ := hx
  unfold rexA_rotFun
  split_ifs with h
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩

/-- The rotation carrying `k - a` to `0` undoes the rotation carrying `a` to `0`. -/
theorem rexA_rotFun_rotFun {k a x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) k) :
    rexA_rotFun k (k - a) (rexA_rotFun k a x) = x := by
  obtain ⟨hx0, hxk⟩ := hx
  unfold rexA_rotFun
  split_ifs with h1 h2 h2 <;> linarith

theorem rexA_rotFun_eq_zero_iff {k a x : ℝ} (hak : a < k) (hx : x ∈ Set.Ico (0 : ℝ) k) :
    rexA_rotFun k a x = 0 ↔ x = a := by
  obtain ⟨hx0, hxk⟩ := hx
  unfold rexA_rotFun
  split_ifs with h
  · constructor
    · intro h'; linarith
    · intro h'; linarith
  · constructor
    · intro h'; linarith
    · intro h'; linarith

/-- On the arc `[a, k)` the rotation is the increasing translation `x ↦ x - a`. -/
theorem rexA_rotFun_lt_of_le {k a x y : ℝ} (hax : a ≤ x) (hxy : x < y) :
    rexA_rotFun k a x < rexA_rotFun k a y := by
  unfold rexA_rotFun
  split_ifs with h1 h2 h2 <;> linarith

/-- Rotations preserve the strict cyclic order on `[0, k)`. -/
theorem rexA_cycBetween_rotFun {k a x y z : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) k) (hy : y ∈ Set.Ico (0 : ℝ) k) (hz : z ∈ Set.Ico (0 : ℝ) k)
    (h : cycBetween x y z) :
    cycBetween (rexA_rotFun k a x) (rexA_rotFun k a y) (rexA_rotFun k a z) := by
  obtain ⟨hx0, hxk⟩ := hx
  obtain ⟨hy0, hyk⟩ := hy
  obtain ⟨hz0, hzk⟩ := hz
  unfold cycBetween at h ⊢
  unfold rexA_rotFun
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> split_ifs <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

/-- The rotation carrying `a` to `0` as a bijection of the circle `[0, k)`; its inverse is the
rotation carrying `k - a` to `0`. -/
def rexA_rotTo (k a : ℝ) (ha : 0 ≤ a) (hak : a ≤ k) : Set.Ico (0 : ℝ) k ≃ Set.Ico (0 : ℝ) k where
  toFun x := ⟨rexA_rotFun k a x.1, rexA_rotFun_mem ha hak x.2⟩
  invFun y := ⟨rexA_rotFun k (k - a) y.1, rexA_rotFun_mem (by linarith) (by linarith) y.2⟩
  left_inv x := Subtype.ext (rexA_rotFun_rotFun x.2)
  right_inv y := Subtype.ext (by
    have h := rexA_rotFun_rotFun (k := k) (a := k - a) y.2
    rwa [sub_sub_cancel] at h)

@[simp] theorem rexA_rotTo_apply_val (k a : ℝ) (ha : 0 ≤ a) (hak : a ≤ k) (x : Set.Ico (0 : ℝ) k) :
    (rexA_rotTo k a ha hak x).1 = rexA_rotFun k a x.1 := rfl

@[simp] theorem rexA_rotTo_symm_apply_val (k a : ℝ) (ha : 0 ≤ a) (hak : a ≤ k)
    (y : Set.Ico (0 : ℝ) k) : ((rexA_rotTo k a ha hak).symm y).1 = rexA_rotFun k (k - a) y.1 := rfl

/-! ## B. Piecewise-affine interpolation through knots

"on each interval between successive marked points use the positive affine map in oriented
interval coordinates": the map with knots `(X j, Y j)`, `j = 0, …, m`, is written as a sum of
clamped hinge terms, one per interval, so that continuity and monotonicity are termwise. -/

/-- The clamp of `x` to the interval `[lo, hi]`. -/
def rexA_clamp (lo hi x : ℝ) : ℝ := min (max x lo) hi

theorem rexA_clamp_of_le_left {lo hi x : ℝ} (hlo : lo ≤ hi) (hx : x ≤ lo) : rexA_clamp lo hi x = lo := by
  unfold rexA_clamp
  rw [max_eq_right hx, min_eq_left hlo]

theorem rexA_clamp_of_le_right {lo hi x : ℝ} (hlo : lo ≤ hi) (hx : hi ≤ x) : rexA_clamp lo hi x = hi := by
  unfold rexA_clamp
  rw [max_eq_left (hlo.trans hx), min_eq_right hx]

theorem rexA_clamp_of_mem {lo hi x : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) : rexA_clamp lo hi x = x := by
  unfold rexA_clamp
  rw [max_eq_left h1, min_eq_left h2]

theorem rexA_clamp_mono (lo hi : ℝ) : Monotone (rexA_clamp lo hi) := by
  intro x y hxy
  unfold rexA_clamp
  exact min_le_min_right _ (max_le_max_right _ hxy)

theorem rexA_clamp_continuous (lo hi : ℝ) : Continuous (rexA_clamp lo hi) :=
  (continuous_id.max continuous_const).min continuous_const

/-- The piecewise-affine function with knots `(X j, Y j)`, `j = 0, …, m`: on `[X j, X (j+1)]` it
is the positive affine map onto `[Y j, Y (j+1)]` (as a sum of clamped hinge terms; its value at
`X 0` is `0`, so the knot values are `Y j - Y 0`). -/
def rexA_pl (m : ℕ) (X Y : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ range m, (Y (j + 1) - Y j) / (X (j + 1) - X j) * (rexA_clamp (X j) (X (j + 1)) x - X j)

theorem rexA_pl_continuous (m : ℕ) (X Y : ℕ → ℝ) : Continuous (rexA_pl m X Y) := by
  unfold rexA_pl
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((rexA_clamp_continuous _ _).sub continuous_const)

section Knots

variable (m : ℕ) (X Y : ℕ → ℝ)
    (hX : ∀ a b, a < b → b ≤ m → X a < X b) (hY : ∀ a b, a < b → b ≤ m → Y a < Y b)

include hX hY in
theorem rexA_pl_monotone : Monotone (rexA_pl m X Y) := by
  intro x y hxy
  unfold rexA_pl
  apply Finset.sum_le_sum
  intro j hj
  have hj' : j + 1 ≤ m := Finset.mem_range.mp hj
  have hXj : X j < X (j + 1) := hX j (j + 1) (Nat.lt_succ_self j) hj'
  have hYj : Y j < Y (j + 1) := hY j (j + 1) (Nat.lt_succ_self j) hj'
  have hslope : 0 ≤ (Y (j + 1) - Y j) / (X (j + 1) - X j) :=
    div_nonneg (by linarith) (by linarith)
  apply mul_le_mul_of_nonneg_left _ hslope
  have := rexA_clamp_mono (X j) (X (j + 1)) hxy
  linarith

include hX in
/-- The value at the knots: `pl (X i) = Y i - Y 0`. -/
theorem rexA_pl_knot (i : ℕ) (hi : i ≤ m) : rexA_pl m X Y (X i) = Y i - Y 0 := by
  unfold rexA_pl
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun j => (Y (j + 1) - Y j) / (X (j + 1) - X j) * (rexA_clamp (X j) (X (j + 1)) (X i) - X j)) hi
  rw [← hsplit]
  have h1 : ∑ j ∈ range i, (Y (j + 1) - Y j) / (X (j + 1) - X j) *
      (rexA_clamp (X j) (X (j + 1)) (X i) - X j) = ∑ j ∈ range i, (Y (j + 1) - Y j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j + 1 ≤ i := Finset.mem_range.mp hj
    have hXj : X j < X (j + 1) := hX j (j + 1) (Nat.lt_succ_self j) (hj'.trans hi)
    have hXi : X (j + 1) ≤ X i := by
      rcases Nat.lt_or_ge (j + 1) i with h | h
      · exact (hX _ _ h hi).le
      · have : j + 1 = i := le_antisymm hj' h
        rw [this]
    rw [rexA_clamp_of_le_right hXj.le hXi]
    have hne : X (j + 1) - X j ≠ 0 := by linarith
    field_simp
  have h2 : ∑ j ∈ Ico i m, (Y (j + 1) - Y j) / (X (j + 1) - X j) *
      (rexA_clamp (X j) (X (j + 1)) (X i) - X j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    obtain ⟨hij, hjm⟩ := Finset.mem_Ico.mp hj
    have hXj : X j < X (j + 1) := hX j (j + 1) (Nat.lt_succ_self j) hjm
    have hXi : X i ≤ X j := by
      rcases Nat.lt_or_ge i j with h | h
      · exact (hX _ _ h (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hjm))).le
      · have : i = j := le_antisymm hij h
        rw [this]
    rw [rexA_clamp_of_le_left hXj.le hXi, sub_self, mul_zero]
  rw [h1, h2, add_zero, Finset.sum_range_sub]

/-- Locating the piece containing a point of `[X 0, X m)` (no monotonicity needed). -/
theorem rexA_exists_piece (x : ℝ) (hx0 : X 0 ≤ x) (hxm : x < X m) :
    ∃ j, j < m ∧ X j ≤ x ∧ x < X (j + 1) := by
  induction m with
  | zero => exact absurd (lt_of_le_of_lt hx0 hxm) (lt_irrefl (X 0))
  | succ n ih =>
    rcases lt_or_ge x (X n) with h | h
    · obtain ⟨j, hj, hj1, hj2⟩ := ih h
      exact ⟨j, Nat.lt_succ_of_lt hj, hj1, hj2⟩
    · exact ⟨n, Nat.lt_succ_self n, h, hxm⟩

include hX hY in
/-- Strict monotonicity on `[X 0, X m]`: the piece containing the smaller point contributes a
strictly increasing affine term, all other terms are monotone. -/
theorem rexA_pl_strictMonoOn : StrictMonoOn (rexA_pl m X Y) (Set.Icc (X 0) (X m)) := by
  intro x hx y hy hxy
  obtain ⟨j, hjm, hj1, hj2⟩ := rexA_exists_piece m X x hx.1 (lt_of_lt_of_le hxy hy.2)
  unfold rexA_pl
  apply Finset.sum_lt_sum
  · intro l hl
    have hl' : l + 1 ≤ m := Finset.mem_range.mp hl
    have hXl : X l < X (l + 1) := hX l (l + 1) (Nat.lt_succ_self l) hl'
    have hYl : Y l < Y (l + 1) := hY l (l + 1) (Nat.lt_succ_self l) hl'
    have hslope : 0 ≤ (Y (l + 1) - Y l) / (X (l + 1) - X l) :=
      div_nonneg (by linarith) (by linarith)
    apply mul_le_mul_of_nonneg_left _ hslope
    have := rexA_clamp_mono (X l) (X (l + 1)) hxy.le
    linarith
  · refine ⟨j, Finset.mem_range.mpr hjm, ?_⟩
    have hXj : X j < X (j + 1) := hX j (j + 1) (Nat.lt_succ_self j) hjm
    have hYj : Y j < Y (j + 1) := hY j (j + 1) (Nat.lt_succ_self j) hjm
    have hslope : 0 < (Y (j + 1) - Y j) / (X (j + 1) - X j) :=
      div_pos (by linarith) (by linarith)
    apply mul_lt_mul_of_pos_left _ hslope
    rw [rexA_clamp_of_mem hj1 hj2.le]
    unfold rexA_clamp
    rw [max_eq_left (hj1.trans hxy.le)]
    have : x < min y (X (j + 1)) := lt_min hxy hj2
    linarith

include hX hY in
/-- The image of `[X 0, X m)` is `[0, Y m)` (monotonicity for `⊆`, the intermediate value theorem
for `⊇`). -/
theorem rexA_pl_image (hY0 : Y 0 = 0) :
    rexA_pl m X Y '' Set.Ico (X 0) (X m) = Set.Ico 0 (Y m) := by
  have hsm := rexA_pl_strictMonoOn m X Y hX hY
  have h0m : X 0 ≤ X m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0]
    · exact (hX 0 m h0 le_rfl).le
  have hk0 : rexA_pl m X Y (X 0) = 0 := by rw [rexA_pl_knot m X Y hX 0 (Nat.zero_le m), sub_self]
  have hkm : rexA_pl m X Y (X m) = Y m := by rw [rexA_pl_knot m X Y hX m le_rfl, hY0, sub_zero]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxI : x ∈ Set.Icc (X 0) (X m) := ⟨hx.1, hx.2.le⟩
    constructor
    · rw [← hk0]
      exact hsm.monotoneOn ⟨le_rfl, h0m⟩ hxI hx.1
    · rw [← hkm]
      exact hsm hxI ⟨h0m, le_rfl⟩ hx.2
  · intro y hy
    have hy' : y ∈ Set.Icc (rexA_pl m X Y (X 0)) (rexA_pl m X Y (X m)) := by
      rw [hk0, hkm]; exact ⟨hy.1, hy.2.le⟩
    obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc h0m (rexA_pl_continuous m X Y).continuousOn hy'
    refine ⟨x, ⟨hx.1, ?_⟩, hxy⟩
    rcases lt_or_eq_of_le hx.2 with h | h
    · exact h
    · exfalso
      rw [h, hkm] at hxy
      exact absurd hy.2 (not_lt.mpr hxy.le)

end Knots

/-! ## C. Bijections of parameter circles -/

/-- A strictly increasing map of `[0, k)` onto `[0, k')` as a bijection of the two circles. -/
def rexA_equivOfStrictMono {k k' : ℝ} (g : ℝ → ℝ) (hg : StrictMonoOn g (Set.Ico 0 k))
    (himg : g '' Set.Ico 0 k = Set.Ico 0 k') : Set.Ico (0 : ℝ) k ≃ Set.Ico (0 : ℝ) k' :=
  Equiv.ofBijective (fun x => ⟨g x.1, by rw [← himg]; exact Set.mem_image_of_mem g x.2⟩)
    ⟨fun x y h => Subtype.ext (hg.injOn x.2 y.2 (congrArg Subtype.val h)),
     fun y => by
      have hy : y.1 ∈ g '' Set.Ico 0 k := by rw [himg]; exact y.2
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

@[simp] theorem rexA_equivOfStrictMono_apply_val {k k' : ℝ} (g : ℝ → ℝ)
    (hg : StrictMonoOn g (Set.Ico 0 k)) (himg : g '' Set.Ico 0 k = Set.Ico 0 k')
    (x : Set.Ico (0 : ℝ) k) : (rexA_equivOfStrictMono g hg himg x).1 = g x.1 := rfl

/-- Traversal points of a circle with `n ≥ 1` edges are the key coordinates `[0, n)`
(`traversalKey p = label + parameter` is a bijection onto `[0, n)`). -/
def rexA_keyEquiv (n : ℕ) [NeZero n] : TraversalPoint n ≃ Set.Ico (0 : ℝ) n where
  toFun p := ⟨traversalKey p, traversalKey_nonneg p, traversalKey_lt_size p⟩
  invFun x := ((⌊x.1⌋₊ : ZMod n), ⟨x.1 - ⌊x.1⌋₊, by
    have h1 := Nat.floor_le x.2.1
    have h2 := Nat.lt_floor_add_one x.1
    exact ⟨by linarith, by linarith⟩⟩)
  left_inv p := by
    obtain ⟨i, s, hs0, hs1⟩ := p
    have hfl : ⌊traversalKey (i, ⟨s, hs0, hs1⟩)⌋₊ = i.val := by
      rw [Nat.floor_eq_iff (traversalKey_nonneg _)]
      unfold traversalKey
      dsimp only
      exact ⟨by linarith, by linarith⟩
    apply Prod.ext
    · show ((⌊traversalKey (i, ⟨s, hs0, hs1⟩)⌋₊ : ℕ) : ZMod n) = i
      rw [hfl, ZMod.natCast_zmod_val]
    · apply Subtype.ext
      show traversalKey (i, ⟨s, hs0, hs1⟩) - (⌊traversalKey (i, ⟨s, hs0, hs1⟩)⌋₊ : ℝ) = s
      rw [hfl]
      unfold traversalKey
      dsimp only
      ring
  right_inv x := by
    apply Subtype.ext
    show traversalKey ((⌊x.1⌋₊ : ZMod n), _) = x.1
    unfold traversalKey
    dsimp only
    have hlt : ⌊x.1⌋₊ < n := (Nat.floor_lt x.2.1).mpr x.2.2
    rw [ZMod.val_natCast_of_lt hlt]
    ring

@[simp] theorem rexA_keyEquiv_apply_val (n : ℕ) [NeZero n] (p : TraversalPoint n) :
    (rexA_keyEquiv n p).1 = traversalKey p := rfl

theorem rexA_traversalKey_keyEquiv_symm (n : ℕ) [NeZero n] (x : Set.Ico (0 : ℝ) n) :
    traversalKey ((rexA_keyEquiv n).symm x) = x.1 := by
  have h := (rexA_keyEquiv n).apply_symm_apply x
  rw [Subtype.ext_iff] at h
  exact h

/-- Transport of a bijection of key circles to a bijection of traversal points. -/
def rexA_ptEquiv {n n' : ℕ} [NeZero n] [NeZero n'] (F : Set.Ico (0 : ℝ) n ≃ Set.Ico (0 : ℝ) n') :
    TraversalPoint n ≃ TraversalPoint n' :=
  (rexA_keyEquiv n).trans (F.trans (rexA_keyEquiv n').symm)

theorem rexA_traversalKey_ptEquiv {n n' : ℕ} [NeZero n] [NeZero n']
    (F : Set.Ico (0 : ℝ) n ≃ Set.Ico (0 : ℝ) n') (p : TraversalPoint n) :
    traversalKey (rexA_ptEquiv F p) = (F (rexA_keyEquiv n p)).1 := by
  unfold rexA_ptEquiv
  rw [Equiv.trans_apply, Equiv.trans_apply, rexA_traversalKey_keyEquiv_symm]

/-- A key-level bijection preserving `cycBetween` gives an orientation-preserving circle map. -/
theorem rexA_traversalBetween_ptEquiv {n n' : ℕ} [NeZero n] [NeZero n']
    (F : Set.Ico (0 : ℝ) n ≃ Set.Ico (0 : ℝ) n')
    (hF : ∀ a b c, cycBetween a.1 b.1 c.1 → cycBetween (F a).1 (F b).1 (F c).1)
    (p q r : TraversalPoint n) (h : traversalBetween p q r) :
    traversalBetween (rexA_ptEquiv F p) (rexA_ptEquiv F q) (rexA_ptEquiv F r) := by
  rw [traversalBetween_iff_cycBetween] at h ⊢
  rw [rexA_traversalKey_ptEquiv, rexA_traversalKey_ptEquiv, rexA_traversalKey_ptEquiv]
  exact hF _ _ _ h

/-- Points of a shadow's parameter circles are determined by component and key. -/
theorem rexA_pt_ext {Γ : Shadow} (P Q : Γ.Pt) (h1 : P.1 = Q.1)
    (h2 : traversalKey P.2 = traversalKey Q.2) : P = Q := by
  obtain ⟨i, p⟩ := P
  obtain ⟨j, q⟩ := Q
  dsimp only at h1 h2
  subst h1
  exact Sigma.ext rfl (heq_of_eq (traversalKey_injective h2))

/-- The key of an occurrence of component `i` lies on the key circle `[0, k_i)`. -/
theorem rexA_visitCoord_mem (D : Diagram) (v : D.Γ.Visit) {i : Fin D.Γ.c} (h : D.compOf v = i) :
    D.visitCoord v ∈ Set.Ico (0 : ℝ) ((D.Γ.comp i).k : ℝ) := by
  refine ⟨D.visitCoord_nonneg v, ?_⟩
  have := D.visitCoord_lt v
  rwa [h] at this

/-! ## D. The circle map of one component and the extension theorem -/

namespace RecordIso

variable {D D' : Diagram} (ι : RecordIso D.record D'.record)

theorem rexA_compOf_Φ (v : D.Γ.Visit) : D'.compOf (ι.Φ v) = ι.e (D.compOf v) := ι.comp_eq v

theorem rexA_visitCoord_Φ_mem (v : D.Γ.Visit) {i : Fin D.Γ.c} (h : D.compOf v = i) :
    D'.visitCoord (ι.Φ v) ∈ Set.Ico (0 : ℝ) ((D'.Γ.comp (ι.e i)).k : ℝ) := by
  refine ⟨D'.visitCoord_nonneg _, ?_⟩
  have := D'.visitCoord_lt (ι.Φ v)
  rwa [rexA_compOf_Φ, h] at this

/-- The key-level circle map of component `i`: a bijection `[0, k_i) ≃ [0, k'_{e i})` preserving
the strict cyclic order and carrying the key of every occurrence of component `i` to the key of
its `Φ`-image (def:gauss-record sm-3:365-369, in key coordinates). -/
theorem rexA_component_key_map (i : Fin D.Γ.c) :
    ∃ F : Set.Ico (0 : ℝ) ((D.Γ.comp i).k : ℝ) ≃ Set.Ico (0 : ℝ) ((D'.Γ.comp (ι.e i)).k : ℝ),
      (∀ a b c, cycBetween a.1 b.1 c.1 → cycBetween (F a).1 (F b).1 (F c).1) ∧
      ∀ v : D.Γ.Visit, D.compOf v = i →
        ∀ hv : D.visitCoord v ∈ Set.Ico (0 : ℝ) ((D.Γ.comp i).k : ℝ),
          (F ⟨D.visitCoord v, hv⟩).1 = D'.visitCoord (ι.Φ v) := by
  have hk : (0 : ℝ) < ((D.Γ.comp i).k : ℝ) := by
    have := (D.Γ.comp i).hk
    exact_mod_cast (show 0 < (D.Γ.comp i).k by omega)
  have hk' : (0 : ℝ) < ((D'.Γ.comp (ι.e i)).k : ℝ) := by
    have := (D'.Γ.comp (ι.e i)).hk
    exact_mod_cast (show 0 < (D'.Γ.comp (ι.e i)).k by omega)
  rcases Nat.eq_zero_or_pos (D.compList i).length with hn | hi
  · -- "If M is empty, choose any positive circle parametrization": the linear rescaling.
    let X : ℕ → ℝ := fun j => (j : ℝ) * ((D.Γ.comp i).k : ℝ)
    let Y : ℕ → ℝ := fun j => (j : ℝ) * ((D'.Γ.comp (ι.e i)).k : ℝ)
    have hX : ∀ a b, a < b → b ≤ 1 → X a < X b := fun a b hab _ => by
      simp only [X]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hab) hk
    have hY : ∀ a b, a < b → b ≤ 1 → Y a < Y b := fun a b hab _ => by
      simp only [Y]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hab) hk'
    have hX0 : X 0 = 0 := by simp [X]
    have hX1 : X 1 = ((D.Γ.comp i).k : ℝ) := by simp [X]
    have hY0 : Y 0 = 0 := by simp [Y]
    have hY1 : Y 1 = ((D'.Γ.comp (ι.e i)).k : ℝ) := by simp [Y]
    have hsm := rexA_pl_strictMonoOn 1 X Y hX hY
    rw [hX0, hX1] at hsm
    have himg := rexA_pl_image 1 X Y hX hY hY0
    rw [hX0, hX1, hY1] at himg
    have hsm' := hsm.mono Set.Ico_subset_Icc_self
    refine ⟨rexA_equivOfStrictMono _ hsm' himg, ?_, ?_⟩
    · intro a b c h
      simp only [rexA_equivOfStrictMono_apply_val]
      exact rexA_cycBetween_of_strictMonoOn hsm' a.2 b.2 c.2 h
    · intro v hv _
      exfalso
      have hmem := (D.mem_compList i v).mpr hv
      rw [List.eq_nil_of_length_eq_zero hn] at hmem
      exact List.not_mem_nil hmem
  · -- Marks present: rotate both circles so that the first mark and its image sit at `0`,
    -- interpolate affinely between successive marks, rotate back.
    let A : ℕ → ℝ := fun j => D.visitCoord (D.ent i hi j)
    let B : ℕ → ℝ := fun j => D'.visitCoord (ι.Φ (D.ent i hi j))
    have hA_mem : ∀ j, A j ∈ Set.Ico (0 : ℝ) ((D.Γ.comp i).k : ℝ) := fun j =>
      rexA_visitCoord_mem D _ (D.compOf_ent i hi j)
    have hB_mem : ∀ j, B j ∈ Set.Ico (0 : ℝ) ((D'.Γ.comp (ι.e i)).k : ℝ) := fun j =>
      ι.rexA_visitCoord_Φ_mem _ (D.compOf_ent i hi j)
    have hA_lt : ∀ a b, a < b → b < (D.compList i).length → A a < A b := fun a b hab hb => by
      simp only [A]
      rw [D.visitCoord_ent_lt_iff, Nat.mod_eq_of_lt (hab.trans hb), Nat.mod_eq_of_lt hb]
      exact hab
    have hA0_le : ∀ a, a < (D.compList i).length → A 0 ≤ A a := fun a ha => by
      rcases Nat.eq_zero_or_pos a with h | h
      · rw [h]
      · exact (hA_lt 0 a h ha).le
    have hB_ne : ∀ b, 0 < b → b < (D.compList i).length → B b ≠ B 0 := fun b hb0 hbn heq => by
      have hc : D'.compOf (ι.Φ (D.ent i hi b)) = D'.compOf (ι.Φ (D.ent i hi 0)) := by
        rw [rexA_compOf_Φ, rexA_compOf_Φ, D.compOf_ent, D.compOf_ent]
      have h1 := D'.visitCoord_injOn hc heq
      have h2 := ι.Φ.injective h1
      rw [D.ent_inj_iff, Nat.mod_eq_of_lt hbn, Nat.zero_mod] at h2
      omega
    -- the knots in rotated coordinates
    let X : ℕ → ℝ := fun j =>
      if j < (D.compList i).length then rexA_rotFun ((D.Γ.comp i).k : ℝ) (A 0) (A j)
      else ((D.Γ.comp i).k : ℝ)
    let Y : ℕ → ℝ := fun j =>
      if j < (D.compList i).length then rexA_rotFun ((D'.Γ.comp (ι.e i)).k : ℝ) (B 0) (B j)
      else ((D'.Γ.comp (ι.e i)).k : ℝ)
    have hX0 : X 0 = 0 := by simp only [X, ite_eq_left hi, rexA_rotFun_self]
    have hXn : X (D.compList i).length = ((D.Γ.comp i).k : ℝ) := by
      simp only [X, lt_irrefl, ite_false]
    have hY0 : Y 0 = 0 := by simp only [Y, ite_eq_left hi, rexA_rotFun_self]
    have hYn : Y (D.compList i).length = ((D'.Γ.comp (ι.e i)).k : ℝ) := by
      simp only [Y, lt_irrefl, ite_false]
    have hXmem : ∀ j, j < (D.compList i).length → X j ∈ Set.Ico (0 : ℝ) ((D.Γ.comp i).k : ℝ) :=
      fun j hj => by
        simp only [X, ite_eq_left hj]
        exact rexA_rotFun_mem (hA_mem 0).1 (hA_mem 0).2.le (hA_mem j)
    have hYmem : ∀ j, j < (D.compList i).length →
        Y j ∈ Set.Ico (0 : ℝ) ((D'.Γ.comp (ι.e i)).k : ℝ) := fun j hj => by
      simp only [Y, ite_eq_left hj]
      exact rexA_rotFun_mem (hB_mem 0).1 (hB_mem 0).2.le (hB_mem j)
    have hX : ∀ a b, a < b → b ≤ (D.compList i).length → X a < X b := fun a b hab hbn => by
      rcases lt_or_eq_of_le hbn with hb | hb
      · have ha : a < (D.compList i).length := hab.trans hb
        simp only [X, ite_eq_left ha, ite_eq_left hb]
        exact rexA_rotFun_lt_of_le (hA0_le a ha) (hA_lt a b hab hb)
      · rw [hb, hXn]
        exact (hXmem a (hb ▸ hab)).2
    -- the images of the marks are in the same order: cyclic-order preservation of `ι`
    have hY : ∀ a b, a < b → b ≤ (D.compList i).length → Y a < Y b := fun a b hab hbn => by
      rcases lt_or_eq_of_le hbn with hb | hb
      · have ha : a < (D.compList i).length := hab.trans hb
        rcases Nat.eq_zero_or_pos a with ha0 | ha0
        · rw [ha0, hY0]
          have hmem := hYmem b hb
          rcases lt_or_eq_of_le hmem.1 with h | h
          · exact h
          · exfalso
            simp only [Y, ite_eq_left hb] at h
            have := (rexA_rotFun_eq_zero_iff (hB_mem 0).2 (hB_mem b)).mp h.symm
            exact hB_ne b (ha0 ▸ hab) hb this
        · have hD : D.VisitBetween (D.ent i hi 0) (D.ent i hi a) (D.ent i hi b) :=
            rexA_cycBetween_of_lt (hA_lt 0 a ha0 ha) (hA_lt a b hab hb)
          have hD' := (ι.visitBetween_iff (D.ent i hi 0) (D.ent i hi a) (D.ent i hi b)
            ((D.compOf_ent i hi a).trans (D.compOf_ent i hi 0).symm)
            ((D.compOf_ent i hi b).trans (D.compOf_ent i hi 0).symm)).mpr hD
          have hc : cycBetween (rexA_rotFun ((D'.Γ.comp (ι.e i)).k : ℝ) (B 0) (B 0))
              (rexA_rotFun ((D'.Γ.comp (ι.e i)).k : ℝ) (B 0) (B a))
              (rexA_rotFun ((D'.Γ.comp (ι.e i)).k : ℝ) (B 0) (B b)) :=
            rexA_cycBetween_rotFun (hB_mem 0) (hB_mem a) (hB_mem b) hD'
          rw [rexA_rotFun_self] at hc
          simp only [Y, ite_eq_left ha, ite_eq_left hb]
          exact (rexA_cycBetween_zero
            (rexA_rotFun_mem (hB_mem 0).1 (hB_mem 0).2.le (hB_mem b)).1 hc).2
      · rw [hb, hYn]
        exact (hYmem a (hb ▸ hab)).2
    -- the piecewise-affine map in rotated coordinates
    have hsm := rexA_pl_strictMonoOn _ X Y hX hY
    rw [hX0, hXn] at hsm
    have himg := rexA_pl_image _ X Y hX hY hY0
    rw [hX0, hXn, hYn] at himg
    have hsm' := hsm.mono Set.Ico_subset_Icc_self
    refine ⟨(rexA_rotTo _ (A 0) (hA_mem 0).1 (hA_mem 0).2.le).trans
      ((rexA_equivOfStrictMono _ hsm' himg).trans
        (rexA_rotTo _ (B 0) (hB_mem 0).1 (hB_mem 0).2.le).symm), ?_, ?_⟩
    · intro a b c h
      simp only [Equiv.trans_apply, rexA_rotTo_symm_apply_val, rexA_equivOfStrictMono_apply_val,
        rexA_rotTo_apply_val]
      apply rexA_cycBetween_rotFun
        (rexA_equivOfStrictMono _ hsm' himg (rexA_rotTo _ (A 0) (hA_mem 0).1 (hA_mem 0).2.le a)).2
        (rexA_equivOfStrictMono _ hsm' himg (rexA_rotTo _ (A 0) (hA_mem 0).1 (hA_mem 0).2.le b)).2
        (rexA_equivOfStrictMono _ hsm' himg (rexA_rotTo _ (A 0) (hA_mem 0).1 (hA_mem 0).2.le c)).2
      apply rexA_cycBetween_of_strictMonoOn hsm'
        (rexA_rotTo _ (A 0) (hA_mem 0).1 (hA_mem 0).2.le a).2
        (rexA_rotTo _ (A 0) (hA_mem 0).1 (hA_mem 0).2.le b).2
        (rexA_rotTo _ (A 0) (hA_mem 0).1 (hA_mem 0).2.le c).2
      exact rexA_cycBetween_rotFun a.2 b.2 c.2 h
    · intro v hv hmem
      obtain ⟨j, hj, hjv⟩ := D.exists_ent i hi v hv
      simp only [Equiv.trans_apply, rexA_rotTo_symm_apply_val, rexA_equivOfStrictMono_apply_val,
        rexA_rotTo_apply_val]
      have e1 : rexA_rotFun ((D.Γ.comp i).k : ℝ) (A 0) (D.visitCoord v) = X j := by
        simp only [X, ite_eq_left hj, A, hjv]
      rw [e1, rexA_pl_knot _ X Y hX j hj.le, hY0, sub_zero]
      simp only [Y, ite_eq_left hj]
      rw [rexA_rotFun_rotFun (hB_mem j)]
      simp only [B, hjv]

/-- def:gauss-record (sm-3:365-369), the PL-extension clause: every named record isomorphism of
the records of two diagrams extends to orientation-preserving circle maps of the parameter circles
carrying every occurrence to its image. -/
theorem rexA_extendsToCircleMaps : ι.ExtendsToCircleMaps := by
  choose F hF using fun i => ι.rexA_component_key_map i
  refine ⟨fun i => rexA_ptEquiv (F i),
    fun i p q r h => rexA_traversalBetween_ptEquiv (F i) (hF i).1 p q r h, fun v => ?_⟩
  apply rexA_pt_ext
  · exact (ι.comp_eq v).symm
  · show traversalKey (rexA_ptEquiv (F (D.visitPt v).1) (D.visitPt v).2) =
      traversalKey (D'.visitPt (ι.Φ v)).2
    rw [rexA_traversalKey_ptEquiv]
    exact (hF _).2 v rfl _

end RecordIso

/-- The extension theorem of def:gauss-record (`recordIso_extend_statement`, design decision 6,
`RecordIso.extend`). -/
theorem rexA_recordIso_extend : recordIso_extend_statement :=
  fun _ _ ι => ι.rexA_extendsToCircleMaps

end

end SM.Link

#print axioms SM.Link.rexA_recordIso_extend
