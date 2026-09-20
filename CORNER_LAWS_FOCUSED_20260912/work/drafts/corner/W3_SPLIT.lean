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

section S7PSplit

/-! ### Wave 3, unit SPLIT (prefix `s7p_`, serving `s7_sliding_law_at`): the interlacement transfer
`s7b_PivotSplit (Interlaces hn hQ) (Interlaces hn₁ h₁) (Interlaces hn₂ h₂) ι₁ ι₂ x` on a SIDE polygon
`Q` of a sliding wall (U_S7B_REPORT §2.2), on both sides, below a radius — the hypotheses `hsplitm`,
`hsplitp` of `s7e_contactSector_of_pivotSplit`.

Method.  `Interlaces` is the cyclic order (`traversalBetween`) of visit positions, and the cyclic order
is invariant under the relabelling `traversalShift M` (`traversalBetween_shift`): so every visit `v` of
`Q` is read through its **rotated key** `κ(v) = (edge v − M).val + parameter v ∈ [0, n)` (`s7p_kappa`),
which starts at the vertex `μ_M`.  In this coordinate the images of the visits of `λ₁` are
`κ = i.val + p_Q`, those of `λ₂` are `κ = D + j.val + p_Q` (`D = contactDistance M a`), the contact
`a`-visit of `x` sits at `D + (r ± η)` and its leg visit at `n − 1 + (1 − η)` (leg `M − 1`) or at
`0 + η` (leg `M`).  Hence: (i) `rel₁`, `rel₂`: on each half the rotated key of the image is an
order-isomorphic reparametrisation of the half's own key (edge indices agree, the same-edge order of
`Q` is the centre's by `ContactOrderAgrees`, and the centre's is the half's by U110-B's parameter
laws, monotone on the cut), so the cyclic order is preserved verbatim (`s7p_cyc_congr`); (ii) the
λ₁-images lie in `(3η, D + r − 3η)`, the λ₂-images in `(D + r + 3η, n − 3η)`: two arcs cut by the two
visits of `x`, whence `cross`, `cross'`, `x_free`; (iii) `x_split`: a crossing not interlacing `x`
has both visits on one side of the contact `a`-visit, so both edge labels are in one half's range and
its cut-edge parameter is on the right side of `r` — the CONVERSE of `s7b_isCrossing_*_image`
(`s7p_mem_range_first/_second`).  The side-of-`r` agreement between `Q` and the centre is sign
constancy along the germ interval (`s7p_side_of_r`, the `s7e_sign_const` argument with the centre as
the second point). -/

/-! #### Pure cyclic order on real keys -/

/-- The strict cyclic order of three reals: the key form of `traversalBetween`. -/
def s7p_cyc (x y z : ℝ) : Prop := (x < y ∧ y < z) ∨ (y < z ∧ z < x) ∨ (z < x ∧ x < y)

omit [NeZero n] in
theorem s7p_traversalBetween_iff (p q r : TraversalPoint n) :
    traversalBetween p q r ↔ s7p_cyc (traversalKey p) (traversalKey q) (traversalKey r) := Iff.rfl

/-- The cyclic order of three keys only depends on their pairwise order. -/
theorem s7p_cyc_congr {α : Type*} (F G : α → ℝ) (h : ∀ u v, G u < G v ↔ F u < F v) (u v w : α) :
    s7p_cyc (G u) (G v) (G w) ↔ s7p_cyc (F u) (F v) (F w) := by
  simp only [s7p_cyc, h]

/-- Keys of the form `edge + parameter` with parameters in `[0, 1)`: the order is decided by the edge
indices, and on a common edge by the parameters. -/
theorem s7p_key_lt_iff_of (e e' : ℕ) (p p' q q' : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) (hp' : 0 ≤ p')
    (hp1' : p' < 1) (hq : 0 ≤ q) (hq1 : q < 1) (hq' : 0 ≤ q') (hq1' : q' < 1)
    (hsame : e = e' → (q < q' ↔ p < p')) :
    (e : ℝ) + q < e' + q' ↔ (e : ℝ) + p < e' + p' := by
  rcases lt_trichotomy e e' with h | h | h
  · have : (e : ℝ) + 1 ≤ e' := by exact_mod_cast h
    constructor <;> intro _ <;> linarith
  · subst h
    simp only [add_lt_add_iff_left]
    exact hsame rfl
  · have : (e' : ℝ) + 1 ≤ e := by exact_mod_cast h
    constructor <;> intro hh <;> exfalso <;> linarith

/-! #### The rotated key `κ` of a visit and interlacement in `κ`-coordinates -/

/-- The key of a visit rotated to start at the vertex `μ_M`: `(edge − M).val + parameter`. -/
noncomputable def s7p_kappa (hn : 3 ≤ n) {Q : LabelledTuple n} (hQ : G1 Q) (M : ZMod n)
    (v : Visit Q) : ℝ :=
  traversalKey (traversalShift M (visitPosition hn hQ v))

omit [NeZero n] in
theorem s7p_kappa_eq (hn : 3 ≤ n) {Q : LabelledTuple n} (hQ : G1 Q) (M : ZMod n) (v : Visit Q) :
    s7p_kappa hn hQ M v = ((v.2.val - M).val : ℝ) + visitParameter v := rfl

theorem s7p_kappa_injective (hn : 3 ≤ n) {Q : LabelledTuple n} (hQ : Generic Q) (M : ZMod n) :
    Function.Injective (s7p_kappa hn hQ.1 M) := by
  intro v w h
  apply visitPosition_injective hn hQ
  have h' := traversalKey_injective h
  have h1 := congrArg Prod.fst h'
  have h2 := congrArg Prod.snd h'
  simp only [traversalShift, sub_left_inj] at h1
  exact Prod.ext h1 h2

/-- `traversalBetween` of visit positions in the rotated coordinate. -/
theorem s7p_between_iff (hn : 3 ≤ n) {Q : LabelledTuple n} (hQ : G1 Q) (M : ZMod n) (u v w : Visit Q) :
    traversalBetween (visitPosition hn hQ u) (visitPosition hn hQ v) (visitPosition hn hQ w) ↔
      s7p_cyc (s7p_kappa hn hQ M u) (s7p_kappa hn hQ M v) (s7p_kappa hn hQ M w) := by
  rw [← traversalBetween_shift M]
  exact Iff.rfl

/-- Interlacement read in the rotated coordinate. -/
theorem s7p_interlaces_iff (hn : 3 ≤ n) {Q : LabelledTuple n} (hQ : Generic Q) (M : ZMod n)
    (x y : Crossing Q) :
    Interlaces hn hQ x y ↔ x ≠ y ∧ ∃ x₀ x₁ : {i // i ∈ x.val}, ∃ y₀ y₁ : {i // i ∈ y.val},
      x₀ ≠ x₁ ∧ y₀ ≠ y₁ ∧
      s7p_cyc (s7p_kappa hn hQ.1 M ⟨x, x₀⟩) (s7p_kappa hn hQ.1 M ⟨y, y₀⟩) (s7p_kappa hn hQ.1 M ⟨x, x₁⟩) ∧
      s7p_cyc (s7p_kappa hn hQ.1 M ⟨x, x₁⟩) (s7p_kappa hn hQ.1 M ⟨y, y₁⟩) (s7p_kappa hn hQ.1 M ⟨x, x₀⟩) := by
  unfold Interlaces crossingVisitBetween crossingVisitPosition
  simp only [s7p_between_iff hn hQ.1 M]

/-! #### The side data of a sliding wall (one side polygon `Q`, the centre `P`) -/

/-- Everything the transfer needs about one side polygon `Q` of a sliding wall with centre `P`:
the contact indices and the centre geometry (fields of `VertexEdgeAt` and `s7a2_exists_intervalLocal`),
genericity of `Q`, the persistent-crossing agreement (`VertexCrossingData`), the parameter windows and
the same-edge order agreement (`VertexLocalData.windows`, `.parameter_order`), and the side-of-`r`
agreement of persistent `a`-visits between `Q` and the centre (`s7p_side_of_r`). -/
structure s7p_SideData (M a : ZMod n) (P Q : LabelledTuple n) (r η : ℝ) : Prop where
  hsep : ContactSeparated M a
  hz : pointZeroTriples P = {contactSupport M a}
  hm : P M ∈ edgeInterior P a
  hr : P M = edgePoint P a r
  hr0 : 0 < r
  hr1 : r < 1
  hη : 0 < η
  hηr : 4 * η < r
  hηr1 : 4 * η < 1 - r
  hQ : Generic Q
  hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)
  hw : ContactParameterWindows P Q M a r η
  hord : ContactOrderAgrees P Q M a
  hside : ∀ j, IsCrossing P {a, j} → ¬ ContactAffected M a {a, j} →
    (edgeParameter Q a j < r ↔ edgeParameter P a j < r)

section S7PSide

variable (hn : 3 ≤ n) {M a : ZMod n} {P Q : LabelledTuple n} {r η : ℝ}
  (hd : s7p_SideData M a P Q r η)

include hn hd in
theorem s7p_D_bounds : 2 ≤ contactDistance M a ∧ contactDistance M a ≤ n - 3 :=
  contactDistance_bounds hn hd.hsep

include hn hd in
theorem s7p_n5 : 5 ≤ n := contactSeparated_size hn hd.hsep

include hn hd in
/-- The crossing parameter at the centre is the Cramer parameter (persistent crossings). -/
theorem s7p_centre_visitParameter (v : Visit P) (hv : ¬ ContactAffected M a v.1.val) (j : ZMod n)
    (hs : v.1.val = {v.2.val, j}) : visitParameter v = edgeParameter P v.2.val j := by
  obtain ⟨⟨s, hcs⟩, ⟨i, hi⟩⟩ := v
  change s = {i, j} at hs
  subst hs
  exact contact_crossingParameter_eq_edgeParameter hn hd.hsep hd.hz hcs hv

/-! ##### Edge offsets of the images -/

theorem s7p_d_first (i : ZMod (firstHalfSize M a)) : (firstHalfIndex M a i - M).val = i.val :=
  cyclicRangeIndex_offset (firstHalfSize_le M a) M i

theorem s7p_d_second (j : ZMod (secondHalfSize M a)) :
    (secondHalfEdgeIndex M a j - M).val = contactDistance M a + j.val := by
  have h1 : secondHalfEdgeIndex M a j - M = ((contactDistance M a + j.val : ℕ) : ZMod n) := by
    simp only [secondHalfEdgeIndex, cyclicRangeIndex, Nat.cast_add, contactDistance_cast]
    ring
  rw [h1, ZMod.val_natCast_of_lt]
  have := j.val_lt
  have h2 : secondHalfSize M a = n - contactDistance M a := rfl
  have hD : contactDistance M a < n := ZMod.val_lt _
  omega

omit [NeZero n] in
theorem s7p_first_val_le (i : ZMod (firstHalfSize M a)) : i.val ≤ contactDistance M a := by
  have := i.val_lt
  have h2 : firstHalfSize M a = contactDistance M a + 1 := rfl
  omega

omit [NeZero n] in
theorem s7p_first_val_eq_iff (i : ZMod (firstHalfSize M a)) :
    i.val = contactDistance M a ↔ i = -1 := by
  have hl := last_index_val_succ (n := firstHalfSize M a)
  have h2 : firstHalfSize M a = contactDistance M a + 1 := rfl
  constructor
  · intro h
    apply ZMod.val_injective
    omega
  · rintro rfl
    omega

omit [NeZero n] in
theorem s7p_first_val_zero_iff (i : ZMod (firstHalfSize M a)) : i.val = 0 ↔ i = 0 :=
  ZMod.val_eq_zero i

theorem s7p_second_val_lt (j : ZMod (secondHalfSize M a)) : j.val < n - contactDistance M a := by
  have := j.val_lt
  have h2 : secondHalfSize M a = n - contactDistance M a := rfl
  omega

theorem s7p_second_val_eq_iff (j : ZMod (secondHalfSize M a)) :
    j.val = n - contactDistance M a - 1 ↔ j = -1 := by
  have hl := last_index_val_succ (n := secondHalfSize M a)
  have h2 : secondHalfSize M a = n - contactDistance M a := rfl
  have hD : contactDistance M a < n := ZMod.val_lt _
  constructor
  · intro h
    apply ZMod.val_injective
    omega
  · rintro rfl
    omega

/-! ##### Parameters of the image visits: the same-edge order of `Q` is the half's -/

include hd in
theorem s7p_first_pair (v : Visit (firstHalf P M a)) :
    ∃ j, v.1.val = {v.2.val, j} ∧
      (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC v).1.val =
        {firstHalfIndex M a v.2.val, firstHalfIndex M a j} := by
  obtain ⟨j, -, hs⟩ := crossing_support_partner v.1 v.2.val v.2.property
  refine ⟨j, hs, ?_⟩
  show Finset.image (firstHalfIndex M a) v.1.val = _
  conv_lhs => rw [hs]
  rw [Finset.image_insert, Finset.image_singleton]

include hd in
theorem s7p_second_pair (v : Visit (secondHalf P M a)) :
    ∃ j, v.1.val = {v.2.val, j} ∧
      (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC v).1.val =
        {secondHalfEdgeIndex M a v.2.val, secondHalfEdgeIndex M a j} := by
  obtain ⟨j, -, hs⟩ := crossing_support_partner v.1 v.2.val v.2.property
  refine ⟨j, hs, ?_⟩
  show Finset.image (secondHalfEdgeIndex M a) v.1.val = _
  conv_lhs => rw [hs]
  rw [Finset.image_insert, Finset.image_singleton]

include hd in
/-- The `Q`-parameter of the image of a visit of `λ₁` is the Cramer parameter of `Q`, the centre
parameter of the image is the Cramer parameter of `P` (same label pair). -/
theorem s7p_first_params (v : Visit (firstHalf P M a)) (j : ZMod (firstHalfSize M a))
    (hs : (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC v).1.val =
      {firstHalfIndex M a v.2.val, firstHalfIndex M a j}) :
    visitParameter (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC v) =
        edgeParameter Q (firstHalfIndex M a v.2.val) (firstHalfIndex M a j) ∧
      visitParameter (s7b_firstHalfVisit hn hd.hsep hd.hm v) =
        edgeParameter P (firstHalfIndex M a v.2.val) (firstHalfIndex M a j) ∧
      IsCrossing P {firstHalfIndex M a v.2.val, firstHalfIndex M a j} ∧
      ¬ ContactAffected M a {firstHalfIndex M a v.2.val, firstHalfIndex M a j} := by
  have hnot : ¬ ContactAffected M a {firstHalfIndex M a v.2.val, firstHalfIndex M a j} := by
    rw [← hs]; exact s7b_firstCrossingQ_not_affected hn hd.hsep hd.hm hd.hQC v.1
  have hcP : IsCrossing P {firstHalfIndex M a v.2.val, firstHalfIndex M a j} := by
    rw [← hs]; exact (s7b_firstHalfCrossing hn hd.hsep hd.hm v.1).property
  refine ⟨visitParameter_eq_of_support_pair hn hd.hQ.1 _ _ hs, ?_, hcP, hnot⟩
  exact s7p_centre_visitParameter hn hd (s7b_firstHalfVisit hn hd.hsep hd.hm v)
    (s7b_firstHalfCrossing_not_affected hn hd.hsep hd.hm v.1) _ hs

include hd in
theorem s7p_second_params (v : Visit (secondHalf P M a)) (j : ZMod (secondHalfSize M a))
    (hs : (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC v).1.val =
      {secondHalfEdgeIndex M a v.2.val, secondHalfEdgeIndex M a j}) :
    visitParameter (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC v) =
        edgeParameter Q (secondHalfEdgeIndex M a v.2.val) (secondHalfEdgeIndex M a j) ∧
      visitParameter (s7b_secondHalfVisit hn hd.hsep hd.hm v) =
        edgeParameter P (secondHalfEdgeIndex M a v.2.val) (secondHalfEdgeIndex M a j) ∧
      IsCrossing P {secondHalfEdgeIndex M a v.2.val, secondHalfEdgeIndex M a j} ∧
      ¬ ContactAffected M a {secondHalfEdgeIndex M a v.2.val, secondHalfEdgeIndex M a j} := by
  have hnot : ¬ ContactAffected M a {secondHalfEdgeIndex M a v.2.val, secondHalfEdgeIndex M a j} := by
    rw [← hs]; exact s7b_secondCrossingQ_not_affected hn hd.hsep hd.hm hd.hQC v.1
  have hcP : IsCrossing P {secondHalfEdgeIndex M a v.2.val, secondHalfEdgeIndex M a j} := by
    rw [← hs]; exact (s7b_secondHalfCrossing hn hd.hsep hd.hm v.1).property
  refine ⟨visitParameter_eq_of_support_pair hn hd.hQ.1 _ _ hs, ?_, hcP, hnot⟩
  exact s7p_centre_visitParameter hn hd (s7b_secondHalfVisit hn hd.hsep hd.hm v)
    (s7b_secondHalfCrossing_not_affected hn hd.hsep hd.hm v.1) _ hs

include hd in
/-- **Same-edge order transfer, `λ₁`**: two visits of `λ₁` on one edge have their images on `Q` in
the same order (`ContactOrderAgrees` to the centre, then U110-B's parameter laws). -/
theorem s7p_first_param_lt_iff (_h₁ : Generic (firstHalf P M a)) (u w : Visit (firstHalf P M a))
    (he : u.2.val = w.2.val) :
    visitParameter (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC u) <
        visitParameter (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC w) ↔
      visitParameter u < visitParameter w := by
  obtain ⟨ju, -, hsu⟩ := s7p_first_pair hn hd u
  obtain ⟨jw, -, hsw⟩ := s7p_first_pair hn hd w
  obtain ⟨hQu, hPu, hcu, hnu⟩ := s7p_first_params hn hd u ju hsu
  obtain ⟨hQw, hPw, hcw, hnw⟩ := s7p_first_params hn hd w jw hsw
  rw [he] at hQu hPu hcu hnu
  rw [hQu, hQw, hd.hord _ _ _ hcu hnu hcw hnw, ← hPu, ← hPw]
  by_cases hcut : w.2.val = -1
  · have hcut' : u.2.val = -1 := he.trans hcut
    rw [s7b_visitParameter_firstHalfVisit_cut hn hd.hsep hd.hz hd.hm hd.hr u hcut',
      s7b_visitParameter_firstHalfVisit_cut hn hd.hsep hd.hz hd.hm hd.hr w hcut]
    have hr0 := hd.hr0
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · have hcut' : u.2.val ≠ -1 := fun h => hcut (he.symm.trans h)
    rw [s7b_visitParameter_firstHalfVisit hn hd.hsep hd.hz hd.hm u hcut',
      s7b_visitParameter_firstHalfVisit hn hd.hsep hd.hz hd.hm w hcut]

include hd in
/-- **Same-edge order transfer, `λ₂`.** -/
theorem s7p_second_param_lt_iff (_h₂ : Generic (secondHalf P M a)) (u w : Visit (secondHalf P M a))
    (he : u.2.val = w.2.val) :
    visitParameter (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC u) <
        visitParameter (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC w) ↔
      visitParameter u < visitParameter w := by
  obtain ⟨ju, -, hsu⟩ := s7p_second_pair hn hd u
  obtain ⟨jw, -, hsw⟩ := s7p_second_pair hn hd w
  obtain ⟨hQu, hPu, hcu, hnu⟩ := s7p_second_params hn hd u ju hsu
  obtain ⟨hQw, hPw, hcw, hnw⟩ := s7p_second_params hn hd w jw hsw
  rw [he] at hQu hPu hcu hnu
  rw [hQu, hQw, hd.hord _ _ _ hcu hnu hcw hnw, ← hPu, ← hPw]
  by_cases hcut : w.2.val = 0
  · have hcut' : u.2.val = 0 := he.trans hcut
    rw [s7b_visitParameter_secondHalfVisit_cut hn hd.hsep hd.hz hd.hm hd.hr u hcut',
      s7b_visitParameter_secondHalfVisit_cut hn hd.hsep hd.hz hd.hm hd.hr w hcut]
    have h1r : 0 < 1 - r := by linarith [hd.hr1]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · have hcut' : u.2.val ≠ 0 := fun h => hcut (he.symm.trans h)
    rw [s7b_visitParameter_secondHalfVisit hn hd.hsep hd.hz hd.hm u hcut',
      s7b_visitParameter_secondHalfVisit hn hd.hsep hd.hz hd.hm w hcut]

/-! ##### The rotated keys of the images are order-isomorphic to the halves' keys -/

include hd in
theorem s7p_kappa_first (v : Visit (firstHalf P M a)) :
    s7p_kappa hn hd.hQ.1 M (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC v) =
      (v.2.val.val : ℝ) + visitParameter (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC v) := by
  rw [s7p_kappa_eq, s7b_firstVisitQ_edge, s7p_d_first]

include hd in
theorem s7p_kappa_second (v : Visit (secondHalf P M a)) :
    s7p_kappa hn hd.hQ.1 M (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC v) =
      ((contactDistance M a + v.2.val.val : ℕ) : ℝ) +
        visitParameter (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC v) := by
  rw [s7p_kappa_eq, s7b_secondVisitQ_edge, s7p_d_second]

/-- The key of a half's visit (rotation by `0`). -/
theorem s7p_kappa_zero {k : ℕ} [NeZero k] (hk : 3 ≤ k) {R : LabelledTuple k} (hR : G1 R) (v : Visit R) :
    s7p_kappa hk hR 0 v = (v.2.val.val : ℝ) + visitParameter v := by
  rw [s7p_kappa_eq, sub_zero]

include hd in
/-- **`κ ∘ ι₁` is order-isomorphic to the key of `λ₁`.** -/
theorem s7p_kappa_first_lt_iff (h₁ : Generic (firstHalf P M a)) (u w : Visit (firstHalf P M a)) :
    s7p_kappa hn hd.hQ.1 M (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC u) <
        s7p_kappa hn hd.hQ.1 M (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC w) ↔
      s7p_kappa (contactHalfSizes_bounds hn hd.hsep).1.1 h₁.1 0 u <
        s7p_kappa (contactHalfSizes_bounds hn hd.hsep).1.1 h₁.1 0 w := by
  have hn₁ := (contactHalfSizes_bounds hn hd.hsep).1.1
  rw [s7p_kappa_first hn hd, s7p_kappa_first hn hd, s7p_kappa_zero hn₁ h₁.1, s7p_kappa_zero hn₁ h₁.1]
  have hu := visitPosition_interior hn hd.hQ.1 (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC u)
  have hw := visitPosition_interior hn hd.hQ.1 (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC w)
  have hu' := visitPosition_interior hn₁ h₁.1 u
  have hw' := visitPosition_interior hn₁ h₁.1 w
  exact s7p_key_lt_iff_of _ _ _ _ _ _ hu'.1.le hu'.2 hw'.1.le hw'.2 hu.1.le hu.2 hw.1.le hw.2
    (fun he => s7p_first_param_lt_iff hn hd h₁ u w (ZMod.val_injective _ he))

include hd in
/-- **`κ ∘ ι₂` is order-isomorphic to the key of `λ₂`.** -/
theorem s7p_kappa_second_lt_iff (h₂ : Generic (secondHalf P M a)) (u w : Visit (secondHalf P M a)) :
    s7p_kappa hn hd.hQ.1 M (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC u) <
        s7p_kappa hn hd.hQ.1 M (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC w) ↔
      s7p_kappa (contactHalfSizes_bounds hn hd.hsep).2.1 h₂.1 0 u <
        s7p_kappa (contactHalfSizes_bounds hn hd.hsep).2.1 h₂.1 0 w := by
  have hn₂ := (contactHalfSizes_bounds hn hd.hsep).2.1
  rw [s7p_kappa_second hn hd, s7p_kappa_second hn hd, s7p_kappa_zero hn₂ h₂.1, s7p_kappa_zero hn₂ h₂.1]
  have hu := visitPosition_interior hn hd.hQ.1 (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC u)
  have hw := visitPosition_interior hn hd.hQ.1 (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC w)
  have hu' := visitPosition_interior hn₂ h₂.1 u
  have hw' := visitPosition_interior hn₂ h₂.1 w
  have key := s7p_key_lt_iff_of (contactDistance M a + u.2.val.val) (contactDistance M a + w.2.val.val)
    _ _ _ _ hu'.1.le hu'.2 hw'.1.le hw'.2 hu.1.le hu.2 hw.1.le hw.2
    (fun he => s7p_second_param_lt_iff hn hd h₂ u w (ZMod.val_injective _ (by omega)))
  rw [key]
  push_cast
  constructor <;> intro h <;> linarith

/-! ##### `rel₁`, `rel₂`: interlacement is preserved by the half crossing maps -/

include hd in
theorem s7p_visit_first_ne (c : Crossing (firstHalf P M a)) (x₀ x₁ : {i // i ∈ c.val}) (h : x₀ ≠ x₁) :
    (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC ⟨c, x₀⟩).2 ≠ (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC ⟨c, x₁⟩).2 := by
  intro he
  apply h
  have h' : s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC ⟨c, x₀⟩ = s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC ⟨c, x₁⟩ :=
    Sigma.ext rfl (heq_of_eq he)
  have := s7b_firstVisitQ_injective hn hd.hsep hd.hm hd.hQC h'
  exact Sigma.mk.inj_iff.mp this |>.2 |> eq_of_heq

include hd in
theorem s7p_visit_second_ne (c : Crossing (secondHalf P M a)) (x₀ x₁ : {i // i ∈ c.val}) (h : x₀ ≠ x₁) :
    (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC ⟨c, x₀⟩).2 ≠ (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC ⟨c, x₁⟩).2 := by
  intro he
  apply h
  have h' : s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC ⟨c, x₀⟩ = s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC ⟨c, x₁⟩ :=
    Sigma.ext rfl (heq_of_eq he)
  have := s7b_secondVisitQ_injective hn hd.hsep hd.hm hd.hQC h'
  exact Sigma.mk.inj_iff.mp this |>.2 |> eq_of_heq

include hd in
/-- **`rel₁`** (field of `s7b_SupportSplit`). -/
theorem s7p_rel_first (h₁ : Generic (firstHalf P M a)) (c c' : Crossing (firstHalf P M a)) :
    Interlaces hn hd.hQ (s7b_firstCrossingQ hn hd.hsep hd.hm hd.hQC c)
        (s7b_firstCrossingQ hn hd.hsep hd.hm hd.hQC c') ↔
      Interlaces (contactHalfSizes_bounds hn hd.hsep).1.1 h₁ c c' := by
  have hn₁ := (contactHalfSizes_bounds hn hd.hsep).1.1
  rw [s7p_interlaces_iff hn hd.hQ M, s7p_interlaces_iff hn₁ h₁ 0]
  have hcong := s7p_cyc_congr _ _ (s7p_kappa_first_lt_iff hn hd h₁)
  constructor
  · rintro ⟨hne, x₀, x₁, y₀, y₁, hx, hy, h1, h2⟩
    refine ⟨fun he => hne (congrArg _ he), ?_⟩
    obtain ⟨w₀, hw₀, hw₀'⟩ := s7b_visit_of_firstCrossingQ hn hd.hsep hd.hm hd.hQC ⟨_, x₀⟩ c rfl
    obtain ⟨w₁, hw₁, hw₁'⟩ := s7b_visit_of_firstCrossingQ hn hd.hsep hd.hm hd.hQC ⟨_, x₁⟩ c rfl
    obtain ⟨z₀, hz₀, hz₀'⟩ := s7b_visit_of_firstCrossingQ hn hd.hsep hd.hm hd.hQC ⟨_, y₀⟩ c' rfl
    obtain ⟨z₁, hz₁, hz₁'⟩ := s7b_visit_of_firstCrossingQ hn hd.hsep hd.hm hd.hQC ⟨_, y₁⟩ c' rfl
    obtain ⟨cw₀, x₀'⟩ := w₀
    obtain ⟨cw₁, x₁'⟩ := w₁
    obtain ⟨cz₀, y₀'⟩ := z₀
    obtain ⟨cz₁, y₁'⟩ := z₁
    dsimp only at hw₀ hw₁ hz₀ hz₁
    subst hw₀ hw₁ hz₀ hz₁
    refine ⟨x₀', x₁', y₀', y₁', ?_, ?_, ?_, ?_⟩
    · intro he; apply hx
      have h' : (⟨_, x₀⟩ : Visit Q) = ⟨_, x₁⟩ := hw₀'.symm.trans (by subst he; exact hw₁')
      exact eq_of_heq (Sigma.mk.inj_iff.mp h').2
    · intro he; apply hy
      have h' : (⟨_, y₀⟩ : Visit Q) = ⟨_, y₁⟩ := hz₀'.symm.trans (by subst he; exact hz₁')
      exact eq_of_heq (Sigma.mk.inj_iff.mp h').2
    · rw [← hcong, hw₀', hz₀', hw₁']; exact h1
    · rw [← hcong, hw₁', hz₁', hw₀']; exact h2
  · rintro ⟨hne, x₀, x₁, y₀, y₁, hx, hy, h1, h2⟩
    refine ⟨fun he => hne (s7b_firstCrossingQ_injective hn hd.hsep hd.hm hd.hQC he),
      (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC ⟨c, x₀⟩).2, (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC ⟨c, x₁⟩).2,
      (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC ⟨c', y₀⟩).2, (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC ⟨c', y₁⟩).2,
      s7p_visit_first_ne hn hd c x₀ x₁ hx, s7p_visit_first_ne hn hd c' y₀ y₁ hy, ?_, ?_⟩
    · exact (hcong ⟨c, x₀⟩ ⟨c', y₀⟩ ⟨c, x₁⟩).mpr h1
    · exact (hcong ⟨c, x₁⟩ ⟨c', y₁⟩ ⟨c, x₀⟩).mpr h2

include hd in
/-- **`rel₂`.** -/
theorem s7p_rel_second (h₂ : Generic (secondHalf P M a)) (c c' : Crossing (secondHalf P M a)) :
    Interlaces hn hd.hQ (s7b_secondCrossingQ hn hd.hsep hd.hm hd.hQC c)
        (s7b_secondCrossingQ hn hd.hsep hd.hm hd.hQC c') ↔
      Interlaces (contactHalfSizes_bounds hn hd.hsep).2.1 h₂ c c' := by
  have hn₂ := (contactHalfSizes_bounds hn hd.hsep).2.1
  rw [s7p_interlaces_iff hn hd.hQ M, s7p_interlaces_iff hn₂ h₂ 0]
  have hcong := s7p_cyc_congr _ _ (s7p_kappa_second_lt_iff hn hd h₂)
  constructor
  · rintro ⟨hne, x₀, x₁, y₀, y₁, hx, hy, h1, h2⟩
    refine ⟨fun he => hne (congrArg _ he), ?_⟩
    obtain ⟨w₀, hw₀, hw₀'⟩ := s7b_visit_of_secondCrossingQ hn hd.hsep hd.hm hd.hQC ⟨_, x₀⟩ c rfl
    obtain ⟨w₁, hw₁, hw₁'⟩ := s7b_visit_of_secondCrossingQ hn hd.hsep hd.hm hd.hQC ⟨_, x₁⟩ c rfl
    obtain ⟨z₀, hz₀, hz₀'⟩ := s7b_visit_of_secondCrossingQ hn hd.hsep hd.hm hd.hQC ⟨_, y₀⟩ c' rfl
    obtain ⟨z₁, hz₁, hz₁'⟩ := s7b_visit_of_secondCrossingQ hn hd.hsep hd.hm hd.hQC ⟨_, y₁⟩ c' rfl
    obtain ⟨cw₀, x₀'⟩ := w₀
    obtain ⟨cw₁, x₁'⟩ := w₁
    obtain ⟨cz₀, y₀'⟩ := z₀
    obtain ⟨cz₁, y₁'⟩ := z₁
    dsimp only at hw₀ hw₁ hz₀ hz₁
    subst hw₀ hw₁ hz₀ hz₁
    refine ⟨x₀', x₁', y₀', y₁', ?_, ?_, ?_, ?_⟩
    · intro he; apply hx
      have h' : (⟨_, x₀⟩ : Visit Q) = ⟨_, x₁⟩ := hw₀'.symm.trans (by subst he; exact hw₁')
      exact eq_of_heq (Sigma.mk.inj_iff.mp h').2
    · intro he; apply hy
      have h' : (⟨_, y₀⟩ : Visit Q) = ⟨_, y₁⟩ := hz₀'.symm.trans (by subst he; exact hz₁')
      exact eq_of_heq (Sigma.mk.inj_iff.mp h').2
    · rw [← hcong, hw₀', hz₀', hw₁']; exact h1
    · rw [← hcong, hw₁', hz₁', hw₀']; exact h2
  · rintro ⟨hne, x₀, x₁, y₀, y₁, hx, hy, h1, h2⟩
    refine ⟨fun he => hne (s7b_secondCrossingQ_injective hn hd.hsep hd.hm hd.hQC he),
      (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC ⟨c, x₀⟩).2, (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC ⟨c, x₁⟩).2,
      (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC ⟨c', y₀⟩).2, (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC ⟨c', y₁⟩).2,
      s7p_visit_second_ne hn hd c x₀ x₁ hx, s7p_visit_second_ne hn hd c' y₀ y₁ hy, ?_, ?_⟩
    · exact (hcong ⟨c, x₀⟩ ⟨c', y₀⟩ ⟨c, x₁⟩).mpr h1
    · exact (hcong ⟨c, x₁⟩ ⟨c', y₁⟩ ⟨c, x₀⟩).mpr h2

/-! ##### The two arcs: `κ`-bounds of the image visits and of the contact visits -/

include hd in
/-- On the cut edge `a`, the `Q`-parameter of a `λ₁`-image is below `r` (centre parameter `r · p`,
side-of-`r` agreement). -/
theorem s7p_first_paramQ_lt_r (v : Visit (firstHalf P M a)) (hv : v.2.val = -1) :
    visitParameter (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC v) < r := by
  obtain ⟨j, -, hs⟩ := s7p_first_pair hn hd v
  obtain ⟨hQv, hPv, hcP, hnot⟩ := s7p_first_params hn hd v j hs
  rw [hv, firstHalfIndex_last] at hQv hPv hcP hnot
  rw [hQv, hd.hside _ hcP hnot, ← hPv,
    s7b_visitParameter_firstHalfVisit_cut hn hd.hsep hd.hz hd.hm hd.hr v hv]
  have h1 := (visitPosition_interior (contactHalfSizes_bounds hn hd.hsep).1.1
    (g1_firstHalf hn hd.hsep hd.hz) v).2
  nlinarith [hd.hr0]

include hd in
/-- On the cut edge `a`, the `Q`-parameter of a `λ₂`-image is above `r`. -/
theorem s7p_second_paramQ_gt_r (v : Visit (secondHalf P M a)) (hv : v.2.val = 0) :
    r < visitParameter (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC v) := by
  obtain ⟨j, -, hs⟩ := s7p_second_pair hn hd v
  obtain ⟨hQv, hPv, hcP, hnot⟩ := s7p_second_params hn hd v j hs
  rw [hv, secondHalfEdgeIndex_zero] at hQv hPv hcP hnot
  have hne : visitParameter (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC v) ≠ r := by
    intro he
    have := s7e_persist_a hn hd.hQ hd.hw (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC v)
      (s7b_secondCrossingQ_not_affected hn hd.hsep hd.hm hd.hQC v.1) (by rw [s7b_secondVisitQ_edge, hv, secondHalfEdgeIndex_zero])
    rw [he, sub_self, abs_zero] at this
    linarith [hd.hη]
  refine lt_of_le_of_ne ?_ hne.symm
  by_contra hlt
  push Not at hlt
  rw [hQv, hd.hside _ hcP hnot, ← hPv,
    s7b_visitParameter_secondHalfVisit_cut hn hd.hsep hd.hz hd.hm hd.hr v hv] at hlt
  have h1 := (visitPosition_interior (contactHalfSizes_bounds hn hd.hsep).2.1
    (g1_secondHalf hn hd.hsep hd.hz) v).1
  nlinarith [hd.hr1]

include hd in
/-- A visit of a `λ₁`-image crossing is the image of a visit of `λ₁` with the same edge index. -/
theorem s7p_kappa_first_bounds (u : Visit Q) (c : Crossing (firstHalf P M a))
    (hu : u.1 = s7b_firstCrossingQ hn hd.hsep hd.hm hd.hQC c) :
    3 * η < s7p_kappa hn hd.hQ.1 M u ∧
      s7p_kappa hn hd.hQ.1 M u < (contactDistance M a : ℝ) + r - 3 * η := by
  obtain ⟨v, -, rfl⟩ := s7b_visit_of_firstCrossingQ hn hd.hsep hd.hm hd.hQC u c hu
  have hnot := s7b_firstCrossingQ_not_affected hn hd.hsep hd.hm hd.hQC v.1
  have hp := visitPosition_interior hn hd.hQ.1 (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC v)
  have hD := s7p_D_bounds hn hd
  have hη := hd.hη
  have hηr := hd.hηr
  have hr1 := hd.hr1
  have hle := s7p_first_val_le (M := M) (a := a) v.2.val
  rw [s7p_kappa_first hn hd]
  rcases Nat.eq_zero_or_pos v.2.val.val with h0 | hpos
  · -- edge `M`
    have he : (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC v).2.val = M := by
      rw [s7b_firstVisitQ_edge, (s7p_first_val_zero_iff _).mp h0, firstHalfIndex_zero]
    have h3 := s7e_persist_M hn hd.hQ hd.hw _ hnot he
    rw [h0]
    have hD2 : (2 : ℝ) ≤ contactDistance M a := by exact_mod_cast hD.1
    constructor <;> push_cast <;> linarith
  · rcases eq_or_ne v.2.val.val (contactDistance M a) with hD' | hne
    · -- edge `a`
      have hv : v.2.val = -1 := (s7p_first_val_eq_iff _).mp hD'
      have he : (s7b_firstVisitQ hn hd.hsep hd.hm hd.hQC v).2.val = a := by
        rw [s7b_firstVisitQ_edge, hv, firstHalfIndex_last]
      have h3 := s7e_persist_a hn hd.hQ hd.hw _ hnot he
      have h4 := s7p_first_paramQ_lt_r hn hd v hv
      rw [abs_of_neg (by linarith)] at h3
      rw [hD']
      have hD2 : (2 : ℝ) ≤ contactDistance M a := by exact_mod_cast hD.1
      constructor <;> linarith
    · have h1 : 1 ≤ v.2.val.val := hpos
      have h2 : v.2.val.val + 1 ≤ contactDistance M a := by omega
      have h1' : (1 : ℝ) ≤ v.2.val.val := by exact_mod_cast h1
      have h2' : (v.2.val.val : ℝ) + 1 ≤ contactDistance M a := by exact_mod_cast h2
      constructor <;> linarith

include hd in
theorem s7p_kappa_second_bounds (u : Visit Q) (c : Crossing (secondHalf P M a))
    (hu : u.1 = s7b_secondCrossingQ hn hd.hsep hd.hm hd.hQC c) :
    (contactDistance M a : ℝ) + r + 3 * η < s7p_kappa hn hd.hQ.1 M u ∧
      s7p_kappa hn hd.hQ.1 M u < (n : ℝ) - 3 * η := by
  obtain ⟨v, -, rfl⟩ := s7b_visit_of_secondCrossingQ hn hd.hsep hd.hm hd.hQC u c hu
  have hnot := s7b_secondCrossingQ_not_affected hn hd.hsep hd.hm hd.hQC v.1
  have hp := visitPosition_interior hn hd.hQ.1 (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC v)
  have hD := s7p_D_bounds hn hd
  have hn5 := s7p_n5 hn hd
  have hη := hd.hη
  have hηr := hd.hηr
  have hηr1 := hd.hηr1
  have hr1 := hd.hr1
  have hlt := s7p_second_val_lt (M := M) (a := a) v.2.val
  have hDn : contactDistance M a < n := ZMod.val_lt _
  rw [s7p_kappa_second hn hd]
  rcases Nat.eq_zero_or_pos v.2.val.val with h0 | hpos
  · -- edge `a`
    have hv : v.2.val = 0 := (ZMod.val_eq_zero _).mp h0
    have he : (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC v).2.val = a := by
      rw [s7b_secondVisitQ_edge, hv, secondHalfEdgeIndex_zero]
    have h3 := s7e_persist_a hn hd.hQ hd.hw _ hnot he
    have h4 := s7p_second_paramQ_gt_r hn hd v hv
    rw [abs_of_pos (by linarith)] at h3
    rw [h0]
    have hDn' : (contactDistance M a : ℝ) + 3 ≤ n := by
      have : contactDistance M a + 3 ≤ n := by omega
      exact_mod_cast this
    constructor <;> push_cast <;> linarith
  · rcases eq_or_ne v.2.val.val (n - contactDistance M a - 1) with hlast | hne
    · -- edge `M - 1`
      have hv : v.2.val = -1 := (s7p_second_val_eq_iff _).mp hlast
      have he : (s7b_secondVisitQ hn hd.hsep hd.hm hd.hQC v).2.val = M - 1 := by
        rw [s7b_secondVisitQ_edge, hv, secondHalfEdgeIndex_last]
      have h3 := s7e_persist_M_sub_one hn hd.hQ hd.hw _ hnot he
      have hsum : contactDistance M a + v.2.val.val = n - 1 := by omega
      rw [hsum]
      have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hn1]
      have hDn' : (contactDistance M a : ℝ) + 3 ≤ n := by
        have : contactDistance M a + 3 ≤ n := by omega
        exact_mod_cast this
      constructor <;> linarith
    · have h1 : contactDistance M a + 1 ≤ contactDistance M a + v.2.val.val := by omega
      have h2 : contactDistance M a + v.2.val.val + 1 ≤ n - 1 := by omega
      have h1' : (contactDistance M a : ℝ) + 1 ≤ ((contactDistance M a + v.2.val.val : ℕ) : ℝ) := by
        exact_mod_cast h1
      have h2' : ((contactDistance M a + v.2.val.val : ℕ) : ℝ) + 1 ≤ (n : ℝ) - 1 := by
        have : contactDistance M a + v.2.val.val + 2 ≤ n := by omega
        have := (Nat.cast_le (α := ℝ)).mpr this
        push_cast at this ⊢
        linarith
      constructor <;> linarith

include hd in
/-- A persistent visit of `Q` has its rotated key in `(3η, n − 3η)`. -/
theorem s7p_kappa_persistent_bounds (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val) :
    3 * η < s7p_kappa hn hd.hQ.1 M u ∧ s7p_kappa hn hd.hQ.1 M u < (n : ℝ) - 3 * η := by
  have hp := visitPosition_interior hn hd.hQ.1 u
  have hη := hd.hη
  have hηr := hd.hηr
  have hr1 := hd.hr1
  have hdlt : (u.2.val - M).val < n := ZMod.val_lt _
  have hl := last_index_val_succ (n := n)
  rw [s7p_kappa_eq]
  constructor
  · rcases Nat.eq_zero_or_pos (u.2.val - M).val with h0 | hpos
    · have he : u.2.val = M := by
        have := (ZMod.val_eq_zero _).mp h0
        exact sub_eq_zero.mp this
      have h3 := s7e_persist_M hn hd.hQ hd.hw u hu he
      rw [h0]; push_cast; linarith
    · have : (1 : ℝ) ≤ (u.2.val - M).val := by exact_mod_cast hpos
      linarith
  · rcases eq_or_ne (u.2.val - M).val (n - 1) with hlast | hne
    · have he : u.2.val = M - 1 := by
        have h1 : u.2.val - M = -1 := by
          apply ZMod.val_injective; omega
        exact sub_eq_iff_eq_add.mp h1 |>.trans (by ring)
      have h3 := s7e_persist_M_sub_one hn hd.hQ hd.hw u hu he
      rw [hlast, Nat.cast_sub (by omega)]
      push_cast
      linarith
    · have : (u.2.val - M).val + 2 ≤ n := by omega
      have := (Nat.cast_le (α := ℝ)).mpr this
      push_cast at this
      linarith

variable (f : Bool) (hc : IsCrossing Q {a, contactLeg f M})

include hd in
/-- The rotated key of the contact `a`-visit: `D + (r ± η)`. -/
theorem s7p_kappa_va_bounds :
    (contactDistance M a : ℝ) + r - η < s7p_kappa hn hd.hQ.1 M (s7e_va hc) ∧
      s7p_kappa hn hd.hQ.1 M (s7e_va hc) < (contactDistance M a : ℝ) + r + η := by
  have h1 := abs_lt.mp (s7e_va_param_near hn hd.hQ f hd.hw hc)
  rw [s7p_kappa_eq, s7e_va_edge]
  have : (a - M).val = contactDistance M a := rfl
  rw [this]
  constructor <;> linarith

include hd in
/-- The rotated key of the leg visit, leg `M − 1`: above `n − η`. -/
theorem s7p_kappa_vl_false (hf : f = false) : (n : ℝ) - η < s7p_kappa hn hd.hQ.1 M (s7e_vl hc) := by
  subst hf
  have h1 := s7e_vl_param_false hn hd.hQ hd.hw hc
  rw [s7p_kappa_eq, s7e_vl_edge]
  have hl := last_index_val_succ (n := n)
  have he : (contactLeg false M - M) = (-1 : ZMod n) := by
    simp only [contactLeg, Bool.false_eq_true, ↓reduceIte]; ring
  rw [he]
  have : ((-1 : ZMod n).val : ℝ) = (n : ℝ) - 1 := by
    have : (-1 : ZMod n).val = n - 1 := by omega
    rw [this, Nat.cast_sub (by omega)]; simp
  rw [this]
  linarith

include hd in
/-- The rotated key of the leg visit, leg `M`: below `η`. -/
theorem s7p_kappa_vl_true (hf : f = true) : s7p_kappa hn hd.hQ.1 M (s7e_vl hc) < η := by
  subst hf
  have h1 := s7e_vl_param_true hn hd.hQ hd.hw hc
  rw [s7p_kappa_eq, s7e_vl_edge]
  have he : (contactLeg true M - M) = (0 : ZMod n) := by simp [contactLeg]
  rw [he, ZMod.val_zero]
  simp only [Nat.cast_zero, zero_add]
  exact h1

/-! ##### The pivot `x = {a, contactLeg f M}` and its two visits -/

/-- The contact crossing of the side polygon (`s7e_xm` / `s7e_xp` in the wall's terms). -/
def s7p_x : Crossing Q := ⟨{a, contactLeg f M}, hc⟩

theorem s7p_x_affected : ContactAffected M a (s7p_x f hc).val :=
  (contactAffected_iff_leg _).mpr ⟨f, rfl⟩

include hd in
/-- The two visits of the contact crossing are the `a`-visit and the leg visit (in one of the two
orders). -/
theorem s7p_x_visits (x₀ x₁ : {i // i ∈ (s7p_x f hc).val}) (hx : x₀ ≠ x₁) :
    ((⟨s7p_x f hc, x₀⟩ : Visit Q) = s7e_va hc ∧ (⟨s7p_x f hc, x₁⟩ : Visit Q) = s7e_vl hc) ∨
      ((⟨s7p_x f hc, x₀⟩ : Visit Q) = s7e_vl hc ∧ (⟨s7p_x f hc, x₁⟩ : Visit Q) = s7e_va hc) := by
  have ha := s7e_a_ne_leg f hd.hsep
  have hne : (⟨s7p_x f hc, x₀⟩ : Visit Q) ≠ ⟨s7p_x f hc, x₁⟩ := by
    intro he; apply hx
    exact Sigma.mk.inj_iff.mp he |>.2 |> eq_of_heq
  rcases s7e_visit_of_fst hc ⟨s7p_x f hc, x₀⟩ rfl ha with h0 | h0 <;>
    rcases s7e_visit_of_fst hc ⟨s7p_x f hc, x₁⟩ rfl ha with h1 | h1
  · exact absurd (h0.trans h1.symm) hne
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩
  · exact absurd (h0.trans h1.symm) hne

include hd in
/-- The leg visit, as a visit of `s7p_x`. -/
theorem s7p_xl_eq : (⟨s7p_x f hc, ⟨contactLeg f M, by simp [s7p_x]⟩⟩ : Visit Q) = s7e_vl hc := by
  have ha := s7e_a_ne_leg f hd.hsep
  rcases s7e_visit_of_fst hc ⟨s7p_x f hc, ⟨contactLeg f M, by simp [s7p_x]⟩⟩ rfl ha with h | h
  · exfalso
    have := congrArg (fun w : Visit Q => w.2.val) h
    exact ha this.symm
  · exact h

/-! ##### `cross`, `cross'`, `x_free`: the two arcs -/

include hd in
/-- **`cross`**: a `λ₁`-image never interlaces a `λ₂`-image. -/
theorem s7p_cross (c₁ : Crossing (firstHalf P M a)) (c₂ : Crossing (secondHalf P M a)) :
    ¬ Interlaces hn hd.hQ (s7b_firstCrossingQ hn hd.hsep hd.hm hd.hQC c₁)
      (s7b_secondCrossingQ hn hd.hsep hd.hm hd.hQC c₂) := by
  intro hI
  obtain ⟨-, x₀, x₁, y₀, y₁, -, -, h1, h2⟩ := (s7p_interlaces_iff hn hd.hQ M _ _).mp hI
  have b0 := s7p_kappa_first_bounds hn hd ⟨_, x₀⟩ c₁ rfl
  have b1 := s7p_kappa_first_bounds hn hd ⟨_, x₁⟩ c₁ rfl
  have d0 := s7p_kappa_second_bounds hn hd ⟨_, y₀⟩ c₂ rfl
  have d1 := s7p_kappa_second_bounds hn hd ⟨_, y₁⟩ c₂ rfl
  have hη := hd.hη
  unfold s7p_cyc at h1 h2
  rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> linarith

include hd in
/-- **`cross'`.** -/
theorem s7p_cross' (c₁ : Crossing (firstHalf P M a)) (c₂ : Crossing (secondHalf P M a)) :
    ¬ Interlaces hn hd.hQ (s7b_secondCrossingQ hn hd.hsep hd.hm hd.hQC c₂)
      (s7b_firstCrossingQ hn hd.hsep hd.hm hd.hQC c₁) :=
  fun h => s7p_cross hn hd c₁ c₂ (interlaces_symm hn hd.hQ h)

include hd in
/-- **`x_free₁`**: the contact crossing interlaces no `λ₁`-image. -/
theorem s7p_x_free_first (c : Crossing (firstHalf P M a)) :
    ¬ Interlaces hn hd.hQ (s7p_x f hc) (s7b_firstCrossingQ hn hd.hsep hd.hm hd.hQC c) := by
  intro hI
  obtain ⟨-, x₀, x₁, y₀, y₁, hx, -, h1, h2⟩ := (s7p_interlaces_iff hn hd.hQ M _ _).mp hI
  have b0 := s7p_kappa_first_bounds hn hd ⟨_, y₀⟩ c rfl
  have b1 := s7p_kappa_first_bounds hn hd ⟨_, y₁⟩ c rfl
  have hva := s7p_kappa_va_bounds hn hd f hc
  have hD := s7p_D_bounds hn hd
  have hη := hd.hη
  have hηr := hd.hηr
  have hηr1 := hd.hηr1
  have hDn' : (contactDistance M a : ℝ) + 3 ≤ n := by
    have : contactDistance M a + 3 ≤ n := by have := s7p_n5 hn hd; omega
    exact_mod_cast this
  rcases s7p_x_visits hd f hc x₀ x₁ hx with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;> rw [e0, e1] at h1 h2 <;>
    unfold s7p_cyc at h1 h2 <;> cases f
  all_goals first
    | (have hvl := s7p_kappa_vl_false hn hd false hc rfl
       rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
         rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> linarith)
    | (have hvl := s7p_kappa_vl_true hn hd true hc rfl
       rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
         rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> linarith)

include hd in
/-- **`x_free₂`.** -/
theorem s7p_x_free_second (c : Crossing (secondHalf P M a)) :
    ¬ Interlaces hn hd.hQ (s7p_x f hc) (s7b_secondCrossingQ hn hd.hsep hd.hm hd.hQC c) := by
  intro hI
  obtain ⟨-, x₀, x₁, y₀, y₁, hx, -, h1, h2⟩ := (s7p_interlaces_iff hn hd.hQ M _ _).mp hI
  have b0 := s7p_kappa_second_bounds hn hd ⟨_, y₀⟩ c rfl
  have b1 := s7p_kappa_second_bounds hn hd ⟨_, y₁⟩ c rfl
  have hva := s7p_kappa_va_bounds hn hd f hc
  have hD := s7p_D_bounds hn hd
  have hη := hd.hη
  have hηr := hd.hηr
  have hηr1 := hd.hηr1
  have hDn' : (contactDistance M a : ℝ) + 3 ≤ n := by
    have : contactDistance M a + 3 ≤ n := by have := s7p_n5 hn hd; omega
    exact_mod_cast this
  rcases s7p_x_visits hd f hc x₀ x₁ hx with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;> rw [e0, e1] at h1 h2 <;>
    unfold s7p_cyc at h1 h2 <;> cases f
  all_goals first
    | (have hvl := s7p_kappa_vl_false hn hd false hc rfl
       rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
         rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> linarith)
    | (have hvl := s7p_kappa_vl_true hn hd true hc rfl
       rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
         rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> linarith)

/-! ##### The converse of `s7b_isCrossing_*_image`: a crossing inside one range is an image -/

include hd in
/-- **A crossing of `Q` with both labels in `M..a` and, on the cut edge `a`, centre parameter below
`r`, is the image of a crossing of `λ₁`.** -/
theorem s7p_mem_range_first (y : Crossing Q) (hy : ¬ ContactAffected M a y.val)
    (hrange : ∀ e ∈ y.val, (e - M).val < firstHalfSize M a)
    (hcut : ∀ j, y.val = {a, j} → edgeParameter P a j < r) :
    ∃ c, s7b_firstCrossingQ hn hd.hsep hd.hm hd.hQC c = y := by
  have hyP : IsCrossing P y.val := (hd.hQC _ hy).mp y.property
  obtain ⟨e₁, e₂, hval, hrem, -⟩ := hyP
  obtain ⟨i₁, hi₁⟩ := (firstHalfIndex_range M a e₁).mpr (hrange e₁ (by rw [hval]; simp))
  obtain ⟨i₂, hi₂⟩ := (firstHalfIndex_range M a e₂).mpr (hrange e₂ (by rw [hval]; simp))
  have hnotP : ¬ ContactAffected M a {e₁, e₂} := by rw [← hval]; exact hy
  have hrem' : remote i₁ i₂ := by
    rw [← hi₁, ← hi₂, s7b_remote_firstHalfIndex_iff hn hd.hsep] at hrem
    rcases hrem with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h
    · exfalso; apply hnotP; right
      rw [← hi₁, ← hi₂, h1, h2, firstHalfIndex_last, firstHalfIndex_zero]
    · exfalso; apply hnotP; right
      rw [← hi₁, ← hi₂, h1, h2, firstHalfIndex_last, firstHalfIndex_zero, Finset.pair_comm]
  let yP : Crossing P := ⟨y.val, (hd.hQC _ hy).mp y.property⟩
  have hseg : ∀ (i : ZMod (firstHalfSize M a)) (e : ZMod n), firstHalfIndex M a i = e → e ∈ y.val →
      crossingPoint yP ∈ edgeSegment (firstHalf P M a) i := by
    intro i e hie he
    have hmem : crossingPoint yP ∈ edgeSegment P e := crossingPoint_mem yP e he
    by_cases hi : i = -1
    · subst hi
      rw [firstHalfIndex_last] at hie
      subst hie
      rw [s7b_mem_edgeSegment_firstHalf_cut hd.hr hd.hr0]
      obtain ⟨j, -, hs⟩ := crossing_support_partner yP _ he
      have hspec := crossingParameter_spec yP _ he
      refine ⟨crossingParameter yP _ he, hspec.1, ?_, hspec.2.2⟩
      have hyv : y.val = {_, j} := hs
      have hpar : crossingParameter yP _ he = edgeParameter P _ j :=
        s7p_centre_visitParameter hn hd ⟨yP, ⟨_, he⟩⟩ hy j hs
      rw [hpar]
      exact (hcut j hyv).le
    · rw [s7b_edgeSegment_firstHalf P M a hi, hie]
      exact hmem
  have hc₁ : IsCrossing (firstHalf P M a) {i₁, i₂} :=
    ⟨i₁, i₂, rfl, hrem', crossingPoint yP, hseg i₁ e₁ hi₁ (by rw [hval]; simp),
      hseg i₂ e₂ hi₂ (by rw [hval]; simp)⟩
  refine ⟨⟨{i₁, i₂}, hc₁⟩, Subtype.ext ?_⟩
  show Finset.image (firstHalfIndex M a) {i₁, i₂} = y.val
  rw [hval]
  simp only [Finset.image_insert, Finset.image_singleton, hi₁, hi₂]

include hd in
/-- **A crossing of `Q` with both labels in `a..M−1` and, on the cut edge `a`, centre parameter at
least `r`, is the image of a crossing of `λ₂`.** -/
theorem s7p_mem_range_second (y : Crossing Q) (hy : ¬ ContactAffected M a y.val)
    (hrange : ∀ e ∈ y.val, (e - a).val < secondHalfSize M a)
    (hcut : ∀ j, y.val = {a, j} → r ≤ edgeParameter P a j) :
    ∃ c, s7b_secondCrossingQ hn hd.hsep hd.hm hd.hQC c = y := by
  have hyP : IsCrossing P y.val := (hd.hQC _ hy).mp y.property
  obtain ⟨e₁, e₂, hval, hrem, -⟩ := hyP
  obtain ⟨i₁, hi₁⟩ := (cyclicRangeIndex_range (secondHalfSize_le M a) a e₁).mpr
    (hrange e₁ (by rw [hval]; simp))
  obtain ⟨i₂, hi₂⟩ := (cyclicRangeIndex_range (secondHalfSize_le M a) a e₂).mpr
    (hrange e₂ (by rw [hval]; simp))
  have hi₁' : secondHalfEdgeIndex M a i₁ = e₁ := hi₁
  have hi₂' : secondHalfEdgeIndex M a i₂ = e₂ := hi₂
  have hnotP : ¬ ContactAffected M a {e₁, e₂} := by rw [← hval]; exact hy
  have hrem' : remote i₁ i₂ := by
    rw [← hi₁', ← hi₂', s7b_remote_secondHalfEdgeIndex_iff hn hd.hsep] at hrem
    rcases hrem with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h
    · exfalso; apply hnotP; left
      rw [← hi₁', ← hi₂', h1, h2, secondHalfEdgeIndex_last, secondHalfEdgeIndex_zero,
        Finset.pair_comm]
    · exfalso; apply hnotP; left
      rw [← hi₁', ← hi₂', h1, h2, secondHalfEdgeIndex_last, secondHalfEdgeIndex_zero]
  let yP : Crossing P := ⟨y.val, (hd.hQC _ hy).mp y.property⟩
  have hseg : ∀ (i : ZMod (secondHalfSize M a)) (e : ZMod n), secondHalfEdgeIndex M a i = e →
      e ∈ y.val → crossingPoint yP ∈ edgeSegment (secondHalf P M a) i := by
    intro i e hie he
    have hmem : crossingPoint yP ∈ edgeSegment P e := crossingPoint_mem yP e he
    by_cases hi : i = 0
    · subst hi
      rw [secondHalfEdgeIndex_zero] at hie
      subst hie
      rw [s7b_mem_edgeSegment_secondHalf_cut hn hd.hsep hd.hr hd.hr1]
      obtain ⟨j, -, hs⟩ := crossing_support_partner yP _ he
      have hspec := crossingParameter_spec yP _ he
      refine ⟨crossingParameter yP _ he, ?_, hspec.2.1, hspec.2.2⟩
      have hyv : y.val = {_, j} := hs
      have hpar : crossingParameter yP _ he = edgeParameter P _ j :=
        s7p_centre_visitParameter hn hd ⟨yP, ⟨_, he⟩⟩ hy j hs
      rw [hpar]
      exact hcut j hyv
    · rw [s7b_edgeSegment_secondHalf P M a hi, hie]
      exact hmem
  have hc₂ : IsCrossing (secondHalf P M a) {i₁, i₂} :=
    ⟨i₁, i₂, rfl, hrem', crossingPoint yP, hseg i₁ e₁ hi₁' (by rw [hval]; simp),
      hseg i₂ e₂ hi₂' (by rw [hval]; simp)⟩
  refine ⟨⟨{i₁, i₂}, hc₂⟩, Subtype.ext ?_⟩
  show Finset.image (secondHalfEdgeIndex M a) {i₁, i₂} = y.val
  rw [hval]
  simp only [Finset.image_insert, Finset.image_singleton, hi₁', hi₂']

/-! ##### `x_split`: a non-neighbour of `x` lies in one of the two arcs -/

variable (huniq : ∀ y : Crossing Q, ContactAffected M a y.val → y.val = {a, contactLeg f M})

include hd huniq in
/-- **`x_split`**: a crossing `y ≠ x` not interlacing `x` is the image of a half crossing. -/
theorem s7p_x_split (y : Crossing Q) (hyx : y ≠ s7p_x f hc)
    (hxy : ¬ Interlaces hn hd.hQ (s7p_x f hc) y) :
    y ∈ Set.range (s7b_firstCrossingQ hn hd.hsep hd.hm hd.hQC) ∪
      Set.range (s7b_secondCrossingQ hn hd.hsep hd.hm hd.hQC) := by
  have hy : ¬ ContactAffected M a y.val := fun h => hyx (Subtype.ext (huniq y h))
  obtain ⟨y₀, y₁, hy01⟩ := crossing_visits_exist y
  have ha := s7e_a_ne_leg f hd.hsep
  let xa : {i // i ∈ (s7p_x f hc).val} := ⟨a, by simp [s7p_x]⟩
  let xl : {i // i ∈ (s7p_x f hc).val} := ⟨contactLeg f M, by simp [s7p_x]⟩
  have hxaxl : xa ≠ xl := fun h => ha (congrArg Subtype.val h)
  have hxl : (⟨s7p_x f hc, xl⟩ : Visit Q) = s7e_vl hc := s7p_xl_eq hd f hc
  -- the negated interlacement, for the two visit orders
  have key : ∀ w₀ w₁ : {i // i ∈ y.val}, w₀ ≠ w₁ →
      ¬ (s7p_cyc (s7p_kappa hn hd.hQ.1 M (s7e_va hc)) (s7p_kappa hn hd.hQ.1 M ⟨y, w₀⟩)
            (s7p_kappa hn hd.hQ.1 M (s7e_vl hc)) ∧
          s7p_cyc (s7p_kappa hn hd.hQ.1 M (s7e_vl hc)) (s7p_kappa hn hd.hQ.1 M ⟨y, w₁⟩)
            (s7p_kappa hn hd.hQ.1 M (s7e_va hc))) := by
    intro w₀ w₁ hne hcyc
    apply hxy
    rw [s7p_interlaces_iff hn hd.hQ M]
    refine ⟨hyx.symm, xa, xl, w₀, w₁, hxaxl, hne, ?_, ?_⟩
    · rw [hxl]; exact hcyc.1
    · rw [hxl]; exact hcyc.2
  have hb0 := s7p_kappa_persistent_bounds hn hd ⟨y, y₀⟩ hy
  have hb1 := s7p_kappa_persistent_bounds hn hd ⟨y, y₁⟩ hy
  have hva := s7p_kappa_va_bounds hn hd f hc
  have hne0 : s7p_kappa hn hd.hQ.1 M ⟨y, y₀⟩ ≠ s7p_kappa hn hd.hQ.1 M (s7e_va hc) :=
    fun h => hyx (congrArg Sigma.fst (s7p_kappa_injective hn hd.hQ M h))
  have hne1 : s7p_kappa hn hd.hQ.1 M ⟨y, y₁⟩ ≠ s7p_kappa hn hd.hQ.1 M (s7e_va hc) :=
    fun h => hyx (congrArg Sigma.fst (s7p_kappa_injective hn hd.hQ M h))
  have hD := s7p_D_bounds hn hd
  have hη := hd.hη
  have hηr := hd.hηr
  have hηr1 := hd.hηr1
  have hDn' : (contactDistance M a : ℝ) + 3 ≤ n := by
    have : contactDistance M a + 3 ≤ n := by have := s7p_n5 hn hd; omega
    exact_mod_cast this
  -- the dichotomy: both visits of `y` before the contact `a`-visit, or both after
  have hdich : (s7p_kappa hn hd.hQ.1 M ⟨y, y₀⟩ < s7p_kappa hn hd.hQ.1 M (s7e_va hc) ∧
        s7p_kappa hn hd.hQ.1 M ⟨y, y₁⟩ < s7p_kappa hn hd.hQ.1 M (s7e_va hc)) ∨
      (s7p_kappa hn hd.hQ.1 M (s7e_va hc) < s7p_kappa hn hd.hQ.1 M ⟨y, y₀⟩ ∧
        s7p_kappa hn hd.hQ.1 M (s7e_va hc) < s7p_kappa hn hd.hQ.1 M ⟨y, y₁⟩) := by
    rcases lt_or_gt_of_ne hne0 with h0 | h0 <;> rcases lt_or_gt_of_ne hne1 with h1 | h1
    · exact Or.inl ⟨h0, h1⟩
    · exfalso
      apply key y₁ y₀ hy01.symm
      unfold s7p_cyc
      cases f
      · have hvl := s7p_kappa_vl_false hn hd false hc rfl
        exact ⟨Or.inl ⟨by linarith, by linarith⟩, Or.inr (Or.inl ⟨by linarith, by linarith⟩)⟩
      · have hvl := s7p_kappa_vl_true hn hd true hc rfl
        exact ⟨Or.inr (Or.inr ⟨by linarith, by linarith⟩), Or.inl ⟨by linarith, by linarith⟩⟩
    · exfalso
      apply key y₀ y₁ hy01
      unfold s7p_cyc
      cases f
      · have hvl := s7p_kappa_vl_false hn hd false hc rfl
        exact ⟨Or.inl ⟨by linarith, by linarith⟩, Or.inr (Or.inl ⟨by linarith, by linarith⟩)⟩
      · have hvl := s7p_kappa_vl_true hn hd true hc rfl
        exact ⟨Or.inr (Or.inr ⟨by linarith, by linarith⟩), Or.inl ⟨by linarith, by linarith⟩⟩
    · exact Or.inr ⟨h0, h1⟩
  have hva' := abs_lt.mp (s7e_va_param_near hn hd.hQ f hd.hw hc)
  have hDa : (a - M).val = contactDistance M a := rfl
  rcases hdich with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · -- both visits before the `a`-visit: `y` is a `λ₁`-image
    left
    have hvisit : ∀ w : {i // i ∈ y.val},
        s7p_kappa hn hd.hQ.1 M ⟨y, w⟩ < s7p_kappa hn hd.hQ.1 M (s7e_va hc) →
        (w.val - M).val < firstHalfSize M a ∧ (w.val = a → visitParameter (⟨y, w⟩ : Visit Q) < r) := by
      intro w hw
      rw [s7p_kappa_eq, s7p_kappa_eq, s7e_va_edge, hDa] at hw
      have hp := visitPosition_interior hn hd.hQ.1 (⟨y, w⟩ : Visit Q)
      have hlt : (((w.val - M).val : ℕ) : ℝ) < contactDistance M a + 1 := by linarith
      have hlt' : (w.val - M).val < contactDistance M a + 1 := by exact_mod_cast hlt
      refine ⟨by rw [show firstHalfSize M a = contactDistance M a + 1 from rfl]; exact hlt', ?_⟩
      intro hwa
      have hd' : (w.val - M).val = contactDistance M a := by rw [hwa]; exact hDa
      rw [hd'] at hw
      have h3 := s7e_persist_a hn hd.hQ hd.hw ⟨y, w⟩ hy hwa
      by_contra hge
      push Not at hge
      rw [abs_of_nonneg (by linarith)] at h3
      linarith
    obtain ⟨hw0, hw0a⟩ := hvisit y₀ h0
    obtain ⟨hw1, hw1a⟩ := hvisit y₁ h1
    apply s7p_mem_range_first hn hd y hy
    · intro e he
      rcases crossing_visits_exhaust y y₀ y₁ hy01 ⟨e, he⟩ with h | h
      · rw [show e = y₀.val from congrArg Subtype.val h]; exact hw0
      · rw [show e = y₁.val from congrArg Subtype.val h]; exact hw1
    · intro j hyj
      have hamem : a ∈ y.val := by rw [hyj]; simp
      have hcP : IsCrossing P {a, j} := by rw [← hyj]; exact (hd.hQC _ hy).mp y.property
      have hnot : ¬ ContactAffected M a {a, j} := by rw [← hyj]; exact hy
      rw [← hd.hside j hcP hnot]
      rcases crossing_visits_exhaust y y₀ y₁ hy01 ⟨a, hamem⟩ with h | h
      · have hwa : y₀.val = a := (congrArg Subtype.val h).symm
        have := hw0a hwa
        rwa [visitParameter_eq_of_support_pair hn hd.hQ.1 ⟨y, y₀⟩ j (by rw [hwa]; exact hyj), hwa]
          at this
      · have hwa : y₁.val = a := (congrArg Subtype.val h).symm
        have := hw1a hwa
        rwa [visitParameter_eq_of_support_pair hn hd.hQ.1 ⟨y, y₁⟩ j (by rw [hwa]; exact hyj), hwa]
          at this
  · -- both visits after the `a`-visit: `y` is a `λ₂`-image
    right
    have hvisit : ∀ w : {i // i ∈ y.val},
        s7p_kappa hn hd.hQ.1 M (s7e_va hc) < s7p_kappa hn hd.hQ.1 M ⟨y, w⟩ →
        (w.val - a).val < secondHalfSize M a ∧ (w.val = a → r < visitParameter (⟨y, w⟩ : Visit Q)) := by
      intro w hw
      rw [s7p_kappa_eq, s7p_kappa_eq, s7e_va_edge, hDa] at hw
      have hp := visitPosition_interior hn hd.hQ.1 (⟨y, w⟩ : Visit Q)
      have hge : (contactDistance M a : ℝ) < (((w.val - M).val : ℕ) : ℝ) + 1 := by linarith
      have hge' : contactDistance M a ≤ (w.val - M).val := by
        have : contactDistance M a < (w.val - M).val + 1 := by exact_mod_cast hge
        omega
      have hdlt : (w.val - M).val < n := ZMod.val_lt _
      have hsub : (w.val - a).val = (w.val - M).val - contactDistance M a := by
        have h' : w.val - a = (w.val - M) - (a - M) := by ring
        rw [h', ZMod.val_sub hge', hDa]
      have hsub' : (w.val - a).val < secondHalfSize M a := by
        rw [hsub]
        have : secondHalfSize M a = n - contactDistance M a := rfl
        omega
      refine ⟨hsub', ?_⟩
      intro hwa
      have hd' : (w.val - M).val = contactDistance M a := by rw [hwa]; exact hDa
      rw [hd'] at hw
      have h3 := s7e_persist_a hn hd.hQ hd.hw ⟨y, w⟩ hy hwa
      by_contra hge
      push Not at hge
      rw [abs_of_nonpos (by linarith)] at h3
      linarith
    obtain ⟨hw0, hw0a⟩ := hvisit y₀ h0
    obtain ⟨hw1, hw1a⟩ := hvisit y₁ h1
    apply s7p_mem_range_second hn hd y hy
    · intro e he
      rcases crossing_visits_exhaust y y₀ y₁ hy01 ⟨e, he⟩ with h | h
      · rw [show e = y₀.val from congrArg Subtype.val h]; exact hw0
      · rw [show e = y₁.val from congrArg Subtype.val h]; exact hw1
    · intro j hyj
      have hamem : a ∈ y.val := by rw [hyj]; simp
      have hcP : IsCrossing P {a, j} := by rw [← hyj]; exact (hd.hQC _ hy).mp y.property
      have hnot : ¬ ContactAffected M a {a, j} := by rw [← hyj]; exact hy
      have hQgt : r < edgeParameter Q a j := by
        rcases crossing_visits_exhaust y y₀ y₁ hy01 ⟨a, hamem⟩ with h | h
        · have hwa : y₀.val = a := (congrArg Subtype.val h).symm
          have := hw0a hwa
          rwa [visitParameter_eq_of_support_pair hn hd.hQ.1 ⟨y, y₀⟩ j (by rw [hwa]; exact hyj), hwa]
            at this
        · have hwa : y₁.val = a := (congrArg Subtype.val h).symm
          have := hw1a hwa
          rwa [visitParameter_eq_of_support_pair hn hd.hQ.1 ⟨y, y₁⟩ j (by rw [hwa]; exact hyj), hwa]
            at this
      exact not_lt.mp (fun hlt => absurd ((hd.hside j hcP hnot).mpr hlt) (not_lt.mpr hQgt.le))

/-! ##### The interlacement transfer on one side polygon -/

include hd huniq in
/-- **The interlacement transfer** (U_S7B_REPORT §2.2) on a side polygon: `s7b_PivotSplit` of the
side's interlacement, the halves' interlacements, the half crossing maps and the contact crossing. -/
theorem s7p_pivotSplit (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a)) :
    s7b_PivotSplit (Interlaces hn hd.hQ) (Interlaces (contactHalfSizes_bounds hn hd.hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hd.hsep).2.1 h₂)
      (s7b_firstCrossingQ hn hd.hsep hd.hm hd.hQC) (s7b_secondCrossingQ hn hd.hsep hd.hm hd.hQC)
      (s7p_x f hc) where
  split :=
    { inj₁ := s7b_firstCrossingQ_injective hn hd.hsep hd.hm hd.hQC
      inj₂ := s7b_secondCrossingQ_injective hn hd.hsep hd.hm hd.hQC
      disjoint := s7b_firstCrossingQ_ne_secondCrossingQ hn hd.hsep hd.hm hd.hQC
      rel₁ := s7p_rel_first hn hd h₁
      rel₂ := s7p_rel_second hn hd h₂
      cross := s7p_cross hn hd
      cross' := fun c₁ c₂ => s7p_cross' hn hd c₁ c₂ }
  x_not₁ := fun c h => s7b_firstCrossingQ_not_affected hn hd.hsep hd.hm hd.hQC c
    (by rw [h]; exact s7p_x_affected f hc)
  x_not₂ := fun c h => s7b_secondCrossingQ_not_affected hn hd.hsep hd.hm hd.hQC c
    (by rw [h]; exact s7p_x_affected f hc)
  x_free₁ := fun c => ⟨s7p_x_free_first hn hd f hc c,
    fun h => s7p_x_free_first hn hd f hc c (interlaces_symm hn hd.hQ h)⟩
  x_free₂ := fun c => ⟨s7p_x_free_second hn hd f hc c,
    fun h => s7p_x_free_second hn hd f hc c (interlaces_symm hn hd.hQ h)⟩
  x_split := fun y hyx hxy _ => s7p_x_split hn hd f hc huniq y hyx hxy

end S7PSide

/-! #### At the wall: the side data of `P₋(t)`, `P₊(t)` and the two transfers below a radius -/

section S7PWall

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} {r η δ : ℝ}
  (h : g.SlidingAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ) (t : g.SideParameter)
  (ht : t.val < δ)

include h hloc ht in
/-- **Side-of-`r` agreement between a side polygon and the centre** for a persistent `a`-visit: the
Cramer parameter is continuous and stays `3η` away from `r` on the whole interval `|u| < δ`
(`VertexLocalData.windows` at every `u`, including the centre), so its sign relative to `r` is
constant on `|u| ≤ t` (`s7a2_pos_of_ne_zero`, applied to `±(param − r)`). -/
theorem s7p_side_of_r (hη : 0 < η) (b : Bool) :
    ∀ j, IsCrossing g.center {a, j} → ¬ ContactAffected M a {a, j} →
    (edgeParameter (g.curve (g.sideTime b t)) a j < r ↔ edgeParameter g.center a j < r) := by
  intro j hc hnot
  have hcont : ∀ u : g.Parameter, |u.val| < δ →
      ContinuousAt (fun w : g.Parameter => edgeParameter (g.curve w) a j - r) u :=
    fun u hu => (s7a2_continuousAt_edgeParameter hn g h.1 hloc hu hc hnot).sub continuousAt_const
  have hne : ∀ u : g.Parameter, |u.val| < δ → edgeParameter (g.curve u) a j - r ≠ 0 := by
    intro u hu h0
    have hcr : IsCrossing (g.curve u) {a, j} := (s7a2_crossing_iff hn g hloc hu {a, j} hnot).mpr hc
    have hw := (hloc u hu).windows.2.1 none j hcr hnot
    simp only [contactWindowEdge, contactWindowCenter] at hw
    rw [h0, abs_zero] at hw
    linarith
  have hcont' : ∀ u : g.Parameter, |u.val| < δ →
      ContinuousAt (fun w : g.Parameter => -(edgeParameter (g.curve w) a j - r)) u :=
    fun u hu => (hcont u hu).neg
  have hne' : ∀ u : g.Parameter, |u.val| < δ → -(edgeParameter (g.curve u) a j - r) ≠ 0 :=
    fun u hu => neg_ne_zero.mpr (hne u hu)
  have h0 : |(g.zeroParameter).val| ≤ t.val := by
    simp only [WallGerm.zeroParameter, abs_zero]
    exact t.property.1.le
  have hlt : |(g.sideTime b t).val| < δ := by rw [g.sideTime_val_abs]; exact ht
  have hz0 : |(g.zeroParameter).val| < δ := lt_of_le_of_lt h0 ht
  constructor
  · intro h1
    by_contra h2
    have hpos : 0 < -(edgeParameter (g.curve (g.sideTime b t)) a j - r) := by linarith
    have hc0 := s7a2_pos_of_ne_zero g ht hcont' hne' b hpos g.zeroParameter h0
    have h2' : ¬ edgeParameter (g.curve g.zeroParameter) a j < r := h2
    linarith
  · intro h1
    by_contra h2
    have hpos : 0 < edgeParameter (g.curve (g.sideTime b t)) a j - r :=
      lt_of_le_of_ne (by linarith) (hne _ hlt).symm
    have hc0 := s7a2_pos_of_ne_zero g ht hcont hne b hpos g.zeroParameter h0
    have h1' : edgeParameter (g.curve g.zeroParameter) a j < r := h1
    linarith

include h hloc ht in
/-- The side data of the side polygon `g.curve (g.sideTime b t)` at a sliding wall. -/
theorem s7p_sideData (hr0 : 0 < r) (hr1 : r < 1) (hr : g.center M = edgePoint g.center a r)
    (hη : 0 < η) (hηr : 4 * η < r) (hηr1 : 4 * η < 1 - r) (b : Bool) :
    s7p_SideData M a g.center (g.curve (g.sideTime b t)) r η where
  hsep := h.1.1
  hz := h.1.2.1
  hm := h.1.2.2.2.1
  hr := hr
  hr0 := hr0
  hr1 := hr1
  hη := hη
  hηr := hηr
  hηr1 := hηr1
  hQ := s7a_sideGeneric g b
  hQC := s7e_hQC hn g h t b
  hw := s7e_hw hn g hloc t ht b
  hord := (s7e_hL hn g hloc t ht b).parameter_order
  hside := s7p_side_of_r hn g h hloc t ht hη b

end S7PWall

/-- **The two interlacement transfers below a radius** — exactly the hypotheses `hsplitm`, `hsplitp` of
`s7e_contactSector_of_pivotSplit` (PLAN §3.3 sliding (2), U_S7B_REPORT §2.2). -/
theorem s7p_exists_pivotSplit (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.SlidingAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      s7b_PivotSplit (Interlaces hn (s7a_sideGeneric g false))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false)) (s7e_xm hn h t) ∧
      s7b_PivotSplit (Interlaces hn (s7a_sideGeneric g true))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true)) (s7e_xp hn h t) := by
  obtain ⟨r, η, hr0, hr1, hr, hη, hηr, hηr1, δ, hδ, -, hloc⟩ :=
    s7a2_exists_intervalLocal hn g M a h.1
  refine ⟨δ, hδ, fun t ht => ⟨?_, ?_⟩⟩
  · exact s7p_pivotSplit hn (s7p_sideData hn g h hloc t ht hr0 hr1 hr hη hηr hηr1 false)
      (s7e_leg g M a) (s7e_hxm hn g h t) (s7e_huniq_m hn g h t) h₁ h₂
  · exact s7p_pivotSplit hn (s7p_sideData hn g h hloc t ht hr0 hr1 hr hη hηr hηr1 true)
      (!s7e_leg g M a) (s7e_hxp hn g h t) (s7e_huniq_p hn g h t) h₁ h₂

/-- **The leaf reduced to the termwise identity alone.**  With both interlacement transfers supplied
(`s7p_exists_pivotSplit`), `s7_sliding_law_at` follows from the termwise identity `hterm` of
`s7e_contactSector_of_pivotSplit` below some radius — quantified over ANY proofs `hsplitm`, `hsplitp`
of the two transfers (they are propositions, so any supplier's proofs serve).  This is PLAN §3.3
sliding (2)-(3) minus the interlacement transfer: `s7b_SlidingTransport.ret`, the relocated corner
correspondence and rotation equality, the coefficient/selector bookkeeping (W2_S7E_REPORT §2, item 2). -/
theorem s7p_sliding_law_at_of_hterm (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n}
    (h : g.SlidingAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (δc : ℝ) (hδc : 0 < δc)
    (hterm : ∀ t : g.SideParameter, t.val < δc →
      ∀ (hsplitm : s7b_PivotSplit (Interlaces hn (s7a_sideGeneric g false))
          (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
          (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
          (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false))
          (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false)) (s7e_xm hn h t))
        (hsplitp : s7b_PivotSplit (Interlaces hn (s7a_sideGeneric g true))
          (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
          (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
          (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true))
          (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true)) (s7e_xp hn h t)),
        ∀ q, s7e_term hn (s7a_sideGeneric g true)
            ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t true)
              (s7a_sideGeneric g true) h₁ h₂ (s7e_xp hn h t) hsplitp).symm q).1 -
          s7e_term hn (s7a_sideGeneric g false)
            ((s7b_slidingDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t false)
              (s7a_sideGeneric g false) h₁ h₂ (s7e_xm hn h t) hsplitm).symm q).1 =
          (g.contactSign M a : ℤ) *
            (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ q.1.1 *
              s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ q.2.1)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  obtain ⟨δs, hδs, hsplit⟩ := s7p_exists_pivotSplit hn g h h₁ h₂
  refine s7e_sliding_law_at_of_contact hn g h h₁ h₂ ⟨min δs δc, lt_min hδs hδc, fun t ht => ?_⟩
  have hts : t.val < δs := lt_of_lt_of_le ht (min_le_left _ _)
  have htc : t.val < δc := lt_of_lt_of_le ht (min_le_right _ _)
  exact s7e_contactSector_of_pivotSplit hn g h t h₁ h₂ (hsplit t hts).1 (hsplit t hts).2
    (hterm t htc (hsplit t hts).1 (hsplit t hts).2)

end S7PSplit


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
