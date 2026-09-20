-- W3_Assembled.lean — corner wave 3 (row 110 thm:C-S7) MERGE, 2026-09-15: W3_Skeleton.lean with the eight unit blocks
-- (sliding: SPLIT s7p_, RET s7r_, ROT s7q_ before `s7_sliding_law_at`; bigon: F s7f_, SITE s7s_, BLOCK s7k_, J s7j_, K s7z_
-- before `s7_bigon_law_at`) and the `w3_` glue: `s7q_box_split` discharged by `s7p_exists_pivotSplit`; the remaining
-- inputs of each leaf as named Props (`w3_Sliding{Ret,Order,Carriers}`, `w3_Bigon{FSector,ReturnedRows,OneNewborn}`) with
-- `w3_s7_sliding_law_at_of` / `w3_s7_bigon_law_at_of`.  The five frozen declarations are byte-identical to the skeleton;
-- both leaves keep their `sorry` (their inputs are not all proved).  See W3_ASSEMBLY_REPORT.md.
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


/-! ### Unit RET (prefix `s7r_`; serving the leaf `s7_sliding_law_at`): the first-return law
`s7b_SlidingTransport.ret` (U_S7B_REPORT §2.1, W2_S7E_REPORT §2 item 2).
Part I — a generic first-return engine on any generic polygon: a mark is *transit* for `(S, ι)`
when it is off the image of `ι` and the smoothing successor acts on it as the plain successor;
if every mark cyclically between `u` and `m'` is transit, the `f`-iterates of `nextMark u` reach
`m'` without touching the image (descent on the number of marks between, `s7a_between_trans`).
Part II — the side polygon of a sliding wall with leg `M − 1` (`f = false`): the marks of `Q`
carried from the halves, their parameter order (the half laws `s7b_visitParameter_*` composed with
`VertexLocalData.visit_order`, and the side-of-`r` law), the non-image marks, and the first-return
law itself.  DEFECT (rule 4): on the side with leg `M` (`f = true`) `s7b_SlidingTransport.ret` is
FALSE as stated — there `nextMark μ_M = v_ℓ` (`s7e_owner_vl_eq_vertex`), so the first `f`-step from
`ι (inl (inl 0)) = μ_M` lands on `ι (inr (inl 0)) = v_ℓ`, an image mark of the OTHER half; the
correct mark map on that side sends `inl (inl 0) ↦ v_a` and `inr (inl 0) ↦ μ_M` (the leg visit is
the skipped extra corner).  It is stated as `s7r_SlidingTransport'` below. -/

section S7RReturn

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)

/-- A mark is *transit* for `(S, ι)`: off the image of `ι`, and the smoothing successor of `S` acts
on it as the plain successor. -/
def s7r_Transit {β : Type*} (S : Finset (Crossing P)) (ι : β → Mark P) (w : Mark P) : Prop :=
  w ∉ Set.range ι ∧ smoothingSuccessor hn hP S w = nextMark hn hP w

omit [NeZero n] in
theorem s7r_not_between_self (p r : Mark P) :
    ¬ traversalBetween (markPosition hn hP.1 p) (markPosition hn hP.1 p) (markPosition hn hP.1 r) := by
  rw [s7e_between_iff hn hP]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith

/-- The successor of `u` lies cyclically between `u` and any third mark `m'`. -/
theorem s7r_between_nextMark (u m' : Mark P) (hne : u ≠ m') (hne' : nextMark hn hP u ≠ m') :
    traversalBetween (markPosition hn hP.1 u) (markPosition hn hP.1 (nextMark hn hP u))
      (markPosition hn hP.1 m') := by
  have hne2 : u ≠ nextMark hn hP u := (markSuccessor_ne_self hn hP u).symm
  rcases s7a_between_or hn hP u (nextMark hn hP u) m' hne2 hne' hne with h | h
  · exact h
  · exact absurd h (nextMark_no_mark_between hn hP rfl m')

/-- The marks between `nextMark u` and `m'` are strictly fewer than those between `u` and `m'`. -/
theorem s7r_card_lt (u m' : Mark P) (hne : u ≠ m') (hnext : nextMark hn hP u ≠ m') :
    (Finset.univ.filter fun w : Mark P => traversalBetween (markPosition hn hP.1 (nextMark hn hP u))
        (markPosition hn hP.1 w) (markPosition hn hP.1 m')).card <
    (Finset.univ.filter fun w : Mark P => traversalBetween (markPosition hn hP.1 u)
        (markPosition hn hP.1 w) (markPosition hn hP.1 m')).card := by
  have hb := s7r_between_nextMark hn hP u m' hne hnext
  apply Finset.card_lt_card
  have hsubset : (Finset.univ.filter fun w : Mark P => traversalBetween
        (markPosition hn hP.1 (nextMark hn hP u)) (markPosition hn hP.1 w) (markPosition hn hP.1 m')) ⊆
      (Finset.univ.filter fun w : Mark P => traversalBetween (markPosition hn hP.1 u)
        (markPosition hn hP.1 w) (markPosition hn hP.1 m')) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact s7a_between_trans hn hP hb hw
  refine (Finset.ssubset_iff_of_subset hsubset).mpr ⟨nextMark hn hP u, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hb
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact s7r_not_between_self hn hP _ _

/-- **The reach lemma**: if every mark cyclically between `u` and `m'` is transit, the iterates of
the smoothing successor starting at `nextMark u` reach `m'` while staying off the image. -/
theorem s7r_reach_of_transit {β : Type*} (S : Finset (Crossing P)) (ι : β → Mark P) (m' : Mark P) :
    ∀ (c : ℕ) (u : Mark P),
      (Finset.univ.filter fun w : Mark P => traversalBetween (markPosition hn hP.1 u)
        (markPosition hn hP.1 w) (markPosition hn hP.1 m')).card = c →
      u ≠ m' →
      (∀ w, traversalBetween (markPosition hn hP.1 u) (markPosition hn hP.1 w) (markPosition hn hP.1 m') →
        s7r_Transit hn hP S ι w) →
      ∃ k : ℕ, ((smoothingSuccessor hn hP S) ^ k) (nextMark hn hP u) = m' ∧
        ∀ j : ℕ, j < k → ((smoothingSuccessor hn hP S) ^ j) (nextMark hn hP u) ∉ Set.range ι := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro u hc hne htr
    by_cases hnext : nextMark hn hP u = m'
    · exact ⟨0, by simpa using hnext, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · have hb := s7r_between_nextMark hn hP u m' hne hnext
      have htrans := htr _ hb
      have hlt := s7r_card_lt hn hP u m' hne hnext
      rw [hc] at hlt
      obtain ⟨k, hk, hgap⟩ := ih _ hlt (nextMark hn hP u) rfl hnext
        (fun w hw => htr w (s7a_between_trans hn hP hb hw))
      refine ⟨k + 1, ?_, ?_⟩
      · rw [pow_succ, Equiv.Perm.mul_apply, htrans.2]; exact hk
      · intro j hj
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · simpa using htrans.1
        · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0.ne'
          rw [pow_succ, Equiv.Perm.mul_apply, htrans.2]
          exact hgap j' (by omega)

/-- **The hit lemma**: with one image mark `m'` as beacon, every mark reaches the image provided each
off-image mark either steps into the image or steps as the plain successor. -/
theorem s7r_hit_of_transit {β : Type*} (S : Finset (Crossing P)) (ι : β → Mark P) (m' : Mark P)
    (hm' : m' ∈ Set.range ι)
    (hstep : ∀ w : Mark P, w ∉ Set.range ι →
      (∃ j : ℕ, ((smoothingSuccessor hn hP S) ^ j) w ∈ Set.range ι) ∨
        smoothingSuccessor hn hP S w = nextMark hn hP w) :
    ∀ (c : ℕ) (u : Mark P),
      (Finset.univ.filter fun w : Mark P => traversalBetween (markPosition hn hP.1 u)
        (markPosition hn hP.1 w) (markPosition hn hP.1 m')).card = c →
      ∃ j : ℕ, ((smoothingSuccessor hn hP S) ^ j) u ∈ Set.range ι := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro u hc
    by_cases hu : u ∈ Set.range ι
    · exact ⟨0, by simpa using hu⟩
    · rcases hstep u hu with ⟨j, hj⟩ | h1
      · exact ⟨j, hj⟩
      · by_cases hne : u = m'
        · exact absurd (hne ▸ hm') hu
        · by_cases hnext : nextMark hn hP u = m'
          · exact ⟨1, by rw [pow_one, h1, hnext]; exact hm'⟩
          · have hlt := s7r_card_lt hn hP u m' hne hnext
            rw [hc] at hlt
            obtain ⟨j, hj⟩ := ih _ hlt (nextMark hn hP u) rfl
            exact ⟨j + 1, by rw [pow_succ, Equiv.Perm.mul_apply, h1]; exact hj⟩

/-- A reach from `ι b` through `u := selectedMarkPerm S (ι b)` is a `step` of `s7b_ReturnTransport`. -/
theorem s7r_step_of_reach {β : Type*} (S : Finset (Crossing P)) (ι : β → Mark P) (b : β) (m' u : Mark P)
    (hu : selectedMarkPerm S (ι b) = u)
    (hreach : ∃ k : ℕ, ((smoothingSuccessor hn hP S) ^ k) (nextMark hn hP u) = m' ∧
        ∀ j : ℕ, j < k → ((smoothingSuccessor hn hP S) ^ j) (nextMark hn hP u) ∉ Set.range ι) :
    ∃ k : ℕ, 0 < k ∧ ((smoothingSuccessor hn hP S) ^ k) (ι b) = m' ∧
      ∀ j : ℕ, 0 < j → j < k → ((smoothingSuccessor hn hP S) ^ j) (ι b) ∉ Set.range ι := by
  obtain ⟨k, hk, hgap⟩ := hreach
  have hf : smoothingSuccessor hn hP S (ι b) = nextMark hn hP u := by
    rw [← hu]; rfl
  refine ⟨k + 1, Nat.succ_pos k, ?_, ?_⟩
  · rw [pow_succ, Equiv.Perm.mul_apply, hf]; exact hk
  · intro j hj0 hjk
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0.ne'
    rw [pow_succ, Equiv.Perm.mul_apply, hf]
    exact hgap j' (by omega)

/-- Composition of reaches through one off-image mark `w` (the contact `a`-visit, whose smoothing
successor is NOT its plain successor). -/
theorem s7r_reach_trans {β : Type*} (S : Finset (Crossing P)) (ι : β → Mark P) {v w m' : Mark P}
    (h1 : ∃ k : ℕ, ((smoothingSuccessor hn hP S) ^ k) v = w ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hP S) ^ j) v ∉ Set.range ι)
    (hw : w ∉ Set.range ι)
    (h2 : ∃ k : ℕ, ((smoothingSuccessor hn hP S) ^ k) (smoothingSuccessor hn hP S w) = m' ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hP S) ^ j) (smoothingSuccessor hn hP S w) ∉ Set.range ι) :
    ∃ k : ℕ, ((smoothingSuccessor hn hP S) ^ k) v = m' ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hP S) ^ j) v ∉ Set.range ι := by
  obtain ⟨k₁, hk₁, hg₁⟩ := h1
  obtain ⟨k₂, hk₂, hg₂⟩ := h2
  have hstep : ∀ j : ℕ, ((smoothingSuccessor hn hP S) ^ (k₁ + 1 + j)) v =
      ((smoothingSuccessor hn hP S) ^ j) (smoothingSuccessor hn hP S w) := by
    intro j
    rw [show k₁ + 1 + j = j + (k₁ + 1) by omega, pow_add, Equiv.Perm.mul_apply, pow_succ',
      Equiv.Perm.mul_apply, hk₁]
  refine ⟨k₁ + 1 + k₂, ?_, ?_⟩
  · rw [hstep k₂]; exact hk₂
  · intro j hj
    rcases Nat.lt_or_ge j k₁ with hlt | hge
    · exact hg₁ j hlt
    · rcases Nat.eq_or_lt_of_le hge with heq | hgt
      · rw [← heq, hk₁]; exact hw
      · obtain ⟨j', rfl⟩ : ∃ j', j = k₁ + 1 + j' := ⟨j - (k₁ + 1), by omega⟩
        rw [hstep j']
        exact hg₂ j' (by omega)

/-- Key decoder (a): a mark cyclically between a mark `u` on edge `e` and the vertex `e + 1` lies on
edge `e` beyond `u` (wrap `e = −1` included). -/
theorem s7r_between_next_vertex (u w : Mark P) (e : ZMod n) (hu : s7e_mEdge u = e)
    (hb : traversalBetween (markPosition hn hP.1 u) (markPosition hn hP.1 w)
      (markPosition hn hP.1 (Sum.inl (e + 1)))) :
    s7e_mEdge w = e ∧ s7e_mParam u < s7e_mParam w := by
  rw [s7e_between_iff hn hP, markKey_vertex, s7e_markKey_eq hn hP u, s7e_markKey_eq hn hP w, hu] at hb
  have hpu0 := s7e_mParam_nonneg hn hP u
  have hpu1 := s7e_mParam_lt_one hn hP u
  have hpw0 := s7e_mParam_nonneg hn hP w
  have hpw1 := s7e_mParam_lt_one hn hP w
  have hw0 : (0 : ℝ) ≤ (s7e_mEdge w).val := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ e.val := Nat.cast_nonneg _
  rcases s7e_val_succ e with ⟨-, hval⟩ | ⟨-, hzero, hval⟩
  · rw [hval] at hb
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have he := s7e_edge_eq_of_key_sandwich hpu0 hpw0 hpw1 h1 h2
      refine ⟨he, ?_⟩
      rw [he] at h1; linarith
    · linarith
    · linarith
  · rw [hzero, ZMod.val_zero, Nat.cast_zero, hval] at hb
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
    · have h5 : n < (s7e_mEdge w).val + 2 := by
        have : ((n : ℝ)) < (s7e_mEdge w).val + 2 := by linarith
        exact_mod_cast this
      have h6 := ZMod.val_lt (s7e_mEdge w)
      have h7 : (s7e_mEdge w).val = n - 1 := by omega
      have h7' : ((s7e_mEdge w).val : ℝ) = (n : ℝ) - 1 := by
        rw [h7, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      have he : s7e_mEdge w = e := by
        apply ZMod.val_injective
        exact_mod_cast h7'.trans hval.symm
      refine ⟨he, ?_⟩
      rw [h7'] at h2; linarith

/-- Key decoder (b): a mark cyclically between two marks `u`, `m'` on one edge `e` with
`param u < param m'` lies on edge `e` with its parameter strictly between theirs. -/
theorem s7r_between_same_edge_of (u w m' : Mark P) (e : ZMod n) (hu : s7e_mEdge u = e)
    (hm' : s7e_mEdge m' = e) (hlt : s7e_mParam u < s7e_mParam m')
    (hb : traversalBetween (markPosition hn hP.1 u) (markPosition hn hP.1 w) (markPosition hn hP.1 m')) :
    s7e_mEdge w = e ∧ s7e_mParam u < s7e_mParam w ∧ s7e_mParam w < s7e_mParam m' := by
  rw [s7e_between_iff hn hP, s7e_markKey_eq hn hP u, s7e_markKey_eq hn hP w, s7e_markKey_eq hn hP m',
    hu, hm'] at hb
  have hpu0 := s7e_mParam_nonneg hn hP u
  have hpw0 := s7e_mParam_nonneg hn hP w
  have hpw1 := s7e_mParam_lt_one hn hP w
  have hpm1 := s7e_mParam_lt_one hn hP m'
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have he : s7e_mEdge w = e := s7e_edge_eq_of_key_sandwich hpu0 hpw0 hpw1 h1 (by linarith)
    rw [he] at h1 h2
    exact ⟨he, by linarith, by linarith⟩
  · linarith
  · linarith

end S7RReturn

section S7RSide

/-! #### Part II: a side polygon `Q` of a sliding wall with leg `M − 1` (`f = false`), relative to
the centre `P` with contact parameter `r` and window half-width `η`.  `hord` is
`VertexLocalData.visit_order` (the same-edge parameter order of persistent visits agrees between `Q`
and the centre) and `hside` the side-of-`r` law on edge `a` (sign constancy through the centre,
`s7a2_pos_of_ne_zero` at `u = 0`). -/

variable (hn : 3 ≤ n) {P Q : LabelledTuple n} (hQ : Generic Q) {M a : ZMod n}
  (hsep : ContactSeparated M a) (hz : pointZeroTriples P = {contactSupport M a})
  (hm : P M ∈ edgeInterior P a) {r η : ℝ} (hr : P M = edgePoint P a r) (hr0 : 0 < r) (hr1 : r < 1)
  (hη : 0 < η)
  (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
  (hw : ContactParameterWindows P Q M a r η)
  (hord : ∀ (u u' : Visit P) (hu : ¬ ContactAffected M a u.1.val) (hu' : ¬ ContactAffected M a u'.1.val),
    u.2.val = u'.2.val →
    (visitParameter (s7a_visit hQC u hu) < visitParameter (s7a_visit hQC u' hu') ↔
      visitParameter u < visitParameter u'))
  (hside : ∀ (u : Visit P) (hu : ¬ ContactAffected M a u.1.val), u.2.val = a →
    (visitParameter (s7a_visit hQC u hu) < r ↔ visitParameter u < r))
  (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a))

theorem s7r_firstVisitQ_eq (v : Visit (firstHalf P M a)) :
    s7b_firstVisitQ hn hsep hm hQC v =
      s7a_visit hQC (s7b_firstHalfVisit hn hsep hm v) (s7b_firstHalfCrossing_not_affected hn hsep hm v.1) :=
  rfl

theorem s7r_secondVisitQ_eq (v : Visit (secondHalf P M a)) :
    s7b_secondVisitQ hn hsep hm hQC v =
      s7a_visit hQC (s7b_secondHalfVisit hn hsep hm v) (s7b_secondHalfCrossing_not_affected hn hsep hm v.1) :=
  rfl

include hz hr hr0 hord in
/-- Same-edge order of the carried visits of `λ₁` on `Q` is the order on `λ₁` (equality of parameters
off the cut, the rescaling `r · t` on it, then `visit_order`). -/
theorem s7r_first_order (v v' : Visit (firstHalf P M a)) (he : v.2.val = v'.2.val) :
    visitParameter (s7b_firstVisitQ hn hsep hm hQC v) < visitParameter (s7b_firstVisitQ hn hsep hm hQC v') ↔
      visitParameter v < visitParameter v' := by
  rw [s7r_firstVisitQ_eq, s7r_firstVisitQ_eq,
    hord (s7b_firstHalfVisit hn hsep hm v) (s7b_firstHalfVisit hn hsep hm v')
      (s7b_firstHalfCrossing_not_affected hn hsep hm v.1) (s7b_firstHalfCrossing_not_affected hn hsep hm v'.1)
      (by rw [s7b_firstHalfVisit_edge hn hsep hm v, s7b_firstHalfVisit_edge hn hsep hm v', he])]
  by_cases hc : v.2.val = -1
  · have hc' : v'.2.val = -1 := he.symm.trans hc
    rw [s7b_visitParameter_firstHalfVisit_cut hn hsep hz hm hr v hc,
      s7b_visitParameter_firstHalfVisit_cut hn hsep hz hm hr v' hc']
    constructor
    · intro h; exact lt_of_not_ge fun h' => by nlinarith
    · intro h; nlinarith
  · have hc' : v'.2.val ≠ -1 := fun h => hc (he.trans h)
    rw [s7b_visitParameter_firstHalfVisit hn hsep hz hm v hc,
      s7b_visitParameter_firstHalfVisit hn hsep hz hm v' hc']

include hz hr hr1 hord in
theorem s7r_second_order (v v' : Visit (secondHalf P M a)) (he : v.2.val = v'.2.val) :
    visitParameter (s7b_secondVisitQ hn hsep hm hQC v) < visitParameter (s7b_secondVisitQ hn hsep hm hQC v') ↔
      visitParameter v < visitParameter v' := by
  rw [s7r_secondVisitQ_eq, s7r_secondVisitQ_eq,
    hord (s7b_secondHalfVisit hn hsep hm v) (s7b_secondHalfVisit hn hsep hm v')
      (s7b_secondHalfCrossing_not_affected hn hsep hm v.1) (s7b_secondHalfCrossing_not_affected hn hsep hm v'.1)
      (by rw [s7b_secondHalfVisit_edge hn hsep hm v, s7b_secondHalfVisit_edge hn hsep hm v', he])]
  by_cases hc : v.2.val = 0
  · have hc' : v'.2.val = 0 := he.symm.trans hc
    rw [s7b_visitParameter_secondHalfVisit_cut hn hsep hz hm hr v hc,
      s7b_visitParameter_secondHalfVisit_cut hn hsep hz hm hr v' hc']
    have h1r : 0 < 1 - r := by linarith
    constructor
    · intro h; exact lt_of_not_ge fun h' => by nlinarith
    · intro h; nlinarith
  · have hc' : v'.2.val ≠ 0 := fun h => hc (he.trans h)
    rw [s7b_visitParameter_secondHalfVisit hn hsep hz hm v hc,
      s7b_visitParameter_secondHalfVisit hn hsep hz hm v' hc']

include hQ hz hr hr0 hw hside h₁ in
/-- A carried cut visit of `λ₁` lies on edge `a` of `Q` below `r − 3η`. -/
theorem s7r_first_cut_lt (v : Visit (firstHalf P M a)) (hv : v.2.val = -1) :
    visitParameter (s7b_firstVisitQ hn hsep hm hQC v) < r - 3 * η := by
  have hlt : visitParameter (s7b_firstVisitQ hn hsep hm hQC v) < r := by
    rw [s7r_firstVisitQ_eq, hside (s7b_firstHalfVisit hn hsep hm v) (s7b_firstHalfCrossing_not_affected hn hsep hm v.1)
      (by rw [s7b_firstHalfVisit_edge hn hsep hm v, hv, firstHalfIndex_last]),
      s7b_visitParameter_firstHalfVisit_cut hn hsep hz hm hr v hv]
    have := s7e_visitParameter_lt_one (contactHalfSizes_bounds hn hsep).1.1 h₁ v
    nlinarith
  have hwin := s7e_persist_a hn hQ hw (s7b_firstVisitQ hn hsep hm hQC v)
    (s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1) (by rw [s7b_firstVisitQ_edge, hv, firstHalfIndex_last])
  rw [abs_of_neg (by linarith)] at hwin
  linarith

include hQ hz hr hr1 hw hside h₂ in
/-- A carried cut visit of `λ₂` lies on edge `a` of `Q` above `r + 3η`. -/
theorem s7r_second_cut_gt (v : Visit (secondHalf P M a)) (hv : v.2.val = 0) :
    r + 3 * η < visitParameter (s7b_secondVisitQ hn hsep hm hQC v) := by
  have hle : r ≤ visitParameter (s7b_secondVisitQ hn hsep hm hQC v) := by
    rw [← not_lt, s7r_secondVisitQ_eq, hside (s7b_secondHalfVisit hn hsep hm v)
      (s7b_secondHalfCrossing_not_affected hn hsep hm v.1)
      (by rw [s7b_secondHalfVisit_edge hn hsep hm v, hv, secondHalfEdgeIndex_zero]),
      s7b_visitParameter_secondHalfVisit_cut hn hsep hz hm hr v hv]
    have := s7e_visitParameter_pos (contactHalfSizes_bounds hn hsep).2.1 h₂ v
    intro h; nlinarith
  have hwin := s7e_persist_a hn hQ hw (s7b_secondVisitQ hn hsep hm hQC v)
    (s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1)
    (by rw [s7b_secondVisitQ_edge, hv, secondHalfEdgeIndex_zero])
  rcases lt_or_eq_of_le hle with h | h
  · rw [abs_of_pos (by linarith)] at hwin; linarith
  · rw [← h, sub_self, abs_zero] at hwin; linarith

/-! ##### The contact crossing `{a, M − 1}` on `Q` and the non-image marks -/

variable (hc : IsCrossing Q {a, contactLeg false M})
  (huniq : ∀ y : Crossing Q, ContactAffected M a y.val → y.val = {a, contactLeg false M})

omit [NeZero n] in
theorem s7r_leg_false : contactLeg false M = M - 1 := by simp [contactLeg]

theorem s7r_vl_affected : ContactAffected M a (s7e_vl hc).1.val := by
  rw [s7e_vl_fst]; exact (contactAffected_iff_leg _).mpr ⟨false, rfl⟩

theorem s7r_va_affected : ContactAffected M a (s7e_va hc).1.val :=
  (contactAffected_iff_leg _).mpr ⟨false, rfl⟩

/-- Which visits of `Q` are image marks of the sliding mark map. -/
theorem s7r_inr_mem_range_iff (vm w : Visit Q) :
    (Sum.inr w : Mark Q) ∈ Set.range (s7b_slidingMark hn hsep hm hQC vm) ↔
      w = vm ∨ (∃ v, s7b_firstVisitQ hn hsep hm hQC v = w) ∨ (∃ v, s7b_secondVisitQ hn hsep hm hQC v = w) := by
  constructor
  · rintro ⟨b, hb⟩
    rcases b with (i | v) | (i | v)
    · rw [s7b_slidingMark_inl_inl] at hb; exact absurd hb Sum.inl_ne_inr
    · rw [s7b_slidingMark_inl_inr] at hb; exact Or.inr (Or.inl ⟨v, Sum.inr_injective hb⟩)
    · by_cases hi : i = 0
      · subst hi; rw [s7b_slidingMark_inr_inl_zero] at hb; exact Or.inl (Sum.inr_injective hb).symm
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC vm hi] at hb; exact absurd hb Sum.inl_ne_inr
    · rw [s7b_slidingMark_inr_inr] at hb; exact Or.inr (Or.inr ⟨v, Sum.inr_injective hb⟩)
  · rintro (rfl | ⟨v, rfl⟩ | ⟨v, rfl⟩)
    · exact ⟨Sum.inr (Sum.inl 0), s7b_slidingMark_inr_inl_zero hn hsep hm hQC _⟩
    · exact ⟨Sum.inl (Sum.inr v), rfl⟩
    · exact ⟨Sum.inr (Sum.inr v), rfl⟩

include hsep in
/-- The contact `a`-visit is not an image mark. -/
theorem s7r_va_not_mem_range :
    (Sum.inr (s7e_va hc) : Mark Q) ∉ Set.range (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) := by
  rw [s7r_inr_mem_range_iff]
  rintro (h | ⟨v, hv⟩ | ⟨v, hv⟩)
  · exact s7e_vl_ne_va hc (s7e_a_ne_leg false hsep) h.symm
  · exact s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_firstVisitQ_fst hn hsep hm hQC v, hv]; exact s7r_va_affected hc)
  · exact s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_secondVisitQ_fst hn hsep hm hQC v, hv]; exact s7r_va_affected hc)

variable (S : Finset (Crossing Q)) (hxS : (s7e_va hc).1 ∈ S)
  (hSimg : ∀ y ∈ S, y ≠ (s7e_va hc).1 →
    y ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪ Set.range (s7b_secondCrossingQ hn hsep hm hQC))

include hsep hSimg in
/-- A visit that is neither contact visit and is carried from neither half is transit. -/
theorem s7r_transit_of (w : Visit Q) (h0 : w ≠ s7e_vl hc)
    (h1 : ∀ v, s7b_firstVisitQ hn hsep hm hQC v ≠ w) (h2 : ∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w)
    (ha : w ≠ s7e_va hc) :
    s7r_Transit hn hQ S (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) (Sum.inr w) := by
  have hnr : (Sum.inr w : Mark Q) ∉ Set.range (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) := by
    rw [s7r_inr_mem_range_iff]
    rintro (h | ⟨v, hv⟩ | ⟨v, hv⟩)
    · exact h0 h
    · exact h1 v hv
    · exact h2 v hv
  refine ⟨hnr, ?_⟩
  have hwS : w.1 ∉ S := by
    intro hwS
    by_cases hwx : w.1 = (s7e_va hc).1
    · rcases s7e_visit_of_fst hc w (by rw [hwx]; rfl) (s7e_a_ne_leg false hsep) with h | h
      · exact ha h
      · exact h0 h
    · rcases hSimg w.1 hwS hwx with ⟨c, hcw⟩ | ⟨c, hcw⟩
      · obtain ⟨v, -, hv⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC w c hcw.symm
        exact h1 v hv
      · obtain ⟨v, -, hv⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC w c hcw.symm
        exact h2 v hv
  exact smoothingSuccessor_visit_of_not_mem hn hQ S w hwS

include hsep hSimg in
/-- **The window lemma**: the marks cyclically between `u` (on edge `e`) and a target `m'` — the next
vertex `e + 1`, or a mark on edge `e` beyond `u` — are all transit as soon as every visit of `Q` in the
parameter window is neither contact visit and carried from neither half. -/
theorem s7r_transit_window (u m' : Mark Q) (e : ZMod n) (hu : s7e_mEdge u = e)
    (hm' : m' = Sum.inl (e + 1) ∨ (s7e_mEdge m' = e ∧ s7e_mParam u < s7e_mParam m'))
    (hex : ∀ w' : Visit Q, w'.2.val = e → s7e_mParam u < visitParameter w' →
      (m' = Sum.inl (e + 1) ∨ visitParameter w' < s7e_mParam m') →
      w' ≠ s7e_vl hc ∧ (∀ v, s7b_firstVisitQ hn hsep hm hQC v ≠ w') ∧
        (∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w') ∧ w' ≠ s7e_va hc) :
    ∀ w, traversalBetween (markPosition hn hQ.1 u) (markPosition hn hQ.1 w) (markPosition hn hQ.1 m') →
      s7r_Transit hn hQ S (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) w := by
  intro w hb
  have hdec : s7e_mEdge w = e ∧ s7e_mParam u < s7e_mParam w ∧
      (m' = Sum.inl (e + 1) ∨ s7e_mParam w < s7e_mParam m') := by
    rcases hm' with rfl | ⟨hme, hlt⟩
    · obtain ⟨h1, h2⟩ := s7r_between_next_vertex hn hQ u w e hu hb
      exact ⟨h1, h2, Or.inl rfl⟩
    · obtain ⟨h1, h2, h3⟩ := s7r_between_same_edge_of hn hQ u w m' e hu hme hlt hb
      exact ⟨h1, h2, Or.inr h3⟩
  have hpos : 0 < s7e_mParam w := lt_of_le_of_lt (s7e_mParam_nonneg hn hQ u) hdec.2.1
  obtain ⟨w', rfl⟩ := s7e_mark_visit_of_param_pos w hpos
  obtain ⟨h0, h1, h2, ha⟩ := hex w' hdec.1 hdec.2.1 hdec.2.2
  exact s7r_transit_of hn hQ hsep hm hQC hc S hSimg w' h0 h1 h2 ha

include hQ hsep hη hw huniq in
/-- On the leg-`M−1` side the leg visit is the last mark on edge `M − 1`: `nextMark v_ℓ = μ_M`. -/
theorem s7r_nextMark_vl : nextMark hn hQ (Sum.inr (s7e_vl hc)) = Sum.inl M := by
  have hnext : nextMark hn hQ (Sum.inr (s7e_vl hc)) = Sum.inl ((s7e_vl hc).2.val + 1) := by
    apply s7e_nextMark_inr_eq_inl hn hQ
    intro u hu
    by_cases hul : u = s7e_vl hc
    · rw [hul]
    · have hup := s7e_persistent_of_edge_leg false hsep hc huniq u (hu.trans (s7e_vl_edge hc)) hul
      have h1 := s7e_persist_M_sub_one hn hQ hw u hup (by rw [hu, s7e_vl_edge, s7r_leg_false])
      have h2 := s7e_vl_param_false hn hQ hw hc
      linarith
  rw [hnext, s7e_vl_edge, s7r_leg_false, sub_add_cancel]

include hQ hsep hη hw huniq hxS in
/-- The smoothing successor of the contact `a`-visit in a sliding row is `μ_M`. -/
theorem s7r_succ_va : smoothingSuccessor hn hQ S (Sum.inr (s7e_va hc)) = Sum.inl M := by
  rw [smoothingSuccessor_visit_of_mem hn hQ S _ hxS, s7e_twin_va hc (s7e_a_ne_leg false hsep)]
  exact s7r_nextMark_vl hn hQ hsep hη hw hc huniq

/-! ##### Generic facts about `nextMark` on a half, and the Q-marks of the half marks -/

/-- The successor of a mark on edge `i` is the vertex `i + 1` or a later visit on edge `i`. -/
theorem s7r_nextMark_shape {k : ℕ} [NeZero k] (hk : 3 ≤ k) {L : LabelledTuple k} (hL : Generic L)
    (m₁ : Mark L) :
    nextMark hk hL m₁ = Sum.inl (s7e_mEdge m₁ + 1) ∨
      ∃ w : Visit L, nextMark hk hL m₁ = Sum.inr w ∧ w.2.val = s7e_mEdge m₁ ∧
        s7e_mParam m₁ < visitParameter w := by
  cases m₁ with
  | inl i =>
    rcases s7e_nextMark_inl hk hL i with h | ⟨w, h, hw⟩
    · exact Or.inl h
    · exact Or.inr ⟨w, h, hw, s7e_visitParameter_pos hk hL w⟩
  | inr v =>
    rcases s7e_nextMark_inr hk hL v with h | ⟨w, h, hw, hp⟩
    · exact Or.inl h
    · exact Or.inr ⟨w, h, hw, hp⟩

/-- No visit of a half lies on its edge `i` strictly between a mark `m₁` on edge `i` and `nextMark m₁`. -/
theorem s7r_no_half_between {k : ℕ} [NeZero k] (hk : 3 ≤ k) {L : LabelledTuple k} (hL : Generic L)
    (m₁ : Mark L) (i : ZMod k) (hi : s7e_mEdge m₁ = i) (v' : Visit L) (hv' : v'.2.val = i)
    (hlo : s7e_mParam m₁ < visitParameter v')
    (hhi : nextMark hk hL m₁ = Sum.inl (i + 1) ∨
      (s7e_mEdge (nextMark hk hL m₁) = i ∧ visitParameter v' < s7e_mParam (nextMark hk hL m₁))) :
    False := by
  rcases hhi with h | ⟨he, hlt⟩
  · have hb := s7e_between_mark_mark_inl hk hL m₁ (Sum.inr v')
      (by rw [hi, s7e_mEdge_inr, hv']) hlo
    rw [hi] at hb
    exact nextMark_no_mark_between hk hL h (Sum.inr v') hb
  · have hb := s7e_between_same_edge hk hL m₁ (Sum.inr v') (nextMark hk hL m₁)
      (by rw [hi, s7e_mEdge_inr, hv']) (by rw [s7e_mEdge_inr, hv', he]) hlo hlt
    exact nextMark_no_mark_between hk hL rfl (Sum.inr v') hb

theorem s7r_edge_first (m₁ : Mark (firstHalf P M a)) :
    s7e_mEdge (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁)) = firstHalfIndex M a (s7e_mEdge m₁) := by
  cases m₁ <;> rfl

include hQ hz hr hr0 hord h₁ in
/-- Parameter transfer for the first half: the Q-parameter order between the Q-mark of `m₁` and a
carried visit on the same edge is the `λ₁`-order. -/
theorem s7r_param_first (m₁ : Mark (firstHalf P M a)) (v' : Visit (firstHalf P M a))
    (he : v'.2.val = s7e_mEdge m₁) :
    s7e_mParam (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁)) <
        visitParameter (s7b_firstVisitQ hn hsep hm hQC v') ↔
      s7e_mParam m₁ < visitParameter v' := by
  cases m₁ with
  | inl i =>
    exact iff_of_true (s7e_visitParameter_pos hn hQ _)
      (s7e_visitParameter_pos (contactHalfSizes_bounds hn hsep).1.1 h₁ v')
  | inr v => exact s7r_first_order hn hsep hz hm hr hr0 hQC hord v v' he.symm

/-! ##### The first-half reach and step -/

include hQ hz hr hr0 hr1 hη hw hord hside huniq hxS hSimg h₂ in
/-- **First-half reach**: from the Q-mark of `m₁ : Mark λ₁`, the smoothing successor of a sliding row
reaches the Q-mark of `nextMark m₁` through transit marks only (the cut edge closes through the
contact `a`-visit, whose smoothing successor is `μ_M`). -/
theorem s7r_reach_first (hn₁ : 3 ≤ firstHalfSize M a) (m₁ : Mark (firstHalf P M a)) :
    ∃ k : ℕ, ((smoothingSuccessor hn hQ S) ^ k)
        (nextMark hn hQ (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁))) =
      s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl (nextMark hn₁ h₁ m₁)) ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (nextMark hn hQ (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁))) ∉
          Set.range (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) := by
  have hedge_u : s7e_mEdge (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁)) =
      firstHalfIndex M a (s7e_mEdge m₁) := s7r_edge_first hn hsep hm hQC hc m₁
  have hinj := s7b_slidingMark_injective hn hsep hm hQC (s7e_vl hc) (s7r_vl_affected hc)
  have hne_u : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁) ≠
      s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl (nextMark hn₁ h₁ m₁)) := fun h =>
    markSuccessor_ne_self hn₁ h₁ m₁ (Sum.inl.inj (hinj h)).symm
  have hva_near := s7e_va_param_near hn hQ false hw hc
  have hva1 := (abs_lt.mp hva_near).1
  have hva2 := (abs_lt.mp hva_near).2
  -- a carried first-half visit on the edge of `m₁`: its `λ₁`-edge, and the transferred lower bound
  have hfirst : ∀ (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) →
      ∀ v' : Visit (firstHalf P M a), s7b_firstVisitQ hn hsep hm hQC v' = w' →
      v'.2.val = s7e_mEdge m₁ ∧
        (s7e_mParam (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁)) < visitParameter w' ↔
          s7e_mParam m₁ < visitParameter v') := by
    intro w' he v' hv'
    have hv'e : v'.2.val = s7e_mEdge m₁ := by
      apply firstHalfIndex_injective M a
      rw [← s7b_firstVisitQ_edge hn hsep hm hQC v', hv', he]
    refine ⟨hv'e, ?_⟩
    rw [← hv']
    exact s7r_param_first hn hQ hsep hz hm hr hr0 hQC hord h₁ hc m₁ v' hv'e
  -- the exclusions shared by every window on a first-half edge other than the cut
  have hoff : ∀ (_ : s7e_mEdge m₁ ≠ -1) (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) →
      w' ≠ s7e_vl hc ∧ (∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w') ∧ w' ≠ s7e_va hc := by
    intro hi1 w' he
    refine ⟨?_, ?_, ?_⟩
    · intro h; rw [h, s7e_vl_edge, s7r_leg_false] at he
      exact s7b_firstHalfIndex_ne_pred hn hsep _ he.symm
    · intro v h; rw [← h, s7b_secondVisitQ_edge] at he
      exact hi1 (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep he.symm).1
    · intro h; rw [h, s7e_va_edge] at he
      exact hi1 (firstHalfIndex_injective M a (he.symm.trans (firstHalfIndex_last M a).symm))
  -- the exclusions on the cut edge `a`, for a window bounded above by `p' < r + η`
  have hcut : ∀ (_ : s7e_mEdge m₁ = -1) (p' : ℝ) (_ : p' < r + η) (w' : Visit Q), w'.2.val = a →
      visitParameter w' < p' →
      w' ≠ s7e_vl hc ∧ (∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w') := by
    intro _ p' hp' w' he hlt
    refine ⟨?_, ?_⟩
    · intro h; rw [h, s7e_vl_edge, s7r_leg_false] at he
      exact s7e_a_ne_M_sub_one hsep he.symm
    · intro v h
      have hv0 : v.2.val = 0 := by
        rw [← h, s7b_secondVisitQ_edge] at he
        exact (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep
          (by rw [firstHalfIndex_last]; exact he.symm)).2
      have := s7r_second_cut_gt hn hQ hsep hz hm hr hr1 hQC hw hside h₂ v hv0
      rw [h] at this
      linarith
  rcases s7r_nextMark_shape hn₁ h₁ m₁ with hnx | ⟨w, hnx, hwe, hwp⟩
  · by_cases hi1 : s7e_mEdge m₁ = -1
    · -- the cut, vertex target `inl 0 ↦ μ_M`: through the contact `a`-visit
      have hm' : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl (nextMark hn₁ h₁ m₁)) = Sum.inl M := by
        rw [hnx, hi1, neg_add_cancel, s7b_slidingMark_inl_inl, firstHalfIndex_zero]
      rw [hm']
      have hea : firstHalfIndex M a (s7e_mEdge m₁) = a := by rw [hi1, firstHalfIndex_last]
      have hlt_u : s7e_mParam (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁)) <
          visitParameter (s7e_va hc) := by
        cases m₁ with
        | inl j => exact s7e_visitParameter_pos hn hQ _
        | inr v =>
          have := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ v hi1
          show visitParameter (s7b_firstVisitQ hn hsep hm hQC v) < _
          linarith
      have hne_va : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁) ≠ Sum.inr (s7e_va hc) :=
        fun h => s7r_va_not_mem_range hn hsep hm hQC hc ⟨_, h⟩
      have hreach₁ := s7r_reach_of_transit hn hQ S _ (Sum.inr (s7e_va hc)) _ _ rfl hne_va
        (s7r_transit_window hn hQ hsep hm hQC hc S hSimg _ _ a (hedge_u.trans hea)
          (Or.inr ⟨s7e_va_edge hc, hlt_u⟩) ?_)
      · refine s7r_reach_trans hn hQ S _ hreach₁ (s7r_va_not_mem_range hn hsep hm hQC hc) ?_
        rw [s7r_succ_va hn hQ hsep hη hw hc huniq S hxS]
        exact ⟨0, by simp, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      · intro w' he hlo hhi
        have hhi' : visitParameter w' < visitParameter (s7e_va hc) := by
          rcases hhi with h | h
          · exact absurd h Sum.inr_ne_inl
          · exact h
        obtain ⟨h0, h2⟩ := hcut hi1 (visitParameter (s7e_va hc)) (by linarith) w' he hhi'
        refine ⟨h0, ?_, h2, fun h => by rw [h] at hhi'; exact lt_irrefl _ hhi'⟩
        intro v' hv'
        obtain ⟨hv'e, hiff⟩ := hfirst w' (by rw [he, hea]) v' hv'
        exact s7r_no_half_between hn₁ h₁ m₁ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
    · -- off the cut, vertex target `inl (i + 1) ↦ μ_{firstHalfIndex i + 1}`
      have hm' : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl (nextMark hn₁ h₁ m₁)) =
          Sum.inl (firstHalfIndex M a (s7e_mEdge m₁) + 1) := by
        rw [hnx, s7b_slidingMark_inl_inl, firstHalfIndex_next M a hi1]
      rw [hm'] at hne_u ⊢
      refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
        (s7r_transit_window hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inl rfl) ?_)
      intro w' he hlo _
      obtain ⟨h0, h2, ha⟩ := hoff hi1 w' he
      refine ⟨h0, ?_, h2, ha⟩
      intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hfirst w' he v' hv'
      exact s7r_no_half_between hn₁ h₁ m₁ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
  · -- target: a visit `w` of `λ₁` on the edge of `m₁`, `↦ firstVisitQ w`
    have hm' : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl (nextMark hn₁ h₁ m₁)) =
        Sum.inr (s7b_firstVisitQ hn hsep hm hQC w) := by rw [hnx, s7b_slidingMark_inl_inr]
    rw [hm'] at hne_u ⊢
    have hwQe : (s7b_firstVisitQ hn hsep hm hQC w).2.val = firstHalfIndex M a (s7e_mEdge m₁) := by
      rw [s7b_firstVisitQ_edge, hwe]
    have hlt_u : s7e_mParam (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m₁)) <
        visitParameter (s7b_firstVisitQ hn hsep hm hQC w) :=
      (s7r_param_first hn hQ hsep hz hm hr hr0 hQC hord h₁ hc m₁ w hwe).mpr hwp
    refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
      (s7r_transit_window hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inr ⟨hwQe, hlt_u⟩) ?_)
    intro w' he hlo hhi
    have hhi' : visitParameter w' < visitParameter (s7b_firstVisitQ hn hsep hm hQC w) := by
      rcases hhi with h | h
      · exact absurd h Sum.inr_ne_inl
      · exact h
    have hex1 : ∀ v', s7b_firstVisitQ hn hsep hm hQC v' ≠ w' := by
      intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hfirst w' he v' hv'
      have hup : visitParameter v' < visitParameter w := by
        rw [← hv'] at hhi'
        exact (s7r_first_order hn hsep hz hm hr hr0 hQC hord v' w (hv'e.trans hwe.symm)).mp hhi'
      exact s7r_no_half_between hn₁ h₁ m₁ _ rfl v' hv'e (hiff.mp hlo)
        (Or.inr ⟨by rw [hnx]; exact hwe, by rw [hnx]; exact hup⟩)
    by_cases hi1 : s7e_mEdge m₁ = -1
    · have hea : firstHalfIndex M a (s7e_mEdge m₁) = a := by rw [hi1, firstHalfIndex_last]
      have hwlt := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ w (hwe.trans hi1)
      obtain ⟨h0, h2⟩ := hcut hi1 _ (by linarith) w' (by rw [he, hea]) hhi'
      refine ⟨h0, hex1, h2, ?_⟩
      intro h; rw [h] at hhi'; linarith
    · obtain ⟨h0, h2, ha⟩ := hoff hi1 w' he
      exact ⟨h0, hex1, h2, ha⟩

include hQ hz hr hr0 hr1 hη hw hord hside huniq hxS hSimg h₂ in
/-- **First-half step** of the first-return law: for `b = inl m`. -/
theorem s7r_step_first (hn₁ : 3 ≤ firstHalfSize M a) (S₁ : Finset (Crossing (firstHalf P M a)))
    (hS₁ : S₁ = s7b_pre (s7b_firstCrossingQ hn hsep hm hQC) S) (m : Mark (firstHalf P M a)) :
    ∃ k : ℕ, 0 < k ∧ ((smoothingSuccessor hn hQ S) ^ k)
        (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m)) =
      s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl (smoothingSuccessor hn₁ h₁ S₁ m)) ∧
      ∀ j : ℕ, 0 < j → j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m)) ∉
          Set.range (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) := by
  have hu : selectedMarkPerm S (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl m)) =
      s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inl (selectedMarkPerm S₁ m)) := by
    cases m with
    | inl i => rfl
    | inr v =>
      rw [s7b_slidingMark_inl_inr, selectedMarkPerm_visit, selectedMarkPerm_visit, s7b_slidingMark_inl_inr]
      congr 1
      by_cases hv : v.1 ∈ S₁
      · have hvQ : (s7b_firstVisitQ hn hsep hm hQC v).1 ∈ S := by
          rw [s7b_firstVisitQ_fst]; rw [hS₁, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_mem S₁ v hv, selectedVisitTwin_of_mem S _ hvQ, s7b_firstVisitQ_visitTwin]
      · have hvQ : (s7b_firstVisitQ hn hsep hm hQC v).1 ∉ S := by
          rw [s7b_firstVisitQ_fst]; rw [hS₁, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_not_mem S₁ v hv, selectedVisitTwin_of_not_mem S _ hvQ]
  exact s7r_step_of_reach hn hQ S _ (Sum.inl m) _ _ hu
    (s7r_reach_first hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc huniq S hxS hSimg hn₁
      (selectedMarkPerm S₁ m))

/-! ##### The second half: its Q-marks (the vertex `0` starts its chain at the contact `a`-visit) -/

/-- The Q-mark from which the chain of a second-half mark starts: the vertex `0 = μ_M` of `λ₂` is
carried to the leg visit `v_ℓ`, whose smoothing successor is that of its twin `v_a`. -/
def s7r_qmark₂ (m₂ : Mark (secondHalf P M a)) : Mark Q :=
  if m₂ = Sum.inl 0 then Sum.inr (s7e_va hc) else s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr m₂)

theorem s7r_qmark₂_zero : s7r_qmark₂ hn hsep hm hQC hc (Sum.inl 0) = Sum.inr (s7e_va hc) := by
  simp [s7r_qmark₂]

theorem s7r_qmark₂_of_ne (m₂ : Mark (secondHalf P M a)) (h : m₂ ≠ Sum.inl 0) :
    s7r_qmark₂ hn hsep hm hQC hc m₂ = s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr m₂) := by
  simp [s7r_qmark₂, h]

theorem s7r_qmark₂_inl {j : ZMod (secondHalfSize M a)} (hj : j ≠ 0) :
    s7r_qmark₂ hn hsep hm hQC hc (Sum.inl j) = Sum.inl (secondHalfEdgeIndex M a j) := by
  rw [s7r_qmark₂_of_ne hn hsep hm hQC hc _ (fun h => hj (Sum.inl.inj h)),
    s7b_slidingMark_inr_inl hn hsep hm hQC _ hj, secondHalfIndex_nonzero M a hj]

theorem s7r_qmark₂_inr (v : Visit (secondHalf P M a)) :
    s7r_qmark₂ hn hsep hm hQC hc (Sum.inr v) = Sum.inr (s7b_secondVisitQ hn hsep hm hQC v) := by
  rw [s7r_qmark₂_of_ne hn hsep hm hQC hc _ Sum.inr_ne_inl, s7b_slidingMark_inr_inr]

theorem s7r_edge_second (m₂ : Mark (secondHalf P M a)) :
    s7e_mEdge (s7r_qmark₂ hn hsep hm hQC hc m₂) = secondHalfEdgeIndex M a (s7e_mEdge m₂) := by
  cases m₂ with
  | inl j =>
    by_cases hj : j = 0
    · subst hj; rw [s7r_qmark₂_zero]
      exact (s7e_va_edge hc).trans (secondHalfEdgeIndex_zero M a).symm
    · rw [s7r_qmark₂_inl hn hsep hm hQC hc hj]; rfl
  | inr v => rw [s7r_qmark₂_inr]; rfl

include hQ hz hr hr1 hη hw hside h₂ in
/-- On the cut (`j = 0`) the Q-mark of `m₂` is at or beyond the contact `a`-visit. -/
theorem s7r_qmark₂_param_zero (m₂ : Mark (secondHalf P M a)) (h0 : s7e_mEdge m₂ = 0) :
    visitParameter (s7e_va hc) ≤ s7e_mParam (s7r_qmark₂ hn hsep hm hQC hc m₂) := by
  cases m₂ with
  | inl j =>
    have hj : j = 0 := h0
    subst hj; rw [s7r_qmark₂_zero]; exact le_rfl
  | inr v =>
    rw [s7r_qmark₂_inr]
    have := s7r_second_cut_gt hn hQ hsep hz hm hr hr1 hQC hw hside h₂ v h0
    have hva := (abs_lt.mp (s7e_va_param_near hn hQ false hw hc)).2
    show visitParameter (s7e_va hc) ≤ visitParameter (s7b_secondVisitQ hn hsep hm hQC v)
    linarith

include hQ hz hr hr1 hη hw hord hside h₂ in
/-- Parameter transfer for the second half. -/
theorem s7r_param_second (hn₂ : 3 ≤ secondHalfSize M a) (m₂ : Mark (secondHalf P M a))
    (v' : Visit (secondHalf P M a)) (he : v'.2.val = s7e_mEdge m₂) :
    s7e_mParam (s7r_qmark₂ hn hsep hm hQC hc m₂) < visitParameter (s7b_secondVisitQ hn hsep hm hQC v') ↔
      s7e_mParam m₂ < visitParameter v' := by
  cases m₂ with
  | inl j =>
    refine iff_of_true ?_ (s7e_visitParameter_pos hn₂ h₂ v')
    by_cases hj : j = 0
    · subst hj; rw [s7r_qmark₂_zero]
      have := s7r_second_cut_gt hn hQ hsep hz hm hr hr1 hQC hw hside h₂ v' he
      have hva := (abs_lt.mp (s7e_va_param_near hn hQ false hw hc)).2
      show visitParameter (s7e_va hc) < _
      linarith
    · rw [s7r_qmark₂_inl hn hsep hm hQC hc hj]; exact s7e_visitParameter_pos hn hQ _
  | inr v => rw [s7r_qmark₂_inr]; exact s7r_second_order hn hsep hz hm hr hr1 hQC hord v v' he.symm

include hQ hz hr hr0 hr1 hη hw hord hside hSimg h₁ in
/-- **Second-half reach**: from the Q-mark of `m₂ : Mark λ₂` the smoothing successor reaches the
Q-mark of `nextMark m₂` through transit marks only (the vertex `0` of `λ₂` is entered from edge
`M − 1` at the leg visit `v_ℓ`, and left through the contact `a`-visit). -/
theorem s7r_reach_second (hn₂ : 3 ≤ secondHalfSize M a) (m₂ : Mark (secondHalf P M a)) :
    ∃ k : ℕ, ((smoothingSuccessor hn hQ S) ^ k) (nextMark hn hQ (s7r_qmark₂ hn hsep hm hQC hc m₂)) =
      s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr (nextMark hn₂ h₂ m₂)) ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (nextMark hn hQ (s7r_qmark₂ hn hsep hm hQC hc m₂)) ∉
          Set.range (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) := by
  have hedge_u := s7r_edge_second hn hsep hm hQC hc m₂
  have hinj := s7b_slidingMark_injective hn hsep hm hQC (s7e_vl hc) (s7r_vl_affected hc)
  have hva_near := s7e_va_param_near hn hQ false hw hc
  have hva1 := (abs_lt.mp hva_near).1
  have hva2 := (abs_lt.mp hva_near).2
  have hvl := s7e_vl_param_false hn hQ hw hc
  have hne_u : s7r_qmark₂ hn hsep hm hQC hc m₂ ≠
      s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr (nextMark hn₂ h₂ m₂)) := by
    by_cases h0 : m₂ = Sum.inl 0
    · subst h0; rw [s7r_qmark₂_zero]; intro h
      exact s7r_va_not_mem_range hn hsep hm hQC hc ⟨_, h.symm⟩
    · rw [s7r_qmark₂_of_ne hn hsep hm hQC hc m₂ h0]; intro h
      exact markSuccessor_ne_self hn₂ h₂ m₂ (Sum.inr.inj (hinj h)).symm
  have hsecond : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
      ∀ v' : Visit (secondHalf P M a), s7b_secondVisitQ hn hsep hm hQC v' = w' →
      v'.2.val = s7e_mEdge m₂ ∧ (s7e_mParam (s7r_qmark₂ hn hsep hm hQC hc m₂) < visitParameter w' ↔
        s7e_mParam m₂ < visitParameter v') := by
    intro w' he v' hv'
    have hv'e : v'.2.val = s7e_mEdge m₂ := by
      apply secondHalfEdgeIndex_injective M a
      rw [← s7b_secondVisitQ_edge hn hsep hm hQC v', hv', he]
    refine ⟨hv'e, ?_⟩
    rw [← hv']
    exact s7r_param_second hn hQ hsep hz hm hr hr1 hη hQC hw hord hside h₂ hc hn₂ m₂ v' hv'e
  have hfirst : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
      s7e_mParam (s7r_qmark₂ hn hsep hm hQC hc m₂) < visitParameter w' →
      ∀ v', s7b_firstVisitQ hn hsep hm hQC v' ≠ w' := by
    intro w' he hlo v' hv'
    rw [← hv', s7b_firstVisitQ_edge] at he
    obtain ⟨hv'1, hj0⟩ := s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep he
    have h1 := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ v' hv'1
    have h2 := s7r_qmark₂_param_zero hn hQ hsep hz hm hr hr1 hη hQC hw hside h₂ hc m₂ hj0
    rw [← hv'] at hlo
    linarith
  have hva_ex : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
      s7e_mParam (s7r_qmark₂ hn hsep hm hQC hc m₂) < visitParameter w' → w' ≠ s7e_va hc := by
    intro w' he hlo h
    rw [h, s7e_va_edge] at he
    have hj0 : s7e_mEdge m₂ = 0 :=
      secondHalfEdgeIndex_injective M a (by rw [← he, secondHalfEdgeIndex_zero])
    have h2 := s7r_qmark₂_param_zero hn hQ hsep hz hm hr hr1 hη hQC hw hside h₂ hc m₂ hj0
    rw [h] at hlo
    linarith
  have hvl_edge : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
      w' = s7e_vl hc → s7e_mEdge m₂ = -1 := by
    intro w' he h
    rw [h, s7e_vl_edge, s7r_leg_false, ← secondHalfEdgeIndex_last M a] at he
    exact (secondHalfEdgeIndex_injective M a he).symm
  have : Fact (1 < secondHalfSize M a) := ⟨by omega⟩
  rcases s7r_nextMark_shape hn₂ h₂ m₂ with hnx | ⟨w, hnx, hwe, hwp⟩
  · by_cases hj1 : s7e_mEdge m₂ = -1
    · -- `j = −1`: `nextMark m₂ = inl 0 ↦ v_ℓ`, the last mark on edge `M − 1`
      have hm' : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr (nextMark hn₂ h₂ m₂)) =
          Sum.inr (s7e_vl hc) := by
        rw [hnx, hj1, neg_add_cancel, s7b_slidingMark_inr_inl_zero]
      rw [hm'] at hne_u ⊢
      have hem : secondHalfEdgeIndex M a (s7e_mEdge m₂) = M - 1 := by rw [hj1, secondHalfEdgeIndex_last]
      have hlt_u : s7e_mParam (s7r_qmark₂ hn hsep hm hQC hc m₂) < visitParameter (s7e_vl hc) := by
        cases m₂ with
        | inl j =>
          have hj : j ≠ 0 := by
            intro h; rw [h] at hj1
            exact absurd hj1.symm (neg_ne_zero.mpr one_ne_zero)
          rw [s7r_qmark₂_inl hn hsep hm hQC hc hj]; exact s7e_visitParameter_pos hn hQ _
        | inr v =>
          rw [s7r_qmark₂_inr]
          have hp := s7e_persist_M_sub_one hn hQ hw (s7b_secondVisitQ hn hsep hm hQC v)
            (s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1)
            (by rw [s7b_secondVisitQ_edge]; exact hem)
          show visitParameter (s7b_secondVisitQ hn hsep hm hQC v) < _
          linarith
      refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
        (s7r_transit_window hn hQ hsep hm hQC hc S hSimg _ _ _ (hedge_u.trans hem)
          (Or.inr ⟨(s7e_vl_edge hc).trans s7r_leg_false, hlt_u⟩) ?_)
      intro w' he hlo hhi
      have hhi' : visitParameter w' < visitParameter (s7e_vl hc) := by
        rcases hhi with h | h
        · exact absurd h Sum.inr_ne_inl
        · exact h
      have he' : w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) := he.trans hem.symm
      refine ⟨fun h => by rw [h] at hhi'; exact lt_irrefl _ hhi', hfirst w' he' hlo, ?_, hva_ex w' he' hlo⟩
      intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hsecond w' he' v' hv'
      exact s7r_no_half_between hn₂ h₂ m₂ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
    · by_cases hj0 : s7e_mEdge m₂ = 0
      · -- `j = 0`: `nextMark m₂ = inl 1 ↦ μ_{a+1}`, entered from the contact `a`-visit
        have hm' : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr (nextMark hn₂ h₂ m₂)) =
            Sum.inl (a + 1) := by
          rw [hnx, hj0, zero_add, s7b_slidingMark_inr_inl hn hsep hm hQC _ one_ne_zero,
            secondHalfIndex_one hn hsep]
        rw [hm'] at hne_u ⊢
        have hem : secondHalfEdgeIndex M a (s7e_mEdge m₂) = a := by rw [hj0, secondHalfEdgeIndex_zero]
        refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
          (s7r_transit_window hn hQ hsep hm hQC hc S hSimg _ _ _ (hedge_u.trans hem) (Or.inl rfl) ?_)
        intro w' he hlo _
        have he' : w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) := he.trans hem.symm
        refine ⟨fun h => ?_, hfirst w' he' hlo, ?_, hva_ex w' he' hlo⟩
        · have := hvl_edge w' he' h
          rw [hj0] at this
          exact absurd this.symm (neg_ne_zero.mpr one_ne_zero)
        · intro v' hv'
          obtain ⟨hv'e, hiff⟩ := hsecond w' he' v' hv'
          exact s7r_no_half_between hn₂ h₂ m₂ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
      · -- `j ≠ 0, −1`: `nextMark m₂ = inl (j+1) ↦ μ_{secondHalfEdgeIndex j + 1}`
        have hj1' : s7e_mEdge m₂ + 1 ≠ 0 := fun h => hj1 (eq_neg_of_add_eq_zero_left h)
        have hm' : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr (nextMark hn₂ h₂ m₂)) =
            Sum.inl (secondHalfEdgeIndex M a (s7e_mEdge m₂) + 1) := by
          rw [hnx, s7b_slidingMark_inr_inl hn hsep hm hQC _ hj1', secondHalfIndex_next M a hj0]
        rw [hm'] at hne_u ⊢
        refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
          (s7r_transit_window hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inl rfl) ?_)
        intro w' he hlo _
        refine ⟨fun h => hj1 (hvl_edge w' he h), hfirst w' he hlo, ?_, hva_ex w' he hlo⟩
        intro v' hv'
        obtain ⟨hv'e, hiff⟩ := hsecond w' he v' hv'
        exact s7r_no_half_between hn₂ h₂ m₂ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
  · -- target: a visit `w` of `λ₂` on the edge of `m₂`, `↦ secondVisitQ w`
    have hm' : s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr (nextMark hn₂ h₂ m₂)) =
        Sum.inr (s7b_secondVisitQ hn hsep hm hQC w) := by rw [hnx, s7b_slidingMark_inr_inr]
    rw [hm'] at hne_u ⊢
    have hwQe : (s7b_secondVisitQ hn hsep hm hQC w).2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) := by
      rw [s7b_secondVisitQ_edge, hwe]
    have hlt_u : s7e_mParam (s7r_qmark₂ hn hsep hm hQC hc m₂) <
        visitParameter (s7b_secondVisitQ hn hsep hm hQC w) :=
      (s7r_param_second hn hQ hsep hz hm hr hr1 hη hQC hw hord hside h₂ hc hn₂ m₂ w hwe).mpr hwp
    refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
      (s7r_transit_window hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inr ⟨hwQe, hlt_u⟩) ?_)
    intro w' he hlo hhi
    have hhi' : visitParameter w' < visitParameter (s7b_secondVisitQ hn hsep hm hQC w) := by
      rcases hhi with h | h
      · exact absurd h Sum.inr_ne_inl
      · exact h
    refine ⟨?_, hfirst w' he hlo, ?_, hva_ex w' he hlo⟩
    · intro h
      have hj1 := hvl_edge w' he h
      have hp := s7e_persist_M_sub_one hn hQ hw (s7b_secondVisitQ hn hsep hm hQC w)
        (s7b_secondCrossingQ_not_affected hn hsep hm hQC w.1)
        (by rw [hwQe, hj1, secondHalfEdgeIndex_last])
      rw [h] at hhi'
      linarith
    · intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hsecond w' he v' hv'
      have hup : visitParameter v' < visitParameter w := by
        rw [← hv'] at hhi'
        exact (s7r_second_order hn hsep hz hm hr hr1 hQC hord v' w (hv'e.trans hwe.symm)).mp hhi'
      exact s7r_no_half_between hn₂ h₂ m₂ _ rfl v' hv'e (hiff.mp hlo)
        (Or.inr ⟨by rw [hnx]; exact hwe, by rw [hnx]; exact hup⟩)

include hQ hz hr hr0 hr1 hη hw hord hside hxS hSimg h₁ in
/-- **Second-half step** of the first-return law: for `b = inr m`. -/
theorem s7r_step_second (hn₂ : 3 ≤ secondHalfSize M a) (S₂ : Finset (Crossing (secondHalf P M a)))
    (hS₂ : S₂ = s7b_pre (s7b_secondCrossingQ hn hsep hm hQC) S) (m : Mark (secondHalf P M a)) :
    ∃ k : ℕ, 0 < k ∧ ((smoothingSuccessor hn hQ S) ^ k)
        (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr m)) =
      s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr (smoothingSuccessor hn₂ h₂ S₂ m)) ∧
      ∀ j : ℕ, 0 < j → j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr m)) ∉
          Set.range (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) := by
  have hu : selectedMarkPerm S (s7b_slidingMark hn hsep hm hQC (s7e_vl hc) (Sum.inr m)) =
      s7r_qmark₂ hn hsep hm hQC hc (selectedMarkPerm S₂ m) := by
    cases m with
    | inl j =>
      by_cases hj : j = 0
      · subst hj
        rw [s7b_slidingMark_inr_inl_zero, selectedMarkPerm_visit, selectedMarkPerm_vertex, s7r_qmark₂_zero,
          selectedVisitTwin_of_mem S _ (by rw [s7e_vl_fst]; exact hxS), s7e_twin_vl hc (s7e_a_ne_leg false hsep)]
      · rw [s7b_slidingMark_inr_inl hn hsep hm hQC _ hj, selectedMarkPerm_vertex, selectedMarkPerm_vertex,
          s7r_qmark₂_inl hn hsep hm hQC hc hj, secondHalfIndex_nonzero M a hj]
    | inr v =>
      rw [s7b_slidingMark_inr_inr, selectedMarkPerm_visit, selectedMarkPerm_visit, s7r_qmark₂_inr]
      congr 1
      by_cases hv : v.1 ∈ S₂
      · have hvQ : (s7b_secondVisitQ hn hsep hm hQC v).1 ∈ S := by
          rw [s7b_secondVisitQ_fst]; rw [hS₂, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_mem S₂ v hv, selectedVisitTwin_of_mem S _ hvQ, s7b_secondVisitQ_visitTwin]
      · have hvQ : (s7b_secondVisitQ hn hsep hm hQC v).1 ∉ S := by
          rw [s7b_secondVisitQ_fst]; rw [hS₂, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_not_mem S₂ v hv, selectedVisitTwin_of_not_mem S _ hvQ]
  exact s7r_step_of_reach hn hQ S _ (Sum.inr m) _ _ hu
    (s7r_reach_second hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc S hSimg hn₂
      (selectedMarkPerm S₂ m))

include hQ hη hw huniq hxS hSimg in
/-- **Hit**: every mark of `Q` reaches the image (beacon `μ_M`; off-image visits are either the
contact `a`-visit, which steps to `μ_M`, or visits of crossings off `S`). -/
theorem s7r_hit (u : Mark Q) :
    ∃ j : ℕ, ((smoothingSuccessor hn hQ S) ^ j) u ∈ Set.range (s7b_slidingMark hn hsep hm hQC (s7e_vl hc)) := by
  refine s7r_hit_of_transit hn hQ S _ (Sum.inl M)
    ⟨Sum.inl (Sum.inl 0), by rw [s7b_slidingMark_inl_inl, firstHalfIndex_zero]⟩ ?_ _ u rfl
  intro w hwr
  cases w with
  | inl i => exact Or.inr (smoothingSuccessor_vertex hn hQ S i)
  | inr w' =>
    by_cases hwS : w'.1 ∈ S
    · by_cases hwx : w'.1 = (s7e_va hc).1
      · rcases s7e_visit_of_fst hc w' (by rw [hwx]; rfl) (s7e_a_ne_leg false hsep) with h | h
        · subst h; left; refine ⟨1, ?_⟩
          rw [pow_one, s7r_succ_va hn hQ hsep hη hw hc huniq S hxS]
          exact ⟨Sum.inl (Sum.inl 0), by rw [s7b_slidingMark_inl_inl, firstHalfIndex_zero]⟩
        · exact absurd ((s7r_inr_mem_range_iff hn hsep hm hQC _ w').mpr (Or.inl h)) hwr
      · exfalso; apply hwr
        rcases hSimg w'.1 hwS hwx with ⟨c, hcw⟩ | ⟨c, hcw⟩
        · obtain ⟨v, -, hv⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC w' c hcw.symm
          exact (s7r_inr_mem_range_iff hn hsep hm hQC _ w').mpr (Or.inr (Or.inl ⟨v, hv⟩))
        · obtain ⟨v, -, hv⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC w' c hcw.symm
          exact (s7r_inr_mem_range_iff hn hsep hm hQC _ w').mpr (Or.inr (Or.inr ⟨v, hv⟩))
    · exact Or.inr (smoothingSuccessor_visit_of_not_mem hn hQ S w' hwS)

include hz hr hr0 hr1 hη hw hord hside huniq hxS hSimg in
/-- **`s7b_SlidingTransport.ret` on the leg-`M−1` side, PROVED**: the first-return law of the smoothing
successor of a sliding row on the marks of `λ₁ ⊕ λ₂` under `s7b_slidingMark` at the leg visit. -/
theorem s7r_slidingTransport_of_leg_false :
    s7b_SlidingTransport hn hsep hm hQC hQ h₁ h₂ S (s7b_pre (s7b_firstCrossingQ hn hsep hm hQC) S)
      (s7b_pre (s7b_secondCrossingQ hn hsep hm hQC) S) (s7e_vl hc) where
  affected := s7r_vl_affected hc
  pivot_mem := by rw [s7e_vl_fst]; exact hxS
  first_pre := rfl
  second_pre := rfl
  ret :=
    { inj := s7b_slidingMark_injective hn hsep hm hQC (s7e_vl hc) (s7r_vl_affected hc)
      step := fun b => by
        rcases b with m | m
        · exact s7r_step_first hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc huniq S hxS hSimg
            (contactHalfSizes_bounds hn hsep).1.1 _ rfl m
        · exact s7r_step_second hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc S hxS hSimg
            (contactHalfSizes_bounds hn hsep).2.1 _ rfl m
      hit := s7r_hit hn hQ hsep hm hη hQC hw hc huniq S hxS hSimg }

/-- The image hypothesis of a sliding row from the pivot split and independence (part IV):
every crossing of a decomposition `S ∋ x` other than `x` is carried from a half. -/
theorem s7r_img_of_decomposition (x : Crossing Q)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) x)
    (hS : IsDecomposition hn hQ S) (hx : x ∈ S) :
    ∀ y ∈ S, y ≠ x → y ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪
      Set.range (s7b_secondCrossingQ hn hsep hm hQC) := by
  intro y hy hyx
  have hind := (s7b_isDecomposition_iff_indep hn hQ S).mp hS
  exact hsplit.x_split y hyx (hind x hx y hy hyx.symm) (hind y hy x hx hyx)

/-! ##### The leg-`M` side: the CORRECTED mark map and transport (rule 4).  With `x = {a, M}` the
smoothing at `x` sends `v_ℓ ↦ nextMark v_a` and `v_a ↦ nextMark v_ℓ`, and `nextMark μ_M = v_ℓ`
(`s7e_owner_vl_eq_vertex`, `f = true`): the carrier through `μ_M` is `μ_M, v_ℓ, [E_a > r], μ_{a+1}, …,
μ_{M−1}, [E_{M−1}]` — the closed SECOND half, with `v_ℓ` the extra corner — and the closed FIRST half is
`[E_M], μ_{M+1}, …, μ_a, [E_a < r], v_a` with `v_a` in the place of `λ₁`'s vertex `0`.  So the vertex `0`
of `λ₁` must be carried to `v_a` and the vertex `0` of `λ₂` to `μ_M`; `s7b_slidingMark` (which fixes
`inl (inl 0) ↦ μ_M`) makes `s7b_SlidingTransport.ret` FALSE on this side: `f (ι (inl (inl 0))) =
nextMark μ_M = v_ℓ = ι (inr (inl 0))` is an image mark of the other half at the first step. -/

/-- The mark map of a sliding row on the leg-`M` side: `λ₁`'s vertex `0` is the contact `a`-visit
`va`, `λ₂`'s vertex `0` is `μ_M`; the leg visit is the skipped extra corner. -/
def s7r_slidingMark' (va : Visit Q) :
    Mark (firstHalf P M a) ⊕ Mark (secondHalf P M a) → Mark Q
  | Sum.inl (Sum.inl i) => if i = 0 then Sum.inr va else Sum.inl (firstHalfIndex M a i)
  | Sum.inl (Sum.inr v) => Sum.inr (s7b_firstVisitQ hn hsep hm hQC v)
  | Sum.inr (Sum.inl i) => Sum.inl (secondHalfIndex M a i)
  | Sum.inr (Sum.inr v) => Sum.inr (s7b_secondVisitQ hn hsep hm hQC v)

/-- The transport structure of a sliding row on the leg-`M` side (the corrected form of
`s7b_SlidingTransport` there; `va` is the contact `a`-visit of `x = {a, M}`). -/
structure s7r_SlidingTransport' (S₁ : Finset (Crossing (firstHalf P M a)))
    (S₂ : Finset (Crossing (secondHalf P M a))) (va : Visit Q) : Prop where
  affected : ContactAffected M a va.1.val
  pivot_mem : va.1 ∈ S
  first_pre : S₁ = s7b_pre (s7b_firstCrossingQ hn hsep hm hQC) S
  second_pre : S₂ = s7b_pre (s7b_secondCrossingQ hn hsep hm hQC) S
  ret : s7b_ReturnTransport (smoothingSuccessor hn hQ S)
    (Equiv.Perm.sumCongr (smoothingSuccessor (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
      (smoothingSuccessor (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂))
    (s7r_slidingMark' hn hsep hm hQC va)

end S7RSide

section S7RLegTrue

variable (hn : 3 ≤ n) {P Q : LabelledTuple n} (hQ : Generic Q) {M a : ZMod n}
  (hsep : ContactSeparated M a) (hz : pointZeroTriples P = {contactSupport M a})
  (hm : P M ∈ edgeInterior P a) {r η : ℝ} (hr : P M = edgePoint P a r) (hr0 : 0 < r) (hr1 : r < 1)
  (hη : 0 < η)
  (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
  (hw : ContactParameterWindows P Q M a r η)
  (hord : ∀ (u u' : Visit P) (hu : ¬ ContactAffected M a u.1.val) (hu' : ¬ ContactAffected M a u'.1.val),
    u.2.val = u'.2.val →
    (visitParameter (s7a_visit hQC u hu) < visitParameter (s7a_visit hQC u' hu') ↔
      visitParameter u < visitParameter u'))
  (hside : ∀ (u : Visit P) (hu : ¬ ContactAffected M a u.1.val), u.2.val = a →
    (visitParameter (s7a_visit hQC u hu) < r ↔ visitParameter u < r))
  (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a))
  (hc : IsCrossing Q {a, contactLeg true M})
  (huniq : ∀ y : Crossing Q, ContactAffected M a y.val → y.val = {a, contactLeg true M})
  (S : Finset (Crossing Q)) (hxS : (s7e_va hc).1 ∈ S)
  (hSimg : ∀ y ∈ S, y ≠ (s7e_va hc).1 →
    y ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪ Set.range (s7b_secondCrossingQ hn hsep hm hQC))

/-! ##### The corrected map is the `s7b_` map at `v_a` composed with the swap `μ_M ↔ v_a`. -/

omit [NeZero n] in
theorem s7r_leg_true : contactLeg true M = M := by simp [contactLeg]

include hn hsep in
/-- `secondHalfIndex (j + 1) = secondHalfEdgeIndex j + 1` for every `j` (the wrap `j = −1` gives `μ_M`). -/
theorem s7r_secondHalfIndex_succ (j : ZMod (secondHalfSize M a)) :
    secondHalfIndex M a (j + 1) = secondHalfEdgeIndex M a j + 1 := by
  by_cases hj : j = 0
  · subst hj; rw [zero_add, secondHalfIndex_one hn hsep, secondHalfEdgeIndex_zero]
  · exact secondHalfIndex_next M a hj

theorem s7r_va_affected' : ContactAffected M a (s7e_va hc).1.val :=
  (contactAffected_iff_leg _).mpr ⟨true, rfl⟩

theorem s7r_slidingMark'_inl_inl_zero :
    s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (Sum.inl 0)) = Sum.inr (s7e_va hc) := by
  simp [s7r_slidingMark']

theorem s7r_slidingMark'_inl_inl {i : ZMod (firstHalfSize M a)} (hi : i ≠ 0) :
    s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (Sum.inl i)) = Sum.inl (firstHalfIndex M a i) := by
  simp [s7r_slidingMark', hi]

theorem s7r_slidingMark'_inl_inr (v : Visit (firstHalf P M a)) :
    s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (Sum.inr v)) =
      Sum.inr (s7b_firstVisitQ hn hsep hm hQC v) := rfl

theorem s7r_slidingMark'_inr_inl (i : ZMod (secondHalfSize M a)) :
    s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (Sum.inl i)) = Sum.inl (secondHalfIndex M a i) := rfl

theorem s7r_slidingMark'_inr_inr (v : Visit (secondHalf P M a)) :
    s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (Sum.inr v)) =
      Sum.inr (s7b_secondVisitQ hn hsep hm hQC v) := rfl

theorem s7r_slidingMark'_eq :
    s7r_slidingMark' hn hsep hm hQC (s7e_va hc) =
      Equiv.swap (Sum.inl M) (Sum.inr (s7e_va hc)) ∘ s7b_slidingMark hn hsep hm hQC (s7e_va hc) := by
  have h1 : ∀ v : Visit (firstHalf P M a), s7b_firstVisitQ hn hsep hm hQC v ≠ s7e_va hc := fun v h =>
    s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_firstVisitQ_fst hn hsep hm hQC v, h]; exact s7r_va_affected' hc)
  have h2 : ∀ v : Visit (secondHalf P M a), s7b_secondVisitQ hn hsep hm hQC v ≠ s7e_va hc := fun v h =>
    s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_secondVisitQ_fst hn hsep hm hQC v, h]; exact s7r_va_affected' hc)
  funext b
  rcases b with (i | v) | (i | v)
  · rw [Function.comp_apply, s7b_slidingMark_inl_inl]
    by_cases hi : i = 0
    · subst hi; rw [s7r_slidingMark'_inl_inl_zero, firstHalfIndex_zero, Equiv.swap_apply_left]
    · rw [s7r_slidingMark'_inl_inl hn hsep hm hQC hc hi]
      refine (Equiv.swap_apply_of_ne_of_ne ?_ Sum.inl_ne_inr).symm
      intro h; apply hi
      exact firstHalfIndex_injective M a ((Sum.inl.inj h).trans (firstHalfIndex_zero M a).symm)
  · rw [Function.comp_apply, s7b_slidingMark_inl_inr, s7r_slidingMark'_inl_inr]
    exact (Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (fun h => h1 v (Sum.inr_injective h))).symm
  · rw [Function.comp_apply, s7r_slidingMark'_inr_inl]
    by_cases hi : i = 0
    · subst hi; rw [s7b_slidingMark_inr_inl_zero, secondHalfIndex_zero, Equiv.swap_apply_right]
    · rw [s7b_slidingMark_inr_inl hn hsep hm hQC _ hi]
      refine (Equiv.swap_apply_of_ne_of_ne ?_ Sum.inl_ne_inr).symm
      intro h; apply hi
      exact secondHalfIndex_injective M a ((Sum.inl.inj h).trans (secondHalfIndex_zero M a).symm)
  · rw [Function.comp_apply, s7b_slidingMark_inr_inr, s7r_slidingMark'_inr_inr]
    exact (Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (fun h => h2 v (Sum.inr_injective h))).symm

theorem s7r_slidingMark'_injective : Function.Injective (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  rw [s7r_slidingMark'_eq]
  exact (Equiv.swap _ _).injective.comp (s7b_slidingMark_injective hn hsep hm hQC _ (s7r_va_affected' hc))

theorem s7r_inr_mem_range_iff' (w : Visit Q) :
    (Sum.inr w : Mark Q) ∈ Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) ↔
      w = s7e_va hc ∨ (∃ v, s7b_firstVisitQ hn hsep hm hQC v = w) ∨
        (∃ v, s7b_secondVisitQ hn hsep hm hQC v = w) := by
  rw [s7r_slidingMark'_eq]
  by_cases hwa : w = s7e_va hc
  · subst hwa
    refine iff_of_true ⟨Sum.inl (Sum.inl 0), ?_⟩ (Or.inl rfl)
    rw [Function.comp_apply, s7b_slidingMark_inl_inl, firstHalfIndex_zero, Equiv.swap_apply_left]
  · have hfix : Equiv.swap (Sum.inl M) (Sum.inr (s7e_va hc)) (Sum.inr w) = Sum.inr w :=
      Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (fun h => hwa (Sum.inr_injective h))
    constructor
    · rintro ⟨b, hb⟩
      have hb' : s7b_slidingMark hn hsep hm hQC (s7e_va hc) b = Sum.inr w := by
        have := congrArg (Equiv.swap (Sum.inl M) (Sum.inr (s7e_va hc))) hb
        rwa [Function.comp_apply, Equiv.swap_apply_self, hfix] at this
      exact (s7r_inr_mem_range_iff hn hsep hm hQC _ w).mp ⟨b, hb'⟩
    · intro h
      obtain ⟨b, hb⟩ := (s7r_inr_mem_range_iff hn hsep hm hQC _ w).mpr h
      exact ⟨b, by rw [Function.comp_apply, hb, hfix]⟩

include hsep in
theorem s7r_vl_not_mem_range' :
    (Sum.inr (s7e_vl hc) : Mark Q) ∉ Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  rw [s7r_inr_mem_range_iff']
  rintro (h | ⟨v, hv⟩ | ⟨v, hv⟩)
  · exact s7e_vl_ne_va hc (s7e_a_ne_leg true hsep) h
  · exact s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_firstVisitQ_fst hn hsep hm hQC v, hv, s7e_vl_fst]; exact s7r_va_affected' hc)
  · exact s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_secondVisitQ_fst hn hsep hm hQC v, hv, s7e_vl_fst]; exact s7r_va_affected' hc)

theorem s7r_va_mem_range' :
    (Sum.inr (s7e_va hc) : Mark Q) ∈ Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) :=
  ⟨Sum.inl (Sum.inl 0), s7r_slidingMark'_inl_inl_zero hn hsep hm hQC hc⟩

include hsep hSimg in
theorem s7r_transit_of' (w : Visit Q) (h0 : w ≠ s7e_va hc)
    (h1 : ∀ v, s7b_firstVisitQ hn hsep hm hQC v ≠ w) (h2 : ∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w)
    (hl : w ≠ s7e_vl hc) :
    s7r_Transit hn hQ S (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) (Sum.inr w) := by
  have hnr : (Sum.inr w : Mark Q) ∉ Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
    rw [s7r_inr_mem_range_iff']
    rintro (h | ⟨v, hv⟩ | ⟨v, hv⟩)
    · exact h0 h
    · exact h1 v hv
    · exact h2 v hv
  refine ⟨hnr, ?_⟩
  have hwS : w.1 ∉ S := by
    intro hwS
    by_cases hwx : w.1 = (s7e_va hc).1
    · rcases s7e_visit_of_fst hc w (by rw [hwx]; rfl) (s7e_a_ne_leg true hsep) with h | h
      · exact h0 h
      · exact hl h
    · rcases hSimg w.1 hwS hwx with ⟨c, hcw⟩ | ⟨c, hcw⟩
      · obtain ⟨v, -, hv⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC w c hcw.symm
        exact h1 v hv
      · obtain ⟨v, -, hv⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC w c hcw.symm
        exact h2 v hv
  exact smoothingSuccessor_visit_of_not_mem hn hQ S w hwS

include hsep hSimg in
theorem s7r_transit_window' (u m' : Mark Q) (e : ZMod n) (hu : s7e_mEdge u = e)
    (hm' : m' = Sum.inl (e + 1) ∨ (s7e_mEdge m' = e ∧ s7e_mParam u < s7e_mParam m'))
    (hex : ∀ w' : Visit Q, w'.2.val = e → s7e_mParam u < visitParameter w' →
      (m' = Sum.inl (e + 1) ∨ visitParameter w' < s7e_mParam m') →
      w' ≠ s7e_va hc ∧ (∀ v, s7b_firstVisitQ hn hsep hm hQC v ≠ w') ∧
        (∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w') ∧ w' ≠ s7e_vl hc) :
    ∀ w, traversalBetween (markPosition hn hQ.1 u) (markPosition hn hQ.1 w) (markPosition hn hQ.1 m') →
      s7r_Transit hn hQ S (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) w := by
  intro w hb
  have hdec : s7e_mEdge w = e ∧ s7e_mParam u < s7e_mParam w ∧
      (m' = Sum.inl (e + 1) ∨ s7e_mParam w < s7e_mParam m') := by
    rcases hm' with rfl | ⟨hme, hlt⟩
    · obtain ⟨h1, h2⟩ := s7r_between_next_vertex hn hQ u w e hu hb
      exact ⟨h1, h2, Or.inl rfl⟩
    · obtain ⟨h1, h2, h3⟩ := s7r_between_same_edge_of hn hQ u w m' e hu hme hlt hb
      exact ⟨h1, h2, Or.inr h3⟩
  have hpos : 0 < s7e_mParam w := lt_of_le_of_lt (s7e_mParam_nonneg hn hQ u) hdec.2.1
  obtain ⟨w', rfl⟩ := s7e_mark_visit_of_param_pos w hpos
  obtain ⟨h0, h1, h2, hl⟩ := hex w' hdec.1 hdec.2.1 hdec.2.2
  exact s7r_transit_of' hn hQ hsep hm hQC hc S hSimg w' h0 h1 h2 hl

include hQ hsep hη hw huniq in
/-- On the leg-`M` side the leg visit is the first mark on edge `M`: `nextMark μ_M = v_ℓ`. -/
theorem s7r_nextMark_M : nextMark hn hQ (Sum.inl M) = Sum.inr (s7e_vl hc) := by
  apply s7e_nextMark_inl_eq_inr hn hQ M (s7e_vl hc) (by rw [s7e_vl_edge, s7r_leg_true])
  intro u hu
  by_cases hul : u = s7e_vl hc
  · rw [hul]
  · have hup := s7e_persistent_of_edge_leg true hsep hc huniq u (by rw [hu, s7r_leg_true]) hul
    have h1 := s7e_persist_M hn hQ hw u hup hu
    have h2 := s7e_vl_param_true hn hQ hw hc
    linarith

include hsep hxS in
theorem s7r_succ_va' : smoothingSuccessor hn hQ S (Sum.inr (s7e_va hc)) = nextMark hn hQ (Sum.inr (s7e_vl hc)) := by
  rw [smoothingSuccessor_visit_of_mem hn hQ S _ hxS, s7e_twin_va hc (s7e_a_ne_leg true hsep)]; rfl

include hsep hxS in
theorem s7r_succ_vl' : smoothingSuccessor hn hQ S (Sum.inr (s7e_vl hc)) = nextMark hn hQ (Sum.inr (s7e_va hc)) := by
  rw [smoothingSuccessor_visit_of_mem hn hQ S _ (by rw [s7e_vl_fst]; exact hxS),
    s7e_twin_vl hc (s7e_a_ne_leg true hsep)]; rfl

/-! ##### The first half on the leg-`M` side: its chain starts at `v_ℓ` for the vertex `0` -/

/-- The Q-mark from which the chain of a first-half mark starts: `λ₁`'s vertex `0` is carried to
`v_a`, whose smoothing successor is that of its twin `v_ℓ`. -/
def s7r_qmark₁' (m₁ : Mark (firstHalf P M a)) : Mark Q :=
  if m₁ = Sum.inl 0 then Sum.inr (s7e_vl hc) else s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl m₁)

theorem s7r_qmark₁'_zero : s7r_qmark₁' hn hsep hm hQC hc (Sum.inl 0) = Sum.inr (s7e_vl hc) := by
  simp [s7r_qmark₁']

theorem s7r_qmark₁'_of_ne (m₁ : Mark (firstHalf P M a)) (h : m₁ ≠ Sum.inl 0) :
    s7r_qmark₁' hn hsep hm hQC hc m₁ = s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl m₁) := by
  simp [s7r_qmark₁', h]

theorem s7r_qmark₁'_inl {i : ZMod (firstHalfSize M a)} (hi : i ≠ 0) :
    s7r_qmark₁' hn hsep hm hQC hc (Sum.inl i) = Sum.inl (firstHalfIndex M a i) := by
  rw [s7r_qmark₁'_of_ne hn hsep hm hQC hc _ (fun h => hi (Sum.inl.inj h)), s7r_slidingMark'_inl_inl hn hsep hm hQC hc hi]

theorem s7r_qmark₁'_inr (v : Visit (firstHalf P M a)) :
    s7r_qmark₁' hn hsep hm hQC hc (Sum.inr v) = Sum.inr (s7b_firstVisitQ hn hsep hm hQC v) := by
  rw [s7r_qmark₁'_of_ne hn hsep hm hQC hc _ Sum.inr_ne_inl, s7r_slidingMark'_inl_inr]

theorem s7r_edge_first' (m₁ : Mark (firstHalf P M a)) :
    s7e_mEdge (s7r_qmark₁' hn hsep hm hQC hc m₁) = firstHalfIndex M a (s7e_mEdge m₁) := by
  cases m₁ with
  | inl i =>
    by_cases hi : i = 0
    · subst hi; rw [s7r_qmark₁'_zero]
      exact ((s7e_vl_edge hc).trans s7r_leg_true).trans (firstHalfIndex_zero M a).symm
    · rw [s7r_qmark₁'_inl hn hsep hm hQC hc hi]; rfl
  | inr v => rw [s7r_qmark₁'_inr]; rfl

include hQ hη hw in
/-- On edge `0` of `λ₁` (Q-edge `M`) the Q-mark of `m₁` is at or beyond the leg visit. -/
theorem s7r_qmark₁'_param_zero (m₁ : Mark (firstHalf P M a)) (h0 : s7e_mEdge m₁ = 0) :
    visitParameter (s7e_vl hc) ≤ s7e_mParam (s7r_qmark₁' hn hsep hm hQC hc m₁) := by
  cases m₁ with
  | inl i =>
    have hi : i = 0 := h0
    subst hi; rw [s7r_qmark₁'_zero]; exact le_rfl
  | inr v =>
    rw [s7r_qmark₁'_inr]
    have hp := s7e_persist_M hn hQ hw (s7b_firstVisitQ hn hsep hm hQC v)
      (s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1)
      (by rw [s7b_firstVisitQ_edge]; exact (congrArg (firstHalfIndex M a) h0).trans (firstHalfIndex_zero M a))
    have hl := s7e_vl_param_true hn hQ hw hc
    show visitParameter (s7e_vl hc) ≤ visitParameter (s7b_firstVisitQ hn hsep hm hQC v)
    linarith

include hQ hz hr hr0 hη hw hord h₁ in
theorem s7r_param_first' (hn₁ : 3 ≤ firstHalfSize M a) (m₁ : Mark (firstHalf P M a))
    (v' : Visit (firstHalf P M a)) (he : v'.2.val = s7e_mEdge m₁) :
    s7e_mParam (s7r_qmark₁' hn hsep hm hQC hc m₁) < visitParameter (s7b_firstVisitQ hn hsep hm hQC v') ↔
      s7e_mParam m₁ < visitParameter v' := by
  cases m₁ with
  | inl i =>
    refine iff_of_true ?_ (s7e_visitParameter_pos hn₁ h₁ v')
    by_cases hi : i = 0
    · subst hi; rw [s7r_qmark₁'_zero]
      have hp := s7e_persist_M hn hQ hw (s7b_firstVisitQ hn hsep hm hQC v')
        (s7b_firstCrossingQ_not_affected hn hsep hm hQC v'.1)
        (by rw [s7b_firstVisitQ_edge]; exact (congrArg (firstHalfIndex M a) he).trans (firstHalfIndex_zero M a))
      have hl := s7e_vl_param_true hn hQ hw hc
      show visitParameter (s7e_vl hc) < _
      linarith
    · rw [s7r_qmark₁'_inl hn hsep hm hQC hc hi]; exact s7e_visitParameter_pos hn hQ _
  | inr v => rw [s7r_qmark₁'_inr]; exact s7r_first_order hn hsep hz hm hr hr0 hQC hord v v' he.symm

include hQ hz hr hr0 hr1 hη hw hord hside hSimg h₂ in
/-- **First-half reach on the leg-`M` side.** -/
theorem s7r_reach_first' (hn₁ : 3 ≤ firstHalfSize M a) (m₁ : Mark (firstHalf P M a)) :
    ∃ k : ℕ, ((smoothingSuccessor hn hQ S) ^ k) (nextMark hn hQ (s7r_qmark₁' hn hsep hm hQC hc m₁)) =
      s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (nextMark hn₁ h₁ m₁)) ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (nextMark hn hQ (s7r_qmark₁' hn hsep hm hQC hc m₁)) ∉
          Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  have hedge_u := s7r_edge_first' hn hsep hm hQC hc m₁
  have hinj := s7r_slidingMark'_injective hn hsep hm hQC hc
  have : Fact (1 < firstHalfSize M a) := ⟨by omega⟩
  have hva_near := s7e_va_param_near hn hQ true hw hc
  have hva1 := (abs_lt.mp hva_near).1
  have hva2 := (abs_lt.mp hva_near).2
  have hvl := s7e_vl_param_true hn hQ hw hc
  have hne_u : s7r_qmark₁' hn hsep hm hQC hc m₁ ≠
      s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (nextMark hn₁ h₁ m₁)) := by
    by_cases h0 : m₁ = Sum.inl 0
    · subst h0; rw [s7r_qmark₁'_zero]; intro h
      exact s7r_vl_not_mem_range' hn hsep hm hQC hc ⟨_, h.symm⟩
    · rw [s7r_qmark₁'_of_ne hn hsep hm hQC hc m₁ h0]; intro h
      exact markSuccessor_ne_self hn₁ h₁ m₁ (Sum.inl.inj (hinj h)).symm
  have hfirst : ∀ (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) →
      ∀ v' : Visit (firstHalf P M a), s7b_firstVisitQ hn hsep hm hQC v' = w' →
      v'.2.val = s7e_mEdge m₁ ∧ (s7e_mParam (s7r_qmark₁' hn hsep hm hQC hc m₁) < visitParameter w' ↔
        s7e_mParam m₁ < visitParameter v') := by
    intro w' he v' hv'
    have hv'e : v'.2.val = s7e_mEdge m₁ := by
      apply firstHalfIndex_injective M a
      rw [← s7b_firstVisitQ_edge hn hsep hm hQC v', hv', he]
    refine ⟨hv'e, ?_⟩
    rw [← hv']
    exact s7r_param_first' hn hQ hsep hz hm hr hr0 hη hQC hw hord h₁ hc hn₁ m₁ v' hv'e
  -- the leg visit lies on a first-half edge only for `i = 0`, where `u` is at or beyond it
  have hvl_ex : ∀ (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) →
      s7e_mParam (s7r_qmark₁' hn hsep hm hQC hc m₁) < visitParameter w' → w' ≠ s7e_vl hc := by
    intro w' he hlo h
    rw [h, s7e_vl_edge, s7r_leg_true] at he
    have hi0 : s7e_mEdge m₁ = 0 :=
      firstHalfIndex_injective M a (by rw [← he, firstHalfIndex_zero])
    have h2 := s7r_qmark₁'_param_zero hn hQ hsep hm hη hQC hw hc m₁ hi0
    rw [h] at hlo
    linarith
  -- the contact `a`-visit and second-half visits lie on a first-half edge only on the cut
  have hcutedge : ∀ (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) → w'.2.val = a →
      s7e_mEdge m₁ = -1 := by
    intro w' he hea
    rw [hea] at he
    exact firstHalfIndex_injective M a (by rw [← he, firstHalfIndex_last])
  have hsecond_cut : ∀ (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) →
      ∀ v', s7b_secondVisitQ hn hsep hm hQC v' = w' → r + 3 * η < visitParameter w' := by
    intro w' he v' hv'
    have hv'0 : v'.2.val = 0 := by
      rw [← hv', s7b_secondVisitQ_edge] at he
      exact (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep he.symm).2
    rw [← hv']
    exact s7r_second_cut_gt hn hQ hsep hz hm hr hr1 hQC hw hside h₂ v' hv'0
  rcases s7r_nextMark_shape hn₁ h₁ m₁ with hnx | ⟨w, hnx, hwe, hwp⟩
  · by_cases hi1 : s7e_mEdge m₁ = -1
    · -- the cut, vertex target `inl 0 ↦ v_a` directly
      have hm' : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (nextMark hn₁ h₁ m₁)) =
          Sum.inr (s7e_va hc) := by
        rw [hnx, hi1, neg_add_cancel, s7r_slidingMark'_inl_inl_zero]
      rw [hm'] at hne_u ⊢
      have hea : firstHalfIndex M a (s7e_mEdge m₁) = a := by rw [hi1, firstHalfIndex_last]
      have hlt_u : s7e_mParam (s7r_qmark₁' hn hsep hm hQC hc m₁) < visitParameter (s7e_va hc) := by
        cases m₁ with
        | inl j =>
          have hj : j ≠ 0 := by
            intro h; rw [h] at hi1
            exact absurd hi1.symm (neg_ne_zero.mpr one_ne_zero)
          rw [s7r_qmark₁'_inl hn hsep hm hQC hc hj]; exact s7e_visitParameter_pos hn hQ _
        | inr v =>
          rw [s7r_qmark₁'_inr]
          have := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ v hi1
          show visitParameter (s7b_firstVisitQ hn hsep hm hQC v) < _
          linarith
      refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
        (s7r_transit_window' hn hQ hsep hm hQC hc S hSimg _ _ a (hedge_u.trans hea)
          (Or.inr ⟨s7e_va_edge hc, hlt_u⟩) ?_)
      intro w' he hlo hhi
      have hhi' : visitParameter w' < visitParameter (s7e_va hc) := by
        rcases hhi with h | h
        · exact absurd h Sum.inr_ne_inl
        · exact h
      have he' : w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) := he.trans hea.symm
      refine ⟨fun h => by rw [h] at hhi'; exact lt_irrefl _ hhi', ?_, ?_, hvl_ex w' he' hlo⟩
      · intro v' hv'
        obtain ⟨hv'e, hiff⟩ := hfirst w' he' v' hv'
        exact s7r_no_half_between hn₁ h₁ m₁ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
      · intro v' hv'
        have := hsecond_cut w' he' v' hv'
        linarith
    · -- off the cut, vertex target `inl (i + 1) ↦ μ_{firstHalfIndex i + 1}`
      have hi1' : s7e_mEdge m₁ + 1 ≠ 0 := fun h => hi1 (eq_neg_of_add_eq_zero_left h)
      have hm' : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (nextMark hn₁ h₁ m₁)) =
          Sum.inl (firstHalfIndex M a (s7e_mEdge m₁) + 1) := by
        rw [hnx, s7r_slidingMark'_inl_inl hn hsep hm hQC hc hi1', firstHalfIndex_next M a hi1]
      rw [hm'] at hne_u ⊢
      refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
        (s7r_transit_window' hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inl rfl) ?_)
      intro w' he hlo _
      refine ⟨fun h => hi1 (hcutedge w' he (by rw [h]; rfl)), ?_, ?_, hvl_ex w' he hlo⟩
      · intro v' hv'
        obtain ⟨hv'e, hiff⟩ := hfirst w' he v' hv'
        exact s7r_no_half_between hn₁ h₁ m₁ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
      · intro v' hv'
        rw [← hv', s7b_secondVisitQ_edge] at he
        exact hi1 (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep he.symm).1
  · -- target: a visit `w` of `λ₁` on the edge of `m₁`, `↦ firstVisitQ w`
    have hm' : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (nextMark hn₁ h₁ m₁)) =
        Sum.inr (s7b_firstVisitQ hn hsep hm hQC w) := by rw [hnx, s7r_slidingMark'_inl_inr]
    rw [hm'] at hne_u ⊢
    have hwQe : (s7b_firstVisitQ hn hsep hm hQC w).2.val = firstHalfIndex M a (s7e_mEdge m₁) := by
      rw [s7b_firstVisitQ_edge, hwe]
    have hlt_u : s7e_mParam (s7r_qmark₁' hn hsep hm hQC hc m₁) <
        visitParameter (s7b_firstVisitQ hn hsep hm hQC w) :=
      (s7r_param_first' hn hQ hsep hz hm hr hr0 hη hQC hw hord h₁ hc hn₁ m₁ w hwe).mpr hwp
    refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
      (s7r_transit_window' hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inr ⟨hwQe, hlt_u⟩) ?_)
    intro w' he hlo hhi
    have hhi' : visitParameter w' < visitParameter (s7b_firstVisitQ hn hsep hm hQC w) := by
      rcases hhi with h | h
      · exact absurd h Sum.inr_ne_inl
      · exact h
    refine ⟨?_, ?_, ?_, hvl_ex w' he hlo⟩
    · intro h
      have hi1 := hcutedge w' he (by rw [h]; rfl)
      have hwlt := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ w (hwe.trans hi1)
      rw [h] at hhi'
      linarith
    · intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hfirst w' he v' hv'
      have hup : visitParameter v' < visitParameter w := by
        rw [← hv'] at hhi'
        exact (s7r_first_order hn hsep hz hm hr hr0 hQC hord v' w (hv'e.trans hwe.symm)).mp hhi'
      exact s7r_no_half_between hn₁ h₁ m₁ _ rfl v' hv'e (hiff.mp hlo)
        (Or.inr ⟨by rw [hnx]; exact hwe, by rw [hnx]; exact hup⟩)
    · intro v' hv'
      have h1 := hsecond_cut w' he v' hv'
      have hi1 : s7e_mEdge m₁ = -1 := by
        rw [← hv', s7b_secondVisitQ_edge] at he
        exact (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep he.symm).1
      have hwlt := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ w (hwe.trans hi1)
      linarith

include hQ hz hr hr0 hr1 hη hw hord hside hxS hSimg h₂ in
/-- **First-half step on the leg-`M` side.** -/
theorem s7r_step_first' (hn₁ : 3 ≤ firstHalfSize M a) (S₁ : Finset (Crossing (firstHalf P M a)))
    (hS₁ : S₁ = s7b_pre (s7b_firstCrossingQ hn hsep hm hQC) S) (m : Mark (firstHalf P M a)) :
    ∃ k : ℕ, 0 < k ∧ ((smoothingSuccessor hn hQ S) ^ k)
        (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl m)) =
      s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl (smoothingSuccessor hn₁ h₁ S₁ m)) ∧
      ∀ j : ℕ, 0 < j → j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl m)) ∉
          Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  have hu : selectedMarkPerm S (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inl m)) =
      s7r_qmark₁' hn hsep hm hQC hc (selectedMarkPerm S₁ m) := by
    cases m with
    | inl i =>
      by_cases hi : i = 0
      · subst hi
        rw [s7r_slidingMark'_inl_inl_zero, selectedMarkPerm_visit, selectedMarkPerm_vertex, s7r_qmark₁'_zero,
          selectedVisitTwin_of_mem S _ hxS, s7e_twin_va hc (s7e_a_ne_leg true hsep)]
      · rw [s7r_slidingMark'_inl_inl hn hsep hm hQC hc hi, selectedMarkPerm_vertex, selectedMarkPerm_vertex,
          s7r_qmark₁'_inl hn hsep hm hQC hc hi]
    | inr v =>
      rw [s7r_slidingMark'_inl_inr, selectedMarkPerm_visit, selectedMarkPerm_visit, s7r_qmark₁'_inr]
      congr 1
      by_cases hv : v.1 ∈ S₁
      · have hvQ : (s7b_firstVisitQ hn hsep hm hQC v).1 ∈ S := by
          rw [s7b_firstVisitQ_fst]; rw [hS₁, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_mem S₁ v hv, selectedVisitTwin_of_mem S _ hvQ, s7b_firstVisitQ_visitTwin]
      · have hvQ : (s7b_firstVisitQ hn hsep hm hQC v).1 ∉ S := by
          rw [s7b_firstVisitQ_fst]; rw [hS₁, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_not_mem S₁ v hv, selectedVisitTwin_of_not_mem S _ hvQ]
  exact s7r_step_of_reach hn hQ S _ (Sum.inl m) _ _ hu
    (s7r_reach_first' hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc S hSimg hn₁
      (selectedMarkPerm S₁ m))

/-! ##### The second half on the leg-`M` side: the vertex `0 ↦ μ_M` leaves through `v_ℓ` then `v_a` -/

theorem s7r_edge_second' (m₂ : Mark (secondHalf P M a)) (h0 : m₂ ≠ Sum.inl 0) :
    s7e_mEdge (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂)) =
      secondHalfEdgeIndex M a (s7e_mEdge m₂) := by
  cases m₂ with
  | inl j =>
    have hj : j ≠ 0 := fun h => h0 (by rw [h])
    rw [s7r_slidingMark'_inr_inl, secondHalfIndex_nonzero M a hj]; rfl
  | inr v => rw [s7r_slidingMark'_inr_inr]; rfl

include hQ hz hr hr1 hord h₂ in
theorem s7r_param_second' (hn₂ : 3 ≤ secondHalfSize M a) (m₂ : Mark (secondHalf P M a)) (h0 : m₂ ≠ Sum.inl 0)
    (v' : Visit (secondHalf P M a)) (he : v'.2.val = s7e_mEdge m₂) :
    s7e_mParam (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂)) <
        visitParameter (s7b_secondVisitQ hn hsep hm hQC v') ↔
      s7e_mParam m₂ < visitParameter v' := by
  cases m₂ with
  | inl j =>
    rw [s7r_slidingMark'_inr_inl]
    exact iff_of_true (s7e_visitParameter_pos hn hQ _) (s7e_visitParameter_pos hn₂ h₂ v')
  | inr v => rw [s7r_slidingMark'_inr_inr]; exact s7r_second_order hn hsep hz hm hr hr1 hQC hord v v' he.symm

include hQ hz hr hr0 hr1 hη hw hord hside hSimg h₁ in
/-- **The chain out of the contact `a`-visit** (the exit of `λ₂`'s vertex `0`): the iterates from
`nextMark v_a` reach the Q-mark of `nextMark (inl 0)` on `λ₂` through transit marks. -/
theorem s7r_reach_from_va' (hn₂ : 3 ≤ secondHalfSize M a) :
    ∃ k : ℕ, ((smoothingSuccessor hn hQ S) ^ k) (nextMark hn hQ (Sum.inr (s7e_va hc))) =
      s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (nextMark hn₂ h₂ (Sum.inl 0))) ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hQ S) ^ j) (nextMark hn hQ (Sum.inr (s7e_va hc))) ∉
          Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  have hva_near := s7e_va_param_near hn hQ true hw hc
  have hva1 := (abs_lt.mp hva_near).1
  have hva2 := (abs_lt.mp hva_near).2
  have hfirst : ∀ (w' : Visit Q), w'.2.val = a → visitParameter (s7e_va hc) < visitParameter w' →
      ∀ v', s7b_firstVisitQ hn hsep hm hQC v' ≠ w' := by
    intro w' he hlo v' hv'
    have hv'1 : v'.2.val = -1 := by
      rw [← hv', s7b_firstVisitQ_edge] at he
      exact firstHalfIndex_injective M a (by rw [he, firstHalfIndex_last])
    have h1 := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ v' hv'1
    rw [← hv'] at hlo
    linarith
  have hvl_ex : ∀ (w' : Visit Q), w'.2.val = a → w' ≠ s7e_vl hc := by
    intro w' he h; rw [h, s7e_vl_edge, s7r_leg_true] at he; exact s7e_a_ne_M hsep he.symm
  have hsecond : ∀ (w' : Visit Q), w'.2.val = a → ∀ v', s7b_secondVisitQ hn hsep hm hQC v' = w' →
      v'.2.val = 0 := by
    intro w' he v' hv'
    rw [← hv', s7b_secondVisitQ_edge] at he
    exact secondHalfEdgeIndex_injective M a (by rw [he, secondHalfEdgeIndex_zero])
  rcases s7r_nextMark_shape hn₂ h₂ (Sum.inl 0) with hnx | ⟨w, hnx, hwe, hwp⟩
  · have hm' : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (nextMark hn₂ h₂ (Sum.inl 0))) =
        Sum.inl (a + 1) := by
      rw [hnx, s7r_slidingMark'_inr_inl]
      show Sum.inl (secondHalfIndex M a (0 + 1)) = _
      rw [zero_add, secondHalfIndex_one hn hsep]
    rw [hm']
    refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl Sum.inr_ne_inl
      (s7r_transit_window' hn hQ hsep hm hQC hc S hSimg _ _ a (s7e_va_edge hc) (Or.inl rfl) ?_)
    intro w' he hlo _
    refine ⟨fun h => by rw [h] at hlo; exact lt_irrefl _ hlo, hfirst w' he hlo, ?_, hvl_ex w' he⟩
    intro v' hv'
    have hv'0 := hsecond w' he v' hv'
    have hb := s7e_between_inl_mark_inl hn₂ h₂ 0 (Sum.inr v') hv'0 (s7e_visitParameter_pos hn₂ h₂ v')
    exact nextMark_no_mark_between hn₂ h₂ hnx (Sum.inr v') hb
  · have hm' : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (nextMark hn₂ h₂ (Sum.inl 0))) =
        Sum.inr (s7b_secondVisitQ hn hsep hm hQC w) := by rw [hnx, s7r_slidingMark'_inr_inr]
    rw [hm']
    have hwe0 : w.2.val = 0 := hwe
    have hwgt := s7r_second_cut_gt hn hQ hsep hz hm hr hr1 hQC hw hside h₂ w hwe0
    have hne : (Sum.inr (s7e_va hc) : Mark Q) ≠ Sum.inr (s7b_secondVisitQ hn hsep hm hQC w) := by
      intro h
      exact s7b_secondCrossingQ_not_affected hn hsep hm hQC w.1
        (by rw [← s7b_secondVisitQ_fst hn hsep hm hQC w, ← Sum.inr_injective h]; exact s7r_va_affected' hc)
    refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne
      (s7r_transit_window' hn hQ hsep hm hQC hc S hSimg _ _ a (s7e_va_edge hc)
        (Or.inr ⟨by show (s7b_secondVisitQ hn hsep hm hQC w).2.val = a; rw [s7b_secondVisitQ_edge, hwe0, secondHalfEdgeIndex_zero], by
          show visitParameter (s7e_va hc) < visitParameter (s7b_secondVisitQ hn hsep hm hQC w); linarith⟩) ?_)
    intro w' he hlo hhi
    have hhi' : visitParameter w' < visitParameter (s7b_secondVisitQ hn hsep hm hQC w) := by
      rcases hhi with h | h
      · exact absurd h Sum.inr_ne_inl
      · exact h
    refine ⟨fun h => by rw [h] at hlo; exact lt_irrefl _ hlo, hfirst w' he hlo, ?_, hvl_ex w' he⟩
    intro v' hv'
    have hv'0 := hsecond w' he v' hv'
    have hup : visitParameter v' < visitParameter w := by
      rw [← hv'] at hhi'
      exact (s7r_second_order hn hsep hz hm hr hr1 hQC hord v' w (hv'0.trans hwe0.symm)).mp hhi'
    have hb := s7e_between_same_edge hn₂ h₂ (Sum.inl 0) (Sum.inr v') (Sum.inr w) hv'0.symm
      (by rw [s7e_mEdge_inr, s7e_mEdge_inr, hv'0, hwe0]) (s7e_visitParameter_pos hn₂ h₂ v') hup
    exact nextMark_no_mark_between hn₂ h₂ hnx (Sum.inr v') hb

include hQ hz hr hr0 hr1 hη hw hord hside huniq hxS hSimg h₁ in
/-- **Second-half reach on the leg-`M` side.** -/
theorem s7r_reach_second' (hn₂ : 3 ≤ secondHalfSize M a) (m₂ : Mark (secondHalf P M a)) :
    ∃ k : ℕ, ((smoothingSuccessor hn hQ S) ^ k)
        (nextMark hn hQ (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂))) =
      s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (nextMark hn₂ h₂ m₂)) ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (nextMark hn hQ (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂))) ∉
          Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  have hinj := s7r_slidingMark'_injective hn hsep hm hQC hc
  have hva_near := s7e_va_param_near hn hQ true hw hc
  have hva1 := (abs_lt.mp hva_near).1
  have hva2 := (abs_lt.mp hva_near).2
  by_cases h0 : m₂ = Sum.inl 0
  · -- the vertex `0 ↦ μ_M`: `nextMark μ_M = v_ℓ`, `f v_ℓ = nextMark v_a`, then the chain out of `v_a`
    subst h0
    rw [s7r_slidingMark'_inr_inl, secondHalfIndex_zero, s7r_nextMark_M hn hQ hsep hη hw hc huniq]
    refine s7r_reach_trans hn hQ S _ ⟨0, by simp, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      (s7r_vl_not_mem_range' hn hsep hm hQC hc) ?_
    rw [s7r_succ_vl' hn hQ hsep hc S hxS]
    exact s7r_reach_from_va' hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc S hSimg hn₂
  · have hedge_u := s7r_edge_second' hn hsep hm hQC hc m₂ h0
    have hne_u : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂) ≠
        s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (nextMark hn₂ h₂ m₂)) := fun h =>
      markSuccessor_ne_self hn₂ h₂ m₂ (Sum.inr.inj (hinj h)).symm
    have hsecond : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
        ∀ v' : Visit (secondHalf P M a), s7b_secondVisitQ hn hsep hm hQC v' = w' →
        v'.2.val = s7e_mEdge m₂ ∧
          (s7e_mParam (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂)) < visitParameter w' ↔
            s7e_mParam m₂ < visitParameter v') := by
      intro w' he v' hv'
      have hv'e : v'.2.val = s7e_mEdge m₂ := by
        apply secondHalfEdgeIndex_injective M a
        rw [← s7b_secondVisitQ_edge hn hsep hm hQC v', hv', he]
      refine ⟨hv'e, ?_⟩
      rw [← hv']
      exact s7r_param_second' hn hQ hsep hz hm hr hr1 hQC hord h₂ hc hn₂ m₂ h0 v' hv'e
    -- on the cut (`j = 0`, forced by `m₂ = inr v`) the Q-mark is beyond `r + 3η`
    have hlow0 : s7e_mEdge m₂ = 0 →
        r + 3 * η < s7e_mParam (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂)) := by
      intro hj0
      cases m₂ with
      | inl j => exact absurd (by rw [show j = 0 from hj0]) h0
      | inr v =>
        rw [s7r_slidingMark'_inr_inr]
        exact s7r_second_cut_gt hn hQ hsep hz hm hr hr1 hQC hw hside h₂ v hj0
    have hfirst : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
        s7e_mParam (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂)) < visitParameter w' →
        ∀ v', s7b_firstVisitQ hn hsep hm hQC v' ≠ w' := by
      intro w' he hlo v' hv'
      rw [← hv', s7b_firstVisitQ_edge] at he
      obtain ⟨hv'1, hj0⟩ := s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep he
      have h1 := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside h₁ v' hv'1
      have h2 := hlow0 hj0
      rw [← hv'] at hlo
      linarith
    have hva_ex : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
        s7e_mParam (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂)) < visitParameter w' →
        w' ≠ s7e_va hc := by
      intro w' he hlo h
      rw [h, s7e_va_edge] at he
      have hj0 : s7e_mEdge m₂ = 0 :=
        secondHalfEdgeIndex_injective M a (by rw [← he, secondHalfEdgeIndex_zero])
      have h2 := hlow0 hj0
      rw [h] at hlo
      linarith
    have hvl_ex : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) → w' ≠ s7e_vl hc := by
      intro w' he h
      rw [h, s7e_vl_edge, s7r_leg_true] at he
      exact s7b_secondHalfEdgeIndex_ne hn hsep _ he.symm
    rcases s7r_nextMark_shape hn₂ h₂ m₂ with hnx | ⟨w, hnx, hwe, hwp⟩
    · -- vertex target `inl (j+1) ↦ μ_{secondHalfEdgeIndex j + 1}` (for `j = −1` this is `μ_M`)
      have hm' : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (nextMark hn₂ h₂ m₂)) =
          Sum.inl (secondHalfEdgeIndex M a (s7e_mEdge m₂) + 1) := by
        rw [hnx, s7r_slidingMark'_inr_inl, s7r_secondHalfIndex_succ hn hsep]
      rw [hm'] at hne_u ⊢
      refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
        (s7r_transit_window' hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inl rfl) ?_)
      intro w' he hlo _
      refine ⟨hva_ex w' he hlo, hfirst w' he hlo, ?_, hvl_ex w' he⟩
      intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hsecond w' he v' hv'
      exact s7r_no_half_between hn₂ h₂ m₂ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
    · have hm' : s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (nextMark hn₂ h₂ m₂)) =
          Sum.inr (s7b_secondVisitQ hn hsep hm hQC w) := by rw [hnx, s7r_slidingMark'_inr_inr]
      rw [hm'] at hne_u ⊢
      have hwQe : (s7b_secondVisitQ hn hsep hm hQC w).2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) := by
        rw [s7b_secondVisitQ_edge, hwe]
      have hlt_u : s7e_mParam (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m₂)) <
          visitParameter (s7b_secondVisitQ hn hsep hm hQC w) :=
        (s7r_param_second' hn hQ hsep hz hm hr hr1 hQC hord h₂ hc hn₂ m₂ h0 w hwe).mpr hwp
      refine s7r_reach_of_transit hn hQ S _ _ _ _ rfl hne_u
        (s7r_transit_window' hn hQ hsep hm hQC hc S hSimg _ _ _ hedge_u (Or.inr ⟨hwQe, hlt_u⟩) ?_)
      intro w' he hlo hhi
      have hhi' : visitParameter w' < visitParameter (s7b_secondVisitQ hn hsep hm hQC w) := by
        rcases hhi with h | h
        · exact absurd h Sum.inr_ne_inl
        · exact h
      refine ⟨hva_ex w' he hlo, hfirst w' he hlo, ?_, hvl_ex w' he⟩
      intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hsecond w' he v' hv'
      have hup : visitParameter v' < visitParameter w := by
        rw [← hv'] at hhi'
        exact (s7r_second_order hn hsep hz hm hr hr1 hQC hord v' w (hv'e.trans hwe.symm)).mp hhi'
      exact s7r_no_half_between hn₂ h₂ m₂ _ rfl v' hv'e (hiff.mp hlo)
        (Or.inr ⟨by rw [hnx]; exact hwe, by rw [hnx]; exact hup⟩)

include hQ hz hr hr0 hr1 hη hw hord hside huniq hxS hSimg h₁ in
/-- **Second-half step on the leg-`M` side.** -/
theorem s7r_step_second' (hn₂ : 3 ≤ secondHalfSize M a) (S₂ : Finset (Crossing (secondHalf P M a)))
    (hS₂ : S₂ = s7b_pre (s7b_secondCrossingQ hn hsep hm hQC) S) (m : Mark (secondHalf P M a)) :
    ∃ k : ℕ, 0 < k ∧ ((smoothingSuccessor hn hQ S) ^ k)
        (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m)) =
      s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (smoothingSuccessor hn₂ h₂ S₂ m)) ∧
      ∀ j : ℕ, 0 < j → j < k → ((smoothingSuccessor hn hQ S) ^ j)
        (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m)) ∉
          Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  have hu : selectedMarkPerm S (s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr m)) =
      s7r_slidingMark' hn hsep hm hQC (s7e_va hc) (Sum.inr (selectedMarkPerm S₂ m)) := by
    cases m with
    | inl j => rfl
    | inr v =>
      rw [s7r_slidingMark'_inr_inr, selectedMarkPerm_visit, selectedMarkPerm_visit, s7r_slidingMark'_inr_inr]
      congr 1
      by_cases hv : v.1 ∈ S₂
      · have hvQ : (s7b_secondVisitQ hn hsep hm hQC v).1 ∈ S := by
          rw [s7b_secondVisitQ_fst]; rw [hS₂, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_mem S₂ v hv, selectedVisitTwin_of_mem S _ hvQ, s7b_secondVisitQ_visitTwin]
      · have hvQ : (s7b_secondVisitQ hn hsep hm hQC v).1 ∉ S := by
          rw [s7b_secondVisitQ_fst]; rw [hS₂, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_not_mem S₂ v hv, selectedVisitTwin_of_not_mem S _ hvQ]
  exact s7r_step_of_reach hn hQ S _ (Sum.inr m) _ _ hu
    (s7r_reach_second' hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc huniq S hxS hSimg hn₂
      (selectedMarkPerm S₂ m))

include hQ hz hr hr0 hr1 hη hw hord hside hxS hSimg h₁ h₂ in
/-- **Hit on the leg-`M` side** (beacon `μ_M`; the leg visit exits through `v_a`'s chain). -/
theorem s7r_hit' (u : Mark Q) :
    ∃ j : ℕ, ((smoothingSuccessor hn hQ S) ^ j) u ∈ Set.range (s7r_slidingMark' hn hsep hm hQC (s7e_va hc)) := by
  refine s7r_hit_of_transit hn hQ S _ (Sum.inl M)
    ⟨Sum.inr (Sum.inl 0), by rw [s7r_slidingMark'_inr_inl, secondHalfIndex_zero]⟩ ?_ _ u rfl
  intro w hwr
  cases w with
  | inl i => exact Or.inr (smoothingSuccessor_vertex hn hQ S i)
  | inr w' =>
    by_cases hwS : w'.1 ∈ S
    · by_cases hwx : w'.1 = (s7e_va hc).1
      · rcases s7e_visit_of_fst hc w' (by rw [hwx]; rfl) (s7e_a_ne_leg true hsep) with h | h
        · exact absurd (h ▸ s7r_va_mem_range' hn hsep hm hQC hc) hwr
        · subst h; left
          obtain ⟨k, hk, -⟩ := s7r_reach_from_va' hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc S hSimg
            (contactHalfSizes_bounds hn hsep).2.1
          refine ⟨k + 1, ?_⟩
          rw [pow_succ, Equiv.Perm.mul_apply, s7r_succ_vl' hn hQ hsep hc S hxS, hk]
          exact ⟨_, rfl⟩
      · exfalso; apply hwr
        rcases hSimg w'.1 hwS hwx with ⟨c, hcw⟩ | ⟨c, hcw⟩
        · obtain ⟨v, -, hv⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC w' c hcw.symm
          exact (s7r_inr_mem_range_iff' hn hsep hm hQC hc w').mpr (Or.inr (Or.inl ⟨v, hv⟩))
        · obtain ⟨v, -, hv⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC w' c hcw.symm
          exact (s7r_inr_mem_range_iff' hn hsep hm hQC hc w').mpr (Or.inr (Or.inr ⟨v, hv⟩))
    · exact Or.inr (smoothingSuccessor_visit_of_not_mem hn hQ S w' hwS)

include hz hr hr0 hr1 hη hw hord hside huniq hxS hSimg in
/-- **The first-return law on the leg-`M` side, PROVED for the corrected mark map** (the corrected
form of `s7b_SlidingTransport.ret` there, rule 4). -/
theorem s7r_slidingTransport_of_leg_true :
    s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S (s7b_pre (s7b_firstCrossingQ hn hsep hm hQC) S)
      (s7b_pre (s7b_secondCrossingQ hn hsep hm hQC) S) (s7e_va hc) where
  affected := s7r_va_affected' hc
  pivot_mem := hxS
  first_pre := rfl
  second_pre := rfl
  ret :=
    { inj := s7r_slidingMark'_injective hn hsep hm hQC hc
      step := fun b => by
        rcases b with m | m
        · exact s7r_step_first' hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc S hxS hSimg
            (contactHalfSizes_bounds hn hsep).1.1 _ rfl m
        · exact s7r_step_second' hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc huniq S hxS hSimg
            (contactHalfSizes_bounds hn hsep).2.1 _ rfl m
      hit := s7r_hit' hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside h₁ h₂ hc S hxS hSimg }

end S7RLegTrue

section S7RTransportConsequences

/-! ##### The consequences of `s7r_SlidingTransport'` (the leg-`M` side): the port of the
`s7b_SlidingTransport` namespace (owners, `componentEquiv`, carrier crossings and `m_Q`) to the corrected
mark map — part I is generic in `ι`, so the proofs are those of SM/CornerChainUnits verbatim; only the two
contact-carrier lemmas exchange their halves. -/

variable {hn : 3 ≤ n} {M a : ZMod n} {hsep : ContactSeparated M a} {P Q : LabelledTuple n}
  {hm : P M ∈ edgeInterior P a}
  {hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)}
  {hQ : Generic Q} {h₁ : Generic (firstHalf P M a)} {h₂ : Generic (secondHalf P M a)}
  {S : Finset (Crossing Q)} {S₁ : Finset (Crossing (firstHalf P M a))}
  {S₂ : Finset (Crossing (secondHalf P M a))} {va : Visit Q}

namespace s7r_SlidingTransport'

variable {hn : 3 ≤ n} {M a : ZMod n} {hsep : ContactSeparated M a} {P Q : LabelledTuple n}
  {hm : P M ∈ edgeInterior P a}
  {hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)}
  {hQ : Generic Q} {h₁ : Generic (firstHalf P M a)} {h₂ : Generic (secondHalf P M a)}
  {S : Finset (Crossing Q)} {S₁ : Finset (Crossing (firstHalf P M a))}
  {S₂ : Finset (Crossing (secondHalf P M a))} {va : Visit Q}

/-- Two marks of `λ₁` have one owner iff their images have one owner on `Q`. -/
theorem owner_inl_iff (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (m m' : Mark (firstHalf P M a)) :
    owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inl m)) =
        owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inl m')) ↔
      owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ m =
        owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ m' := by
  rw [owner_eq_iff, owner_eq_iff, h.ret.sameCycle_iff, s7b_sumCongr_sameCycle_inl]

theorem owner_inr_iff (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (m m' : Mark (secondHalf P M a)) :
    owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inr m)) =
        owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inr m')) ↔
      owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ m =
        owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ m' := by
  rw [owner_eq_iff, owner_eq_iff, h.ret.sameCycle_iff, s7b_sumCongr_sameCycle_inr]

/-- Marks of the two different halves never share an owner on `Q`. -/
theorem owner_inl_ne_inr (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (m : Mark (firstHalf P M a)) (m' : Mark (secondHalf P M a)) :
    owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inl m)) ≠
      owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inr m')) := by
  rw [Ne, owner_eq_iff, h.ret.sameCycle_iff]
  exact s7b_sumCongr_not_sameCycle _ _ m m'

/-- **The carrier correspondence of a sliding row**: the carriers of `S` on `Q` are the carriers of
`S₁` on `λ₁` together with those of `S₂` on `λ₂` (eq. s7c:sliding-residual). -/
def componentEquiv (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) :
    Component hn hQ S ≃
      Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ ⊕
        Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ :=
  h.ret.cycleEquiv.symm.trans (s7b_sumCongr_cycleEquiv _ _)

theorem componentEquiv_owner_inl (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (m : Mark (firstHalf P M a)) :
    h.componentEquiv (owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inl m))) =
      Sum.inl (owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ m) := by
  have he : owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inl m)) =
      h.ret.cycleEquiv (Quotient.mk _ (Sum.inl m)) := rfl
  show s7b_sumCongr_cycleEquiv _ _
    (h.ret.cycleEquiv.symm (owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inl m)))) = _
  rw [he, Equiv.symm_apply_apply]
  rfl

theorem componentEquiv_owner_inr (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (m : Mark (secondHalf P M a)) :
    h.componentEquiv (owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inr m))) =
      Sum.inr (owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ m) := by
  have he : owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inr m)) =
      h.ret.cycleEquiv (Quotient.mk _ (Sum.inr m)) := rfl
  show s7b_sumCongr_cycleEquiv _ _
    (h.ret.cycleEquiv.symm (owner hn hQ S (s7r_slidingMark' hn hsep hm hQC va (Sum.inr m)))) = _
  rw [he, Equiv.symm_apply_apply]
  rfl

/-- The owner on `Q` of a visit carried from `λ₁`, in terms of the half owner. -/
theorem componentEquiv_owner_firstVisit
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) (w : Visit (firstHalf P M a)) :
    h.componentEquiv (owner hn hQ S (Sum.inr (s7b_firstVisitQ hn hsep hm hQC w))) =
      Sum.inl (owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ (Sum.inr w)) :=
  h.componentEquiv_owner_inl (Sum.inr w)

theorem componentEquiv_owner_secondVisit
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) (w : Visit (secondHalf P M a)) :
    h.componentEquiv (owner hn hQ S (Sum.inr (s7b_secondVisitQ hn hsep hm hQC w))) =
      Sum.inr (owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ (Sum.inr w)) :=
  h.componentEquiv_owner_inr (Sum.inr w)

/-- On the leg-`M` side the carrier through the contact vertex `μ_M` on `Q` corresponds to `λ₂`'s
carrier through its vertex `0 = μ_M` (the roles of the two contact carriers are exchanged with respect
to the leg-`M−1` side, `s7b_SlidingTransport.componentEquiv_owner_vertexM`). -/
theorem componentEquiv_owner_vertexM (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) :
    h.componentEquiv (owner hn hQ S (Sum.inl M)) =
      Sum.inr (owner (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ (Sum.inl 0)) := by
  have he : (Sum.inl M : Mark Q) = s7r_slidingMark' hn hsep hm hQC va (Sum.inr (Sum.inl 0)) := by
    show _ = Sum.inl (secondHalfIndex M a 0)
    rw [secondHalfIndex_zero]
  rw [he, h.componentEquiv_owner_inr]

/-- On the leg-`M` side the carrier through the contact `a`-visit `va` on `Q` corresponds to `λ₁`'s
carrier through its vertex `0 = μ_M`. -/
theorem componentEquiv_owner_pivot (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) :
    h.componentEquiv (owner hn hQ S (Sum.inr va)) =
      Sum.inl (owner (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ (Sum.inl 0)) := by
  have he : (Sum.inr va : Mark Q) = s7r_slidingMark' hn hsep hm hQC va (Sum.inl (Sum.inl 0)) := by
    simp [s7r_slidingMark']
  rw [he, h.componentEquiv_owner_inl]

/-- A carried crossing of `λ₁` is a crossing of the carrier `q` of `S` iff it is a crossing of the
corresponding half carrier. -/
theorem firstCrossingQ_mem_carrierCrossings_iff
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) (c : Crossing (firstHalf P M a))
    (q : Component hn hQ S) (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
    (hq : h.componentEquiv q = Sum.inl q₁) :
    s7b_firstCrossingQ hn hsep hm hQC c ∈ carrierCrossings hn hQ S q ↔
      c ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ := by
  rw [mem_carrierCrossings, mem_carrierCrossings]
  have hmem : s7b_firstCrossingQ hn hsep hm hQC c ∈ S ↔ c ∈ S₁ := by
    rw [h.first_pre, s7b_mem_pre]
  rw [hmem]
  refine and_congr Iff.rfl ⟨fun hall w hw => ?_, fun hall v hv => ?_⟩
  · have hv := hall (s7b_firstVisitQ hn hsep hm hQC w) (by
      rw [s7b_firstVisitQ_fst, hw])
    have := h.componentEquiv_owner_firstVisit w
    rw [hv, hq] at this
    exact (Sum.inl.inj this).symm
  · obtain ⟨w, hw, rfl⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC v c hv
    apply h.componentEquiv.injective
    rw [h.componentEquiv_owner_firstVisit, hall w hw, hq]

theorem secondCrossingQ_mem_carrierCrossings_iff
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) (c : Crossing (secondHalf P M a))
    (q : Component hn hQ S) (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂)
    (hq : h.componentEquiv q = Sum.inr q₂) :
    s7b_secondCrossingQ hn hsep hm hQC c ∈ carrierCrossings hn hQ S q ↔
      c ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ := by
  rw [mem_carrierCrossings, mem_carrierCrossings]
  have hmem : s7b_secondCrossingQ hn hsep hm hQC c ∈ S ↔ c ∈ S₂ := by
    rw [h.second_pre, s7b_mem_pre]
  rw [hmem]
  refine and_congr Iff.rfl ⟨fun hall w hw => ?_, fun hall v hv => ?_⟩
  · have hv := hall (s7b_secondVisitQ hn hsep hm hQC w) (by
      rw [s7b_secondVisitQ_fst, hw])
    have := h.componentEquiv_owner_secondVisit w
    rw [hv, hq] at this
    exact (Sum.inr.inj this).symm
  · obtain ⟨w, hw, rfl⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC v c hv
    apply h.componentEquiv.injective
    rw [h.componentEquiv_owner_secondVisit, hall w hw, hq]

/-- A carried crossing of `λ₂` is never a crossing of a carrier corresponding to a carrier of `λ₁`
(and symmetrically). -/
theorem secondCrossingQ_notMem_carrierCrossings
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) (c : Crossing (secondHalf P M a))
    (q : Component hn hQ S) (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁)
    (hq : h.componentEquiv q = Sum.inl q₁) :
    s7b_secondCrossingQ hn hsep hm hQC c ∉ carrierCrossings hn hQ S q := by
  intro hc
  rw [mem_carrierCrossings] at hc
  obtain ⟨i, j, hs, -, -⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hv := hc.2 (s7b_secondVisitQ hn hsep hm hQC ⟨c, ⟨i, hi⟩⟩) rfl
  have := h.componentEquiv_owner_secondVisit ⟨c, ⟨i, hi⟩⟩
  rw [hv, hq] at this
  exact Sum.inl_ne_inr this

theorem firstCrossingQ_notMem_carrierCrossings
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va) (c : Crossing (firstHalf P M a))
    (q : Component hn hQ S) (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂)
    (hq : h.componentEquiv q = Sum.inr q₂) :
    s7b_firstCrossingQ hn hsep hm hQC c ∉ carrierCrossings hn hQ S q := by
  intro hc
  rw [mem_carrierCrossings] at hc
  obtain ⟨i, j, hs, -, -⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hv := hc.2 (s7b_firstVisitQ hn hsep hm hQC ⟨c, ⟨i, hi⟩⟩) rfl
  have := h.componentEquiv_owner_firstVisit ⟨c, ⟨i, hi⟩⟩
  rw [hv, hq] at this
  exact Sum.inr_ne_inl this

/-- Under the pivot split (part IV: the crossings of `Q` off the two images are `x₋` and the
crossings interlacing it), every carrier crossing of `S` is carried from a half: a crossing
interlacing `x₋ ∈ S` has its visits on two different carriers (lem:carriers (iii)). -/
theorem carrierCrossings_mem_range
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) va.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S) {y : Crossing Q}
    (hy : y ∈ carrierCrossings hn hQ S q) :
    y ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪
      Set.range (s7b_secondCrossingQ hn hsep hm hQC) := by
  rw [mem_carrierCrossings] at hy
  have hyx : y ≠ va.1 := fun he => hy.1 (he ▸ h.pivot_mem)
  have hnot : ∀ z : Crossing Q, Interlaces hn hQ y z → z ∈ S → False := by
    intro z hz hzS
    have hN : y ∈ supportNeighbors hn hQ S := (mem_supportNeighbors hn hQ S y).mpr ⟨z, hzS, hz⟩
    obtain ⟨i, j, hs, -, -⟩ := y.property
    have hi : i ∈ y.val := by rw [hs]; simp
    have hsep' := (carriers_lemma hn hQ hS).neighbor_visits_separated y hN ⟨y, ⟨i, hi⟩⟩ rfl
    exact hsep' ((hy.2 ⟨y, ⟨i, hi⟩⟩ rfl).trans (hy.2 (visitTwin ⟨y, ⟨i, hi⟩⟩) rfl).symm)
  exact hsplit.x_split y hyx (fun hI => hnot _ (interlaces_symm hn hQ hI) h.pivot_mem)
    (fun hI => hnot _ hI h.pivot_mem)

/-- **`m_Q` of a carrier corresponding to a carrier of `λ₁`**: its crossings are exactly the carried
crossings of the half carrier, so the counts agree (eq. s7c:sliding-residual for the self-crossings;
the input to the coefficient transport of U110-D and to the slot `d_Q`). -/
theorem carrierCrossings_eq_img_first
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) va.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁) (hq : h.componentEquiv q = Sum.inl q₁) :
    carrierCrossings hn hQ S q =
      s7b_img (s7b_firstCrossingQ_injective hn hsep hm hQC)
        (carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁) := by
  ext y
  rw [s7b_mem_img]
  constructor
  · intro hy
    rcases h.carrierCrossings_mem_range hsplit hS q hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact ⟨c, (h.firstCrossingQ_mem_carrierCrossings_iff c q q₁ hq).mp hy, rfl⟩
    · exact absurd hy (h.secondCrossingQ_notMem_carrierCrossings c q q₁ hq)
  · rintro ⟨c, hc, rfl⟩
    exact (h.firstCrossingQ_mem_carrierCrossings_iff c q q₁ hq).mpr hc

theorem carrierCrossings_eq_img_second
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) va.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂) (hq : h.componentEquiv q = Sum.inr q₂) :
    carrierCrossings hn hQ S q =
      s7b_img (s7b_secondCrossingQ_injective hn hsep hm hQC)
        (carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂) := by
  ext y
  rw [s7b_mem_img]
  constructor
  · intro hy
    rcases h.carrierCrossings_mem_range hsplit hS q hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact absurd hy (h.firstCrossingQ_notMem_carrierCrossings c q q₂ hq)
    · exact ⟨c, (h.secondCrossingQ_mem_carrierCrossings_iff c q q₂ hq).mp hy, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact (h.secondCrossingQ_mem_carrierCrossings_iff c q q₂ hq).mpr hc

theorem carrierCrossingCount_eq_first
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) va.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁) (hq : h.componentEquiv q = Sum.inl q₁) :
    carrierCrossingCount hn hQ S q =
      carrierCrossingCount (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ := by
  unfold carrierCrossingCount
  rw [h.carrierCrossings_eq_img_first hsplit hS q q₁ hq, s7b_img, Finset.card_map]

theorem carrierCrossingCount_eq_second
    (h : s7r_SlidingTransport' hn hQ hsep hm hQC h₁ h₂ S S₁ S₂ va)
    (hsplit : s7b_PivotSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) va.1)
    (hS : IsDecomposition hn hQ S) (q : Component hn hQ S)
    (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂) (hq : h.componentEquiv q = Sum.inr q₂) :
    carrierCrossingCount hn hQ S q =
      carrierCrossingCount (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ := by
  unfold carrierCrossingCount
  rw [h.carrierCrossings_eq_img_second hsplit hS q q₂ hq, s7b_img, Finset.card_map]

end s7r_SlidingTransport'

end S7RTransportConsequences

section S7RGerm

/-! ##### Instantiation at a sliding wall germ: the local data of lem:wall-sides (V) supplies every
hypothesis of `s7r_slidingTransport_of_leg_false` below the interval radius. -/

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} {r η δ : ℝ}

/-- **Sign constancy between a side and the centre**: the `u = 0` case of `s7a2_pos_of_ne_zero`
(W2_S7E_REPORT §2: "sign constancy on the interval replaces the approach clause"). -/
theorem s7r_sign_const_center (h : g.SlidingAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ)
    (hη : 0 < η) (t : g.SideParameter) (ht : t.val < δ) (b : Bool) (j : ZMod n)
    (hc : IsCrossing g.center {a, j}) (hnot : ¬ ContactAffected M a {a, j}) :
    edgeParameter (g.curve (g.sideTime b t)) a j < r ↔ edgeParameter g.center a j < r := by
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
  have hlt : |(g.sideTime b t).val| < δ := by rw [g.sideTime_val_abs]; exact ht
  have h0 : (g.zeroParameter).val = 0 := rfl
  have h0abs : |(g.zeroParameter).val| ≤ t.val := by rw [h0, abs_zero]; exact t.property.1.le
  have hcenter : g.center = g.curve g.zeroParameter := rfl
  constructor
  · intro h1
    by_contra h2
    have hpos : 0 < -(edgeParameter (g.curve (g.sideTime b t)) a j - r) := by linarith
    have := s7a2_pos_of_ne_zero g ht hcont' hne' b hpos g.zeroParameter h0abs
    rw [← hcenter] at this
    linarith
  · intro h1
    by_contra h2
    have hpos : 0 < edgeParameter (g.curve (g.sideTime b t)) a j - r :=
      lt_of_le_of_ne (by linarith) (hne _ hlt).symm
    have := s7a2_pos_of_ne_zero g ht hcont hne b hpos g.zeroParameter h0abs
    rw [← hcenter] at this
    linarith

/-- The side-of-`r` law on edge `a` for a side, relative to the centre. -/
theorem s7r_hside (h : g.SlidingAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ) (hη : 0 < η)
    (t : g.SideParameter) (ht : t.val < δ) (b : Bool) :
    ∀ (u : Visit g.center) (hu : ¬ ContactAffected M a u.1.val), u.2.val = a →
      (visitParameter (s7a_visit (s7e_hQC hn g h t b) u hu) < r ↔ visitParameter u < r) := by
  intro u hu he
  obtain ⟨j, -, hj⟩ := crossing_support_partner u.1 u.2.val u.2.property
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.1.2.1
  have h1 : visitParameter u = edgeParameter g.center a j := by
    rw [contact_visitParameter_eq_of_support_pair hn h.1.1 hz u hu j hj, he]
  have h2 : visitParameter (s7a_visit (s7e_hQC hn g h t b) u hu) =
      edgeParameter (g.curve (g.sideTime b t)) a j := by
    rw [visitParameter_eq_of_support_pair hn (s7a_sideGeneric g b).1 (s7a_visit (s7e_hQC hn g h t b) u hu) j hj,
      s7a_visit_edge, he]
  have hj' : u.1.val = {a, j} := by rw [hj, he]
  have hnot : ¬ ContactAffected M a {a, j} := by rw [← hj']; exact hu
  have hc : IsCrossing g.center {a, j} := by rw [← hj']; exact u.1.property
  rw [h1, h2]
  exact s7r_sign_const_center hn g h hloc hη t ht b j hc hnot

/-- The same-edge order law for a side, relative to the centre (`VertexLocalData.visit_order`). -/
theorem s7r_hord (h : g.SlidingAt M a) (hloc : s7a2_IntervalLocal hn g M a r η δ)
    (t : g.SideParameter) (ht : t.val < δ) (b : Bool) :
    ∀ (u u' : Visit g.center) (hu : ¬ ContactAffected M a u.1.val) (hu' : ¬ ContactAffected M a u'.1.val),
      u.2.val = u'.2.val →
      (visitParameter (s7a_visit (s7e_hQC hn g h t b) u hu) <
          visitParameter (s7a_visit (s7e_hQC hn g h t b) u' hu') ↔
        visitParameter u < visitParameter u') :=
  fun u u' hu hu' he =>
    (hloc (g.sideTime b t) (by rw [g.sideTime_val_abs]; exact ht)).visit_order (s7a_sideGeneric g b).1
      ⟨u, hu⟩ ⟨u', hu'⟩ he

include hn in
/-- On a side carrying `{a, M − 1}`, that is the only contact-affected crossing (the sliding pattern). -/
theorem s7r_huniq (h : g.SlidingAt M a) (t : g.SideParameter) (b : Bool)
    (hc : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg false M}) :
    ∀ y : Crossing (g.curve (g.sideTime b t)), ContactAffected M a y.val → y.val = {a, contactLeg false M} := by
  intro y hy
  obtain ⟨f', hf'⟩ := (contactAffected_iff_leg _).mp hy
  cases f'
  · exact hf'
  · exfalso
    have hp := s7e_pattern hn h t
    have hy' : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg true M} := hf' ▸ y.property
    cases b <;> cases hl : s7e_leg g M a <;> simp only [hl, Bool.not_true, Bool.not_false] at hp
    · exact hp.2.1 hy'
    · exact hp.2.1 hc
    · exact hp.2.2.2 hc
    · exact hp.2.2.2 hy'

/-- **The sliding transport instances below a radius** (U_S7B §2.1, the `s7b_SlidingTransport.ret`
deliverable): on any side `b` of a sliding wall carrying the contact crossing `{a, M − 1}` (so
`b = false` when `s7e_leg g M a = false`, `b = true` when it is `true`), every sliding row `S ∋ x`
whose other crossings are carried from the halves is a `s7b_SlidingTransport` at the leg visit; hence
`componentEquiv`, `carrierCrossings_eq_img_first/_second`, `carrierCrossingCount_eq_*` apply (with
`hSimg` from `s7r_img_of_decomposition` on a decomposition and the pivot split).  The OTHER side
(leg `M`) is `s7r_slidingTransport_of_leg_true` (black box, corrected mark map). -/
theorem s7r_slidingTransport_side (h : g.SlidingAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → ∀ b : Bool,
      ∀ (hc : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg false M})
        (S : Finset (Crossing (g.curve (g.sideTime b t)))), (s7e_va hc).1 ∈ S →
        (∀ y ∈ S, y ≠ (s7e_va hc).1 →
          y ∈ Set.range (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b)) ∪
            Set.range (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b))) →
        s7b_SlidingTransport hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b) (s7a_sideGeneric g b) h₁ h₂ S
          (s7b_pre (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b)) S)
          (s7b_pre (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b)) S) (s7e_vl hc) := by
  obtain ⟨r, η, hr0, hr1, hr, hη, -, -, δ, hδ, -, hloc⟩ := s7a2_exists_intervalLocal hn g M a h.1
  refine ⟨δ, hδ, fun t ht b hc S hxS hSimg => ?_⟩
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.1.2.1
  exact s7r_slidingTransport_of_leg_false hn (s7a_sideGeneric g b) h.1.1 hz h.1.2.2.2.1 hr hr0 hr1 hη
    (s7e_hQC hn g h t b) (s7e_hw hn g hloc t ht b) (s7r_hord hn g h hloc t ht b)
    (s7r_hside hn g h hloc hη t ht b) h₁ h₂ hc (s7r_huniq hn g h t b hc) S hxS hSimg


include hn in
/-- On a side carrying `{a, M}`, that is the only contact-affected crossing (the sliding pattern). -/
theorem s7r_huniq' (h : g.SlidingAt M a) (t : g.SideParameter) (b : Bool)
    (hc : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg true M}) :
    ∀ y : Crossing (g.curve (g.sideTime b t)), ContactAffected M a y.val → y.val = {a, contactLeg true M} := by
  intro y hy
  obtain ⟨f', hf'⟩ := (contactAffected_iff_leg _).mp hy
  cases f'
  · exfalso
    have hp := s7e_pattern hn h t
    have hy' : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg false M} := hf' ▸ y.property
    cases b <;> cases hl : s7e_leg g M a <;> simp only [hl, Bool.not_true, Bool.not_false] at hp
    · exact hp.2.1 hc
    · exact hp.2.1 hy'
    · exact hp.2.2.2 hy'
    · exact hp.2.2.2 hc
  · exact hf'

/-- **The sliding transport instances below a radius on the leg-`M` side** (the corrected structure
`s7r_SlidingTransport'`; the side `b = true` when `s7e_leg g M a = false`, `b = false` when it is `true`). -/
theorem s7r_slidingTransport_side' (h : g.SlidingAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → ∀ b : Bool,
      ∀ (hc : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg true M})
        (S : Finset (Crossing (g.curve (g.sideTime b t)))), (s7e_va hc).1 ∈ S →
        (∀ y ∈ S, y ≠ (s7e_va hc).1 →
          y ∈ Set.range (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b)) ∪
            Set.range (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b))) →
        s7r_SlidingTransport' hn (s7a_sideGeneric g b) h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b) h₁ h₂ S
          (s7b_pre (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b)) S)
          (s7b_pre (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7e_hQC hn g h t b)) S) (s7e_va hc) := by
  obtain ⟨r, η, hr0, hr1, hr, hη, -, -, δ, hδ, -, hloc⟩ := s7a2_exists_intervalLocal hn g M a h.1
  refine ⟨δ, hδ, fun t ht b hc S hxS hSimg => ?_⟩
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.1.2.1
  exact s7r_slidingTransport_of_leg_true hn (s7a_sideGeneric g b) h.1.1 hz h.1.2.2.2.1 hr hr0 hr1 hη
    (s7e_hQC hn g h t b) (s7e_hw hn g hloc t ht b) (s7r_hord hn g h hloc t ht b)
    (s7r_hside hn g h hloc hη t ht b) h₁ h₂ hc (s7r_huniq' hn g h t b hc) S hxS hSimg

end S7RGerm


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

/-- **DISCHARGED at assembly by unit SPLIT** (`s7p_exists_pivotSplit`, whose conclusion is the unfolded
statement): the two interlacement transfers below a radius. -/
theorem s7q_box_split (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      s7q_Split hn g h t false h₁ h₂ (s7e_xm hn h t) ∧ s7q_Split hn g h t true h₁ h₂ (s7e_xp hn h t) := by
  obtain ⟨δ, hδ, hs⟩ := s7p_exists_pivotSplit hn g h h₁ h₂
  exact ⟨δ, hδ, fun t ht => ⟨(hs t ht).1, (hs t ht).2⟩⟩

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

/-- **DISCHARGED at assembly by unit RET** (`s7r_first_order` / `s7r_second_order` at the germ data `s7r_hord`,
`s7a2_exists_intervalLocal`): the same-edge order agreement on both sides below a radius. -/
theorem s7q_box_order :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → ∀ b : Bool, s7q_OrderAgrees hn g h t b := by
  obtain ⟨r, η, hr0, hr1, hr, hη, -, -, δ, hδ, -, hloc⟩ := s7a2_exists_intervalLocal hn g M a h.1
  refine ⟨δ, hδ, fun t ht b => ?_⟩
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.1.2.1
  unfold s7q_OrderAgrees
  exact ⟨fun v w he => (s7r_first_order hn h.1.1 hz h.1.2.2.2.1 hr hr0 (s7e_hQC hn g h t b)
      (s7r_hord hn g h hloc t ht b) v w he).symm,
    fun v w he => (s7r_second_order hn h.1.1 hz h.1.2.2.2.1 hr hr1 (s7e_hQC hn g h t b)
      (s7r_hord hn g h hloc t ht b) v w he).symm⟩

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


section W3Sliding

/-! ### Wave-3 assembly glue (sliding leaf, prefix `w3_`).  Unit SPLIT DISCHARGED `s7q_box_split`
(`s7p_exists_pivotSplit`; connected inside the ROT block above).  Unit RET proved the first-return law on the
leg-`(M−1)` side (`s7r_slidingTransport_side`: a `s7b_SlidingTransport` at the leg visit `s7e_vl`) and on the leg-`M`
side in the CORRECTED form `s7r_slidingTransport_side'` (`s7r_SlidingTransport'` at the `a`-visit `s7e_va`):
W3_RET_REPORT §2 shows that `s7b_SlidingTransport.ret` is FALSE as stated on the leg-`M` side, so ROT's box
`s7q_box_ret` (= `w3_SlidingRet` below) is NOT provable as stated on that side; ROT's row derivation
(`s7q_CarrierData`, `s7q_rowData_of_transport`, the `componentEquiv` bookkeeping) has to be re-run on
`s7r_SlidingTransport'` for that side before RET's output can be consumed.  The three Props below are ROT's
black-box statements VERBATIM (checked by `w3_SlidingRet_of_box` etc., which typecheck the identity of shapes);
`w3_s7_sliding_law_at_of` is the frozen leaf statement from them. -/

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.SlidingAt M a)

/-- **Remaining Prop S1** = the statement of `s7q_box_ret` (RET → ROT interface; defect note above). -/
def w3_SlidingRet (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) : Prop :=
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
              (s7a_sideGeneric g true) h₁ h₂ (s7e_xp hn h t) hsplitp).symm q).1 q.1.1 q.2.1 vm)

/-- **Prop S2 (PROVED at assembly)** = the statement of `s7q_box_order` (same-edge parameter order agreement of the half
visits under `s7b_firstVisitQ`/`s7b_secondVisitQ`); its proof `w3_SlidingOrder_of_box := s7q_box_order` is sorry-free:
RET's `s7r_first_order`/`s7r_second_order` (the half visit's `Q`-parameter is the centre visit's, rescaled monotonically on
the cut edge) at the germ data `s7r_hord`. -/
def w3_SlidingOrder : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → ∀ b : Bool, s7q_OrderAgrees hn g h t b

/-- **Remaining Prop S3** = the statement of `s7q_box_carriers` (ROT (a)-(c): over bits, rotation equalities, weights). -/
def w3_SlidingCarriers (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) : Prop :=
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
            (s7q_contactTurns hn g h h₁ h₂ q.1.1 q.2.1 (!first)) τ)

/-- Shape check: ROT's sorried box IS Prop S1 (carries `sorryAx`; not on the path of any `w3_*_of`). -/
theorem w3_SlidingRet_of_box (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    w3_SlidingRet hn g h h₁ h₂ := s7q_box_ret hn g h h₁ h₂

/-- **Prop S2 PROVED**: `s7q_box_order` is discharged in the ROT block above (sorry-free). -/
theorem w3_SlidingOrder_of_box : w3_SlidingOrder hn g h := s7q_box_order hn g h

theorem w3_SlidingCarriers_of_box (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    w3_SlidingCarriers hn g h h₁ h₂ := s7q_box_carriers hn g h h₁ h₂

/-- ROT's `s7q_box_rows` with its three boxes as hypotheses (proof = ROT's, the three `obtain`s on the hypotheses). -/
theorem w3_box_rows_of (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (hret : w3_SlidingRet hn g h h₁ h₂) (hcar : w3_SlidingCarriers hn g h h₁ h₂) (hord : w3_SlidingOrder hn g h) :
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
  obtain ⟨δ₁, hδ₁, hret⟩ := hret
  obtain ⟨first, τ, δ₂, hτ, hδ₂, hcar⟩ := hcar
  obtain ⟨δ₃, hδ₃, hord⟩ := hord
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

/-- **`w3_s7_sliding_law_at_of`: the frozen leaf statement of `s7_sliding_law_at` from the three remaining Props**
(proof = ROT's `s7q_exists_contactSector` + `s7e_sliding_law_at_of_contact`, with `s7q_box_split` now proved). -/
theorem w3_s7_sliding_law_at_of (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (hret : w3_SlidingRet hn g h h₁ h₂) (hord : w3_SlidingOrder hn g h) (hcar : w3_SlidingCarriers hn g h h₁ h₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  refine s7e_sliding_law_at_of_contact hn g h h₁ h₂ ?_
  obtain ⟨δ₁, hδ₁, hsplit⟩ := s7q_box_split hn g h h₁ h₂
  obtain ⟨first, τ, δ₂, hτ, hδ₂, hrows⟩ := w3_box_rows_of hn g h h₁ h₂ hret hcar hord
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht => ?_⟩
  obtain ⟨hsplitm, hsplitp⟩ := hsplit t (lt_of_lt_of_le ht (min_le_left _ _))
  have hr := hrows t (lt_of_lt_of_le ht (min_le_right _ _)) hsplitm hsplitp
  exact s7e_contactSector_of_pivotSplit hn g h t h₁ h₂ hsplitm hsplitp fun q =>
    s7q_hterm_of_rows hn g h h₁ h₂ t first hτ hsplitm hsplitp q (hr q).1 (hr q).2.1 (hr q).2.2.1
      (hr q).2.2.2

/-- **`w3_s7_sliding_law_at_of₂`: the leaf from the TWO Props still open** (S2 = `w3_SlidingOrder` is PROVED:
`s7q_box_order`, discharged from RET's `s7r_first_order`/`s7r_second_order` at the germ data). -/
theorem w3_s7_sliding_law_at_of₂ (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (hret : w3_SlidingRet hn g h h₁ h₂) (hcar : w3_SlidingCarriers hn g h h₁ h₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) :=
  w3_s7_sliding_law_at_of hn g h h₁ h₂ hret (s7q_box_order hn g h) hcar

end W3Sliding

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


/-! ### Unit U110-F (wave 3, prefix `s7f_`; PLAN_FINAL §3.3 bigon (1), sm-4:396-448: the two-newborn
sector `B = (1−ε)J`, eq. s7c:sector-split, and the row bookkeeping around it).

**The shape U110-K consumes** (stated first, as required).  Notation: `P₂ = g.curve (g.sideTime
(s7f_side g M a) t)` is the side carrying the two newborn crossings `x = {a, M−1}`, `y = {a, M}`
(`s7f_x`, `s7f_y`), `P₀` the other side, `δ_dir = s7f_dirSign g M a` (`+1` iff `P₋ = P₀`,
eq. s7c:bigon-signs), `ε := Interlaces hn hP₂ x y` (`s7f_Interlacing`), `s = g.contactSign M a`,
`J = s · C(λ₁) · C(λ₂)`, `term = s7e_term` (lem:C-X1's summand, `0` off `Ind`), `lift` the reading of a
support of `P₀` on `P₂` (`s7f_lift`; every crossing of `P₀` is persistent), `Eligible T₀` = every
crossing of `T₀` lifts into a half image (`T₀ ∩ N = ∅`, `s7f_Eligible`).

* `s7f_exists_law_residual` / `s7f_law_residual` — **the assembled shape**, below a radius:
  `C(P₊) − C(P₋) = (1−ε)·J + δ_dir·(Σ_{eligible T₀} (term₂(lift T₀) − term₀(T₀)) +
  Σ_{eligible T₀} (term₂(T₀∪{x}) + term₂(T₀∪{y})))`.  U110-K's remaining obligation is exactly sm-4:448
  "`R_ret = ε·J`" for the second summand (skein extraction G, two-component row H, rotation ledger I,
  floor J, cb:singleton).
* `s7f_sector_split` — **eq. s7c:sector-split** `δ_dir · Σ_two(P₂) = (1−ε)·J` below a radius
  (`ε = 1` PROVED outright: `s7f_twoNewbornSum_eq_zero`; `ε = 0` from black boxes 1-2).
* `s7f_law_decomposition` (every `t`, no radius, no black box): `C(P₊) − C(P₋) = δ_dir · ((Σ_pers(P₂) −
  C(P₀)) + Σ_one(P₂) + Σ_two(P₂))`; `s7f_persistentSum_eq_sum_lift`, `s7f_oneNewbornSum_eq_sum_lift`
  rewrite the first two sectors over the supports of `P₀` (PROVED); `s7f_oneNewbornSum_of_split`
  restricts `Σ_one` to the eligible `T₀` (PROVED from the split); `s7f_persistent_difference_of_transport`
  restricts `Σ_pers − C(P₀)` to the eligible rows (from black box 3).
* `s7f_term_eq_zero_of_ineligible` — sm-4:418-420 "if `T` meets `N`, both newborns are dominated": every
  one- or two-newborn support containing an ineligible old crossing has term `0`.  PROVED (pure).
* `s7f_twoNewbornDecompositionEquiv` — eq. s7c:eligible-bijection on the two-newborn rows at `ε = 0`:
  `{T' ∈ Ind(G_{P₂}) : x, y ∈ T'} ≃ Ind(G_{λ₁}) × Ind(G_{λ₂})`, `T' = {x, y} ∪ ι₁T₁ ∪ ι₂T₂`
  (`s7f_BigonSplit.twoNewbornEquiv`, U110-B's `eligibleEquiv` pattern).  PROVED.
* `s7f_bigonSplit_of` — the split from its open geometric fields only (`inj/disjoint/x_not/y_not` are
  U110-B's).  PROVED.
* `s7f_triangle_data` — eq. s7c:triangle-data on a carrier (`wt = s₀`, `|rot| = 1`, `d = 0`, `c = 1` from
  `s7c_carrierWeight_triangle` and row 105 `corner_values_of_floor hF`).  PROVED.

**Black boxes** (`sorry`, geometric; stated exactly as consumed — see W3_F_REPORT.md §2):
1. `s7f_exists_bigonSplit`: the bigon support split of `P₂` — U110-B §2.2's `rel₁ rel₂ cross cross'` in
   their bigon form on `P₂`, the newborns' independence from the half images (`x_free y_free`) and the
   dichotomy "an old crossing interlacing neither newborn lies in a half image" (`x_split y_split`,
   sm-4:414-416).  Reduced to those fields by `s7f_bigonSplit_of`.
2. `s7f_exists_twoNewbornTerm`: the `ε = 0` termwise identity, sm-4:434-447 — `T ∪ {x, y}` smooths to
   the contact triangle (three corners of turn `−s₀`, crossing-free uniform carrier, `wt = s₀`
   (`s7c_carrierWeight_triangle`), coefficient `1` by `corner_values`(i)) plus the successors of
   `T₁, T₂`: `term(T ∪ {x, y}) = s₀ · term(T₁) · term(T₂)` with `s₀ = δ_dir · s` (`s7f_s₀_eq_chi`).
3. `s7f_exists_ineligible_transport`: sm-4:418-421 — for an INELIGIBLE persistent support the terms on
   `P₂` and `P₀` agree (U110-A/A2/D transport with `x, y` MIXED crossings of the carriers).
Not this unit's (U110-K/G/H/I/J): the eligible persistent rows (skein extraction) and the eligible
one-newborn rows (cb:singleton). -/

section S7FBigonSides

variable {g : WallGerm n} {M a : ZMod n}

/-- The bigon side: `true` iff `P₊` carries the two newborn crossings (read at the base parameter;
constant along the side by `s7f_pattern`).  `P₂ := g.curve (g.sideTime (s7f_side g M a) t)`,
`P₀ := g.curve (g.sideTime (!s7f_side g M a) t)` (sm-4:397-399). -/
noncomputable def s7f_side (g : WallGerm n) (M a : ZMod n) : Bool :=
  decide (IsCrossing (g.sideTuple true g.sideBase).val {a, M})

/-- eq. s7c:bigon-signs: `δ_dir = +1` if `P₋ = P₀` (the newborns are on `P₊`), `−1` if `P₋ = P₂`. -/
def s7f_dirSign (g : WallGerm n) (M a : ZMod n) : ℤ := if s7f_side g M a then 1 else -1

omit [NeZero n] in
theorem s7f_dirSign_sq (g : WallGerm n) (M a : ZMod n) : s7f_dirSign g M a * s7f_dirSign g M a = 1 := by
  unfold s7f_dirSign
  split_ifs <;> norm_num

/-- The bigon crossing pattern of lem:wall-sides (V) (`vertex_sides`, `BigonCrossingPattern`) read
with the side `s7f_side`: `P₂(t)` has both contact crossings and `P₀(t)` neither, at EVERY `t`. -/
theorem s7f_pattern (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    IsCrossing (g.curve (g.sideTime (s7f_side g M a) t)) {a, M - 1} ∧
    IsCrossing (g.curve (g.sideTime (s7f_side g M a) t)) {a, M} ∧
    ¬ IsCrossing (g.curve (g.sideTime (!s7f_side g M a) t)) {a, M - 1} ∧
    ¬ IsCrossing (g.curve (g.sideTime (!s7f_side g M a) t)) {a, M} := by
  have hpat : BigonCrossingPattern (g.curve (g.sideTime true t)) (g.curve (g.sideTime false t)) M a :=
    ((vertex_sides hn g h.1).2.2.2.1 t t).2.1 h.2
  have hbase : BigonCrossingPattern (g.curve (g.sideTime true g.sideBase))
      (g.curve (g.sideTime false t)) M a :=
    ((vertex_sides hn g h.1).2.2.2.1 g.sideBase t).2.1 h.2
  unfold s7f_side
  by_cases hM : IsCrossing (g.sideTuple true g.sideBase).val {a, M}
  · rw [decide_eq_true hM]
    simp only [Bool.not_true]
    rcases hpat with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact ⟨h1, h2, h3, h4⟩
    · exfalso
      rcases hbase with ⟨_, _, _, b4⟩ | ⟨_, b2, _, _⟩
      · exact b4 h4
      · exact b2 hM
  · rw [decide_eq_false hM]
    simp only [Bool.not_false]
    rcases hpat with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exfalso
      rcases hbase with ⟨_, b2, _, _⟩ | ⟨_, _, _, b4⟩
      · exact hM b2
      · exact h4 b4
    · exact ⟨h3, h4, h1, h2⟩

omit [NeZero n] in
/-- Genericity of the newborn side `P₂(t)`. -/
theorem s7f_hP₂ (g : WallGerm n) (M a : ZMod n) (t : g.SideParameter) :
    Generic (g.curve (g.sideTime (s7f_side g M a) t)) := s7a_sideGeneric g _

omit [NeZero n] in
/-- Genericity of the newborn-free side `P₀(t)`. -/
theorem s7f_hP₀ (g : WallGerm n) (M a : ZMod n) (t : g.SideParameter) :
    Generic (g.curve (g.sideTime (!s7f_side g M a) t)) := s7a_sideGeneric g _

/-- The newborn crossing `x = {a, M − 1}` of `P₂(t)`. -/
noncomputable def s7f_x (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    Crossing (g.curve (g.sideTime (s7f_side g M a) t)) :=
  ⟨{a, M - 1}, (s7f_pattern hn h t).1⟩

/-- The newborn crossing `y = {a, M}` of `P₂(t)`. -/
noncomputable def s7f_y (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    Crossing (g.curve (g.sideTime (s7f_side g M a) t)) :=
  ⟨{a, M}, (s7f_pattern hn h t).2.1⟩

theorem s7f_x_val (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    (s7f_x hn h t).val = {a, M - 1} := rfl

theorem s7f_y_val (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    (s7f_y hn h t).val = {a, M} := rfl

theorem s7f_x_ne_y (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    s7f_x hn h t ≠ s7f_y hn h t :=
  fun he => contact_pairs_distinct hn h.1.1 (congrArg Subtype.val he)

theorem s7f_x_affected (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    ContactAffected M a (s7f_x hn h t).val := Or.inl rfl

theorem s7f_y_affected (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    ContactAffected M a (s7f_y hn h t).val := Or.inr rfl

/-- `x` and `y` are the ONLY contact-affected crossings of `P₂(t)`. -/
theorem s7f_eq_x_or_y_of_affected (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter)
    (z : Crossing (g.curve (g.sideTime (s7f_side g M a) t))) (hz : ContactAffected M a z.val) :
    z = s7f_x hn h t ∨ z = s7f_y hn h t := by
  rcases hz with hz | hz
  · exact Or.inl (Subtype.ext hz)
  · exact Or.inr (Subtype.ext hz)

/-- Every crossing of `P₀(t)` is persistent. -/
theorem s7f_P₀_not_affected (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter)
    (z : Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) : ¬ ContactAffected M a z.val := by
  rintro (hz | hz)
  · exact (s7f_pattern hn h t).2.2.1 (hz ▸ z.property)
  · exact (s7f_pattern hn h t).2.2.2 (hz ▸ z.property)

/-- The last clause of `VertexCrossingData` (lem:wall-sides (V)) at a vertex–edge wall: persistent
crossings of either side agree with the centre's (U110-B's `hQC` for the side `b`). -/
theorem s7f_hQC (hn : 3 ≤ n) (h : g.VertexEdgeAt M a) (t : g.SideParameter) (b : Bool) :
    ∀ s, ¬ ContactAffected M a s →
      (IsCrossing (g.curve (g.sideTime b t)) s ↔ IsCrossing g.center s) := by
  intro s hs
  have := ((vertex_sides hn g h).2.2.2.1 t t).2.2.2 s hs
  cases b
  · exact this.2
  · exact this.1

/-- `s₀ = δ_dir · s` is the contact sign read on `P₀` (eq. s7c:bigon-signs with
`vertex_contact_signs`: `χ(P₋) = s`, `χ(P₊) = −s`). -/
theorem s7f_s₀_eq_chi (h : g.BigonAt M a) (t : g.SideParameter) :
    s7f_dirSign g M a * (g.contactSign M a : ℤ) =
      (chi (g.curve (g.sideTime (!s7f_side g M a) t)) a (a + 1) M : ℤ) := by
  obtain ⟨-, hm, hp⟩ := g.vertex_contact_signs h.1 t t
  unfold s7f_dirSign
  cases s7f_side g M a
  · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    have : chi (g.curve (g.sideTime true t)) a (a + 1) M = -g.contactSign M a := hp
    rw [this, SignType.coe_neg]
    ring
  · simp only [Bool.not_true, ↓reduceIte, one_mul]
    have : chi (g.curve (g.sideTime false t)) a (a + 1) M = g.contactSign M a := hm
    rw [this]

end S7FBigonSides

section S7FSectors

variable {g : WallGerm n} {M a : ZMod n}

/-- The interlacing indicator `ε` of the two newborn chords (sm-4:409). -/
def s7f_Interlacing (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) : Prop :=
  Interlaces hn (s7f_hP₂ g M a t) (s7f_x hn h t) (s7f_y hn h t)

/-- The two-newborn sector of `P₂(t)` (undirected: `B = δ_dir · s7f_twoNewbornSum`). -/
noncomputable def s7f_twoNewbornSum (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
      (fun T => s7f_x hn h t ∈ T ∧ s7f_y hn h t ∈ T), s7e_term hn (s7f_hP₂ g M a t) T

/-- The one-newborn sector of `P₂(t)`. -/
noncomputable def s7f_oneNewbornSum (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
      (fun T => (s7f_x hn h t ∈ T ∧ s7f_y hn h t ∉ T) ∨ (s7f_x hn h t ∉ T ∧ s7f_y hn h t ∈ T)),
    s7e_term hn (s7f_hP₂ g M a t) T

/-- The persistent (newborn-free) sector of `P₂(t)`. -/
noncomputable def s7f_persistentSum (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
      (fun T => s7f_x hn h t ∉ T ∧ s7f_y hn h t ∉ T), s7e_term hn (s7f_hP₂ g M a t) T

omit [NeZero n] in
/-- A finite sum split by two predicates into the three sectors "neither", "exactly one", "both"
(instance-free: the sectors are any finsets with the stated memberships). -/
theorem s7f_sum_split3 {ι : Type*} [Fintype ι] (F : ι → ℤ) (p q : ι → Prop) (s₀ s₁ s₂ : Finset ι)
    (h₀ : ∀ S, S ∈ s₀ ↔ ¬ p S ∧ ¬ q S) (h₁ : ∀ S, S ∈ s₁ ↔ (p S ∧ ¬ q S) ∨ (¬ p S ∧ q S))
    (h₂ : ∀ S, S ∈ s₂ ↔ p S ∧ q S) :
    ∑ S, F S = ∑ S ∈ s₀, F S + ∑ S ∈ s₁, F S + ∑ S ∈ s₂, F S := by
  classical
  have hd₀₁ : Disjoint s₀ s₁ := Finset.disjoint_left.mpr fun S hs0 hs1 => by
    have a0 := (h₀ S).mp hs0
    have a1 := (h₁ S).mp hs1
    tauto
  have hd₀₁₂ : Disjoint (s₀ ∪ s₁) s₂ := Finset.disjoint_left.mpr fun S hs hs2 => by
    rw [Finset.mem_union] at hs
    have a2 := (h₂ S).mp hs2
    rcases hs with hs | hs
    · have a0 := (h₀ S).mp hs
      tauto
    · have a1 := (h₁ S).mp hs
      tauto
  have hu : s₀ ∪ s₁ ∪ s₂ = Finset.univ := by
    ext S
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, h₀, h₁, h₂]
    tauto
  rw [← Finset.sum_union hd₀₁, ← Finset.sum_union hd₀₁₂, hu]

/-- lem:C-X1 on `P₂(t)` split into the three newborn sectors. -/
theorem s7f_cornerStateSum_P₂ (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    cornerStateSum hn (s7f_hP₂ g M a t) =
      s7f_persistentSum hn h t + s7f_oneNewbornSum hn h t + s7f_twoNewbornSum hn h t := by
  rw [s7e_cornerStateSum_eq_sum_term]
  unfold s7f_persistentSum s7f_oneNewbornSum s7f_twoNewbornSum
  exact s7f_sum_split3 (s7e_term hn (s7f_hP₂ g M a t)) (fun T => s7f_x hn h t ∈ T)
    (fun T => s7f_y hn h t ∈ T) _ _ _
    (fun S => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun S => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun S => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])

theorem s7f_directed_difference_aux (hn : 3 ≤ n) (g : WallGerm n) (t : g.SideParameter) (b : Bool) :
    cornerStateSum hn (g.sideTuple true t).property - cornerStateSum hn (g.sideTuple false t).property =
      (if b then 1 else -1 : ℤ) *
        (cornerStateSum hn (s7a_sideGeneric g (t := t) b) -
          cornerStateSum hn (s7a_sideGeneric g (t := t) (!b))) := by
  have ep : cornerStateSum hn (g.sideTuple true t).property =
      cornerStateSum hn (s7a_sideGeneric g (t := t) true) := rfl
  have em : cornerStateSum hn (g.sideTuple false t).property =
      cornerStateSum hn (s7a_sideGeneric g (t := t) false) := rfl
  rw [ep, em]
  cases b
  · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    ring
  · simp only [Bool.not_true, ↓reduceIte, one_mul]

/-- The directed difference (sm-4:399-406): `C(P₊) − C(P₋) = δ_dir (C(P₂) − C(P₀))`. -/
theorem s7f_directed_difference (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (t : g.SideParameter) :
    cornerStateSum hn (g.sideTuple true t).property - cornerStateSum hn (g.sideTuple false t).property =
      s7f_dirSign g M a * (cornerStateSum hn (s7f_hP₂ g M a t) - cornerStateSum hn (s7f_hP₀ g M a t)) :=
  s7f_directed_difference_aux hn g t (s7f_side g M a)

/-- **The row decomposition for U110-K** (sm-4:396-448): the directed difference is `δ_dir` times the
persistent-sector difference, the one-newborn sector and the two-newborn sector of `P₂`.  The last is
`B` (eq. s7c:sector-split, `s7f_sector_split`); the first two form `R_ret` (sm-4:448, U110-K). -/
theorem s7f_law_decomposition (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    cornerStateSum hn (g.sideTuple true t).property - cornerStateSum hn (g.sideTuple false t).property =
      s7f_dirSign g M a *
        ((s7f_persistentSum hn h t - cornerStateSum hn (s7f_hP₀ g M a t)) +
          s7f_oneNewbornSum hn h t + s7f_twoNewbornSum hn h t) := by
  rw [s7f_directed_difference hn g M a t, s7f_cornerStateSum_P₂ hn h t]
  ring

/-- **`ε = 1`: the two-newborn sector is empty** (sm-4:445 "When `ε = 1` it is empty"): a support
containing two interlacing crossings is not a decomposition. -/
theorem s7f_twoNewbornSum_eq_zero (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter)
    (hI : s7f_Interlacing hn h t) : s7f_twoNewbornSum hn h t = 0 := by
  apply Finset.sum_eq_zero
  intro T hT
  have hxy := (Finset.mem_filter.mp hT).2
  apply s7e_term_of_not
  intro hdec
  rw [s7b_isDecomposition_iff_indep] at hdec
  exact hdec _ hxy.1 _ hxy.2 (s7f_x_ne_y hn h t) hI

end S7FSectors

section S7FSplit

/-! #### The bigon support split (abstract; U110-B part IV's pattern).  `R` is the interlacement
relation of `P₂`, `R₁, R₂` those of the halves, `ι₁, ι₂` the half crossing maps into `P₂`, `x, y` the
two newborns.  Beyond `s7b_SupportSplit`: the newborns lie outside both images and interlace nothing in
them (the newborn chords are independent of every internal label of `A` and `B`), and an old label
interlacing neither newborn is internal to one interval (`x_split`, `y_split`; the complement is the
common old neighbourhood `N`, sm-4:414-416). -/

variable {γ γ₁ γ₂ : Type*} [DecidableEq γ]

structure s7f_BigonSplit (R : γ → γ → Prop) (R₁ : γ₁ → γ₁ → Prop) (R₂ : γ₂ → γ₂ → Prop)
    (ι₁ : γ₁ → γ) (ι₂ : γ₂ → γ) (x y : γ) : Prop where
  split : s7b_SupportSplit R R₁ R₂ ι₁ ι₂
  x_not₁ : ∀ c, ι₁ c ≠ x
  x_not₂ : ∀ c, ι₂ c ≠ x
  y_not₁ : ∀ c, ι₁ c ≠ y
  y_not₂ : ∀ c, ι₂ c ≠ y
  x_free₁ : ∀ c, ¬ R x (ι₁ c) ∧ ¬ R (ι₁ c) x
  x_free₂ : ∀ c, ¬ R x (ι₂ c) ∧ ¬ R (ι₂ c) x
  y_free₁ : ∀ c, ¬ R y (ι₁ c) ∧ ¬ R (ι₁ c) y
  y_free₂ : ∀ c, ¬ R y (ι₂ c) ∧ ¬ R (ι₂ c) y
  x_split : ∀ z, z ≠ x → z ≠ y → ¬ R x z → ¬ R z x → z ∈ Set.range ι₁ ∪ Set.range ι₂
  y_split : ∀ z, z ≠ x → z ≠ y → ¬ R y z → ¬ R z y → z ∈ Set.range ι₁ ∪ Set.range ι₂

namespace s7f_BigonSplit

variable {R : γ → γ → Prop} {R₁ : γ₁ → γ₁ → Prop} {R₂ : γ₂ → γ₂ → Prop} {ι₁ : γ₁ → γ} {ι₂ : γ₂ → γ}
  {x y : γ}

omit [DecidableEq γ] in
/-- sm-4:418-420: an old support meeting `N` dominates both newborns — no extension by a newborn is
independent (the `x` case). -/
theorem not_indep_of_mem_x (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y) {T : Finset γ}
    (hz : ∃ z ∈ T, z ≠ x ∧ z ≠ y ∧ z ∉ Set.range ι₁ ∪ Set.range ι₂) (hx : x ∈ T) :
    ¬ s7b_Indep R T := by
  intro hT
  obtain ⟨z, hzT, hzx, hzy, hzr⟩ := hz
  exact hzr (h.x_split z hzx hzy (hT x hx z hzT (Ne.symm hzx)) (hT z hzT x hx hzx))

omit [DecidableEq γ] in
/-- The `y` case. -/
theorem not_indep_of_mem_y (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y) {T : Finset γ}
    (hz : ∃ z ∈ T, z ≠ x ∧ z ≠ y ∧ z ∉ Set.range ι₁ ∪ Set.range ι₂) (hy : y ∈ T) :
    ¬ s7b_Indep R T := by
  intro hT
  obtain ⟨z, hzT, hzx, hzy, hzr⟩ := hz
  exact hzr (h.y_split z hzx hzy (hT y hy z hzT (Ne.symm hzy)) (hT z hzT y hy hzy))

theorem indep_insert (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y) (hxy : ¬ R x y ∧ ¬ R y x)
    {S₁ : Finset γ₁} {S₂ : Finset γ₂} (h₁ : s7b_Indep R₁ S₁) (h₂ : s7b_Indep R₂ S₂) :
    s7b_Indep R (insert x (insert y (h.split.joinSupport S₁ S₂))) := by
  intro u hu u' hu' hne hR
  rw [Finset.mem_insert, Finset.mem_insert] at hu hu'
  rcases hu with rfl | rfl | hu
  · rcases hu' with rfl | rfl | hu'
    · exact hne rfl
    · exact hxy.1 hR
    · rcases (h.split.mem_joinSupport _ _ u').mp hu' with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
      · exact (h.x_free₁ c).1 hR
      · exact (h.x_free₂ c).1 hR
  · rcases hu' with rfl | rfl | hu'
    · exact hxy.2 hR
    · exact hne rfl
    · rcases (h.split.mem_joinSupport _ _ u').mp hu' with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
      · exact (h.y_free₁ c).1 hR
      · exact (h.y_free₂ c).1 hR
  · rcases hu' with rfl | rfl | hu'
    · rcases (h.split.mem_joinSupport _ _ u).mp hu with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
      · exact (h.x_free₁ c).2 hR
      · exact (h.x_free₂ c).2 hR
    · rcases (h.split.mem_joinSupport _ _ u).mp hu with ⟨c, -, rfl⟩ | ⟨c, -, rfl⟩
      · exact (h.y_free₁ c).2 hR
      · exact (h.y_free₂ c).2 hR
    · exact h.split.indep_joinSupport h₁ h₂ u hu u' hu' hne hR

theorem pre₁_insert [Fintype γ₁] (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y) (S : Finset γ) :
    s7b_pre ι₁ (insert x (insert y S)) = s7b_pre ι₁ S := by
  ext c
  rw [s7b_mem_pre, s7b_mem_pre, Finset.mem_insert, Finset.mem_insert]
  exact ⟨fun hc => (hc.resolve_left (h.x_not₁ c)).resolve_left (h.y_not₁ c),
    fun hc => Or.inr (Or.inr hc)⟩

theorem pre₂_insert [Fintype γ₂] (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y) (S : Finset γ) :
    s7b_pre ι₂ (insert x (insert y S)) = s7b_pre ι₂ S := by
  ext c
  rw [s7b_mem_pre, s7b_mem_pre, Finset.mem_insert, Finset.mem_insert]
  exact ⟨fun hc => (hc.resolve_left (h.x_not₂ c)).resolve_left (h.y_not₂ c),
    fun hc => Or.inr (Or.inr hc)⟩

theorem insert_join_pre [Fintype γ₁] [Fintype γ₂] (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y)
    {S : Finset γ} (hS : s7b_Indep R S) (hx : x ∈ S) (hy : y ∈ S) :
    insert x (insert y (h.split.joinSupport (s7b_pre ι₁ S) (s7b_pre ι₂ S))) = S := by
  ext z
  rw [Finset.mem_insert, Finset.mem_insert, h.split.mem_joinSupport]
  constructor
  · rintro (rfl | rfl | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact hx
    · exact hy
    · exact (s7b_mem_pre ι₁ S c).mp hc
    · exact (s7b_mem_pre ι₂ S c).mp hc
  · intro hz
    by_cases hzx : z = x
    · exact Or.inl hzx
    by_cases hzy : z = y
    · exact Or.inr (Or.inl hzy)
    right; right
    rcases h.x_split z hzx hzy (hS x hx z hz (Ne.symm hzx)) (hS z hz x hx hzx) with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact Or.inl ⟨c, (s7b_mem_pre ι₁ S c).mpr hz, rfl⟩
    · exact Or.inr ⟨c, (s7b_mem_pre ι₂ S c).mpr hz, rfl⟩

/-- **eq. s7c:eligible-bijection on the two-newborn rows** (`ε = 0`, sm-4:434-435 "`T ∪ {x, y}` is a
support … every two-newborn support arises this way"), abstractly: independent sets of `R` containing
both newborns correspond to pairs of independent sets of `R₁`, `R₂`; the inverse is
`(T₁, T₂) ↦ {x, y} ∪ ι₁ T₁ ∪ ι₂ T₂`. -/
def twoNewbornEquiv [Fintype γ₁] [Fintype γ₂] (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y)
    (hxy : ¬ R x y ∧ ¬ R y x) :
    {S : Finset γ // s7b_Indep R S ∧ x ∈ S ∧ y ∈ S} ≃
      {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂} where
  toFun S := (⟨s7b_pre ι₁ S.1, h.split.indep_pre₁ S.2.1⟩,
    ⟨s7b_pre ι₂ S.1, h.split.indep_pre₂ S.2.1⟩)
  invFun p := ⟨insert x (insert y (h.split.joinSupport p.1.1 p.2.1)), h.indep_insert hxy p.1.2 p.2.2,
    Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
  left_inv S := Subtype.ext (h.insert_join_pre S.2.1 S.2.2.1 S.2.2.2)
  right_inv p := by
    ext1
    · exact Subtype.ext ((h.pre₁_insert _).trans (h.split.pre₁_joinSupport _ _))
    · exact Subtype.ext ((h.pre₂_insert _).trans (h.split.pre₂_joinSupport _ _))

theorem twoNewbornEquiv_symm_apply [Fintype γ₁] [Fintype γ₂] (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y)
    (hxy : ¬ R x y ∧ ¬ R y x)
    (p : {S₁ : Finset γ₁ // s7b_Indep R₁ S₁} × {S₂ : Finset γ₂ // s7b_Indep R₂ S₂}) :
    ((h.twoNewbornEquiv hxy).symm p).1 = insert x (insert y (h.split.joinSupport p.1.1 p.2.1)) := rfl

theorem twoNewbornEquiv_apply [Fintype γ₁] [Fintype γ₂] (h : s7f_BigonSplit R R₁ R₂ ι₁ ι₂ x y)
    (hxy : ¬ R x y ∧ ¬ R y x) (S : {S : Finset γ // s7b_Indep R S ∧ x ∈ S ∧ y ∈ S}) :
    ((h.twoNewbornEquiv hxy S).1.1 = s7b_pre ι₁ S.1) ∧ ((h.twoNewbornEquiv hxy S).2.1 = s7b_pre ι₂ S.1) :=
  ⟨rfl, rfl⟩

end s7f_BigonSplit

end S7FSplit

section S7FDecompositions

/-- **eq. s7c:eligible-bijection on the actual two-newborn decompositions** (`ε = 0`): given the
bigon split of the interlacement relations, `{T' ∈ Ind(G_{P₂}) : x, y ∈ T'} ≃ Ind(G_{λ₁}) × Ind(G_{λ₂})`
(`s7b_slidingDecompositionEquiv`'s pattern). -/
def s7f_twoNewbornDecompositionEquiv (hn : 3 ≤ n) {M a : ZMod n} (hsep : ContactSeparated M a)
    {P Q : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hQ : Generic Q) (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a))
    (x y : Crossing Q)
    (hsplit : s7f_BigonSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) x y)
    (hxy : ¬ Interlaces hn hQ x y ∧ ¬ Interlaces hn hQ y x) :
    {S : Finset (Crossing Q) // IsDecomposition hn hQ S ∧ x ∈ S ∧ y ∈ S} ≃
      {S₁ : Finset (Crossing (firstHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂} where
  toFun S := (⟨s7b_pre _ S.1, (s7b_isDecomposition_iff_indep _ _ _).mpr
      (hsplit.split.indep_pre₁ ((s7b_isDecomposition_iff_indep _ _ _).mp S.2.1))⟩,
    ⟨s7b_pre _ S.1, (s7b_isDecomposition_iff_indep _ _ _).mpr
      (hsplit.split.indep_pre₂ ((s7b_isDecomposition_iff_indep _ _ _).mp S.2.1))⟩)
  invFun p := ⟨insert x (insert y (hsplit.split.joinSupport p.1.1 p.2.1)),
    (s7b_isDecomposition_iff_indep _ _ _).mpr (hsplit.indep_insert hxy
      ((s7b_isDecomposition_iff_indep _ _ _).mp p.1.2) ((s7b_isDecomposition_iff_indep _ _ _).mp p.2.2)),
    Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
  left_inv S := Subtype.ext
    (hsplit.insert_join_pre ((s7b_isDecomposition_iff_indep _ _ _).mp S.2.1) S.2.2.1 S.2.2.2)
  right_inv p := by
    ext1
    · exact Subtype.ext ((hsplit.pre₁_insert _).trans (hsplit.split.pre₁_joinSupport _ _))
    · exact Subtype.ext ((hsplit.pre₂_insert _).trans (hsplit.split.pre₂_joinSupport _ _))

theorem s7f_twoNewbornDecompositionEquiv_symm_apply (hn : 3 ≤ n) {M a : ZMod n}
    (hsep : ContactSeparated M a) {P Q : LabelledTuple n} (hm : P M ∈ edgeInterior P a)
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (hQ : Generic Q) (h₁ : Generic (firstHalf P M a)) (h₂ : Generic (secondHalf P M a))
    (x y : Crossing Q)
    (hsplit : s7f_BigonSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) x y)
    (hxy : ¬ Interlaces hn hQ x y ∧ ¬ Interlaces hn hQ y x)
    (q : {S₁ : Finset (Crossing (firstHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf P M a)) //
          IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂}) :
    ((s7f_twoNewbornDecompositionEquiv hn hsep hm hQC hQ h₁ h₂ x y hsplit hxy).symm q).1 =
      insert x (insert y (hsplit.split.joinSupport q.1.1 q.2.1)) := rfl

end S7FDecompositions

section S7FTriangle

/-- **eq. s7c:triangle-data on a carrier** (sm-4:437-441; the `ε = 0` contact triangle of BLACK BOX 2):
three corners of turn `−s₀` and no carrier crossing give `wt = s₀` (`s7c_carrierWeight_triangle`) and, by
row 105 `corner_values`(i) (`corner_values_of_floor hF`), `|rot| = 1`, `d = 0`, `c = 1`. -/
theorem s7f_triangle_data (hF : FloorTheoremData) (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S) {s₀ : SignType}
    (hs₀ : s₀ ≠ 0) (h3 : ccpCornerCount hn hP S q = 3)
    (hturn : ∀ j, turn (ccpCornerPolygon hn hP S q) j = -s₀)
    (hfree : carrierCrossingCount hn hP S q = 0) :
    carrierWeight hn hP S q = s₀ ∧ |carrierRotation hn hP S q| = 1 ∧ cornerSlot hn hP S q = 0 ∧
      cornerCoefficient hn hP S q hS = 1 := by
  have hw := s7c_carrierWeight_triangle hn hP S q hs₀ h3 hturn
  have hne : carrierWeight hn hP S q ≠ 0 := by
    rw [hw]
    rcases SignType.trichotomy s₀ with rfl | rfl | rfl
    · norm_num
    · exact absurd rfl hs₀
    · norm_num
  have hu : CarrierUniform hn hP S q := s7c_carrierUniform_of_weight_ne_zero hn hP S q hne
  exact ⟨hw, (corner_values_of_floor hF).embedded_value n hn P hP S hS q hu hfree⟩

end S7FTriangle

section S7FSectorSplit

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.BigonAt M a)
  (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))

/-- **BLACK BOX 1 (geometric; U110-B §2.2 in its bigon form, U_S7B_REPORT §2.2/§2.4).**  Below a radius,
the interlacement relation of `P₂(t)` splits along the two half crossing maps with the newborns as in
`s7f_BigonSplit`: `rel₁ rel₂` (the halves' interlacement is the restriction of `P₂`'s), `cross cross'`
(no interlacement between the two images), the newborns' freedom from both images, and the dichotomy
`x_split`/`y_split` (sm-4:414-416; the converse of `s7b_isCrossing_firstHalf_image`).  The fields
`inj₁ inj₂ disjoint x_not y_not` are already proved in U110-B (`s7b_firstCrossingQ_injective`,
`s7b_firstCrossingQ_ne_secondCrossingQ`, `s7b_firstCrossingQ_not_affected` with `s7f_x_affected`);
`s7f_bigonSplit_of` below assembles them. -/
theorem s7f_exists_bigonSplit :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t) := by
  sorry

/-! ### Unit FB2 (wave 4, prefix `s7fb_`; serving F's BLACK BOX 2 `s7f_exists_twoNewbornTerm`,
OPEN_ITEMS_20260916 §A-08): the `ε = 0` two-newborn term identity
`term(T ∪ {x, y}) = s₀ · term(T₁) · term(T₂)` on the newborn side `P₂`.

Part A — the geometry of the newborn side polygon `Q` (generic, relative to the centre `Pc`
with contact parameter `r` and window half-width `η`): the four newborn visits `x_a, x_ℓ`
(of `x = {a, M−1}`) and `y_a, y_ℓ` (of `y = {a, M}`), their windows, the three successor facts
`nextMark x_ℓ = μ_M`, `nextMark μ_M = y_ℓ`, `nextMark y_a = x_a` (the last under `y_a < x_a` on
`E_a`), and the dichotomy: the newborns do not interlace iff `y_a` precedes `x_a` on `E_a`.
Together these make the contact triangle `x_a → μ_M → y_ℓ → x_a` of sm-4:437-441. -/

section S7FBSide

variable {Pc Q : LabelledTuple n} (hQ : Generic Q) (hsep : ContactSeparated M a)
  {r η : ℝ} (hη : 0 < η)
  (hw : ContactParameterWindows Pc Q M a r η)
  (hcx : IsCrossing Q {a, contactLeg false M}) (hcy : IsCrossing Q {a, contactLeg true M})

omit [NeZero n] in
theorem s7fb_leg_false : contactLeg false M = M - 1 := by simp [contactLeg]

omit [NeZero n] in
theorem s7fb_leg_true : contactLeg true M = M := by simp [contactLeg]

include hcx hcy

omit [NeZero n] hcy in
theorem s7fb_xl_edge : (s7e_vl hcx).2.val = M - 1 := by rw [s7e_vl_edge, s7fb_leg_false]

omit [NeZero n] hcx in
theorem s7fb_yl_edge : (s7e_vl hcy).2.val = M := by rw [s7e_vl_edge, s7fb_leg_true]

omit hcy in
theorem s7fb_xa_affected : ContactAffected M a (s7e_va hcx).1.val :=
  (contactAffected_iff_leg _).mpr ⟨false, rfl⟩

omit hcy in
theorem s7fb_xl_affected : ContactAffected M a (s7e_vl hcx).1.val := by
  rw [s7e_vl_fst]; exact s7fb_xa_affected hcx

omit hcx in
theorem s7fb_ya_affected : ContactAffected M a (s7e_va hcy).1.val :=
  (contactAffected_iff_leg _).mpr ⟨true, rfl⟩

omit hcx in
theorem s7fb_yl_affected : ContactAffected M a (s7e_vl hcy).1.val := by
  rw [s7e_vl_fst]; exact s7fb_ya_affected hcy

include hn hsep in
/-- The two newborn crossings are distinct. -/
theorem s7fb_x_ne_y : (s7e_va hcx).1 ≠ (s7e_va hcy).1 := by
  intro he
  have hv := congrArg Subtype.val he
  rw [s7e_va_fst_val, s7e_va_fst_val, s7fb_leg_false, s7fb_leg_true] at hv
  exact contact_pairs_distinct hn hsep hv

include hn hsep in
theorem s7fb_xa_ne_ya : s7e_va hcx ≠ s7e_va hcy :=
  fun he => s7fb_x_ne_y hn hsep hcx hcy (congrArg Sigma.fst he)

include hsep in
omit [NeZero n] in
/-- Every visit of the newborn side is one of the four newborn visits or persistent. -/
theorem s7fb_visit_cases (v : Visit Q) :
    v = s7e_va hcx ∨ v = s7e_vl hcx ∨ v = s7e_va hcy ∨ v = s7e_vl hcy ∨
      ¬ ContactAffected M a v.1.val := by
  by_cases hv : ContactAffected M a v.1.val
  · rcases hv with hv | hv
    · rcases s7e_visit_of_fst hcx v (by rw [hv, s7fb_leg_false]) (s7e_a_ne_leg false hsep) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases s7e_visit_of_fst hcy v (by rw [hv, s7fb_leg_true]) (s7e_a_ne_leg true hsep) with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hv)))

include hsep in
omit [NeZero n] in
/-- A visit on edge `a` other than the two newborn `a`-visits is persistent. -/
theorem s7fb_persistent_of_edge_a (v : Visit Q) (he : v.2.val = a) (hx : v ≠ s7e_va hcx)
    (hy : v ≠ s7e_va hcy) : ¬ ContactAffected M a v.1.val := by
  rcases s7fb_visit_cases hsep hcx hcy v with h | h | h | h | h
  · exact absurd h hx
  · exfalso; rw [h, s7fb_xl_edge] at he; exact s7e_a_ne_M_sub_one hsep he.symm
  · exact absurd h hy
  · exfalso; rw [h, s7fb_yl_edge] at he; exact s7e_a_ne_M hsep he.symm
  · exact h

omit [NeZero n] in
include hn hsep in
/-- A visit on edge `M − 1` other than `x_ℓ` is persistent. -/
theorem s7fb_persistent_of_edge_pred (v : Visit Q) (he : v.2.val = M - 1) (hx : v ≠ s7e_vl hcx) :
    ¬ ContactAffected M a v.1.val := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  rcases s7fb_visit_cases hsep hcx hcy v with h | h | h | h | h
  · exfalso; rw [h, s7e_va_edge] at he; exact s7e_a_ne_M_sub_one hsep he
  · exact absurd h hx
  · exfalso; rw [h, s7e_va_edge] at he; exact s7e_a_ne_M_sub_one hsep he
  · exfalso; rw [h, s7fb_yl_edge] at he; exact prev_ne_self M he.symm
  · exact h

omit [NeZero n] in
include hn hsep in
/-- A visit on edge `M` other than `y_ℓ` is persistent. -/
theorem s7fb_persistent_of_edge_M (v : Visit Q) (he : v.2.val = M) (hy : v ≠ s7e_vl hcy) :
    ¬ ContactAffected M a v.1.val := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  rcases s7fb_visit_cases hsep hcx hcy v with h | h | h | h | h
  · exfalso; rw [h, s7e_va_edge] at he; exact s7e_a_ne_M hsep he
  · exfalso; rw [h, s7fb_xl_edge] at he; exact prev_ne_self M he
  · exfalso; rw [h, s7e_va_edge] at he; exact s7e_a_ne_M hsep he
  · exact absurd h hy
  · exact h

/-! #### The windows of the four newborn visits -/

omit [NeZero n] in
include hn hQ hw in
omit hcy in
theorem s7fb_xa_near : |visitParameter (s7e_va hcx) - r| < η := s7e_va_param_near hn hQ false hw hcx

omit [NeZero n] in
include hn hQ hw in
omit hcx in
theorem s7fb_ya_near : |visitParameter (s7e_va hcy) - r| < η := s7e_va_param_near hn hQ true hw hcy

omit [NeZero n] in
include hn hQ hw in
omit hcy in
theorem s7fb_xl_param : 1 - η < visitParameter (s7e_vl hcx) := s7e_vl_param_false hn hQ hw hcx

omit [NeZero n] in
include hn hQ hw in
omit hcx in
theorem s7fb_yl_param : visitParameter (s7e_vl hcy) < η := s7e_vl_param_true hn hQ hw hcy

include hn hQ hw in
omit hcx hcy in
/-- A persistent visit on edge `a` lies below `r − 3η` or above `r + 3η`. -/
theorem s7fb_persist_a_cases (u : Visit Q) (hu : ¬ ContactAffected M a u.1.val) (he : u.2.val = a) :
    visitParameter u < r - 3 * η ∨ r + 3 * η < visitParameter u := by
  have h := s7e_persist_a hn hQ hw u hu he
  rcases lt_or_ge (visitParameter u) r with hlt | hge
  · left; rw [abs_of_neg (by linarith)] at h; linarith
  · right; rw [abs_of_nonneg (by linarith)] at h; linarith

/-! #### The three successor facts of the contact triangle -/

include hn hQ hsep hη hw in
/-- `nextMark x_ℓ = μ_M`: the leg visit of `x` is the last mark on edge `M − 1`. -/
theorem s7fb_nextMark_xl : nextMark hn hQ (Sum.inr (s7e_vl hcx)) = Sum.inl M := by
  have hnext : nextMark hn hQ (Sum.inr (s7e_vl hcx)) = Sum.inl ((s7e_vl hcx).2.val + 1) := by
    apply s7e_nextMark_inr_eq_inl hn hQ
    intro u hu
    by_cases hul : u = s7e_vl hcx
    · rw [hul]
    · have hup := s7fb_persistent_of_edge_pred hn hsep hcx hcy u (hu.trans (s7fb_xl_edge hcx)) hul
      have h1 := s7e_persist_M_sub_one hn hQ hw u hup (hu.trans (s7fb_xl_edge hcx))
      have h2 := s7fb_xl_param hn hQ hw hcx
      linarith
  rw [hnext, s7fb_xl_edge, sub_add_cancel]

include hn hQ hsep hη hw in
/-- `nextMark μ_M = y_ℓ`: the leg visit of `y` is the first mark on edge `M`. -/
theorem s7fb_nextMark_M : nextMark hn hQ (Sum.inl M) = Sum.inr (s7e_vl hcy) := by
  apply s7e_nextMark_inl_eq_inr hn hQ M (s7e_vl hcy) (s7fb_yl_edge hcy)
  intro u hu
  by_cases hul : u = s7e_vl hcy
  · rw [hul]
  · have hup := s7fb_persistent_of_edge_M hn hsep hcx hcy u hu hul
    have h1 := s7e_persist_M hn hQ hw u hup hu
    have h2 := s7fb_yl_param hn hQ hw hcy
    linarith

include hn hQ hsep hw in
/-- `nextMark y_a = x_a` when `y_a` precedes `x_a` on `E_a`: no other visit lies between them. -/
theorem s7fb_nextMark_ya (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx)) :
    nextMark hn hQ (Sum.inr (s7e_va hcy)) = Sum.inr (s7e_va hcx) := by
  apply s7e_nextMark_inr_eq_inr hn hQ (s7e_va hcy) (s7e_va hcx) rfl hlt
  intro u hu hlu
  by_cases hux : u = s7e_va hcx
  · rw [hux]
  by_cases huy : u = s7e_va hcy
  · rw [huy] at hlu; exact absurd hlu (lt_irrefl _)
  have hup := s7fb_persistent_of_edge_a hsep hcx hcy u hu hux huy
  have hya := (abs_lt.mp (s7fb_ya_near hn hQ hw hcy)).1
  have hxa := (abs_lt.mp (s7fb_xa_near hn hQ hw hcx)).2
  rcases s7fb_persist_a_cases hn hQ hw u hup hu with h | h
  · exfalso; linarith
  · linarith

/-! #### The interlacing dichotomy: `¬ Interlaces x y ⟹ y_a < x_a` -/

include hn hQ in
/-- The two newborn `a`-visits have distinct parameters. -/
theorem s7fb_xa_param_ne_ya (hsep : ContactSeparated M a) :
    visitParameter (s7e_va hcx) ≠ visitParameter (s7e_va hcy) := fun he =>
  s7fb_xa_ne_ya hn hsep hcx hcy (s7e_visit_eq_of_param hn hQ _ _ rfl he)

omit [NeZero n] hcx hcy in
/-- The `a`-slot and the leg slot of the newborn `x`. -/
theorem s7fb_slot_a (hc : IsCrossing Q {a, contactLeg false M}) :
    a ∈ (⟨{a, contactLeg false M}, hc⟩ : Crossing Q).val := by simp

omit [NeZero n] hcx hcy in
theorem s7fb_slot_leg (hc : IsCrossing Q {a, contactLeg false M}) :
    contactLeg false M ∈ (⟨{a, contactLeg false M}, hc⟩ : Crossing Q).val := by simp

omit [NeZero n] hcx hcy in
theorem s7fb_slot_a' (hc : IsCrossing Q {a, contactLeg true M}) :
    a ∈ (⟨{a, contactLeg true M}, hc⟩ : Crossing Q).val := by simp

omit [NeZero n] hcx hcy in
theorem s7fb_slot_leg' (hc : IsCrossing Q {a, contactLeg true M}) :
    contactLeg true M ∈ (⟨{a, contactLeg true M}, hc⟩ : Crossing Q).val := by simp

omit [NeZero n] in
include hsep in
omit hcy in
/-- The visit of `x` at its leg slot is `x_ℓ`. -/
theorem s7fb_visit_leg_eq_xl :
    (⟨⟨{a, contactLeg false M}, hcx⟩, ⟨contactLeg false M, s7fb_slot_leg hcx⟩⟩ : Visit Q) = s7e_vl hcx :=
  s7e_visit_eq_vl hcx _ rfl rfl (s7e_a_ne_leg false hsep)

omit [NeZero n] in
include hsep in
omit hcx in
theorem s7fb_visit_leg_eq_yl :
    (⟨⟨{a, contactLeg true M}, hcy⟩, ⟨contactLeg true M, s7fb_slot_leg' hcy⟩⟩ : Visit Q) = s7e_vl hcy :=
  s7e_visit_eq_vl hcy _ rfl rfl (s7e_a_ne_leg true hsep)

include hn hQ hsep in
/-- **The dichotomy.**  If `x_a` precedes `y_a` on `E_a` the four newborn visits alternate
(`x_a, y_a, x_ℓ, y_ℓ`) and the newborns interlace; so non-interlacing newborns have `y_a < x_a`. -/
theorem s7fb_ya_lt_xa_of_not_interlaces
    (hI : ¬ Interlaces hn hQ ⟨{a, contactLeg false M}, hcx⟩ ⟨{a, contactLeg true M}, hcy⟩) :
    visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx) := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  by_contra hge
  have hlt : visitParameter (s7e_va hcx) < visitParameter (s7e_va hcy) :=
    lt_of_le_of_ne (not_lt.mp hge) (s7fb_xa_param_ne_ya hn hQ hcx hcy hsep)
  apply hI
  refine ⟨fun he => s7fb_x_ne_y hn hsep hcx hcy he, ⟨a, s7fb_slot_a hcx⟩,
    ⟨contactLeg false M, s7fb_slot_leg hcx⟩, ⟨a, s7fb_slot_a' hcy⟩, ⟨contactLeg true M, s7fb_slot_leg' hcy⟩,
    fun he => s7e_a_ne_leg false hsep (congrArg Subtype.val he),
    fun he => s7e_a_ne_leg true hsep (congrArg Subtype.val he), ?_, ?_⟩
  · -- `y_a` lies between `x_a` and `x_ℓ`
    show traversalBetween (markPosition hn hQ.1 (Sum.inr (s7e_va hcx)))
      (markPosition hn hQ.1 (Sum.inr (s7e_va hcy)))
      (markPosition hn hQ.1 (Sum.inr (⟨⟨{a, contactLeg false M}, hcx⟩,
        ⟨contactLeg false M, s7fb_slot_leg hcx⟩⟩ : Visit Q)))
    rw [s7fb_visit_leg_eq_xl hsep hcx, s7e_between_iff hn hQ, s7e_markKey_eq hn hQ, s7e_markKey_eq hn hQ,
      s7e_markKey_eq hn hQ]
    simp only [s7e_mEdge_inr, s7e_mParam_inr, s7e_va_edge, s7fb_xl_edge]
    have hpl1 := s7e_visitParameter_lt_one hn hQ (s7e_vl hcx)
    have hpl0 := s7e_visitParameter_pos hn hQ (s7e_vl hcx)
    have hpx1 := s7e_visitParameter_lt_one hn hQ (s7e_va hcx)
    have hpx0 := s7e_visitParameter_pos hn hQ (s7e_va hcx)
    have hpy0 := s7e_visitParameter_pos hn hQ (s7e_va hcy)
    have hpy1 := s7e_visitParameter_lt_one hn hQ (s7e_va hcy)
    have hne : a.val ≠ (M - 1).val := fun he => s7e_a_ne_M_sub_one hsep (ZMod.val_injective n he)
    rcases Nat.lt_or_gt_of_ne hne with hal | hal
    · left
      have : (a.val : ℝ) + 1 ≤ (M - 1).val := by exact_mod_cast hal
      constructor <;> linarith
    · right; right
      have : ((M - 1).val : ℝ) + 1 ≤ a.val := by exact_mod_cast hal
      constructor <;> linarith
  · -- `y_ℓ` lies between `x_ℓ` and `x_a`
    show traversalBetween (markPosition hn hQ.1 (Sum.inr (⟨⟨{a, contactLeg false M}, hcx⟩,
        ⟨contactLeg false M, s7fb_slot_leg hcx⟩⟩ : Visit Q)))
      (markPosition hn hQ.1 (Sum.inr (⟨⟨{a, contactLeg true M}, hcy⟩,
        ⟨contactLeg true M, s7fb_slot_leg' hcy⟩⟩ : Visit Q)))
      (markPosition hn hQ.1 (Sum.inr (s7e_va hcx)))
    rw [s7fb_visit_leg_eq_xl hsep hcx, s7fb_visit_leg_eq_yl hsep hcy, s7e_between_iff hn hQ,
      s7e_markKey_eq hn hQ, s7e_markKey_eq hn hQ, s7e_markKey_eq hn hQ]
    simp only [s7e_mEdge_inr, s7e_mParam_inr, s7e_va_edge, s7fb_xl_edge, s7fb_yl_edge]
    have hpl1 := s7e_visitParameter_lt_one hn hQ (s7e_vl hcx)
    have hpl0 := s7e_visitParameter_pos hn hQ (s7e_vl hcx)
    have hpM1 := s7e_visitParameter_lt_one hn hQ (s7e_vl hcy)
    have hpM0 := s7e_visitParameter_pos hn hQ (s7e_vl hcy)
    have hpx1 := s7e_visitParameter_lt_one hn hQ (s7e_va hcx)
    have hpx0 := s7e_visitParameter_pos hn hQ (s7e_va hcx)
    have hneM : a.val ≠ M.val := fun he => s7e_a_ne_M hsep (ZMod.val_injective n he)
    have hnel : a.val ≠ (M - 1).val := fun he => s7e_a_ne_M_sub_one hsep (ZMod.val_injective n he)
    rcases s7e_val_succ (M - 1) with ⟨-, hval⟩ | ⟨hM1, -, hval⟩
    · -- `M ≠ 0`: `M.val = (M − 1).val + 1`
      rw [sub_add_cancel] at hval
      rcases Nat.lt_or_gt_of_ne hneM with haM | haM
      · -- `a.val < M.val`, hence `a.val < (M − 1).val`
        have hal : a.val < (M - 1).val := by
          have h1 : (a.val : ℝ) + 1 ≤ M.val := by exact_mod_cast haM
          have h2 : a.val ≤ (M - 1).val := by
            by_contra hc
            have : ((M - 1).val : ℝ) + 1 ≤ a.val := by exact_mod_cast not_le.mp hc
            linarith
          exact lt_of_le_of_ne h2 hnel
        right; right
        have : (a.val : ℝ) + 1 ≤ (M - 1).val := by exact_mod_cast hal
        constructor <;> linarith
      · left
        have : (M.val : ℝ) + 1 ≤ a.val := by exact_mod_cast haM
        constructor <;> linarith
    · -- `M = 0`: `(M − 1).val = n − 1`, `M.val = 0`, and `1 ≤ a.val ≤ n − 2`
      have hM0 : M = 0 := by linear_combination hM1
      have hMv : (M.val : ℝ) = 0 := by rw [hM0, ZMod.val_zero, Nat.cast_zero]
      have ha1 : (1 : ℝ) ≤ a.val := by
        have : a.val ≠ 0 := fun h0 => s7e_a_ne_M hsep (by rw [hM0]; exact (ZMod.val_eq_zero a).mp h0)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
      have ha2 : (a.val : ℝ) + 1 ≤ n - 1 := by
        have hlt' : a.val < n := ZMod.val_lt a
        have hne' : a.val ≠ n - 1 := by
          intro he
          apply s7e_a_ne_M_sub_one hsep
          rw [hM0, zero_sub]
          apply ZMod.val_injective n
          rw [he]
          have := last_index_val_succ (n := n)
          omega
        have : a.val + 1 ≤ n - 1 := by omega
        have h3 : ((a.val + 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast this
        rw [Nat.cast_sub (by omega : 1 ≤ n)] at h3
        push_cast at h3
        linarith
      right; left
      constructor <;> linarith

end S7FBSide

/-! Part B — the bigon mark map and the first-return law (U_S7B_REPORT §2.4 "the bigon mark map …
Not started"; the `ε = 0` case `T ∪ {x, y}` on `P₂`).  The marks of `λ₁ ⊔ λ₂` sit inside the marks
of `Q` by `s7fb_mark`: `λ₁`'s vertex `0 = μ_M` is the `a`-visit `y_a` of `y` (the closed first half
is `[E_M], μ_{M+1}, …, μ_a, [E_a < r], y_a`), `λ₂`'s vertex `0 = P M` is the leg visit `x_ℓ` of `x`
(the closed second half is `[E_a > r], μ_{a+1}, …, μ_{M−1}, x_ℓ`), all other vertices and the carried
visits as in `s7b_slidingMark`; a third summand `Unit` is sent to `μ_M`, the vertex of the contact
triangle `μ_M → y_ℓ → x_a → μ_M` (Part A).  The first-return law is proved with RET's engine
(`s7r_reach_of_transit`, `s7r_step_of_reach`, `s7r_hit_of_transit`) exactly as `s7r_slidingTransport_of_leg_false`,
with the chains of `λ₁`'s vertex `0` starting at `y_ℓ` and of `λ₂`'s vertex `0` at `x_a`. -/

section S7FBMap

variable {Pc Q : LabelledTuple n} (hQ : Generic Q) (hsep : ContactSeparated M a)
  (hz : pointZeroTriples Pc = {contactSupport M a}) (hm : Pc M ∈ edgeInterior Pc a) {r η : ℝ}
  (hr : Pc M = edgePoint Pc a r) (hr0 : 0 < r) (hr1 : r < 1) (hη : 0 < η)
  (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing Pc s))
  (hw : ContactParameterWindows Pc Q M a r η)
  (hord : ∀ (u u' : Visit Pc) (hu : ¬ ContactAffected M a u.1.val) (hu' : ¬ ContactAffected M a u'.1.val),
    u.2.val = u'.2.val →
    (visitParameter (s7a_visit hQC u hu) < visitParameter (s7a_visit hQC u' hu') ↔
      visitParameter u < visitParameter u'))
  (hside : ∀ (u : Visit Pc) (hu : ¬ ContactAffected M a u.1.val), u.2.val = a →
    (visitParameter (s7a_visit hQC u hu) < r ↔ visitParameter u < r))
  (hg₁ : Generic (firstHalf Pc M a)) (hg₂ : Generic (secondHalf Pc M a))
  (hcx : IsCrossing Q {a, contactLeg false M}) (hcy : IsCrossing Q {a, contactLeg true M})

/-- **The bigon mark map** `(Mark λ₁ ⊕ Mark λ₂) ⊕ Unit → Mark Q` (`ε = 0`): `λ₁`'s vertex `0 ↦ y_a`,
`λ₂`'s vertex `0 ↦ x_ℓ`, the other vertices and the carried visits as `s7b_slidingMark`, the `Unit`
to the contact vertex `μ_M`. -/
def s7fb_mark : (Mark (firstHalf Pc M a) ⊕ Mark (secondHalf Pc M a)) ⊕ Unit → Mark Q
  | Sum.inl (Sum.inl (Sum.inl i)) =>
      if i = 0 then Sum.inr (s7e_va hcy) else Sum.inl (firstHalfIndex M a i)
  | Sum.inl (Sum.inl (Sum.inr v)) => Sum.inr (s7b_firstVisitQ hn hsep hm hQC v)
  | Sum.inl (Sum.inr (Sum.inl j)) =>
      if j = 0 then Sum.inr (s7e_vl hcx) else Sum.inl (secondHalfIndex M a j)
  | Sum.inl (Sum.inr (Sum.inr v)) => Sum.inr (s7b_secondVisitQ hn hsep hm hQC v)
  | Sum.inr _ => Sum.inl M

theorem s7fb_mark_inl_inl_zero :
    s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl (Sum.inl 0))) = Sum.inr (s7e_va hcy) := by
  simp [s7fb_mark]

theorem s7fb_mark_inl_inl {i : ZMod (firstHalfSize M a)} (hi : i ≠ 0) :
    s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl (Sum.inl i))) = Sum.inl (firstHalfIndex M a i) := by
  simp [s7fb_mark, hi]

theorem s7fb_mark_inl_inr (v : Visit (firstHalf Pc M a)) :
    s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl (Sum.inr v))) =
      Sum.inr (s7b_firstVisitQ hn hsep hm hQC v) := rfl

theorem s7fb_mark_inr_inl_zero :
    s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr (Sum.inl 0))) = Sum.inr (s7e_vl hcx) := by
  simp [s7fb_mark]

theorem s7fb_mark_inr_inl {j : ZMod (secondHalfSize M a)} (hj : j ≠ 0) :
    s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr (Sum.inl j))) = Sum.inl (secondHalfIndex M a j) := by
  simp [s7fb_mark, hj]

theorem s7fb_mark_inr_inr (v : Visit (secondHalf Pc M a)) :
    s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr (Sum.inr v))) =
      Sum.inr (s7b_secondVisitQ hn hsep hm hQC v) := rfl

theorem s7fb_mark_unit (u : Unit) : s7fb_mark hn hsep hm hQC hcx hcy (Sum.inr u) = Sum.inl M := rfl

/-- On `Mark λ₁ ⊕ Mark λ₂` the bigon map is `swap (μ_M, y_a) ∘ s7b_slidingMark … x_ℓ`. -/
theorem s7fb_mark_inl_eq (b : Mark (firstHalf Pc M a) ⊕ Mark (secondHalf Pc M a)) :
    s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl b) =
      Equiv.swap (Sum.inl M : Mark Q) (Sum.inr (s7e_va hcy)) (s7b_slidingMark hn hsep hm hQC (s7e_vl hcx) b) := by
  have hya : ∀ v : Visit (firstHalf Pc M a), s7b_firstVisitQ hn hsep hm hQC v ≠ s7e_va hcy := by
    intro v h
    exact s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_firstVisitQ_fst hn hsep hm hQC v, h]; exact s7fb_ya_affected hcy)
  have hya' : ∀ v : Visit (secondHalf Pc M a), s7b_secondVisitQ hn hsep hm hQC v ≠ s7e_va hcy := by
    intro v h
    exact s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_secondVisitQ_fst hn hsep hm hQC v, h]; exact s7fb_ya_affected hcy)
  rcases b with (i | v) | (j | v)
  · by_cases hi : i = 0
    · subst hi
      rw [s7fb_mark_inl_inl_zero, s7b_slidingMark_inl_inl, firstHalfIndex_zero, Equiv.swap_apply_left]
    · rw [s7fb_mark_inl_inl hn hsep hm hQC hcx hcy hi, s7b_slidingMark_inl_inl]
      rw [Equiv.swap_apply_of_ne_of_ne]
      · intro h; exact hi (firstHalfIndex_injective M a ((Sum.inl.inj h).trans (firstHalfIndex_zero M a).symm))
      · exact Sum.inl_ne_inr
  · rw [s7fb_mark_inl_inr, s7b_slidingMark_inl_inr, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl]
    exact fun h => hya v (Sum.inr.inj h)
  · by_cases hj : j = 0
    · subst hj
      rw [s7fb_mark_inr_inl_zero, s7b_slidingMark_inr_inl_zero, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl]
      intro h
      have h' := Sum.inr.inj h
      have := congrArg (fun v : Visit Q => v.2.val) h'
      rw [s7fb_xl_edge, s7e_va_edge] at this
      exact s7e_a_ne_M_sub_one hsep this.symm
    · rw [s7fb_mark_inr_inl hn hsep hm hQC hcx hcy hj, s7b_slidingMark_inr_inl hn hsep hm hQC _ hj,
        Equiv.swap_apply_of_ne_of_ne]
      · intro h
        rw [secondHalfIndex_nonzero M a hj] at h
        exact s7b_secondHalfEdgeIndex_ne hn hsep j (Sum.inl.inj h)
      · exact Sum.inl_ne_inr
  · rw [s7fb_mark_inr_inr, s7b_slidingMark_inr_inr, Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl]
    exact fun h => hya' v (Sum.inr.inj h)

/-- The bigon map never sends a half mark to `μ_M`. -/
theorem s7fb_mark_inl_ne_M (b : Mark (firstHalf Pc M a) ⊕ Mark (secondHalf Pc M a)) :
    s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl b) ≠ Sum.inl M := by
  rw [s7fb_mark_inl_eq]
  intro h
  have h' : s7b_slidingMark hn hsep hm hQC (s7e_vl hcx) b = Sum.inr (s7e_va hcy) := by
    have := congrArg (Equiv.swap (Sum.inl M : Mark Q) (Sum.inr (s7e_va hcy))) h
    rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
  rcases b with (i | v) | (j | v)
  · rw [s7b_slidingMark_inl_inl] at h'; exact Sum.inl_ne_inr h'
  · rw [s7b_slidingMark_inl_inr] at h'
    exact s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_firstVisitQ_fst hn hsep hm hQC v, Sum.inr.inj h']; exact s7fb_ya_affected hcy)
  · by_cases hj : j = 0
    · subst hj
      rw [s7b_slidingMark_inr_inl_zero] at h'
      have := congrArg (fun v : Visit Q => v.2.val) (Sum.inr.inj h')
      rw [s7fb_xl_edge, s7e_va_edge] at this
      exact s7e_a_ne_M_sub_one hsep this.symm
    · rw [s7b_slidingMark_inr_inl hn hsep hm hQC _ hj] at h'; exact Sum.inl_ne_inr h'
  · rw [s7b_slidingMark_inr_inr] at h'
    exact s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_secondVisitQ_fst hn hsep hm hQC v, Sum.inr.inj h']; exact s7fb_ya_affected hcy)

theorem s7fb_mark_injective : Function.Injective (s7fb_mark hn hsep hm hQC hcx hcy) := by
  rintro (b | u) (b' | u') h
  · rw [s7fb_mark_inl_eq, s7fb_mark_inl_eq] at h
    exact congrArg Sum.inl
      (s7b_slidingMark_injective hn hsep hm hQC (s7e_vl hcx) (s7fb_xl_affected hcx) (Equiv.injective _ h))
  · exact absurd h (s7fb_mark_inl_ne_M hn hsep hm hQC hcx hcy b)
  · exact absurd h.symm (s7fb_mark_inl_ne_M hn hsep hm hQC hcx hcy b')
  · rfl

/-- Which visits of `Q` are image marks of the bigon map. -/
theorem s7fb_inr_mem_range_iff (w : Visit Q) :
    (Sum.inr w : Mark Q) ∈ Set.range (s7fb_mark hn hsep hm hQC hcx hcy) ↔
      w = s7e_va hcy ∨ w = s7e_vl hcx ∨ (∃ v, s7b_firstVisitQ hn hsep hm hQC v = w) ∨
        (∃ v, s7b_secondVisitQ hn hsep hm hQC v = w) := by
  constructor
  · rintro ⟨b, hb⟩
    rcases b with ((i | v) | (j | v)) | u
    · by_cases hi : i = 0
      · subst hi; rw [s7fb_mark_inl_inl_zero] at hb; exact Or.inl (Sum.inr_injective hb).symm
      · rw [s7fb_mark_inl_inl hn hsep hm hQC hcx hcy hi] at hb; exact absurd hb Sum.inl_ne_inr
    · rw [s7fb_mark_inl_inr] at hb; exact Or.inr (Or.inr (Or.inl ⟨v, Sum.inr_injective hb⟩))
    · by_cases hj : j = 0
      · subst hj; rw [s7fb_mark_inr_inl_zero] at hb; exact Or.inr (Or.inl (Sum.inr_injective hb).symm)
      · rw [s7fb_mark_inr_inl hn hsep hm hQC hcx hcy hj] at hb; exact absurd hb Sum.inl_ne_inr
    · rw [s7fb_mark_inr_inr] at hb; exact Or.inr (Or.inr (Or.inr ⟨v, Sum.inr_injective hb⟩))
    · rw [s7fb_mark_unit] at hb; exact absurd hb Sum.inl_ne_inr
  · rintro (rfl | rfl | ⟨v, rfl⟩ | ⟨v, rfl⟩)
    · exact ⟨Sum.inl (Sum.inl (Sum.inl 0)), s7fb_mark_inl_inl_zero hn hsep hm hQC hcx hcy⟩
    · exact ⟨Sum.inl (Sum.inr (Sum.inl 0)), s7fb_mark_inr_inl_zero hn hsep hm hQC hcx hcy⟩
    · exact ⟨Sum.inl (Sum.inl (Sum.inr v)), rfl⟩
    · exact ⟨Sum.inl (Sum.inr (Sum.inr v)), rfl⟩

theorem s7fb_M_mem_range : (Sum.inl M : Mark Q) ∈ Set.range (s7fb_mark hn hsep hm hQC hcx hcy) :=
  ⟨Sum.inr (), rfl⟩

/-- The `a`-visit `x_a` of `x` is not an image mark (it is the smoothing corner of the triangle). -/
theorem s7fb_xa_not_mem_range :
    (Sum.inr (s7e_va hcx) : Mark Q) ∉ Set.range (s7fb_mark hn hsep hm hQC hcx hcy) := by
  rw [s7fb_inr_mem_range_iff]
  rintro (h | h | ⟨v, hv⟩ | ⟨v, hv⟩)
  · exact s7fb_xa_ne_ya hn hsep hcx hcy h
  · exact s7e_vl_ne_va hcx (s7e_a_ne_leg false hsep) h.symm
  · exact s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_firstVisitQ_fst hn hsep hm hQC v, hv]; exact s7fb_xa_affected hcx)
  · exact s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_secondVisitQ_fst hn hsep hm hQC v, hv]; exact s7fb_xa_affected hcx)

/-- The leg visit `y_ℓ` of `y` is not an image mark (the other smoothing corner of the triangle). -/
theorem s7fb_yl_not_mem_range :
    (Sum.inr (s7e_vl hcy) : Mark Q) ∉ Set.range (s7fb_mark hn hsep hm hQC hcx hcy) := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  rw [s7fb_inr_mem_range_iff]
  rintro (h | h | ⟨v, hv⟩ | ⟨v, hv⟩)
  · exact s7e_vl_ne_va hcy (s7e_a_ne_leg true hsep) h
  · have := congrArg (fun v : Visit Q => v.2.val) h
    rw [s7fb_yl_edge, s7fb_xl_edge] at this
    exact prev_ne_self M this.symm
  · exact s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_firstVisitQ_fst hn hsep hm hQC v, hv]; exact s7fb_yl_affected hcy)
  · exact s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1
      (by rw [← s7b_secondVisitQ_fst hn hsep hm hQC v, hv]; exact s7fb_yl_affected hcy)

/-! #### The support and the transit marks -/

variable (T : Finset (Crossing Q)) (hxT : (s7e_va hcx).1 ∈ T) (hyT : (s7e_va hcy).1 ∈ T)
  (hTimg : ∀ z ∈ T, z ≠ (s7e_va hcx).1 → z ≠ (s7e_va hcy).1 →
    z ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪ Set.range (s7b_secondCrossingQ hn hsep hm hQC))
  (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))

include hsep hTimg in
/-- A visit that is none of the four newborn visits and is carried from neither half is transit. -/
theorem s7fb_transit_of (w : Visit Q) (h0 : w ≠ s7e_va hcy) (h1 : ∀ v, s7b_firstVisitQ hn hsep hm hQC v ≠ w)
    (h2 : ∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w) (h3 : w ≠ s7e_vl hcx) (h4 : w ≠ s7e_va hcx)
    (h5 : w ≠ s7e_vl hcy) :
    s7r_Transit hn hQ T (s7fb_mark hn hsep hm hQC hcx hcy) (Sum.inr w) := by
  have hnr : (Sum.inr w : Mark Q) ∉ Set.range (s7fb_mark hn hsep hm hQC hcx hcy) := by
    rw [s7fb_inr_mem_range_iff]
    rintro (h | h | ⟨v, hv⟩ | ⟨v, hv⟩)
    · exact h0 h
    · exact h3 h
    · exact h1 v hv
    · exact h2 v hv
  refine ⟨hnr, ?_⟩
  have hwT : w.1 ∉ T := by
    intro hwT
    by_cases hwx : w.1 = (s7e_va hcx).1
    · rcases s7e_visit_of_fst hcx w (by rw [hwx]; rfl) (s7e_a_ne_leg false hsep) with h | h
      · exact h4 h
      · exact h3 h
    by_cases hwy : w.1 = (s7e_va hcy).1
    · rcases s7e_visit_of_fst hcy w (by rw [hwy]; rfl) (s7e_a_ne_leg true hsep) with h | h
      · exact h0 h
      · exact h5 h
    rcases hTimg w.1 hwT hwx hwy with ⟨c, hcw⟩ | ⟨c, hcw⟩
    · obtain ⟨v, -, hv⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC w c hcw.symm
      exact h1 v hv
    · obtain ⟨v, -, hv⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC w c hcw.symm
      exact h2 v hv
  exact smoothingSuccessor_visit_of_not_mem hn hQ T w hwT

include hsep hTimg in
/-- **The window lemma** (RET's `s7r_transit_window` for the bigon map): every mark cyclically between
`u` (on edge `e`) and a target `m'` (the next vertex, or a mark on edge `e` beyond `u`) is transit as
soon as every visit in the parameter window is none of the four newborn visits and carried from
neither half. -/
theorem s7fb_transit_window (u m' : Mark Q) (e : ZMod n) (hu : s7e_mEdge u = e)
    (hm' : m' = Sum.inl (e + 1) ∨ (s7e_mEdge m' = e ∧ s7e_mParam u < s7e_mParam m'))
    (hex : ∀ w' : Visit Q, w'.2.val = e → s7e_mParam u < visitParameter w' →
      (m' = Sum.inl (e + 1) ∨ visitParameter w' < s7e_mParam m') →
      w' ≠ s7e_va hcy ∧ (∀ v, s7b_firstVisitQ hn hsep hm hQC v ≠ w') ∧
        (∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w') ∧ w' ≠ s7e_vl hcx ∧ w' ≠ s7e_va hcx ∧
        w' ≠ s7e_vl hcy) :
    ∀ w, traversalBetween (markPosition hn hQ.1 u) (markPosition hn hQ.1 w) (markPosition hn hQ.1 m') →
      s7r_Transit hn hQ T (s7fb_mark hn hsep hm hQC hcx hcy) w := by
  intro w hb
  have hdec : s7e_mEdge w = e ∧ s7e_mParam u < s7e_mParam w ∧
      (m' = Sum.inl (e + 1) ∨ s7e_mParam w < s7e_mParam m') := by
    rcases hm' with rfl | ⟨hme, hlt⟩
    · obtain ⟨h1, h2⟩ := s7r_between_next_vertex hn hQ u w e hu hb
      exact ⟨h1, h2, Or.inl rfl⟩
    · obtain ⟨h1, h2, h3⟩ := s7r_between_same_edge_of hn hQ u w m' e hu hme hlt hb
      exact ⟨h1, h2, Or.inr h3⟩
  have hpos : 0 < s7e_mParam w := lt_of_le_of_lt (s7e_mParam_nonneg hn hQ u) hdec.2.1
  obtain ⟨w', rfl⟩ := s7e_mark_visit_of_param_pos w hpos
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hex w' hdec.1 hdec.2.1 hdec.2.2
  exact s7fb_transit_of hn hQ hsep hm hQC hcx hcy T hTimg w' h0 h1 h2 h3 h4 h5

/-! #### The chain starts of the half marks -/

/-- The mark of `Q` whose successor starts the chain of `m₁ : Mark λ₁`: the twin `y_ℓ` for the vertex
`0 ↦ y_a` (a selected visit), the image mark otherwise. -/
def s7fb_qmark₁ (m₁ : Mark (firstHalf Pc M a)) : Mark Q :=
  if m₁ = Sum.inl 0 then Sum.inr (s7e_vl hcy) else s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl m₁))

/-- The chain start of `m₂ : Mark λ₂`: the twin `x_a` for the vertex `0 ↦ x_ℓ`, the image mark otherwise. -/
def s7fb_qmark₂ (m₂ : Mark (secondHalf Pc M a)) : Mark Q :=
  if m₂ = Sum.inl 0 then Sum.inr (s7e_va hcx) else s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr m₂))

theorem s7fb_qmark₁_zero : s7fb_qmark₁ hn hsep hm hQC hcx hcy (Sum.inl 0) = Sum.inr (s7e_vl hcy) := by
  simp [s7fb_qmark₁]

theorem s7fb_qmark₁_inl {i : ZMod (firstHalfSize M a)} (hi : i ≠ 0) :
    s7fb_qmark₁ hn hsep hm hQC hcx hcy (Sum.inl i) = Sum.inl (firstHalfIndex M a i) := by
  have : (Sum.inl i : Mark (firstHalf Pc M a)) ≠ Sum.inl 0 := fun h => hi (Sum.inl.inj h)
  simp [s7fb_qmark₁, this, s7fb_mark, hi]

theorem s7fb_qmark₁_inr (v : Visit (firstHalf Pc M a)) :
    s7fb_qmark₁ hn hsep hm hQC hcx hcy (Sum.inr v) = Sum.inr (s7b_firstVisitQ hn hsep hm hQC v) := by
  simp [s7fb_qmark₁, s7fb_mark]

theorem s7fb_qmark₂_zero : s7fb_qmark₂ hn hsep hm hQC hcx hcy (Sum.inl 0) = Sum.inr (s7e_va hcx) := by
  simp [s7fb_qmark₂]

theorem s7fb_qmark₂_inl {j : ZMod (secondHalfSize M a)} (hj : j ≠ 0) :
    s7fb_qmark₂ hn hsep hm hQC hcx hcy (Sum.inl j) = Sum.inl (secondHalfEdgeIndex M a j) := by
  have : (Sum.inl j : Mark (secondHalf Pc M a)) ≠ Sum.inl 0 := fun h => hj (Sum.inl.inj h)
  simp [s7fb_qmark₂, this, s7fb_mark, hj, secondHalfIndex_nonzero M a hj]

theorem s7fb_qmark₂_inr (v : Visit (secondHalf Pc M a)) :
    s7fb_qmark₂ hn hsep hm hQC hcx hcy (Sum.inr v) = Sum.inr (s7b_secondVisitQ hn hsep hm hQC v) := by
  simp [s7fb_qmark₂, s7fb_mark]

theorem s7fb_edge_first (m₁ : Mark (firstHalf Pc M a)) :
    s7e_mEdge (s7fb_qmark₁ hn hsep hm hQC hcx hcy m₁) = firstHalfIndex M a (s7e_mEdge m₁) := by
  cases m₁ with
  | inl i =>
    by_cases hi : i = 0
    · subst hi; rw [s7fb_qmark₁_zero, s7e_mEdge_inr, s7fb_yl_edge, s7e_mEdge_inl, firstHalfIndex_zero]
    · rw [s7fb_qmark₁_inl hn hsep hm hQC hcx hcy hi]; rfl
  | inr v => rw [s7fb_qmark₁_inr, s7e_mEdge_inr, s7b_firstVisitQ_edge]; rfl

theorem s7fb_edge_second (m₂ : Mark (secondHalf Pc M a)) :
    s7e_mEdge (s7fb_qmark₂ hn hsep hm hQC hcx hcy m₂) = secondHalfEdgeIndex M a (s7e_mEdge m₂) := by
  cases m₂ with
  | inl j =>
    by_cases hj : j = 0
    · subst hj; rw [s7fb_qmark₂_zero, s7e_mEdge_inr, s7e_va_edge, s7e_mEdge_inl, secondHalfEdgeIndex_zero]
    · rw [s7fb_qmark₂_inl hn hsep hm hQC hcx hcy hj]; rfl
  | inr v => rw [s7fb_qmark₂_inr, s7e_mEdge_inr, s7b_secondVisitQ_edge]; rfl

include hQ hz hr hr0 hη hw hord hg₁ in
/-- Parameter transfer for the first half: the Q-order between the chain start of `m₁` and a carried
visit on the same edge is the `λ₁`-order (for the vertex `0` both sides are true: the chain starts at
`y_ℓ`, below every persistent visit of `E_M`). -/
theorem s7fb_param_first (m₁ : Mark (firstHalf Pc M a)) (v' : Visit (firstHalf Pc M a))
    (he : v'.2.val = s7e_mEdge m₁) :
    s7e_mParam (s7fb_qmark₁ hn hsep hm hQC hcx hcy m₁) < visitParameter (s7b_firstVisitQ hn hsep hm hQC v') ↔
      s7e_mParam m₁ < visitParameter v' := by
  cases m₁ with
  | inl i =>
    refine iff_of_true ?_ (s7e_visitParameter_pos (contactHalfSizes_bounds hn hsep).1.1 hg₁ v')
    by_cases hi : i = 0
    · subst hi
      rw [s7fb_qmark₁_zero, s7e_mParam_inr]
      have hM := s7e_persist_M hn hQ hw (s7b_firstVisitQ hn hsep hm hQC v')
        (s7b_firstCrossingQ_not_affected hn hsep hm hQC v'.1)
        (by rw [s7b_firstVisitQ_edge, he, s7e_mEdge_inl, firstHalfIndex_zero])
      have := s7fb_yl_param hn hQ hw hcy
      linarith
    · rw [s7fb_qmark₁_inl hn hsep hm hQC hcx hcy hi]; exact s7e_visitParameter_pos hn hQ _
  | inr v => rw [s7fb_qmark₁_inr]; exact s7r_first_order hn hsep hz hm hr hr0 hQC hord v v' he.symm

include hQ hz hr hr1 hη hw hord hside hg₂ in
/-- Parameter transfer for the second half (for the vertex `0` the chain starts at `x_a`, below every
carried cut visit of `λ₂`). -/
theorem s7fb_param_second (m₂ : Mark (secondHalf Pc M a)) (v' : Visit (secondHalf Pc M a))
    (he : v'.2.val = s7e_mEdge m₂) :
    s7e_mParam (s7fb_qmark₂ hn hsep hm hQC hcx hcy m₂) < visitParameter (s7b_secondVisitQ hn hsep hm hQC v') ↔
      s7e_mParam m₂ < visitParameter v' := by
  cases m₂ with
  | inl j =>
    refine iff_of_true ?_ (s7e_visitParameter_pos (contactHalfSizes_bounds hn hsep).2.1 hg₂ v')
    by_cases hj : j = 0
    · subst hj
      rw [s7fb_qmark₂_zero, s7e_mParam_inr]
      have := s7r_second_cut_gt hn hQ hsep hz hm hr hr1 hQC hw hside hg₂ v' he
      have hxa := (abs_lt.mp (s7fb_xa_near hn hQ hw hcx)).2
      linarith
    · rw [s7fb_qmark₂_inl hn hsep hm hQC hcx hcy hj]; exact s7e_visitParameter_pos hn hQ _
  | inr v => rw [s7fb_qmark₂_inr]; exact s7r_second_order hn hsep hz hm hr hr1 hQC hord v v' he.symm

include hQ hz hr hr1 hη hw hside hg₂ in
/-- On the cut (`j = 0`) the chain start of `m₂` is at or beyond `x_a`. -/
theorem s7fb_qmark₂_param_zero (m₂ : Mark (secondHalf Pc M a)) (h0 : s7e_mEdge m₂ = 0) :
    visitParameter (s7e_va hcx) ≤ s7e_mParam (s7fb_qmark₂ hn hsep hm hQC hcx hcy m₂) := by
  cases m₂ with
  | inl j =>
    have hj : j = 0 := h0
    subst hj; rw [s7fb_qmark₂_zero]; exact le_rfl
  | inr v =>
    rw [s7fb_qmark₂_inr, s7e_mParam_inr]
    have := s7r_second_cut_gt hn hQ hsep hz hm hr hr1 hQC hw hside hg₂ v h0
    have hxa := (abs_lt.mp (s7fb_xa_near hn hQ hw hcx)).2
    linarith

include hQ hz hr hr0 hη hw hside hg₁ in
/-- On the cut (`i = −1`) the chain start of `m₁` lies below `y_a` (a carried cut visit is below
`r − 3η`; the vertex `μ_a` has parameter `0`). -/
theorem s7fb_qmark₁_param_cut (m₁ : Mark (firstHalf Pc M a)) (h1 : s7e_mEdge m₁ = -1) :
    s7e_mParam (s7fb_qmark₁ hn hsep hm hQC hcx hcy m₁) < visitParameter (s7e_va hcy) := by
  have hya := (abs_lt.mp (s7fb_ya_near hn hQ hw hcy)).1
  have : Fact (1 < firstHalfSize M a) := ⟨by have := (contactHalfSizes_bounds hn hsep).1.1; omega⟩
  cases m₁ with
  | inl i =>
    have hi : i = -1 := h1
    have hi0 : i ≠ 0 := by rw [hi]; exact neg_ne_zero.mpr one_ne_zero
    rw [s7fb_qmark₁_inl hn hsep hm hQC hcx hcy hi0, s7e_mParam_inl]
    exact s7e_visitParameter_pos hn hQ _
  | inr v =>
    rw [s7fb_qmark₁_inr, s7e_mParam_inr]
    have := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside hg₁ v h1
    linarith

end S7FBMap

section S7FBReturn

variable {Pc Q : LabelledTuple n} (hQ : Generic Q) (hsep : ContactSeparated M a)
  (hz : pointZeroTriples Pc = {contactSupport M a}) (hm : Pc M ∈ edgeInterior Pc a) {r η : ℝ}
  (hr : Pc M = edgePoint Pc a r) (hr0 : 0 < r) (hr1 : r < 1) (hη : 0 < η)
  (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing Pc s))
  (hw : ContactParameterWindows Pc Q M a r η)
  (hord : ∀ (u u' : Visit Pc) (hu : ¬ ContactAffected M a u.1.val) (hu' : ¬ ContactAffected M a u'.1.val),
    u.2.val = u'.2.val →
    (visitParameter (s7a_visit hQC u hu) < visitParameter (s7a_visit hQC u' hu') ↔
      visitParameter u < visitParameter u'))
  (hside : ∀ (u : Visit Pc) (hu : ¬ ContactAffected M a u.1.val), u.2.val = a →
    (visitParameter (s7a_visit hQC u hu) < r ↔ visitParameter u < r))
  (hg₁ : Generic (firstHalf Pc M a)) (hg₂ : Generic (secondHalf Pc M a))
  (hcx : IsCrossing Q {a, contactLeg false M}) (hcy : IsCrossing Q {a, contactLeg true M})
  (T : Finset (Crossing Q)) (hxT : (s7e_va hcx).1 ∈ T) (hyT : (s7e_va hcy).1 ∈ T)
  (hTimg : ∀ z ∈ T, z ≠ (s7e_va hcx).1 → z ≠ (s7e_va hcy).1 →
    z ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪ Set.range (s7b_secondCrossingQ hn hsep hm hQC))
  (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))

/-! #### The first-half reach and step -/

include hQ hz hr hr0 hr1 hη hw hord hside hg₂ hTimg hlt in
/-- **First-half reach**: from the chain start of `m₁ : Mark λ₁` the smoothing successor reaches the
image of `nextMark m₁` through transit marks only (on the cut the chain ends at `y_a`, `λ₁`'s vertex `0`). -/
theorem s7fb_reach_first (hn₁ : 3 ≤ firstHalfSize M a) (m₁ : Mark (firstHalf Pc M a)) :
    ∃ k : ℕ, ((smoothingSuccessor hn hQ T) ^ k)
        (nextMark hn hQ (s7fb_qmark₁ hn hsep hm hQC hcx hcy m₁)) =
      s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl (nextMark hn₁ hg₁ m₁))) ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hQ T) ^ j)
        (nextMark hn hQ (s7fb_qmark₁ hn hsep hm hQC hcx hcy m₁)) ∉
          Set.range (s7fb_mark hn hsep hm hQC hcx hcy) := by
  have hedge_u := s7fb_edge_first hn hsep hm hQC hcx hcy m₁
  have hinj := s7fb_mark_injective hn hsep hm hQC hcx hcy
  have hya1 := (abs_lt.mp (s7fb_ya_near hn hQ hw hcy)).1
  have hya2 := (abs_lt.mp (s7fb_ya_near hn hQ hw hcy)).2
  have hne_u : s7fb_qmark₁ hn hsep hm hQC hcx hcy m₁ ≠
      s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl (nextMark hn₁ hg₁ m₁))) := by
    by_cases h0 : m₁ = Sum.inl 0
    · subst h0; rw [s7fb_qmark₁_zero]; intro h
      exact s7fb_yl_not_mem_range hn hsep hm hQC hcx hcy ⟨_, h.symm⟩
    · rw [show s7fb_qmark₁ hn hsep hm hQC hcx hcy m₁ = s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl m₁))
        by simp [s7fb_qmark₁, h0]]
      intro h
      exact markSuccessor_ne_self hn₁ hg₁ m₁ (Sum.inl.inj (Sum.inl.inj (hinj h))).symm
  -- a carried first-half visit on the edge of `m₁`: its `λ₁`-edge and the transferred order
  have hfirst : ∀ (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) →
      ∀ v' : Visit (firstHalf Pc M a), s7b_firstVisitQ hn hsep hm hQC v' = w' →
      v'.2.val = s7e_mEdge m₁ ∧
        (s7e_mParam (s7fb_qmark₁ hn hsep hm hQC hcx hcy m₁) < visitParameter w' ↔
          s7e_mParam m₁ < visitParameter v') := by
    intro w' he v' hv'
    have hv'e : v'.2.val = s7e_mEdge m₁ := by
      apply firstHalfIndex_injective M a
      rw [← s7b_firstVisitQ_edge hn hsep hm hQC v', hv', he]
    refine ⟨hv'e, ?_⟩
    rw [← hv']
    exact s7fb_param_first hn hQ hsep hz hm hr hr0 hη hQC hw hord hg₁ hcx hcy m₁ v' hv'e
  -- `x_ℓ` never lies on a first-half edge
  have hxl : ∀ (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) → w' ≠ s7e_vl hcx := by
    intro w' he h
    rw [h, s7fb_xl_edge] at he
    exact s7b_firstHalfIndex_ne_pred hn hsep _ he.symm
  -- `y_ℓ` never lies strictly above the chain start on a first-half edge
  have hyl : ∀ (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) →
      s7e_mParam (s7fb_qmark₁ hn hsep hm hQC hcx hcy m₁) < visitParameter w' → w' ≠ s7e_vl hcy := by
    intro w' he hlo h
    rw [h, s7fb_yl_edge] at he
    have hi0 : s7e_mEdge m₁ = 0 := firstHalfIndex_injective M a (by rw [← he, firstHalfIndex_zero])
    rw [h] at hlo
    cases m₁ with
    | inl i =>
      have hi : i = 0 := hi0
      subst hi
      rw [s7fb_qmark₁_zero, s7e_mParam_inr] at hlo
      exact lt_irrefl _ hlo
    | inr v =>
      rw [s7fb_qmark₁_inr, s7e_mParam_inr] at hlo
      have hM := s7e_persist_M hn hQ hw (s7b_firstVisitQ hn hsep hm hQC v)
        (s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1)
        (by rw [s7b_firstVisitQ_edge]; show firstHalfIndex M a (s7e_mEdge (Sum.inr v)) = M
            rw [hi0, firstHalfIndex_zero])
      have := s7fb_yl_param hn hQ hw hcy
      linarith
  -- the exclusions on a first-half edge OTHER than the cut
  have hoff : ∀ (_ : s7e_mEdge m₁ ≠ -1) (w' : Visit Q), w'.2.val = firstHalfIndex M a (s7e_mEdge m₁) →
      w' ≠ s7e_va hcy ∧ (∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w') ∧ w' ≠ s7e_va hcx := by
    intro hi1 w' he
    have hea : w'.2.val ≠ a := by
      intro h; rw [h] at he
      exact hi1 (firstHalfIndex_injective M a (he.symm.trans (firstHalfIndex_last M a).symm))
    refine ⟨?_, ?_, ?_⟩
    · intro h; rw [h, s7e_va_edge] at hea; exact hea rfl
    · intro v h; rw [← h, s7b_secondVisitQ_edge] at he
      exact hi1 (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep he.symm).1
    · intro h; rw [h, s7e_va_edge] at hea; exact hea rfl
  -- the exclusions on the cut edge `a` for a window bounded above by `p' ≤ p(y_a)`
  have hcut : ∀ (_ : s7e_mEdge m₁ = -1) (p' : ℝ) (_ : p' ≤ visitParameter (s7e_va hcy)) (w' : Visit Q),
      w'.2.val = a → visitParameter w' < p' →
      w' ≠ s7e_va hcy ∧ (∀ v, s7b_secondVisitQ hn hsep hm hQC v ≠ w') ∧ w' ≠ s7e_va hcx := by
    intro _ p' hp' w' he hlt'
    refine ⟨?_, ?_, ?_⟩
    · intro h; rw [h] at hlt'; linarith
    · intro v h
      have hv0 : v.2.val = 0 := by
        rw [← h, s7b_secondVisitQ_edge] at he
        exact (s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep
          (by rw [firstHalfIndex_last]; exact he.symm)).2
      have := s7r_second_cut_gt hn hQ hsep hz hm hr hr1 hQC hw hside hg₂ v hv0
      rw [h] at this
      linarith
    · intro h; rw [h] at hlt'; linarith
  rcases s7r_nextMark_shape hn₁ hg₁ m₁ with hnx | ⟨w, hnx, hwe, hwp⟩
  · by_cases hi1 : s7e_mEdge m₁ = -1
    · -- the cut, vertex target `inl 0 ↦ y_a`
      have hm' : s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl (nextMark hn₁ hg₁ m₁))) =
          Sum.inr (s7e_va hcy) := by
        rw [hnx, hi1, neg_add_cancel, s7fb_mark_inl_inl_zero]
      rw [hm'] at hne_u ⊢
      have hea : firstHalfIndex M a (s7e_mEdge m₁) = a := by rw [hi1, firstHalfIndex_last]
      have hlt_u := s7fb_qmark₁_param_cut hn hQ hsep hz hm hr hr0 hη hQC hw hside hg₁ hcx hcy m₁ hi1
      refine s7r_reach_of_transit hn hQ T _ _ _ _ rfl hne_u
        (s7fb_transit_window hn hQ hsep hm hQC hcx hcy T hTimg _ _ a (hedge_u.trans hea)
          (Or.inr ⟨s7e_va_edge hcy, hlt_u⟩) ?_)
      intro w' he hlo hhi
      have hhi' : visitParameter w' < visitParameter (s7e_va hcy) := by
        rcases hhi with h | h
        · exact absurd h Sum.inr_ne_inl
        · exact h
      obtain ⟨h0, h2, h4⟩ := hcut hi1 (visitParameter (s7e_va hcy)) le_rfl w' he hhi'
      refine ⟨h0, ?_, h2, hxl w' (by rw [he, hea]), h4, hyl w' (by rw [he, hea]) hlo⟩
      intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hfirst w' (by rw [he, hea]) v' hv'
      exact s7r_no_half_between hn₁ hg₁ m₁ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
    · -- off the cut, vertex target `inl (i + 1) ↦ μ_{firstHalfIndex i + 1}`
      have hi1' : s7e_mEdge m₁ + 1 ≠ 0 := fun h => hi1 (eq_neg_of_add_eq_zero_left h)
      have hm' : s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl (nextMark hn₁ hg₁ m₁))) =
          Sum.inl (firstHalfIndex M a (s7e_mEdge m₁) + 1) := by
        rw [hnx, s7fb_mark_inl_inl hn hsep hm hQC hcx hcy hi1', firstHalfIndex_next M a hi1]
      rw [hm'] at hne_u ⊢
      refine s7r_reach_of_transit hn hQ T _ _ _ _ rfl hne_u
        (s7fb_transit_window hn hQ hsep hm hQC hcx hcy T hTimg _ _ _ hedge_u (Or.inl rfl) ?_)
      intro w' he hlo _
      obtain ⟨h0, h2, h4⟩ := hoff hi1 w' he
      refine ⟨h0, ?_, h2, hxl w' he, h4, hyl w' he hlo⟩
      intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hfirst w' he v' hv'
      exact s7r_no_half_between hn₁ hg₁ m₁ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
  · -- target: a visit `w` of `λ₁` on the edge of `m₁`, `↦ firstVisitQ w`
    have hm' : s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl (nextMark hn₁ hg₁ m₁))) =
        Sum.inr (s7b_firstVisitQ hn hsep hm hQC w) := by rw [hnx, s7fb_mark_inl_inr]
    rw [hm'] at hne_u ⊢
    have hwQe : (s7b_firstVisitQ hn hsep hm hQC w).2.val = firstHalfIndex M a (s7e_mEdge m₁) := by
      rw [s7b_firstVisitQ_edge, hwe]
    have hlt_u : s7e_mParam (s7fb_qmark₁ hn hsep hm hQC hcx hcy m₁) <
        visitParameter (s7b_firstVisitQ hn hsep hm hQC w) :=
      (s7fb_param_first hn hQ hsep hz hm hr hr0 hη hQC hw hord hg₁ hcx hcy m₁ w hwe).mpr hwp
    refine s7r_reach_of_transit hn hQ T _ _ _ _ rfl hne_u
      (s7fb_transit_window hn hQ hsep hm hQC hcx hcy T hTimg _ _ _ hedge_u (Or.inr ⟨hwQe, hlt_u⟩) ?_)
    intro w' he hlo hhi
    have hhi' : visitParameter w' < visitParameter (s7b_firstVisitQ hn hsep hm hQC w) := by
      rcases hhi with h | h
      · exact absurd h Sum.inr_ne_inl
      · exact h
    have hex1 : ∀ v', s7b_firstVisitQ hn hsep hm hQC v' ≠ w' := by
      intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hfirst w' he v' hv'
      have hup : visitParameter v' < visitParameter w := by
        rw [← hv'] at hhi'
        exact (s7r_first_order hn hsep hz hm hr hr0 hQC hord v' w (hv'e.trans hwe.symm)).mp hhi'
      exact s7r_no_half_between hn₁ hg₁ m₁ _ rfl v' hv'e (hiff.mp hlo)
        (Or.inr ⟨by rw [hnx]; exact hwe, by rw [hnx]; exact hup⟩)
    by_cases hi1 : s7e_mEdge m₁ = -1
    · have hea : firstHalfIndex M a (s7e_mEdge m₁) = a := by rw [hi1, firstHalfIndex_last]
      have hwlt := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside hg₁ w (hwe.trans hi1)
      obtain ⟨h0, h2, h4⟩ := hcut hi1 _ (by linarith) w' (by rw [he, hea]) hhi'
      exact ⟨h0, hex1, h2, hxl w' he, h4, hyl w' he hlo⟩
    · obtain ⟨h0, h2, h4⟩ := hoff hi1 w' he
      exact ⟨h0, hex1, h2, hxl w' he, h4, hyl w' he hlo⟩

include hQ hz hr hr0 hr1 hη hw hord hside hg₂ hyT hTimg hlt in
/-- **First-half step** of the first-return law: for `b = inl (inl m)`. -/
theorem s7fb_step_first (hn₁ : 3 ≤ firstHalfSize M a) (S₁ : Finset (Crossing (firstHalf Pc M a)))
    (hS₁ : S₁ = s7b_pre (s7b_firstCrossingQ hn hsep hm hQC) T) (m : Mark (firstHalf Pc M a)) :
    ∃ k : ℕ, 0 < k ∧ ((smoothingSuccessor hn hQ T) ^ k)
        (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl m))) =
      s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl (smoothingSuccessor hn₁ hg₁ S₁ m))) ∧
      ∀ j : ℕ, 0 < j → j < k → ((smoothingSuccessor hn hQ T) ^ j)
        (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl m))) ∉
          Set.range (s7fb_mark hn hsep hm hQC hcx hcy) := by
  have hu : selectedMarkPerm T (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl m))) =
      s7fb_qmark₁ hn hsep hm hQC hcx hcy (selectedMarkPerm S₁ m) := by
    cases m with
    | inl i =>
      by_cases hi : i = 0
      · subst hi
        rw [s7fb_mark_inl_inl_zero, selectedMarkPerm_visit, selectedMarkPerm_vertex, s7fb_qmark₁_zero,
          selectedVisitTwin_of_mem T _ hyT, s7e_twin_va hcy (s7e_a_ne_leg true hsep)]
      · rw [s7fb_mark_inl_inl hn hsep hm hQC hcx hcy hi, selectedMarkPerm_vertex, selectedMarkPerm_vertex,
          s7fb_qmark₁_inl hn hsep hm hQC hcx hcy hi]
    | inr v =>
      rw [s7fb_mark_inl_inr, selectedMarkPerm_visit, selectedMarkPerm_visit, s7fb_qmark₁_inr]
      congr 1
      by_cases hv : v.1 ∈ S₁
      · have hvQ : (s7b_firstVisitQ hn hsep hm hQC v).1 ∈ T := by
          rw [s7b_firstVisitQ_fst]; rw [hS₁, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_mem S₁ v hv, selectedVisitTwin_of_mem T _ hvQ, s7b_firstVisitQ_visitTwin]
      · have hvQ : (s7b_firstVisitQ hn hsep hm hQC v).1 ∉ T := by
          rw [s7b_firstVisitQ_fst]; rw [hS₁, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_not_mem S₁ v hv, selectedVisitTwin_of_not_mem T _ hvQ]
  exact s7r_step_of_reach hn hQ T _ (Sum.inl (Sum.inl m)) _ _ hu
    (s7fb_reach_first hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside hg₁ hg₂ hcx hcy T hTimg hlt hn₁
      (selectedMarkPerm S₁ m))

/-! #### The second-half reach and step -/

include hQ hz hr hr0 hr1 hη hw hord hside hg₁ hTimg hlt in
/-- **Second-half reach**: from the chain start of `m₂ : Mark λ₂` the smoothing successor reaches the
image of `nextMark m₂` through transit marks only (the vertex `0` of `λ₂` is entered from edge `M − 1`
at `x_ℓ` and left through `x_a`). -/
theorem s7fb_reach_second (hn₂ : 3 ≤ secondHalfSize M a) (m₂ : Mark (secondHalf Pc M a)) :
    ∃ k : ℕ, ((smoothingSuccessor hn hQ T) ^ k)
        (nextMark hn hQ (s7fb_qmark₂ hn hsep hm hQC hcx hcy m₂)) =
      s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr (nextMark hn₂ hg₂ m₂))) ∧
      ∀ j : ℕ, j < k → ((smoothingSuccessor hn hQ T) ^ j)
        (nextMark hn hQ (s7fb_qmark₂ hn hsep hm hQC hcx hcy m₂)) ∉
          Set.range (s7fb_mark hn hsep hm hQC hcx hcy) := by
  have hedge_u := s7fb_edge_second hn hsep hm hQC hcx hcy m₂
  have hinj := s7fb_mark_injective hn hsep hm hQC hcx hcy
  have hxa1 := (abs_lt.mp (s7fb_xa_near hn hQ hw hcx)).1
  have hxa2 := (abs_lt.mp (s7fb_xa_near hn hQ hw hcx)).2
  have hxl := s7fb_xl_param hn hQ hw hcx
  have hne_u : s7fb_qmark₂ hn hsep hm hQC hcx hcy m₂ ≠
      s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr (nextMark hn₂ hg₂ m₂))) := by
    by_cases h0 : m₂ = Sum.inl 0
    · subst h0; rw [s7fb_qmark₂_zero]; intro h
      exact s7fb_xa_not_mem_range hn hsep hm hQC hcx hcy ⟨_, h.symm⟩
    · rw [show s7fb_qmark₂ hn hsep hm hQC hcx hcy m₂ = s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr m₂))
        by simp [s7fb_qmark₂, h0]]
      intro h
      exact markSuccessor_ne_self hn₂ hg₂ m₂ (Sum.inr.inj (Sum.inl.inj (hinj h))).symm
  have hsecond : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
      ∀ v' : Visit (secondHalf Pc M a), s7b_secondVisitQ hn hsep hm hQC v' = w' →
      v'.2.val = s7e_mEdge m₂ ∧ (s7e_mParam (s7fb_qmark₂ hn hsep hm hQC hcx hcy m₂) < visitParameter w' ↔
        s7e_mParam m₂ < visitParameter v') := by
    intro w' he v' hv'
    have hv'e : v'.2.val = s7e_mEdge m₂ := by
      apply secondHalfEdgeIndex_injective M a
      rw [← s7b_secondVisitQ_edge hn hsep hm hQC v', hv', he]
    refine ⟨hv'e, ?_⟩
    rw [← hv']
    exact s7fb_param_second hn hQ hsep hz hm hr hr1 hη hQC hw hord hside hg₂ hcx hcy m₂ v' hv'e
  -- no first-half visit lies strictly above the chain start on a second-half edge
  have hfirst : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
      s7e_mParam (s7fb_qmark₂ hn hsep hm hQC hcx hcy m₂) < visitParameter w' →
      ∀ v', s7b_firstVisitQ hn hsep hm hQC v' ≠ w' := by
    intro w' he hlo v' hv'
    rw [← hv', s7b_firstVisitQ_edge] at he
    obtain ⟨hv'1, hj0⟩ := s7b_firstHalfIndex_eq_secondHalfEdgeIndex hn hsep he
    have h1 := s7r_first_cut_lt hn hQ hsep hz hm hr hr0 hQC hw hside hg₁ v' hv'1
    have h2 := s7fb_qmark₂_param_zero hn hQ hsep hz hm hr hr1 hη hQC hw hside hg₂ hcx hcy m₂ hj0
    rw [← hv'] at hlo
    linarith
  -- neither newborn `a`-visit lies strictly above the chain start
  have hxa_ex : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
      s7e_mParam (s7fb_qmark₂ hn hsep hm hQC hcx hcy m₂) < visitParameter w' →
      w' ≠ s7e_va hcx ∧ w' ≠ s7e_va hcy := by
    intro w' he hlo
    constructor
    · intro h
      rw [h, s7e_va_edge] at he
      have hj0 : s7e_mEdge m₂ = 0 :=
        secondHalfEdgeIndex_injective M a (by rw [← he, secondHalfEdgeIndex_zero])
      have h2 := s7fb_qmark₂_param_zero hn hQ hsep hz hm hr hr1 hη hQC hw hside hg₂ hcx hcy m₂ hj0
      rw [h] at hlo
      linarith
    · intro h
      rw [h, s7e_va_edge] at he
      have hj0 : s7e_mEdge m₂ = 0 :=
        secondHalfEdgeIndex_injective M a (by rw [← he, secondHalfEdgeIndex_zero])
      have h2 := s7fb_qmark₂_param_zero hn hQ hsep hz hm hr hr1 hη hQC hw hside hg₂ hcx hcy m₂ hj0
      rw [h] at hlo
      linarith
  -- `y_ℓ` never lies on a second-half edge
  have hyl : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) → w' ≠ s7e_vl hcy := by
    intro w' he h
    rw [h, s7fb_yl_edge] at he
    exact s7b_secondHalfEdgeIndex_ne hn hsep _ he.symm
  -- `x_ℓ` lies on a second-half edge only on the last one
  have hxl_edge : ∀ (w' : Visit Q), w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) →
      w' = s7e_vl hcx → s7e_mEdge m₂ = -1 := by
    intro w' he h
    rw [h, s7fb_xl_edge, ← secondHalfEdgeIndex_last M a] at he
    exact (secondHalfEdgeIndex_injective M a he).symm
  have : Fact (1 < secondHalfSize M a) := ⟨by omega⟩
  rcases s7r_nextMark_shape hn₂ hg₂ m₂ with hnx | ⟨w, hnx, hwe, hwp⟩
  · by_cases hj1 : s7e_mEdge m₂ = -1
    · -- `j = −1`: `nextMark m₂ = inl 0 ↦ x_ℓ`, the last mark on edge `M − 1`
      have hm' : s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr (nextMark hn₂ hg₂ m₂))) =
          Sum.inr (s7e_vl hcx) := by
        rw [hnx, hj1, neg_add_cancel, s7fb_mark_inr_inl_zero]
      rw [hm'] at hne_u ⊢
      have hem : secondHalfEdgeIndex M a (s7e_mEdge m₂) = M - 1 := by rw [hj1, secondHalfEdgeIndex_last]
      have hlt_u : s7e_mParam (s7fb_qmark₂ hn hsep hm hQC hcx hcy m₂) < visitParameter (s7e_vl hcx) := by
        cases m₂ with
        | inl j =>
          have hj : j ≠ 0 := by
            intro h; rw [h] at hj1
            exact absurd hj1.symm (neg_ne_zero.mpr one_ne_zero)
          rw [s7fb_qmark₂_inl hn hsep hm hQC hcx hcy hj]; exact s7e_visitParameter_pos hn hQ _
        | inr v =>
          rw [s7fb_qmark₂_inr]
          have hp := s7e_persist_M_sub_one hn hQ hw (s7b_secondVisitQ hn hsep hm hQC v)
            (s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1)
            (by rw [s7b_secondVisitQ_edge]; exact hem)
          show visitParameter (s7b_secondVisitQ hn hsep hm hQC v) < _
          linarith
      refine s7r_reach_of_transit hn hQ T _ _ _ _ rfl hne_u
        (s7fb_transit_window hn hQ hsep hm hQC hcx hcy T hTimg _ _ _ (hedge_u.trans hem)
          (Or.inr ⟨s7fb_xl_edge hcx, hlt_u⟩) ?_)
      intro w' he hlo hhi
      have hhi' : visitParameter w' < visitParameter (s7e_vl hcx) := by
        rcases hhi with h | h
        · exact absurd h Sum.inr_ne_inl
        · exact h
      have he' : w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) := he.trans hem.symm
      obtain ⟨hx4, hy0⟩ := hxa_ex w' he' hlo
      refine ⟨hy0, hfirst w' he' hlo, ?_, fun h => by rw [h] at hhi'; exact lt_irrefl _ hhi', hx4, hyl w' he'⟩
      intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hsecond w' he' v' hv'
      exact s7r_no_half_between hn₂ hg₂ m₂ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
    · by_cases hj0 : s7e_mEdge m₂ = 0
      · -- `j = 0`: `nextMark m₂ = inl 1 ↦ μ_{a+1}`, entered from `x_a`
        have hm' : s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr (nextMark hn₂ hg₂ m₂))) =
            Sum.inl (a + 1) := by
          rw [hnx, hj0, zero_add, s7fb_mark_inr_inl hn hsep hm hQC hcx hcy one_ne_zero,
            secondHalfIndex_one hn hsep]
        rw [hm'] at hne_u ⊢
        have hem : secondHalfEdgeIndex M a (s7e_mEdge m₂) = a := by rw [hj0, secondHalfEdgeIndex_zero]
        refine s7r_reach_of_transit hn hQ T _ _ _ _ rfl hne_u
          (s7fb_transit_window hn hQ hsep hm hQC hcx hcy T hTimg _ _ _ (hedge_u.trans hem) (Or.inl rfl) ?_)
        intro w' he hlo _
        have he' : w'.2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) := he.trans hem.symm
        obtain ⟨hx4, hy0⟩ := hxa_ex w' he' hlo
        refine ⟨hy0, hfirst w' he' hlo, ?_, fun h => ?_, hx4, hyl w' he'⟩
        · intro v' hv'
          obtain ⟨hv'e, hiff⟩ := hsecond w' he' v' hv'
          exact s7r_no_half_between hn₂ hg₂ m₂ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
        · have := hxl_edge w' he' h
          rw [hj0] at this
          exact absurd this.symm (neg_ne_zero.mpr one_ne_zero)
      · -- `j ≠ 0, −1`: `nextMark m₂ = inl (j+1) ↦ μ_{secondHalfEdgeIndex j + 1}`
        have hj1' : s7e_mEdge m₂ + 1 ≠ 0 := fun h => hj1 (eq_neg_of_add_eq_zero_left h)
        have hm' : s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr (nextMark hn₂ hg₂ m₂))) =
            Sum.inl (secondHalfEdgeIndex M a (s7e_mEdge m₂) + 1) := by
          rw [hnx, s7fb_mark_inr_inl hn hsep hm hQC hcx hcy hj1', secondHalfIndex_next M a hj0]
        rw [hm'] at hne_u ⊢
        refine s7r_reach_of_transit hn hQ T _ _ _ _ rfl hne_u
          (s7fb_transit_window hn hQ hsep hm hQC hcx hcy T hTimg _ _ _ hedge_u (Or.inl rfl) ?_)
        intro w' he hlo _
        obtain ⟨hx4, hy0⟩ := hxa_ex w' he hlo
        refine ⟨hy0, hfirst w' he hlo, ?_, fun h => hj1 (hxl_edge w' he h), hx4, hyl w' he⟩
        intro v' hv'
        obtain ⟨hv'e, hiff⟩ := hsecond w' he v' hv'
        exact s7r_no_half_between hn₂ hg₂ m₂ _ rfl v' hv'e (hiff.mp hlo) (Or.inl hnx)
  · -- target: a visit `w` of `λ₂` on the edge of `m₂`, `↦ secondVisitQ w`
    have hm' : s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr (nextMark hn₂ hg₂ m₂))) =
        Sum.inr (s7b_secondVisitQ hn hsep hm hQC w) := by rw [hnx, s7fb_mark_inr_inr]
    rw [hm'] at hne_u ⊢
    have hwQe : (s7b_secondVisitQ hn hsep hm hQC w).2.val = secondHalfEdgeIndex M a (s7e_mEdge m₂) := by
      rw [s7b_secondVisitQ_edge, hwe]
    have hlt_u : s7e_mParam (s7fb_qmark₂ hn hsep hm hQC hcx hcy m₂) <
        visitParameter (s7b_secondVisitQ hn hsep hm hQC w) :=
      (s7fb_param_second hn hQ hsep hz hm hr hr1 hη hQC hw hord hside hg₂ hcx hcy m₂ w hwe).mpr hwp
    refine s7r_reach_of_transit hn hQ T _ _ _ _ rfl hne_u
      (s7fb_transit_window hn hQ hsep hm hQC hcx hcy T hTimg _ _ _ hedge_u (Or.inr ⟨hwQe, hlt_u⟩) ?_)
    intro w' he hlo hhi
    have hhi' : visitParameter w' < visitParameter (s7b_secondVisitQ hn hsep hm hQC w) := by
      rcases hhi with h | h
      · exact absurd h Sum.inr_ne_inl
      · exact h
    obtain ⟨hx4, hy0⟩ := hxa_ex w' he hlo
    refine ⟨hy0, hfirst w' he hlo, ?_, ?_, hx4, hyl w' he⟩
    · intro v' hv'
      obtain ⟨hv'e, hiff⟩ := hsecond w' he v' hv'
      have hup : visitParameter v' < visitParameter w := by
        rw [← hv'] at hhi'
        exact (s7r_second_order hn hsep hz hm hr hr1 hQC hord v' w (hv'e.trans hwe.symm)).mp hhi'
      exact s7r_no_half_between hn₂ hg₂ m₂ _ rfl v' hv'e (hiff.mp hlo)
        (Or.inr ⟨by rw [hnx]; exact hwe, by rw [hnx]; exact hup⟩)
    · intro h
      have hj1 := hxl_edge w' he h
      have hp := s7e_persist_M_sub_one hn hQ hw (s7b_secondVisitQ hn hsep hm hQC w)
        (s7b_secondCrossingQ_not_affected hn hsep hm hQC w.1)
        (by rw [hwQe, hj1, secondHalfEdgeIndex_last])
      rw [h] at hhi'
      linarith

include hQ hz hr hr0 hr1 hη hw hord hside hg₁ hxT hTimg hlt in
/-- **Second-half step** of the first-return law: for `b = inl (inr m)`. -/
theorem s7fb_step_second (hn₂ : 3 ≤ secondHalfSize M a) (S₂ : Finset (Crossing (secondHalf Pc M a)))
    (hS₂ : S₂ = s7b_pre (s7b_secondCrossingQ hn hsep hm hQC) T) (m : Mark (secondHalf Pc M a)) :
    ∃ k : ℕ, 0 < k ∧ ((smoothingSuccessor hn hQ T) ^ k)
        (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr m))) =
      s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr (smoothingSuccessor hn₂ hg₂ S₂ m))) ∧
      ∀ j : ℕ, 0 < j → j < k → ((smoothingSuccessor hn hQ T) ^ j)
        (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr m))) ∉
          Set.range (s7fb_mark hn hsep hm hQC hcx hcy) := by
  have hxlT : (s7e_vl hcx).1 ∈ T := by rw [s7e_vl_fst]; exact hxT
  have hu : selectedMarkPerm T (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr m))) =
      s7fb_qmark₂ hn hsep hm hQC hcx hcy (selectedMarkPerm S₂ m) := by
    cases m with
    | inl j =>
      by_cases hj : j = 0
      · subst hj
        rw [s7fb_mark_inr_inl_zero, selectedMarkPerm_visit, selectedMarkPerm_vertex, s7fb_qmark₂_zero,
          selectedVisitTwin_of_mem T _ hxlT, s7e_twin_vl hcx (s7e_a_ne_leg false hsep)]
      · rw [s7fb_mark_inr_inl hn hsep hm hQC hcx hcy hj, selectedMarkPerm_vertex, selectedMarkPerm_vertex,
          s7fb_qmark₂_inl hn hsep hm hQC hcx hcy hj, secondHalfIndex_nonzero M a hj]
    | inr v =>
      rw [s7fb_mark_inr_inr, selectedMarkPerm_visit, selectedMarkPerm_visit, s7fb_qmark₂_inr]
      congr 1
      by_cases hv : v.1 ∈ S₂
      · have hvQ : (s7b_secondVisitQ hn hsep hm hQC v).1 ∈ T := by
          rw [s7b_secondVisitQ_fst]; rw [hS₂, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_mem S₂ v hv, selectedVisitTwin_of_mem T _ hvQ, s7b_secondVisitQ_visitTwin]
      · have hvQ : (s7b_secondVisitQ hn hsep hm hQC v).1 ∉ T := by
          rw [s7b_secondVisitQ_fst]; rw [hS₂, s7b_mem_pre] at hv; exact hv
        rw [selectedVisitTwin_of_not_mem S₂ v hv, selectedVisitTwin_of_not_mem T _ hvQ]
  exact s7r_step_of_reach hn hQ T _ (Sum.inl (Sum.inr m)) _ _ hu
    (s7fb_reach_second hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside hg₁ hg₂ hcx hcy T hTimg hlt hn₂
      (selectedMarkPerm S₂ m))

/-! #### The contact triangle and the hit -/

include hQ hsep hη hw hcx in
/-- The three steps of the contact triangle: `μ_M ↦ y_ℓ ↦ x_a ↦ μ_M`. -/
theorem s7fb_succ_M : smoothingSuccessor hn hQ T (Sum.inl M) = Sum.inr (s7e_vl hcy) := by
  rw [smoothingSuccessor_vertex, markSuccessor_apply]
  exact s7fb_nextMark_M hn hQ hsep hη hw hcx hcy

include hQ hsep hw hyT hlt in
theorem s7fb_succ_yl : smoothingSuccessor hn hQ T (Sum.inr (s7e_vl hcy)) = Sum.inr (s7e_va hcx) := by
  rw [smoothingSuccessor_visit_of_mem hn hQ T _ (by rw [s7e_vl_fst]; exact hyT),
    s7e_twin_vl hcy (s7e_a_ne_leg true hsep), markSuccessor_apply]
  exact s7fb_nextMark_ya hn hQ hsep hw hcx hcy hlt

include hQ hsep hη hw hcy hxT in
theorem s7fb_succ_xa : smoothingSuccessor hn hQ T (Sum.inr (s7e_va hcx)) = Sum.inl M := by
  rw [smoothingSuccessor_visit_of_mem hn hQ T _ hxT, s7e_twin_va hcx (s7e_a_ne_leg false hsep),
    markSuccessor_apply]
  exact s7fb_nextMark_xl hn hQ hsep hη hw hcx hcy

include hQ hsep hη hw hxT hyT hlt in
/-- **The triangle step**: `μ_M` returns to itself in three steps through the two off-image
smoothing corners `y_ℓ`, `x_a`. -/
theorem s7fb_step_unit :
    ∃ k : ℕ, 0 < k ∧ ((smoothingSuccessor hn hQ T) ^ k) (Sum.inl M) = Sum.inl M ∧
      ∀ j : ℕ, 0 < j → j < k → ((smoothingSuccessor hn hQ T) ^ j) (Sum.inl M : Mark Q) ∉
        Set.range (s7fb_mark hn hsep hm hQC hcx hcy) := by
  have h1 : ((smoothingSuccessor hn hQ T) ^ 1) (Sum.inl M : Mark Q) = Sum.inr (s7e_vl hcy) := by
    rw [pow_one]; exact s7fb_succ_M hn hQ hsep hη hw hcx hcy T
  have h2 : ((smoothingSuccessor hn hQ T) ^ 2) (Sum.inl M : Mark Q) = Sum.inr (s7e_va hcx) := by
    rw [pow_succ', Equiv.Perm.mul_apply, h1]
    exact s7fb_succ_yl hn hQ hsep hw hcx hcy T hyT hlt
  have h3 : ((smoothingSuccessor hn hQ T) ^ 3) (Sum.inl M : Mark Q) = Sum.inl M := by
    rw [pow_succ', Equiv.Perm.mul_apply, h2]
    exact s7fb_succ_xa hn hQ hsep hη hw hcx hcy T hxT
  refine ⟨3, by norm_num, h3, ?_⟩
  intro j hj0 hj3
  interval_cases j
  · rw [h1]; exact s7fb_yl_not_mem_range hn hsep hm hQC hcx hcy
  · rw [h2]; exact s7fb_xa_not_mem_range hn hsep hm hQC hcx hcy

include hQ hη hw hxT hyT hTimg hlt in
/-- **Hit**: every mark reaches the image (beacon `μ_M`; the off-image visits are `x_a`, `y_ℓ` — which
reach `μ_M` in one and two steps — and the visits of crossings off `T`, which are transit). -/
theorem s7fb_hit (u : Mark Q) :
    ∃ j : ℕ, ((smoothingSuccessor hn hQ T) ^ j) u ∈ Set.range (s7fb_mark hn hsep hm hQC hcx hcy) := by
  refine s7r_hit_of_transit hn hQ T _ (Sum.inl M) (s7fb_M_mem_range hn hsep hm hQC hcx hcy) ?_ _ u rfl
  intro w hwr
  cases w with
  | inl i => exact Or.inr (smoothingSuccessor_vertex hn hQ T i)
  | inr w' =>
    rcases s7fb_visit_cases hsep hcx hcy w' with h | h | h | h | h
    · subst h; left; refine ⟨1, ?_⟩
      rw [pow_one, s7fb_succ_xa hn hQ hsep hη hw hcx hcy T hxT]
      exact s7fb_M_mem_range hn hsep hm hQC hcx hcy
    · exact absurd ((s7fb_inr_mem_range_iff hn hsep hm hQC hcx hcy w').mpr (Or.inr (Or.inl h))) hwr
    · exact absurd ((s7fb_inr_mem_range_iff hn hsep hm hQC hcx hcy w').mpr (Or.inl h)) hwr
    · subst h; left; refine ⟨2, ?_⟩
      rw [pow_succ, Equiv.Perm.mul_apply, pow_one, s7fb_succ_yl hn hQ hsep hw hcx hcy T hyT hlt,
        s7fb_succ_xa hn hQ hsep hη hw hcx hcy T hxT]
      exact s7fb_M_mem_range hn hsep hm hQC hcx hcy
    · by_cases hwT : w'.1 ∈ T
      · exfalso; apply hwr
        have hwx : w'.1 ≠ (s7e_va hcx).1 := fun he => h (he ▸ s7fb_xa_affected hcx)
        have hwy : w'.1 ≠ (s7e_va hcy).1 := fun he => h (he ▸ s7fb_ya_affected hcy)
        rcases hTimg w'.1 hwT hwx hwy with ⟨c, hcw⟩ | ⟨c, hcw⟩
        · obtain ⟨v, -, hv⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC w' c hcw.symm
          exact (s7fb_inr_mem_range_iff hn hsep hm hQC hcx hcy w').mpr (Or.inr (Or.inr (Or.inl ⟨v, hv⟩)))
        · obtain ⟨v, -, hv⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC w' c hcw.symm
          exact (s7fb_inr_mem_range_iff hn hsep hm hQC hcx hcy w').mpr (Or.inr (Or.inr (Or.inr ⟨v, hv⟩)))
      · exact Or.inr (smoothingSuccessor_visit_of_not_mem hn hQ T w' hwT)

/-- **The bigon transport structure** of a two-newborn row `T ∋ x, y` of the newborn side `Q`, with
its two half supports `S₁, S₂` (the preimages of `T`): every other crossing of `T` is carried from a
half, and the smoothing successor of `T` is the first-return map of `g₁ ⊔ g₂ ⊔ id_Unit` on the image
of the bigon mark map (the `Unit` summand is the contact triangle). -/
structure s7fb_BigonTransport (S₁ : Finset (Crossing (firstHalf Pc M a)))
    (S₂ : Finset (Crossing (secondHalf Pc M a))) : Prop where
  x_mem : (s7e_va hcx).1 ∈ T
  y_mem : (s7e_va hcy).1 ∈ T
  first_pre : S₁ = s7b_pre (s7b_firstCrossingQ hn hsep hm hQC) T
  second_pre : S₂ = s7b_pre (s7b_secondCrossingQ hn hsep hm hQC) T
  img : ∀ z ∈ T, z ≠ (s7e_va hcx).1 → z ≠ (s7e_va hcy).1 →
    z ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪ Set.range (s7b_secondCrossingQ hn hsep hm hQC)
  ret : s7b_ReturnTransport (smoothingSuccessor hn hQ T)
    (Equiv.Perm.sumCongr
      (Equiv.Perm.sumCongr (smoothingSuccessor (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁)
        (smoothingSuccessor (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂))
      (1 : Equiv.Perm Unit))
    (s7fb_mark hn hsep hm hQC hcx hcy)

include hz hr hr0 hr1 hη hw hord hside hxT hyT hTimg hlt in
/-- **The first-return law of a two-newborn row, PROVED** (U_S7B_REPORT §2.4's bigon mark map,
`ε = 0` case). -/
theorem s7fb_bigonTransport_of :
    s7fb_BigonTransport hn hQ hsep hm hQC hg₁ hg₂ hcx hcy T
      (s7b_pre (s7b_firstCrossingQ hn hsep hm hQC) T) (s7b_pre (s7b_secondCrossingQ hn hsep hm hQC) T) where
  x_mem := hxT
  y_mem := hyT
  first_pre := rfl
  second_pre := rfl
  img := hTimg
  ret :=
    { inj := s7fb_mark_injective hn hsep hm hQC hcx hcy
      step := fun b => by
        rcases b with (m | m) | u
        · exact s7fb_step_first hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside hg₁ hg₂ hcx hcy T hyT hTimg
            hlt (contactHalfSizes_bounds hn hsep).1.1 _ rfl m
        · exact s7fb_step_second hn hQ hsep hz hm hr hr0 hr1 hη hQC hw hord hside hg₁ hg₂ hcx hcy T hxT hTimg
            hlt (contactHalfSizes_bounds hn hsep).2.1 _ rfl m
        · exact s7fb_step_unit hn hQ hsep hm hη hQC hw hcx hcy T hxT hyT hlt
      hit := s7fb_hit hn hQ hsep hm hη hQC hw hcx hcy T hxT hyT hTimg hlt }

end S7FBReturn

/-! Part C — consequences of the bigon transport (the port of `namespace s7b_SlidingTransport`, with the
third summand): the carrier correspondence `Component Q T ≃ (Component λ₁ S₁ ⊕ Component λ₂ S₂) ⊕ Unit`,
the owners, the carrier crossings of the half carriers (`m_q = m_{qᵢ}`), and the contact triangle:
its marks are exactly `μ_M, y_ℓ, x_a`, it has no carrier crossing and exactly three corners. -/

section S7FBTransport

variable {Pc Q : LabelledTuple n} (hQ : Generic Q) (hsep : ContactSeparated M a)
  (hm : Pc M ∈ edgeInterior Pc a) {r η : ℝ} (hη : 0 < η)
  (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing Pc s))
  (hw : ContactParameterWindows Pc Q M a r η)
  (hg₁ : Generic (firstHalf Pc M a)) (hg₂ : Generic (secondHalf Pc M a))
  (hcx : IsCrossing Q {a, contactLeg false M}) (hcy : IsCrossing Q {a, contactLeg true M})
  (T : Finset (Crossing Q)) (S₁ : Finset (Crossing (firstHalf Pc M a)))
  (S₂ : Finset (Crossing (secondHalf Pc M a)))
  (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))

omit [NeZero n] in
/-- The cycle space of the identity on `Unit` is a point. -/
def s7fb_unitCycleEquiv : Quotient (Equiv.Perm.SameCycle.setoid (1 : Equiv.Perm Unit)) ≃ Unit where
  toFun _ := ()
  invFun _ := Quotient.mk _ ()
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h u => cases u; rfl
  right_inv u := by cases u; rfl

omit [NeZero n] in
theorem s7fb_unitCycleEquiv_mk (u : Unit) :
    s7fb_unitCycleEquiv (Quotient.mk (Equiv.Perm.SameCycle.setoid (1 : Equiv.Perm Unit)) u) = () := rfl

namespace s7fb_BigonTransport

variable {hn} {hQ} {hsep} {hm} {hQC} {hg₁} {hg₂} {hcx} {hcy} {T} {S₁} {S₂}
variable (hT : s7fb_BigonTransport hn hQ hsep hm hQC hg₁ hg₂ hcx hcy T S₁ S₂)
include hT

/-- **The carrier correspondence of a two-newborn row**: the carriers of `T` on `Q` are the carriers
of `S₁` on `λ₁`, those of `S₂` on `λ₂`, and the contact triangle. -/
def componentEquiv :
    Component hn hQ T ≃
      (Component (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ ⊕
        Component (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂) ⊕ Unit :=
  hT.ret.cycleEquiv.symm.trans ((s7b_sumCongr_cycleEquiv _ _).trans
    (Equiv.sumCongr (s7b_sumCongr_cycleEquiv _ _) s7fb_unitCycleEquiv))

theorem componentEquiv_owner_mark (b : (Mark (firstHalf Pc M a) ⊕ Mark (secondHalf Pc M a)) ⊕ Unit) :
    hT.componentEquiv (owner hn hQ T (s7fb_mark hn hsep hm hQC hcx hcy b)) =
      (Equiv.sumCongr (s7b_sumCongr_cycleEquiv _ _) s7fb_unitCycleEquiv)
        (s7b_sumCongr_cycleEquiv _ _ (Quotient.mk _ b)) := by
  have he : owner hn hQ T (s7fb_mark hn hsep hm hQC hcx hcy b) = hT.ret.cycleEquiv (Quotient.mk _ b) := rfl
  show (Equiv.sumCongr (s7b_sumCongr_cycleEquiv _ _) s7fb_unitCycleEquiv)
    (s7b_sumCongr_cycleEquiv _ _ (hT.ret.cycleEquiv.symm
      (owner hn hQ T (s7fb_mark hn hsep hm hQC hcx hcy b)))) = _
  rw [he, Equiv.symm_apply_apply]

theorem componentEquiv_owner_first (m : Mark (firstHalf Pc M a)) :
    hT.componentEquiv (owner hn hQ T (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl m)))) =
      Sum.inl (Sum.inl (owner (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ m)) := by
  rw [componentEquiv_owner_mark]; rfl

theorem componentEquiv_owner_second (m : Mark (secondHalf Pc M a)) :
    hT.componentEquiv (owner hn hQ T (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr m)))) =
      Sum.inl (Sum.inr (owner (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ m)) := by
  rw [componentEquiv_owner_mark]; rfl

/-- The carrier through the contact vertex `μ_M` is the triangle. -/
theorem componentEquiv_owner_M : hT.componentEquiv (owner hn hQ T (Sum.inl M)) = Sum.inr () := by
  have := hT.componentEquiv_owner_mark (Sum.inr ())
  rw [s7fb_mark_unit] at this
  rw [this]; rfl

theorem componentEquiv_owner_firstVisit (w : Visit (firstHalf Pc M a)) :
    hT.componentEquiv (owner hn hQ T (Sum.inr (s7b_firstVisitQ hn hsep hm hQC w))) =
      Sum.inl (Sum.inl (owner (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ (Sum.inr w))) :=
  hT.componentEquiv_owner_first (Sum.inr w)

theorem componentEquiv_owner_secondVisit (w : Visit (secondHalf Pc M a)) :
    hT.componentEquiv (owner hn hQ T (Sum.inr (s7b_secondVisitQ hn hsep hm hQC w))) =
      Sum.inl (Sum.inr (owner (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ (Sum.inr w))) :=
  hT.componentEquiv_owner_second (Sum.inr w)

/-- `λ₁`'s carrier through its vertex `0` is the carrier of `Q` through `y_a`. -/
theorem componentEquiv_owner_ya :
    hT.componentEquiv (owner hn hQ T (Sum.inr (s7e_va hcy))) =
      Sum.inl (Sum.inl (owner (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ (Sum.inl 0))) := by
  rw [← s7fb_mark_inl_inl_zero hn hsep hm hQC hcx hcy]; exact hT.componentEquiv_owner_first _

/-- `λ₂`'s carrier through its vertex `0` is the carrier of `Q` through `x_ℓ`. -/
theorem componentEquiv_owner_xl :
    hT.componentEquiv (owner hn hQ T (Sum.inr (s7e_vl hcx))) =
      Sum.inl (Sum.inr (owner (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ (Sum.inl 0))) := by
  rw [← s7fb_mark_inr_inl_zero hn hsep hm hQC hcx hcy]; exact hT.componentEquiv_owner_second _

/-! #### The triangle -/

include hη hw in
theorem owner_yl : owner hn hQ T (Sum.inr (s7e_vl hcy)) = owner hn hQ T (Sum.inl M) := by
  rw [← s7fb_succ_M hn hQ hsep hη hw hcx hcy T, owner_successor]

include hη hw hlt in
theorem owner_xa : owner hn hQ T (Sum.inr (s7e_va hcx)) = owner hn hQ T (Sum.inl M) := by
  rw [← s7fb_succ_yl hn hQ hsep hw hcx hcy T hT.y_mem hlt, owner_successor, hT.owner_yl hη hw]

include hη hw hlt in
/-- The forward orbit of `μ_M` is the triangle `{μ_M, y_ℓ, x_a}`. -/
theorem pow_M_mem (k : ℕ) :
    ((smoothingSuccessor hn hQ T) ^ k) (Sum.inl M : Mark Q) = Sum.inl M ∨
      ((smoothingSuccessor hn hQ T) ^ k) (Sum.inl M : Mark Q) = Sum.inr (s7e_vl hcy) ∨
      ((smoothingSuccessor hn hQ T) ^ k) (Sum.inl M : Mark Q) = Sum.inr (s7e_va hcx) := by
  induction k with
  | zero => left; simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    rcases ih with h | h | h <;> rw [h]
    · right; left; exact s7fb_succ_M hn hQ hsep hη hw hcx hcy T
    · right; right; exact s7fb_succ_yl hn hQ hsep hw hcx hcy T hT.y_mem hlt
    · left; exact s7fb_succ_xa hn hQ hsep hη hw hcx hcy T hT.x_mem

include hη hw hlt in
/-- The marks owned by the triangle are exactly `μ_M`, `y_ℓ`, `x_a`. -/
theorem owner_eq_M_iff (w : Mark Q) :
    owner hn hQ T w = owner hn hQ T (Sum.inl M) ↔
      w = Sum.inl M ∨ w = Sum.inr (s7e_vl hcy) ∨ w = Sum.inr (s7e_va hcx) := by
  constructor
  · intro h
    have hsc := (owner_eq_iff hn hQ T _ _).mp h.symm
    obtain ⟨k, -, hk⟩ := hsc.exists_pow_eq'
    rw [← hk]
    exact hT.pow_M_mem hη hw hlt k
  · rintro (rfl | rfl | rfl)
    · rfl
    · exact hT.owner_yl hη hw
    · exact hT.owner_xa hη hw hlt

/-- The triangle carrier `componentEquiv.symm (inr ())` is the carrier of `μ_M`. -/
theorem symm_inr_unit : hT.componentEquiv.symm (Sum.inr ()) = owner hn hQ T (Sum.inl M) := by
  rw [← hT.componentEquiv_owner_M, Equiv.symm_apply_apply]

include hη hw hlt in
/-- The triangle has no carrier crossing. -/
theorem carrierCrossings_M_eq_empty : carrierCrossings hn hQ T (owner hn hQ T (Sum.inl M)) = ∅ := by
  ext z
  simp only [Finset.notMem_empty, iff_false]
  intro hz
  rw [mem_carrierCrossings] at hz
  obtain ⟨i, j, hs, -, -⟩ := z.property
  have hi : i ∈ z.val := by rw [hs]; simp
  have hv := hz.2 ⟨z, ⟨i, hi⟩⟩ rfl
  rcases (hT.owner_eq_M_iff hη hw hlt _).mp hv with h | h | h
  · exact Sum.inr_ne_inl h
  · have h' : z = (s7e_vl hcy).1 := congrArg Sigma.fst (Sum.inr.inj h)
    rw [s7e_vl_fst] at h'
    exact hz.1 (h' ▸ hT.y_mem)
  · have h' : z = (s7e_va hcx).1 := congrArg Sigma.fst (Sum.inr.inj h)
    exact hz.1 (h' ▸ hT.x_mem)

include hη hw hlt in
theorem carrierCrossingCount_M : carrierCrossingCount hn hQ T (owner hn hQ T (Sum.inl M)) = 0 := by
  unfold carrierCrossingCount
  rw [hT.carrierCrossings_M_eq_empty hη hw hlt, Finset.card_empty]

include hη hw hlt in
/-- The corner list of the triangle has exactly the three marks `μ_M`, `y_ℓ`, `x_a`. -/
theorem mem_cornerList_M_iff (w : Mark Q) :
    w ∈ ccpCornerList hn hQ T (owner hn hQ T (Sum.inl M)) ↔
      w = Sum.inl M ∨ w = Sum.inr (s7e_vl hcy) ∨ w = Sum.inr (s7e_va hcx) := by
  rw [mem_ccpCornerList, hT.owner_eq_M_iff hη hw hlt]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rcases h with rfl | rfl | rfl
    · exact isTrueCorner_vertex T M
    · rw [isTrueCorner_visit, s7e_vl_fst]; exact hT.y_mem
    · rw [isTrueCorner_visit]; exact hT.x_mem

include hη hw hlt in
/-- **The triangle has three corners.** -/
theorem ccpCornerCount_M : ccpCornerCount hn hQ T (owner hn hQ T (Sum.inl M)) = 3 := by
  have hnd := ccpCornerList_nodup hn hQ T (owner hn hQ T (Sum.inl M))
  have hset : (ccpCornerList hn hQ T (owner hn hQ T (Sum.inl M))).toFinset =
      {(Sum.inl M : Mark Q), Sum.inr (s7e_vl hcy), Sum.inr (s7e_va hcx)} := by
    ext w
    rw [List.mem_toFinset, hT.mem_cornerList_M_iff hη hw hlt]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have hne1 : (Sum.inl M : Mark Q) ≠ Sum.inr (s7e_vl hcy) := Sum.inl_ne_inr
  have hne2 : (Sum.inl M : Mark Q) ≠ Sum.inr (s7e_va hcx) := Sum.inl_ne_inr
  have hne3 : (Sum.inr (s7e_vl hcy) : Mark Q) ≠ Sum.inr (s7e_va hcx) := by
    intro h
    have := congrArg (fun v : Visit Q => v.2.val) (Sum.inr.inj h)
    rw [s7fb_yl_edge, s7e_va_edge] at this
    exact s7e_a_ne_M hsep this.symm
  unfold ccpCornerCount
  rw [← List.toFinset_card_of_nodup hnd, hset, Finset.card_insert_of_notMem, Finset.card_pair hne3]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hne1, hne2⟩

/-! #### Every vertex of `Q` is an image mark -/

theorem inl_mem_range (i : ZMod n) :
    (Sum.inl i : Mark Q) ∈ Set.range (s7fb_mark hn hsep hm hQC hcx hcy) := by
  by_cases hiM : i = M
  · subst hiM; exact ⟨Sum.inr (), rfl⟩
  have hb := contactHalfSizes_bounds hn hsep
  set D := contactDistance M a with hD
  set d := (i - M).val with hd
  have hdn : d < n := ZMod.val_lt _
  have hd0 : d ≠ 0 := by
    intro h0
    exact hiM (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp h0))
  have hDn : D < n := ZMod.val_lt _
  have hcast : ((D : ℕ) : ZMod n) = a - M := contactDistance_cast M a
  rcases Nat.lt_or_ge D d with hDd | hdD
  · -- `i` lies on the second half: `i = a + (d − D)`, an edge label `j ≠ 0` of `λ₂`
    have h1 : firstHalfSize M a = D + 1 := rfl
    have h2 : secondHalfSize M a = n - D := rfl
    have hpos : 0 < n - D := by omega
    have : NeZero (secondHalfSize M a) := ⟨by rw [h2]; omega⟩
    let j : ZMod (secondHalfSize M a) := ((d - D : ℕ) : ZMod (secondHalfSize M a))
    have hjval : j.val = d - D := by
      show ((d - D : ℕ) : ZMod (secondHalfSize M a)).val = d - D
      rw [ZMod.val_natCast_of_lt]; rw [h2]; omega
    have hj0 : j ≠ 0 := by
      intro h; rw [← ZMod.val_eq_zero, hjval] at h; omega
    refine ⟨Sum.inl (Sum.inr (Sum.inl j)), ?_⟩
    rw [s7fb_mark_inr_inl hn hsep hm hQC hcx hcy hj0, secondHalfIndex_nonzero M a hj0]
    congr 1
    show a + ((j.val : ℕ) : ZMod n) = i
    rw [hjval, Nat.cast_sub hDd.le, hcast, hd, ZMod.natCast_zmod_val]
    ring
  · -- `i` lies on the first half: `i = M + d`, a vertex label `d ≠ 0` of `λ₁`
    have h1 : firstHalfSize M a = D + 1 := rfl
    have : NeZero (firstHalfSize M a) := ⟨by rw [h1]; omega⟩
    let i' : ZMod (firstHalfSize M a) := ((d : ℕ) : ZMod (firstHalfSize M a))
    have hival : i'.val = d := by
      show ((d : ℕ) : ZMod (firstHalfSize M a)).val = d
      rw [ZMod.val_natCast_of_lt]; rw [h1]; omega
    have hi0 : i' ≠ 0 := by
      intro h; rw [← ZMod.val_eq_zero, hival] at h; exact hd0 h
    refine ⟨Sum.inl (Sum.inl (Sum.inl i')), ?_⟩
    rw [s7fb_mark_inl_inl hn hsep hm hQC hcx hcy hi0]
    congr 1
    show M + ((i'.val : ℕ) : ZMod n) = i
    rw [hival, hd, ZMod.natCast_zmod_val]
    ring

/-! #### True corners across the map, and the off-image marks -/

theorem isTrueCorner_first (m : Mark (firstHalf Pc M a)) :
    IsTrueCorner T (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl m))) ↔ IsTrueCorner S₁ m := by
  cases m with
  | inl i =>
    by_cases hi : i = 0
    · subst hi
      rw [s7fb_mark_inl_inl_zero, isTrueCorner_visit]
      exact iff_of_true hT.y_mem (isTrueCorner_vertex S₁ 0)
    · rw [s7fb_mark_inl_inl hn hsep hm hQC hcx hcy hi]; exact Iff.rfl
  | inr v =>
    rw [s7fb_mark_inl_inr, isTrueCorner_visit, isTrueCorner_visit, s7b_firstVisitQ_fst, hT.first_pre, s7b_mem_pre]

theorem isTrueCorner_second (m : Mark (secondHalf Pc M a)) :
    IsTrueCorner T (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr m))) ↔ IsTrueCorner S₂ m := by
  cases m with
  | inl j =>
    by_cases hj : j = 0
    · subst hj
      rw [s7fb_mark_inr_inl_zero, isTrueCorner_visit, s7e_vl_fst]
      exact iff_of_true hT.x_mem (isTrueCorner_vertex S₂ 0)
    · rw [s7fb_mark_inr_inl hn hsep hm hQC hcx hcy hj]; exact Iff.rfl
  | inr v =>
    rw [s7fb_mark_inr_inr, isTrueCorner_visit, isTrueCorner_visit, s7b_secondVisitQ_fst, hT.second_pre,
      s7b_mem_pre]

include hη hw hlt in
/-- An off-image mark not owned by the triangle is a visit of a crossing off `T`: not a true corner. -/
theorem not_isTrueCorner_of_off_image (w : Mark Q)
    (hwr : w ∉ Set.range (s7fb_mark hn hsep hm hQC hcx hcy))
    (hnt : owner hn hQ T w ≠ owner hn hQ T (Sum.inl M)) : ¬ IsTrueCorner T w := by
  cases w with
  | inl i => exact absurd (hT.inl_mem_range i) hwr
  | inr w' =>
    rw [isTrueCorner_visit]
    intro hwT
    rcases s7fb_visit_cases hsep hcx hcy w' with h | h | h | h | h
    · subst h; exact hnt (hT.owner_xa hη hw hlt)
    · exact hwr ((s7fb_inr_mem_range_iff hn hsep hm hQC hcx hcy w').mpr (Or.inr (Or.inl h)))
    · exact hwr ((s7fb_inr_mem_range_iff hn hsep hm hQC hcx hcy w').mpr (Or.inl h))
    · subst h; exact hnt (hT.owner_yl hη hw)
    · have hwx : w'.1 ≠ (s7e_va hcx).1 := fun he => h (he ▸ s7fb_xa_affected hcx)
      have hwy : w'.1 ≠ (s7e_va hcy).1 := fun he => h (he ▸ s7fb_ya_affected hcy)
      rcases hT.img w'.1 hwT hwx hwy with ⟨c, hcw⟩ | ⟨c, hcw⟩
      · obtain ⟨v, -, hv⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC w' c hcw.symm
        exact hwr ((s7fb_inr_mem_range_iff hn hsep hm hQC hcx hcy w').mpr (Or.inr (Or.inr (Or.inl ⟨v, hv⟩))))
      · obtain ⟨v, -, hv⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC w' c hcw.symm
        exact hwr ((s7fb_inr_mem_range_iff hn hsep hm hQC hcx hcy w').mpr (Or.inr (Or.inr (Or.inr ⟨v, hv⟩))))

/-! #### Carrier crossings of the half carriers -/

theorem firstCrossingQ_mem_carrierCrossings_iff (c : Crossing (firstHalf Pc M a))
    (q : Component hn hQ T) (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inl q₁)) :
    s7b_firstCrossingQ hn hsep hm hQC c ∈ carrierCrossings hn hQ T q ↔
      c ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁ := by
  rw [mem_carrierCrossings, mem_carrierCrossings]
  have hmem : s7b_firstCrossingQ hn hsep hm hQC c ∈ T ↔ c ∈ S₁ := by
    rw [hT.first_pre, s7b_mem_pre]
  rw [hmem]
  refine and_congr Iff.rfl ⟨fun hall w hw => ?_, fun hall v hv => ?_⟩
  · have hv := hall (s7b_firstVisitQ hn hsep hm hQC w) (by rw [s7b_firstVisitQ_fst, hw])
    have := hT.componentEquiv_owner_firstVisit w
    rw [hv, hq] at this
    exact (Sum.inl.inj (Sum.inl.inj this)).symm
  · obtain ⟨w, hw, rfl⟩ := s7b_visit_of_firstCrossingQ hn hsep hm hQC v c hv
    apply hT.componentEquiv.injective
    rw [hT.componentEquiv_owner_firstVisit, hall w hw, hq]

theorem secondCrossingQ_mem_carrierCrossings_iff (c : Crossing (secondHalf Pc M a))
    (q : Component hn hQ T) (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inr q₂)) :
    s7b_secondCrossingQ hn hsep hm hQC c ∈ carrierCrossings hn hQ T q ↔
      c ∈ carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂ := by
  rw [mem_carrierCrossings, mem_carrierCrossings]
  have hmem : s7b_secondCrossingQ hn hsep hm hQC c ∈ T ↔ c ∈ S₂ := by
    rw [hT.second_pre, s7b_mem_pre]
  rw [hmem]
  refine and_congr Iff.rfl ⟨fun hall w hw => ?_, fun hall v hv => ?_⟩
  · have hv := hall (s7b_secondVisitQ hn hsep hm hQC w) (by rw [s7b_secondVisitQ_fst, hw])
    have := hT.componentEquiv_owner_secondVisit w
    rw [hv, hq] at this
    exact (Sum.inr.inj (Sum.inl.inj this)).symm
  · obtain ⟨w, hw, rfl⟩ := s7b_visit_of_secondCrossingQ hn hsep hm hQC v c hv
    apply hT.componentEquiv.injective
    rw [hT.componentEquiv_owner_secondVisit, hall w hw, hq]

theorem secondCrossingQ_notMem_carrierCrossings (c : Crossing (secondHalf Pc M a))
    (q : Component hn hQ T) (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inl q₁)) :
    s7b_secondCrossingQ hn hsep hm hQC c ∉ carrierCrossings hn hQ T q := by
  intro hc
  rw [mem_carrierCrossings] at hc
  obtain ⟨i, j, hs, -, -⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hv := hc.2 (s7b_secondVisitQ hn hsep hm hQC ⟨c, ⟨i, hi⟩⟩) rfl
  have := hT.componentEquiv_owner_secondVisit ⟨c, ⟨i, hi⟩⟩
  rw [hv, hq] at this
  exact Sum.inl_ne_inr (Sum.inl.inj this)

theorem firstCrossingQ_notMem_carrierCrossings (c : Crossing (firstHalf Pc M a))
    (q : Component hn hQ T) (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inr q₂)) :
    s7b_firstCrossingQ hn hsep hm hQC c ∉ carrierCrossings hn hQ T q := by
  intro hc
  rw [mem_carrierCrossings] at hc
  obtain ⟨i, j, hs, -, -⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hv := hc.2 (s7b_firstVisitQ hn hsep hm hQC ⟨c, ⟨i, hi⟩⟩) rfl
  have := hT.componentEquiv_owner_firstVisit ⟨c, ⟨i, hi⟩⟩
  rw [hv, hq] at this
  exact Sum.inr_ne_inl (Sum.inl.inj this)

/-- Under the bigon split, every carrier crossing of `T` is carried from a half: a crossing
interlacing `x ∈ T` has its two visits on different carriers (lem:carriers (iii)). -/
theorem carrierCrossings_mem_range
    (hsplit : s7f_BigonSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 hg₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 hg₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) (s7e_va hcx).1 (s7e_va hcy).1)
    (hS : IsDecomposition hn hQ T) (q : Component hn hQ T) {y : Crossing Q}
    (hy : y ∈ carrierCrossings hn hQ T q) :
    y ∈ Set.range (s7b_firstCrossingQ hn hsep hm hQC) ∪ Set.range (s7b_secondCrossingQ hn hsep hm hQC) := by
  rw [mem_carrierCrossings] at hy
  have hyx : y ≠ (s7e_va hcx).1 := fun he => hy.1 (he ▸ hT.x_mem)
  have hyy : y ≠ (s7e_va hcy).1 := fun he => hy.1 (he ▸ hT.y_mem)
  have hnot : ∀ z : Crossing Q, Interlaces hn hQ y z → z ∈ T → False := by
    intro z hz hzT
    have hN : y ∈ supportNeighbors hn hQ T := (mem_supportNeighbors hn hQ T y).mpr ⟨z, hzT, hz⟩
    obtain ⟨i, j, hs, -, -⟩ := y.property
    have hi : i ∈ y.val := by rw [hs]; simp
    have hsep' := (carriers_lemma hn hQ hS).neighbor_visits_separated y hN ⟨y, ⟨i, hi⟩⟩ rfl
    exact hsep' ((hy.2 ⟨y, ⟨i, hi⟩⟩ rfl).trans (hy.2 (visitTwin ⟨y, ⟨i, hi⟩⟩) rfl).symm)
  exact hsplit.x_split y hyx hyy (fun hI => hnot _ (interlaces_symm hn hQ hI) hT.x_mem)
    (fun hI => hnot _ hI hT.x_mem)

/-- **`m_q` of a carrier corresponding to a carrier of `λ₁`**: its crossings are the carried crossings
of the half carrier. -/
theorem carrierCrossings_eq_img_first
    (hsplit : s7f_BigonSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 hg₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 hg₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) (s7e_va hcx).1 (s7e_va hcy).1)
    (hS : IsDecomposition hn hQ T) (q : Component hn hQ T)
    (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inl q₁)) :
    carrierCrossings hn hQ T q =
      s7b_img (s7b_firstCrossingQ_injective hn hsep hm hQC)
        (carrierCrossings (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁) := by
  ext y
  rw [s7b_mem_img]
  constructor
  · intro hy
    rcases hT.carrierCrossings_mem_range hsplit hS q hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact ⟨c, (hT.firstCrossingQ_mem_carrierCrossings_iff c q q₁ hq).mp hy, rfl⟩
    · exact absurd hy (hT.secondCrossingQ_notMem_carrierCrossings c q q₁ hq)
  · rintro ⟨c, hc, rfl⟩
    exact (hT.firstCrossingQ_mem_carrierCrossings_iff c q q₁ hq).mpr hc

theorem carrierCrossings_eq_img_second
    (hsplit : s7f_BigonSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 hg₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 hg₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) (s7e_va hcx).1 (s7e_va hcy).1)
    (hS : IsDecomposition hn hQ T) (q : Component hn hQ T)
    (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inr q₂)) :
    carrierCrossings hn hQ T q =
      s7b_img (s7b_secondCrossingQ_injective hn hsep hm hQC)
        (carrierCrossings (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂) := by
  ext y
  rw [s7b_mem_img]
  constructor
  · intro hy
    rcases hT.carrierCrossings_mem_range hsplit hS q hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact absurd hy (hT.firstCrossingQ_notMem_carrierCrossings c q q₂ hq)
    · exact ⟨c, (hT.secondCrossingQ_mem_carrierCrossings_iff c q q₂ hq).mp hy, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact (hT.secondCrossingQ_mem_carrierCrossings_iff c q q₂ hq).mpr hc

end s7fb_BigonTransport

end S7FBTransport

/-! Part D — the ordered corner correspondence.  Along the first-return law, the corner cycle of a
half carrier `qᵢ` is carried onto the corner cycle of the corresponding carrier of `T` (the next
corner is the first true corner on the forward orbit, `ccp_corner_chain`; the off-image marks on the
orbit of an image mark are visits of crossings off `T`, hence never corners), so the corner list of
`Q`'s carrier is a rotation of the image of the half's corner list (`List.formPerm_eq_formPerm_iff`).
This gives the index bijection `ZMod k ≃ ZMod k₁` with `ccpCornerMark q j = ι (ccpCornerMark q₁ (j + s))`
used for the turns (weights) and for the corner-polygon family (rotation). -/

section S7FBCorners

variable {Pc Q : LabelledTuple n} (hQ : Generic Q) (hsep : ContactSeparated M a)
  (hm : Pc M ∈ edgeInterior Pc a) {r η : ℝ} (hη : 0 < η)
  (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing Pc s))
  (hw : ContactParameterWindows Pc Q M a r η)
  (hg₁ : Generic (firstHalf Pc M a)) (hg₂ : Generic (secondHalf Pc M a))
  (hcx : IsCrossing Q {a, contactLeg false M}) (hcy : IsCrossing Q {a, contactLeg true M})
  (T : Finset (Crossing Q)) (S₁ : Finset (Crossing (firstHalf Pc M a)))
  (S₂ : Finset (Crossing (secondHalf Pc M a)))
  (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))

omit [NeZero n] in
/-- `Cycle.next` depends on its point only (the membership proof is irrelevant); stated with an explicit
`DecidableEq` instance so that it unifies with the library's instance. -/
theorem s7fb_cycle_next_congr {α : Type*} (inst : DecidableEq α) (s : Cycle α) (hs : s.Nodup) {x y : α}
    (hxy : x = y) (hx : x ∈ s) (hy : y ∈ s) : @Cycle.next _ inst s hs x hx = @Cycle.next _ inst s hs y hy := by
  subst hxy; rfl

namespace s7fb_BigonTransport

variable {hn} {hQ} {hsep} {hm} {hQC} {hg₁} {hg₂} {hcx} {hcy} {T} {S₁} {S₂}
variable (hT : s7fb_BigonTransport hn hQ hsep hm hQC hg₁ hg₂ hcx hcy T S₁ S₂)
include hT

/-! #### Iterated steps -/

/-- Iterating the first-return steps of the first half: `g₁^m c` is reached from `ι c` in `K` steps whose
intermediate marks are off the image or images of intermediate `g₁`-iterates. -/
theorem pow_first (c : Mark (firstHalf Pc M a)) (m : ℕ) :
    ∃ K : ℕ, ((smoothingSuccessor hn hQ T) ^ K) (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl c))) =
        s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl
          (((smoothingSuccessor (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁) ^ m) c))) ∧
      (1 ≤ m → 1 ≤ K) ∧ (m = 0 → K = 0) ∧
      ∀ j : ℕ, 0 < j → j < K →
        ((smoothingSuccessor hn hQ T) ^ j) (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl c))) ∉
            Set.range (s7fb_mark hn hsep hm hQC hcx hcy) ∨
          ∃ r : ℕ, 1 ≤ r ∧ r < m ∧
            ((smoothingSuccessor hn hQ T) ^ j) (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl c))) =
              s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl
                (((smoothingSuccessor (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁) ^ r) c))) := by
  induction m with
  | zero =>
    exact ⟨0, by simp, fun h => absurd h (by omega), fun _ => rfl, fun j hj0 hj => absurd hj (by omega)⟩
  | succ m ih =>
    obtain ⟨K, hK, -, hK0, hint⟩ := ih
    obtain ⟨k, hk0, hk, hgap⟩ := hT.ret.step (Sum.inl (Sum.inl
      (((smoothingSuccessor (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁) ^ m) c)))
    have hk' : ((smoothingSuccessor hn hQ T) ^ k) (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl
        (((smoothingSuccessor (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁) ^ m) c)))) =
        s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl
          (((smoothingSuccessor (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁) ^ (m + 1)) c))) := by
      rw [hk, pow_succ', Equiv.Perm.mul_apply]; rfl
    have hshift : ∀ j : ℕ, ((smoothingSuccessor hn hQ T) ^ (K + j))
        (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl c))) =
        ((smoothingSuccessor hn hQ T) ^ j) (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl
          (((smoothingSuccessor (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁) ^ m) c)))) := by
      intro j
      rw [add_comm, pow_add, Equiv.Perm.mul_apply, hK]
    refine ⟨K + k, ?_, fun _ => by omega, fun h => absurd h (by omega), ?_⟩
    · rw [hshift, hk']
    · intro j hj0 hj
      rcases Nat.lt_or_ge j K with hjK | hjK
      · rcases hint j hj0 hjK with h | ⟨r, hr1, hrm, hr⟩
        · exact Or.inl h
        · exact Or.inr ⟨r, hr1, by omega, hr⟩
      · rcases Nat.eq_or_lt_of_le hjK with hjK' | hjK'
        · subst hjK'
          rcases Nat.eq_zero_or_pos m with hm0 | hm0
          · subst hm0
            -- `K = 0` contradicts `0 < j = K`
            exfalso
            have : K = 0 := hK0 rfl
            omega
          · right
            exact ⟨m, hm0, by omega, hK⟩
        · left
          obtain ⟨j', rfl⟩ : ∃ j', j = K + j' := ⟨j - K, by omega⟩
          rw [hshift]
          exact hgap j' (by omega) (by omega)

/-- Off-image marks on the orbit of a first-half image mark are not true corners of `T`. -/
theorem not_corner_of_orbit_first (hη : 0 < η) (hw : ContactParameterWindows Pc Q M a r η)
    (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))
    (c : Mark (firstHalf Pc M a)) (j : ℕ)
    (hoff : ((smoothingSuccessor hn hQ T) ^ j) (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl c))) ∉
      Set.range (s7fb_mark hn hsep hm hQC hcx hcy)) :
    ¬ IsTrueCorner T (((smoothingSuccessor hn hQ T) ^ j) (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl c)))) := by
  apply hT.not_isTrueCorner_of_off_image hη hw hlt _ hoff
  rw [ccp_pow_owner]
  intro h
  have h1 := hT.componentEquiv_owner_first c
  rw [h, hT.componentEquiv_owner_M] at h1
  exact Sum.inr_ne_inl h1

/-- The carrier of `T` corresponding to `q₁` is the owner of the image of any mark owned by `q₁`. -/
theorem owner_first_eq (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁) (q : Component hn hQ T)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inl q₁)) (c : Mark (firstHalf Pc M a))
    (hc : owner (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ c = q₁) :
    owner hn hQ T (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl c))) = q := by
  apply hT.componentEquiv.injective
  rw [hT.componentEquiv_owner_first, hc, hq]

/-- **The corner successor is carried** (first half): consecutive corners of `q₁` are carried to
consecutive corners of the corresponding carrier `q` of `T`. -/
theorem cornerMark_succ_first (hη : 0 < η) (hw : ContactParameterWindows Pc Q M a r η)
    (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))
    (hS : IsDecomposition hn hQ T) (hS₁ : IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁)
    (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁) (q : Component hn hQ T)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inl q₁))
    (j : ZMod (ccpCornerCount hn hQ T q)) (j₁ : ZMod (ccpCornerCount (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁))
    (hj : ccpCornerMark hn hQ T q j =
      s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl (ccpCornerMark (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁ j₁)))) :
    ccpCornerMark hn hQ T q (j + 1) =
      s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl
        (ccpCornerMark (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁ (j₁ + 1)))) := by
  set f := smoothingSuccessor hn hQ T
  set g₁ := smoothingSuccessor (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁
  set ι' : Mark (firstHalf Pc M a) → Mark Q := fun c => s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl c))
  set c := ccpCornerMark (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁ j₁ with hcdef
  have hc_owner : owner (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ c = q₁ := ccpCornerMark_owner _ hg₁ S₁ q₁ j₁
  have hc : IsTrueCorner S₁ c := ccpCornerMark_isTrueCorner _ hg₁ S₁ q₁ j₁
  have hqc : owner hn hQ T (ι' c) = q := hT.owner_first_eq q₁ q hq c hc_owner
  -- the chain in `λ₁`: `g₁^m c` is the next corner of `q₁`
  obtain ⟨m, hm1, hmc, hmint⟩ := ccp_corner_chain (contactHalfSizes_bounds hn hsep).1.1 hg₁ hS₁ q₁ c hc_owner hc
  have hmc' : (g₁ ^ m) c = ccpCornerMark (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁ (j₁ + 1) := by
    rw [ccpCornerMark_add_one]; exact hmc
  have hc'corner : IsTrueCorner S₁ ((g₁ ^ m) c) := by
    rw [hmc']; exact ccpCornerMark_isTrueCorner _ hg₁ S₁ q₁ (j₁ + 1)
  -- its transport to `Q`
  obtain ⟨K, hK, hK1, -, hKint⟩ := hT.pow_first c m
  have hK1' : 1 ≤ K := hK1 hm1
  have hKcorner : ∀ i : ℕ, 1 ≤ i → i < K → ¬ IsTrueCorner T ((f ^ i) (ι' c)) := by
    intro i hi1 hiK
    rcases hKint i hi1 hiK with h | ⟨r, hr1, hrm, hr⟩
    · exact hT.not_corner_of_orbit_first hη hw hlt c i h
    · show ¬ IsTrueCorner T ((f ^ i) (ι' c))
      rw [hr, hT.isTrueCorner_first]
      exact hmint r hr1 hrm
  -- the chain in `Q`: `f^m' (ι' c)` is the next corner of `q`
  obtain ⟨m', hm'1, hm'c, hm'int⟩ := ccp_corner_chain hn hQ hS q (ι' c) hqc ((hT.isTrueCorner_first c).mpr hc)
  have hm'c' : (f ^ m') (ι' c) = ccpCornerMark hn hQ T q (j + 1) := by
    rw [ccpCornerMark_add_one]
    exact hm'c.trans (s7fb_cycle_next_congr _ _ _ hj.symm _ _)
  have hnext_corner : IsTrueCorner T ((f ^ m') (ι' c)) := by
    rw [hm'c']; exact ccpCornerMark_isTrueCorner hn hQ T q (j + 1)
  -- the two chains have the same length
  have hKm : K = m' := by
    rcases lt_trichotomy K m' with h | h | h
    · exfalso
      apply hm'int K hK1' h
      show IsTrueCorner T ((f ^ K) (ι' c))
      rw [hK]
      exact (hT.isTrueCorner_first _).mpr hc'corner
    · exact h
    · exfalso
      exact hKcorner m' hm'1 h hnext_corner
  rw [← hm'c', ← hKm, hK, hmc']

/-! #### The corner list of a first-half carrier is a rotation of the image list -/

/-- Membership in the corner list of the carrier `q ↔ inl (inl q₁)`: exactly the images of the
corners of `q₁`. -/
theorem mem_cornerList_first_iff (hη : 0 < η) (hw : ContactParameterWindows Pc Q M a r η)
    (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))
    (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁) (q : Component hn hQ T)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inl q₁)) (z : Mark Q) :
    z ∈ ccpCornerList hn hQ T q ↔
      z ∈ (ccpCornerList (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁).map
        (fun c => s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl c))) := by
  rw [mem_ccpCornerList, List.mem_map]
  constructor
  · rintro ⟨hz, hzc⟩
    have hnt : owner hn hQ T z ≠ owner hn hQ T (Sum.inl M) := by
      rw [hz]; intro h
      have := hT.componentEquiv_owner_M
      rw [← h, hq] at this
      exact Sum.inl_ne_inr this
    by_cases hzr : z ∈ Set.range (s7fb_mark hn hsep hm hQC hcx hcy)
    · obtain ⟨b, rfl⟩ := hzr
      rcases b with (c | c) | u
      · refine ⟨c, ?_, rfl⟩
        rw [mem_ccpCornerList]
        refine ⟨?_, (hT.isTrueCorner_first c).mp hzc⟩
        have := hT.componentEquiv_owner_first c
        rw [hz, hq] at this
        exact (Sum.inl.inj (Sum.inl.inj this)).symm
      · exfalso
        have := hT.componentEquiv_owner_second c
        rw [hz, hq] at this
        exact Sum.inl_ne_inr (Sum.inl.inj this)
      · exfalso
        rw [s7fb_mark_unit] at hz hnt
        exact hnt rfl
    · exact absurd hzc (hT.not_isTrueCorner_of_off_image hη hw hlt z hzr hnt)
  · rintro ⟨c, hc, rfl⟩
    rw [mem_ccpCornerList] at hc
    exact ⟨hT.owner_first_eq q₁ q hq c hc.1, (hT.isTrueCorner_first c).mpr hc.2⟩

/-- **The corner list of `q ↔ inl (inl q₁)` is a rotation of the image of the corner list of `q₁`.** -/
theorem cornerList_first_rotated (hη : 0 < η) (hw : ContactParameterWindows Pc Q M a r η)
    (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))
    (hS : IsDecomposition hn hQ T) (hS₁ : IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁)
    (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁) (q : Component hn hQ T)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inl q₁)) :
    (ccpCornerList hn hQ T q).IsRotated
      ((ccpCornerList (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁).map
        (fun c => s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl c)))) := by
  set ι' : Mark (firstHalf Pc M a) → Mark Q := fun c => s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl c))
  have hι' : Function.Injective ι' := fun c c' h =>
    Sum.inl.inj (Sum.inl.inj (s7fb_mark_injective hn hsep hm hQC hcx hcy h))
  set L := ccpCornerList hn hQ T q with hL
  set L₁ := (ccpCornerList (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁).map ι' with hL₁
  have hLnd : L.Nodup := ccpCornerList_nodup hn hQ T q
  have hL₁nd : L₁.Nodup := (ccpCornerList_nodup _ hg₁ S₁ q₁).map hι'
  have hmem : ∀ z, z ∈ L ↔ z ∈ L₁ := hT.mem_cornerList_first_iff hη hw hlt q₁ q hq
  have hk : 3 ≤ L.length := ccpCornerCount_ge_three hn hQ hS q
  have h3 : Fact (1 < ccpCornerCount hn hQ T q) := ⟨by have : ccpCornerCount hn hQ T q = L.length := rfl; omega⟩
  have hk₁ : 3 ≤ (ccpCornerList (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁).length :=
    ccpCornerCount_ge_three _ hg₁ hS₁ q₁
  have h3₁ : Fact (1 < ccpCornerCount (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁) :=
    ⟨by have : ccpCornerCount (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁ =
        (ccpCornerList (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁).length := rfl; omega⟩
  have hperm : L.formPerm = L₁.formPerm := by
    ext z
    by_cases hz : z ∈ L
    · have hz₁ : z ∈ L₁ := (hmem z).mp hz
      -- `z = L[i]` and `z = ι' (list₁[i₁])`
      obtain ⟨i, hi, hzi⟩ := List.mem_iff_getElem.mp hz
      obtain ⟨c, hc, hzc⟩ := List.mem_map.mp hz₁
      obtain ⟨i₁, hi₁, hci⟩ := List.mem_iff_getElem.mp hc
      set j : ZMod (ccpCornerCount hn hQ T q) := (i : ZMod (ccpCornerCount hn hQ T q)) with hjdef
      set j₁ : ZMod (ccpCornerCount (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁) :=
        (i₁ : ZMod (ccpCornerCount (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁)) with hj₁def
      have hjval : j.val = i := ZMod.val_natCast_of_lt hi
      have hj₁val : j₁.val = i₁ := ZMod.val_natCast_of_lt hi₁
      have hmarkj : ccpCornerMark hn hQ T q j = z := by
        show L[j.val]'(ZMod.val_lt j) = z
        simp only [hjval, hzi]
      have hmarkj₁ : ccpCornerMark (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁ j₁ = c := by
        show (ccpCornerList (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁)[j₁.val]'(ZMod.val_lt j₁) = c
        simp only [hj₁val, hci]
      have hsucc := hT.cornerMark_succ_first hη hw hlt hS hS₁ q₁ q hq j j₁ (by rw [hmarkj, hmarkj₁]; exact hzc.symm)
      -- the successors as list entries
      have hval1 : (j + 1).val = (i + 1) % L.length := by
        rw [ZMod.val_add, hjval, ZMod.val_one]; rfl
      have hval1₁ : (j₁ + 1).val = (i₁ + 1) % (ccpCornerList (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁).length := by
        rw [ZMod.val_add, hj₁val, ZMod.val_one]; rfl
      have hi₁' : i₁ < L₁.length := by rw [hL₁, List.length_map]; exact hi₁
      have hL₁i : L₁[i₁]'hi₁' = z := by
        show (List.map ι' (ccpCornerList (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁))[i₁]'hi₁' = z
        simp only [List.getElem_map, hci, hzc]
      calc L.formPerm z = L.formPerm (L[i]'hi) := by rw [hzi]
        _ = L[(i + 1) % L.length]'(Nat.mod_lt _ (by omega)) := List.formPerm_apply_getElem L hLnd i hi
        _ = ccpCornerMark hn hQ T q (j + 1) := by
          show _ = L[(j + 1).val]'(ZMod.val_lt _)
          simp only [hval1]
        _ = ι' (ccpCornerMark (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁ (j₁ + 1)) := hsucc
        _ = ι' ((ccpCornerList (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁)[(i₁ + 1) %
              (ccpCornerList (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁).length]'
              (Nat.mod_lt _ (by omega))) := by
          show ι' ((ccpCornerList (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁)[(j₁ + 1).val]'(ZMod.val_lt _)) = _
          simp only [hval1₁]
        _ = L₁[(i₁ + 1) % L₁.length]'(Nat.mod_lt _ (by omega)) := by
          simp only [hL₁, List.getElem_map, List.length_map]
        _ = L₁.formPerm (L₁[i₁]'hi₁') := (List.formPerm_apply_getElem L₁ hL₁nd i₁ hi₁').symm
        _ = L₁.formPerm z := by rw [hL₁i]
    · have hz₁ : z ∉ L₁ := fun h => hz ((hmem z).mpr h)
      rw [List.formPerm_apply_of_notMem hz, List.formPerm_apply_of_notMem hz₁]
  rcases (List.formPerm_eq_formPerm_iff hLnd hL₁nd).mp hperm with h | ⟨h, -⟩
  · exact h
  · exfalso; omega

/-- **The corner marks correspond up to a cyclic shift** (first half): `ccpCornerMark q j = ι
(ccpCornerMark q₁ (j + s))`, and the corner counts agree. -/
theorem cornerMark_first_shift (hη : 0 < η) (hw : ContactParameterWindows Pc Q M a r η)
    (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))
    (hS : IsDecomposition hn hQ T) (hS₁ : IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁)
    (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁) (q : Component hn hQ T)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inl q₁)) :
    ccpCornerCount hn hQ T q = ccpCornerCount (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁ ∧
      ∃ s : ℕ, ∀ j : ZMod (ccpCornerCount hn hQ T q),
        ccpCornerMark hn hQ T q j =
          s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl
            (ccpCornerMark (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁
              ((j.val + s : ℕ) : ZMod (ccpCornerCount (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁))))) := by
  set ι' : Mark (firstHalf Pc M a) → Mark Q := fun c => s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl c))
  have hrot := (hT.cornerList_first_rotated hη hw hlt hS hS₁ q₁ q hq).symm
  obtain ⟨s, -, hs⟩ := List.isRotated_iff_mod.mp hrot
  have hlen : (ccpCornerList hn hQ T q).length =
      (ccpCornerList (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁).length := by
    rw [← hs, List.length_rotate, List.length_map]
  refine ⟨hlen, s, fun j => ?_⟩
  show (ccpCornerList hn hQ T q)[j.val]'(ZMod.val_lt j) =
    ι' ((ccpCornerList (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁)[
      (((j.val + s : ℕ) : ZMod (ccpCornerCount (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁))).val]'(ZMod.val_lt _))
  have hj : j.val < ((ccpCornerList (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁).map ι' |>.rotate s).length := by
    rw [hs]; exact ZMod.val_lt j
  have h1 : (ccpCornerList hn hQ T q)[j.val]'(ZMod.val_lt j) =
      ((ccpCornerList (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁).map ι' |>.rotate s)[j.val]'hj := by
    congr 1; exact hs.symm
  rw [h1, List.getElem_rotate, List.getElem_map]
  congr 2
  rw [List.length_map, ZMod.val_natCast]
  rfl


/-! #### The same for the second half -/

/-- Iterating the first-return steps of the second half: `g₁^m c` is reached from `ι c` in `K` steps whose
intermediate marks are off the image or images of intermediate `g₁`-iterates. -/
theorem pow_second (c : Mark (secondHalf Pc M a)) (m : ℕ) :
    ∃ K : ℕ, ((smoothingSuccessor hn hQ T) ^ K) (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr c))) =
        s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr
          (((smoothingSuccessor (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂) ^ m) c))) ∧
      (1 ≤ m → 1 ≤ K) ∧ (m = 0 → K = 0) ∧
      ∀ j : ℕ, 0 < j → j < K →
        ((smoothingSuccessor hn hQ T) ^ j) (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr c))) ∉
            Set.range (s7fb_mark hn hsep hm hQC hcx hcy) ∨
          ∃ r : ℕ, 1 ≤ r ∧ r < m ∧
            ((smoothingSuccessor hn hQ T) ^ j) (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr c))) =
              s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr
                (((smoothingSuccessor (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂) ^ r) c))) := by
  induction m with
  | zero =>
    exact ⟨0, by simp, fun h => absurd h (by omega), fun _ => rfl, fun j hj0 hj => absurd hj (by omega)⟩
  | succ m ih =>
    obtain ⟨K, hK, -, hK0, hint⟩ := ih
    obtain ⟨k, hk0, hk, hgap⟩ := hT.ret.step (Sum.inl (Sum.inr
      (((smoothingSuccessor (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂) ^ m) c)))
    have hk' : ((smoothingSuccessor hn hQ T) ^ k) (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr
        (((smoothingSuccessor (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂) ^ m) c)))) =
        s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr
          (((smoothingSuccessor (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂) ^ (m + 1)) c))) := by
      rw [hk, pow_succ', Equiv.Perm.mul_apply]; rfl
    have hshift : ∀ j : ℕ, ((smoothingSuccessor hn hQ T) ^ (K + j))
        (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr c))) =
        ((smoothingSuccessor hn hQ T) ^ j) (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr
          (((smoothingSuccessor (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂) ^ m) c)))) := by
      intro j
      rw [add_comm, pow_add, Equiv.Perm.mul_apply, hK]
    refine ⟨K + k, ?_, fun _ => by omega, fun h => absurd h (by omega), ?_⟩
    · rw [hshift, hk']
    · intro j hj0 hj
      rcases Nat.lt_or_ge j K with hjK | hjK
      · rcases hint j hj0 hjK with h | ⟨r, hr1, hrm, hr⟩
        · exact Or.inl h
        · exact Or.inr ⟨r, hr1, by omega, hr⟩
      · rcases Nat.eq_or_lt_of_le hjK with hjK' | hjK'
        · subst hjK'
          rcases Nat.eq_zero_or_pos m with hm0 | hm0
          · subst hm0
            -- `K = 0` contradicts `0 < j = K`
            exfalso
            have : K = 0 := hK0 rfl
            omega
          · right
            exact ⟨m, hm0, by omega, hK⟩
        · left
          obtain ⟨j', rfl⟩ : ∃ j', j = K + j' := ⟨j - K, by omega⟩
          rw [hshift]
          exact hgap j' (by omega) (by omega)

/-- Off-image marks on the orbit of a second-half image mark are not true corners of `T`. -/
theorem not_corner_of_orbit_second (hη : 0 < η) (hw : ContactParameterWindows Pc Q M a r η)
    (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))
    (c : Mark (secondHalf Pc M a)) (j : ℕ)
    (hoff : ((smoothingSuccessor hn hQ T) ^ j) (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr c))) ∉
      Set.range (s7fb_mark hn hsep hm hQC hcx hcy)) :
    ¬ IsTrueCorner T (((smoothingSuccessor hn hQ T) ^ j) (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr c)))) := by
  apply hT.not_isTrueCorner_of_off_image hη hw hlt _ hoff
  rw [ccp_pow_owner]
  intro h
  have h1 := hT.componentEquiv_owner_second c
  rw [h, hT.componentEquiv_owner_M] at h1
  exact Sum.inr_ne_inl h1

/-- The carrier of `T` corresponding to `q₂` is the owner of the image of any mark owned by `q₂`. -/
theorem owner_second_eq (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂) (q : Component hn hQ T)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inr q₂)) (c : Mark (secondHalf Pc M a))
    (hc : owner (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ c = q₂) :
    owner hn hQ T (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr c))) = q := by
  apply hT.componentEquiv.injective
  rw [hT.componentEquiv_owner_second, hc, hq]

/-- **The corner successor is carried** (second half): consecutive corners of `q₂` are carried to
consecutive corners of the corresponding carrier `q` of `T`. -/
theorem cornerMark_succ_second (hη : 0 < η) (hw : ContactParameterWindows Pc Q M a r η)
    (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))
    (hS : IsDecomposition hn hQ T) (hS₂ : IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂)
    (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂) (q : Component hn hQ T)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inr q₂))
    (j : ZMod (ccpCornerCount hn hQ T q)) (j₂ : ZMod (ccpCornerCount (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂))
    (hj : ccpCornerMark hn hQ T q j =
      s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr (ccpCornerMark (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂ j₂)))) :
    ccpCornerMark hn hQ T q (j + 1) =
      s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr
        (ccpCornerMark (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂ (j₂ + 1)))) := by
  set f := smoothingSuccessor hn hQ T
  set g₂ := smoothingSuccessor (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂
  set ι' : Mark (secondHalf Pc M a) → Mark Q := fun c => s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr c))
  set c := ccpCornerMark (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂ j₂ with hcdef
  have hc_owner : owner (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ c = q₂ := ccpCornerMark_owner _ hg₂ S₂ q₂ j₂
  have hc : IsTrueCorner S₂ c := ccpCornerMark_isTrueCorner _ hg₂ S₂ q₂ j₂
  have hqc : owner hn hQ T (ι' c) = q := hT.owner_second_eq q₂ q hq c hc_owner
  -- the chain in `λ₁`: `g₁^m c` is the next corner of `q₂`
  obtain ⟨m, hm1, hmc, hmint⟩ := ccp_corner_chain (contactHalfSizes_bounds hn hsep).2.1 hg₂ hS₂ q₂ c hc_owner hc
  have hmc' : (g₂ ^ m) c = ccpCornerMark (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂ (j₂ + 1) := by
    rw [ccpCornerMark_add_one]; exact hmc
  have hc'corner : IsTrueCorner S₂ ((g₂ ^ m) c) := by
    rw [hmc']; exact ccpCornerMark_isTrueCorner _ hg₂ S₂ q₂ (j₂ + 1)
  -- its transport to `Q`
  obtain ⟨K, hK, hK1, -, hKint⟩ := hT.pow_second c m
  have hK1' : 1 ≤ K := hK1 hm1
  have hKcorner : ∀ i : ℕ, 1 ≤ i → i < K → ¬ IsTrueCorner T ((f ^ i) (ι' c)) := by
    intro i hi1 hiK
    rcases hKint i hi1 hiK with h | ⟨r, hr1, hrm, hr⟩
    · exact hT.not_corner_of_orbit_second hη hw hlt c i h
    · show ¬ IsTrueCorner T ((f ^ i) (ι' c))
      rw [hr, hT.isTrueCorner_second]
      exact hmint r hr1 hrm
  -- the chain in `Q`: `f^m' (ι' c)` is the next corner of `q`
  obtain ⟨m', hm'1, hm'c, hm'int⟩ := ccp_corner_chain hn hQ hS q (ι' c) hqc ((hT.isTrueCorner_second c).mpr hc)
  have hm'c' : (f ^ m') (ι' c) = ccpCornerMark hn hQ T q (j + 1) := by
    rw [ccpCornerMark_add_one]
    exact hm'c.trans (s7fb_cycle_next_congr _ _ _ hj.symm _ _)
  have hnext_corner : IsTrueCorner T ((f ^ m') (ι' c)) := by
    rw [hm'c']; exact ccpCornerMark_isTrueCorner hn hQ T q (j + 1)
  -- the two chains have the same length
  have hKm : K = m' := by
    rcases lt_trichotomy K m' with h | h | h
    · exfalso
      apply hm'int K hK1' h
      show IsTrueCorner T ((f ^ K) (ι' c))
      rw [hK]
      exact (hT.isTrueCorner_second _).mpr hc'corner
    · exact h
    · exfalso
      exact hKcorner m' hm'1 h hnext_corner
  rw [← hm'c', ← hKm, hK, hmc']

/-! #### The corner list of a second-half carrier is a rotation of the image list -/

/-- Membership in the corner list of the carrier `q ↔ inl (inl q₂)`: exactly the images of the
corners of `q₂`. -/
theorem mem_cornerList_second_iff (hη : 0 < η) (hw : ContactParameterWindows Pc Q M a r η)
    (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))
    (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂) (q : Component hn hQ T)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inr q₂)) (z : Mark Q) :
    z ∈ ccpCornerList hn hQ T q ↔
      z ∈ (ccpCornerList (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂).map
        (fun c => s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr c))) := by
  rw [mem_ccpCornerList, List.mem_map]
  constructor
  · rintro ⟨hz, hzc⟩
    have hnt : owner hn hQ T z ≠ owner hn hQ T (Sum.inl M) := by
      rw [hz]; intro h
      have := hT.componentEquiv_owner_M
      rw [← h, hq] at this
      exact Sum.inl_ne_inr this
    by_cases hzr : z ∈ Set.range (s7fb_mark hn hsep hm hQC hcx hcy)
    · obtain ⟨b, rfl⟩ := hzr
      rcases b with (c | c) | u
      · exfalso
        have := hT.componentEquiv_owner_first c
        rw [hz, hq] at this
        exact Sum.inr_ne_inl (Sum.inl.inj this)
      · refine ⟨c, ?_, rfl⟩
        rw [mem_ccpCornerList]
        refine ⟨?_, (hT.isTrueCorner_second c).mp hzc⟩
        have := hT.componentEquiv_owner_second c
        rw [hz, hq] at this
        exact (Sum.inr.inj (Sum.inl.inj this)).symm
      · exfalso
        rw [s7fb_mark_unit] at hz hnt
        exact hnt rfl
    · exact absurd hzc (hT.not_isTrueCorner_of_off_image hη hw hlt z hzr hnt)
  · rintro ⟨c, hc, rfl⟩
    rw [mem_ccpCornerList] at hc
    exact ⟨hT.owner_second_eq q₂ q hq c hc.1, (hT.isTrueCorner_second c).mpr hc.2⟩

/-- **The corner list of `q ↔ inl (inl q₂)` is a rotation of the image of the corner list of `q₂`.** -/
theorem cornerList_second_rotated (hη : 0 < η) (hw : ContactParameterWindows Pc Q M a r η)
    (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))
    (hS : IsDecomposition hn hQ T) (hS₂ : IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂)
    (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂) (q : Component hn hQ T)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inr q₂)) :
    (ccpCornerList hn hQ T q).IsRotated
      ((ccpCornerList (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂).map
        (fun c => s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr c)))) := by
  set ι' : Mark (secondHalf Pc M a) → Mark Q := fun c => s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr c))
  have hι' : Function.Injective ι' := fun c c' h =>
    Sum.inr.inj (Sum.inl.inj (s7fb_mark_injective hn hsep hm hQC hcx hcy h))
  set L := ccpCornerList hn hQ T q with hL
  set L₂ := (ccpCornerList (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂).map ι' with hL₂
  have hLnd : L.Nodup := ccpCornerList_nodup hn hQ T q
  have hL₂nd : L₂.Nodup := (ccpCornerList_nodup _ hg₂ S₂ q₂).map hι'
  have hmem : ∀ z, z ∈ L ↔ z ∈ L₂ := hT.mem_cornerList_second_iff hη hw hlt q₂ q hq
  have hk : 3 ≤ L.length := ccpCornerCount_ge_three hn hQ hS q
  have h3 : Fact (1 < ccpCornerCount hn hQ T q) := ⟨by have : ccpCornerCount hn hQ T q = L.length := rfl; omega⟩
  have hk₂ : 3 ≤ (ccpCornerList (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂).length :=
    ccpCornerCount_ge_three _ hg₂ hS₂ q₂
  have h3₂ : Fact (1 < ccpCornerCount (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂) :=
    ⟨by have : ccpCornerCount (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂ =
        (ccpCornerList (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂).length := rfl; omega⟩
  have hperm : L.formPerm = L₂.formPerm := by
    ext z
    by_cases hz : z ∈ L
    · have hz₂ : z ∈ L₂ := (hmem z).mp hz
      -- `z = L[i]` and `z = ι' (list₁[i₂])`
      obtain ⟨i, hi, hzi⟩ := List.mem_iff_getElem.mp hz
      obtain ⟨c, hc, hzc⟩ := List.mem_map.mp hz₂
      obtain ⟨i₂, hi₂, hci⟩ := List.mem_iff_getElem.mp hc
      set j : ZMod (ccpCornerCount hn hQ T q) := (i : ZMod (ccpCornerCount hn hQ T q)) with hjdef
      set j₂ : ZMod (ccpCornerCount (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂) :=
        (i₂ : ZMod (ccpCornerCount (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂)) with hj₂def
      have hjval : j.val = i := ZMod.val_natCast_of_lt hi
      have hj₂val : j₂.val = i₂ := ZMod.val_natCast_of_lt hi₂
      have hmarkj : ccpCornerMark hn hQ T q j = z := by
        show L[j.val]'(ZMod.val_lt j) = z
        simp only [hjval, hzi]
      have hmarkj₂ : ccpCornerMark (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂ j₂ = c := by
        show (ccpCornerList (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂)[j₂.val]'(ZMod.val_lt j₂) = c
        simp only [hj₂val, hci]
      have hsucc := hT.cornerMark_succ_second hη hw hlt hS hS₂ q₂ q hq j j₂ (by rw [hmarkj, hmarkj₂]; exact hzc.symm)
      -- the successors as list entries
      have hval1 : (j + 1).val = (i + 1) % L.length := by
        rw [ZMod.val_add, hjval, ZMod.val_one]; rfl
      have hval1₂ : (j₂ + 1).val = (i₂ + 1) % (ccpCornerList (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂).length := by
        rw [ZMod.val_add, hj₂val, ZMod.val_one]; rfl
      have hi₂' : i₂ < L₂.length := by rw [hL₂, List.length_map]; exact hi₂
      have hL₂i : L₂[i₂]'hi₂' = z := by
        show (List.map ι' (ccpCornerList (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂))[i₂]'hi₂' = z
        simp only [List.getElem_map, hci, hzc]
      calc L.formPerm z = L.formPerm (L[i]'hi) := by rw [hzi]
        _ = L[(i + 1) % L.length]'(Nat.mod_lt _ (by omega)) := List.formPerm_apply_getElem L hLnd i hi
        _ = ccpCornerMark hn hQ T q (j + 1) := by
          show _ = L[(j + 1).val]'(ZMod.val_lt _)
          simp only [hval1]
        _ = ι' (ccpCornerMark (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂ (j₂ + 1)) := hsucc
        _ = ι' ((ccpCornerList (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂)[(i₂ + 1) %
              (ccpCornerList (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂).length]'
              (Nat.mod_lt _ (by omega))) := by
          show ι' ((ccpCornerList (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂)[(j₂ + 1).val]'(ZMod.val_lt _)) = _
          simp only [hval1₂]
        _ = L₂[(i₂ + 1) % L₂.length]'(Nat.mod_lt _ (by omega)) := by
          simp only [hL₂, List.getElem_map, List.length_map]
        _ = L₂.formPerm (L₂[i₂]'hi₂') := (List.formPerm_apply_getElem L₂ hL₂nd i₂ hi₂').symm
        _ = L₂.formPerm z := by rw [hL₂i]
    · have hz₂ : z ∉ L₂ := fun h => hz ((hmem z).mpr h)
      rw [List.formPerm_apply_of_notMem hz, List.formPerm_apply_of_notMem hz₂]
  rcases (List.formPerm_eq_formPerm_iff hLnd hL₂nd).mp hperm with h | ⟨h, -⟩
  · exact h
  · exfalso; omega

/-- **The corner marks correspond up to a cyclic shift** (second half): `ccpCornerMark q j = ι
(ccpCornerMark q₂ (j + s))`, and the corner counts agree. -/
theorem cornerMark_second_shift (hη : 0 < η) (hw : ContactParameterWindows Pc Q M a r η)
    (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))
    (hS : IsDecomposition hn hQ T) (hS₂ : IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂)
    (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂) (q : Component hn hQ T)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inr q₂)) :
    ccpCornerCount hn hQ T q = ccpCornerCount (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂ ∧
      ∃ s : ℕ, ∀ j : ZMod (ccpCornerCount hn hQ T q),
        ccpCornerMark hn hQ T q j =
          s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr
            (ccpCornerMark (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂
              ((j.val + s : ℕ) : ZMod (ccpCornerCount (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂))))) := by
  set ι' : Mark (secondHalf Pc M a) → Mark Q := fun c => s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr c))
  have hrot := (hT.cornerList_second_rotated hη hw hlt hS hS₂ q₂ q hq).symm
  obtain ⟨s, -, hs⟩ := List.isRotated_iff_mod.mp hrot
  have hlen : (ccpCornerList hn hQ T q).length =
      (ccpCornerList (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂).length := by
    rw [← hs, List.length_rotate, List.length_map]
  refine ⟨hlen, s, fun j => ?_⟩
  show (ccpCornerList hn hQ T q)[j.val]'(ZMod.val_lt j) =
    ι' ((ccpCornerList (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂)[
      (((j.val + s : ℕ) : ZMod (ccpCornerCount (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂))).val]'(ZMod.val_lt _))
  have hj : j.val < ((ccpCornerList (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂).map ι' |>.rotate s).length := by
    rw [hs]; exact ZMod.val_lt j
  have h1 : (ccpCornerList hn hQ T q)[j.val]'(ZMod.val_lt j) =
      ((ccpCornerList (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂).map ι' |>.rotate s)[j.val]'hj := by
    congr 1; exact hs.symm
  rw [h1, List.getElem_rotate, List.getElem_map]
  congr 2
  rw [List.length_map, ZMod.val_natCast]
  rfl

end s7fb_BigonTransport

end S7FBCorners

/-! Part D (continued) — turns.  Chirotopes outside the contact triple persist from the centre to the
side (`ChirotopesOutsideZerosAgree`), so vertex turns and the crossing signs of persistent crossings
agree between `Q`, the centre and the halves (whose edges are the centre's, the cut edges positive
multiples of `E_a`); the two special corners `y_a ↦ λ₁`'s vertex `0` and `x_ℓ ↦ λ₂`'s vertex `0` are
compared directly through `chi_edge` and `Pc M = Pc a + r • E_a`. -/

section S7FBTurns

variable {Pc Q : LabelledTuple n} (hQ : Generic Q) (hsep : ContactSeparated M a)
  (hz : pointZeroTriples Pc = {contactSupport M a}) (hm : Pc M ∈ edgeInterior Pc a) {r η : ℝ}
  (hr : Pc M = edgePoint Pc a r) (hr0 : 0 < r) (hr1 : r < 1) (hη : 0 < η)
  (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing Pc s))
  (hw : ContactParameterWindows Pc Q M a r η)
  (hchi : ChirotopesOutsideZerosAgree Pc Q)
  (hg₁ : Generic (firstHalf Pc M a)) (hg₂ : Generic (secondHalf Pc M a))
  (hcx : IsCrossing Q {a, contactLeg false M}) (hcy : IsCrossing Q {a, contactLeg true M})

omit [NeZero n] in
/-- `det` is linear in its second argument (difference form). -/
theorem s7fb_det_sub_right (u v w : Plane) : det u (v - w) = det u v - det u w := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

omit [NeZero n] in
theorem s7fb_det_self (u : Plane) : det u u = 0 := by simp only [det]; ring

omit [NeZero n] in
/-- The sign of a difference of two reals of opposite strict signs is the sign of the first. -/
theorem s7fb_sign_sub_of_opposite {x y : ℝ} (h : SignType.sign y * SignType.sign x = -1) :
    SignType.sign (x - y) = SignType.sign x := by
  rcases SignType.trichotomy (SignType.sign y) with h₀ | h₀ | h₀ <;>
    rcases SignType.trichotomy (SignType.sign x) with h₁ | h₁ | h₁ <;>
    rw [h₀, h₁] at h <;> first | exact absurd h (by decide) | skip
  · have hy := sign_eq_neg_one_iff.mp h₀
    have hx := sign_eq_one_iff.mp h₁
    rw [h₁, sign_eq_one_iff]; linarith
  · have hy := sign_eq_one_iff.mp h₀
    have hx := sign_eq_neg_one_iff.mp h₁
    rw [h₁, sign_eq_neg_one_iff]; linarith

omit [NeZero n] in
theorem s7fb_sign_smul_pos {c : ℝ} (hc : 0 < c) (x : ℝ) : SignType.sign (c * x) = SignType.sign x := by
  rw [sign_mul, sign_pos hc, one_mul]

include hz hchi in
/-- Chirotope persistence for a triple other than the contact support. -/
theorem s7fb_chi_eq (i j k : ZMod n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hnot : ({i, j, k} : Finset (ZMod n)) ≠ contactSupport M a) : chi Q i j k = chi Pc i j k :=
  (hchi i j k hij hjk hik (by rw [hz, Finset.mem_singleton]; exact hnot)).1

include hn hsep hz hchi in
/-- Vertex turns of the side agree with the centre's. -/
theorem s7fb_turn_eq (i : ZMod n) : turn Q i = turn Pc i := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  exact s7fb_chi_eq hz hchi (i - 1) i (i + 1) (prev_ne_self i) (next_ne_self i).symm (prev_ne_next hn i)
    (fun h => contactSupport_ne_turnSupport hn hsep i h.symm)

include hn hsep in
/-- A triple `{e, e+1, k}` with `k` an endpoint label of a persistent remote pair `{e, f}` (`k = f` or
`k = f + 1`) is never the contact support. -/
theorem s7fb_triple_ne_contactSupport (e f : ZMod n) (hrem : remote e f)
    (hnot : ¬ ContactAffected M a {e, f}) (k : ZMod n) (hk : k = f ∨ k = f + 1) :
    ({e, e + 1, k} : Finset (ZMod n)) ≠ contactSupport M a := by
  intro heq
  obtain ⟨hfe, hfe1, hf1e, hf1e1⟩ := remote_endpoints e f hrem
  have hea : e = a := contactSupport_successive hn hsep (by rw [← heq]; simp) (by rw [← heq]; simp)
  have hkm : k ∈ contactSupport M a := by rw [← heq]; simp
  simp only [contactSupport, Finset.mem_insert, Finset.mem_singleton] at hkm
  rcases hkm with hkm | hkm | hkm
  · rcases hk with rfl | rfl
    · exact hfe (by rw [hkm, hea])
    · exact hf1e (by rw [hkm, hea])
  · rcases hk with rfl | rfl
    · exact hfe1 (by rw [hkm, hea])
    · exact hf1e1 (by rw [hkm, hea])
  · apply hnot
    rcases hk with rfl | rfl
    · right; rw [hea, hkm]
    · left; rw [hea, eq_sub_of_add_eq hkm]

include hn hQ hsep hz hchi in
/-- **Crossing signs of persistent crossings agree between the side and the centre**: through the
chirotopes `χ_{e,e+1,f}`, `χ_{e,e+1,f+1}` (opposite on `Q` by the crossing test, both persistent) and
`det(E_e, E_f) = det(E_e, P_{f+1} − P_e) − det(E_e, P_f − P_e)`. -/
theorem s7fb_crossingSign_centre (e f : ZMod n) (hc : IsCrossing Q {e, f})
    (hnot : ¬ ContactAffected M a {e, f}) :
    crossingSign Q e f = SignType.sign (det (edge Pc e) (edge Pc f)) := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  have hrem := crossing_pair_remote hc
  obtain ⟨hfe, hfe1, hf1e, hf1e1⟩ := remote_endpoints e f hrem
  have htest := (((crossing_test hn Q hQ.1).1 e f hrem).mp hc).1
  have h1 : chi Q e (e + 1) f = chi Pc e (e + 1) f :=
    s7fb_chi_eq hz hchi e (e + 1) f (next_ne_self e).symm hfe1.symm hfe.symm
      (s7fb_triple_ne_contactSupport hn hsep e f hrem hnot f (Or.inl rfl))
  have h2 : chi Q e (e + 1) (f + 1) = chi Pc e (e + 1) (f + 1) :=
    s7fb_chi_eq hz hchi e (e + 1) (f + 1) (next_ne_self e).symm hf1e1.symm hf1e.symm
      (s7fb_triple_ne_contactSupport hn hsep e f hrem hnot (f + 1) (Or.inr rfl))
  rw [s7a_crossingSign_eq_chi hn hQ.1 hc, h2]
  rw [h1, h2, chi_edge, chi_edge] at htest
  rw [chi_edge]
  have hE : det (edge Pc e) (edge Pc f) =
      det (edge Pc e) (Pc (f + 1) - Pc e) - det (edge Pc e) (Pc f - Pc e) := by
    rw [← s7fb_det_sub_right]
    congr 1
    simp only [edge]; abel
  rw [hE]
  exact (s7fb_sign_sub_of_opposite htest).symm

/-! #### The edges and turns of the halves against the centre -/

omit [NeZero n] in
include hr in
theorem s7fb_PcM_eq : Pc M = Pc a + r • edge Pc a := hr

include hr hr0 in
/-- The edges of `λ₁` are positive multiples of the centre's edges (the cut edge is `r • E_a`). -/
theorem s7fb_edge_first_smul (i : ZMod (firstHalfSize M a)) :
    ∃ c : ℝ, 0 < c ∧ edge (firstHalf Pc M a) i = c • edge Pc (firstHalfIndex M a i) := by
  by_cases hi : i = -1
  · subst hi
    refine ⟨r, hr0, ?_⟩
    show firstHalf Pc M a (-1 + 1) - firstHalf Pc M a (-1) = _
    rw [neg_add_cancel]
    show Pc (firstHalfIndex M a 0) - Pc (firstHalfIndex M a (-1)) = _
    rw [firstHalfIndex_zero, firstHalfIndex_last, hr]
    show Pc a + r • edge Pc a - Pc a = r • edge Pc a
    abel
  · exact ⟨1, one_pos, by rw [edge_firstHalf Pc M a hi, one_smul]⟩

include hn hsep hr hr1 in
/-- The edges of `λ₂` are positive multiples of the centre's edges (the cut edge is `(1 − r) • E_a`). -/
theorem s7fb_edge_second_smul (j : ZMod (secondHalfSize M a)) :
    ∃ c : ℝ, 0 < c ∧ edge (secondHalf Pc M a) j = c • edge Pc (secondHalfEdgeIndex M a j) := by
  by_cases hj : j = 0
  · subst hj
    refine ⟨1 - r, by linarith, ?_⟩
    show secondHalf Pc M a (0 + 1) - secondHalf Pc M a 0 = _
    rw [zero_add]
    show Pc (secondHalfIndex M a 1) - Pc (secondHalfIndex M a 0) = _
    have h0 : secondHalfIndex M a 0 = M := by simp [secondHalfIndex]
    rw [secondHalfIndex_one hn hsep, h0, secondHalfEdgeIndex_zero]
    show Pc (a + 1) - Pc M = (1 - r) • edge Pc a
    rw [hr]
    show Pc (a + 1) - (Pc a + r • edge Pc a) = (1 - r) • (Pc (a + 1) - Pc a)
    rw [sub_smul, one_smul]; abel
  · exact ⟨1, one_pos, by rw [edge_secondHalf Pc M a hj, one_smul]⟩

include hn hsep hr hr0 in
/-- The turn of `λ₁` at a vertex other than `0` is the centre's turn at the carried vertex. -/
theorem s7fb_turn_first (i : ZMod (firstHalfSize M a)) (hi : i ≠ 0) :
    turn (firstHalf Pc M a) i = turn Pc (firstHalfIndex M a i) := by
  have hb := (contactHalfSizes_bounds hn hsep).1.1
  have hfact : Fact (1 < firstHalfSize M a) := ⟨by omega⟩
  by_cases hi1 : i = -1
  · subst hi1
    -- the vertex `μ_a`: incoming `E_{a−1}`, outgoing the cut `r • E_a`
    have hprev : firstHalfIndex M a (-1 - 1) = a - 1 := by
      have h := firstHalfIndex_next M a (i := -1 - 1) (fun h => one_ne_zero (sub_eq_self.mp h))
      rw [sub_add_cancel, firstHalfIndex_last] at h
      exact eq_sub_of_add_eq h.symm
    rw [firstHalfIndex_last]
    show chi (firstHalf Pc M a) (-1 - 1) (-1) (-1 + 1) = chi Pc (a - 1) a (a + 1)
    rw [neg_add_cancel]
    show SignType.sign (det (Pc (firstHalfIndex M a (-1)) - Pc (firstHalfIndex M a (-1 - 1)))
      (Pc (firstHalfIndex M a 0) - Pc (firstHalfIndex M a (-1 - 1)))) = _
    rw [firstHalfIndex_last, firstHalfIndex_zero, hprev, hr]
    show SignType.sign (det (Pc a - Pc (a - 1)) (Pc a + r • edge Pc a - Pc (a - 1))) =
      SignType.sign (det (Pc a - Pc (a - 1)) (Pc (a + 1) - Pc (a - 1)))
    have e1 : Pc a + r • edge Pc a - Pc (a - 1) = (Pc a - Pc (a - 1)) + r • edge Pc a := by abel
    have e2 : Pc (a + 1) - Pc (a - 1) = (Pc a - Pc (a - 1)) + edge Pc a := by simp only [edge]; abel
    rw [e1, e2, det_add_right, det_add_right, s7fb_det_self, zero_add, zero_add, det_smul_right,
      s7fb_sign_smul_pos hr0]
  · -- an interior vertex: the neighbours are carried too
    have hnext : firstHalfIndex M a (i + 1) = firstHalfIndex M a i + 1 := firstHalfIndex_next M a hi1
    have hprev : firstHalfIndex M a (i - 1) = firstHalfIndex M a i - 1 := by
      have h := firstHalfIndex_next M a (i := i - 1) (by
        intro h; apply hi; have := congrArg (· + 1) h; simp only [sub_add_cancel, neg_add_cancel] at this; exact this)
      rw [sub_add_cancel] at h
      exact eq_sub_of_add_eq h.symm
    show chi (firstHalf Pc M a) (i - 1) i (i + 1) = _
    show SignType.sign (det (Pc (firstHalfIndex M a i) - Pc (firstHalfIndex M a (i - 1)))
      (Pc (firstHalfIndex M a (i + 1)) - Pc (firstHalfIndex M a (i - 1)))) = _
    rw [hnext, hprev]
    rfl

include hn hsep hr hr1 in
/-- The turn of `λ₂` at a vertex other than `0` is the centre's turn at the carried vertex. -/
theorem s7fb_turn_second (j : ZMod (secondHalfSize M a)) (hj : j ≠ 0) :
    turn (secondHalf Pc M a) j = turn Pc (secondHalfEdgeIndex M a j) := by
  have hb := (contactHalfSizes_bounds hn hsep).2.1
  have hfact : Fact (1 < secondHalfSize M a) := ⟨by omega⟩
  have h1r : 0 < 1 - r := by linarith
  by_cases hj1 : j = 1
  · subst hj1
    -- the vertex `μ_{a+1}`: incoming the cut `(1 − r) • E_a`, outgoing `E_{a+1}`
    have h2 : secondHalfIndex M a (1 + 1) = a + 1 + 1 := by
      rw [secondHalfIndex_next M a one_ne_zero, ← secondHalfIndex_nonzero M a one_ne_zero,
        secondHalfIndex_one hn hsep]
    have h1' : secondHalfEdgeIndex M a 1 = a + 1 := by
      rw [← secondHalfIndex_nonzero M a one_ne_zero, secondHalfIndex_one hn hsep]
    rw [h1']
    show chi (secondHalf Pc M a) (1 - 1) 1 (1 + 1) = chi Pc (a + 1 - 1) (a + 1) (a + 1 + 1)
    rw [sub_self, add_sub_cancel_right]
    show SignType.sign (det (Pc (secondHalfIndex M a 1) - Pc (secondHalfIndex M a 0))
      (Pc (secondHalfIndex M a (1 + 1)) - Pc (secondHalfIndex M a 0))) = _
    have h0 : secondHalfIndex M a 0 = M := by simp [secondHalfIndex]
    rw [secondHalfIndex_one hn hsep, h2, h0]
    show SignType.sign (det (Pc (a + 1) - Pc M) (Pc (a + 1 + 1) - Pc M)) =
      SignType.sign (det (Pc (a + 1) - Pc a) (Pc (a + 1 + 1) - Pc a))
    rw [hr]
    have e1 : Pc (a + 1) - (Pc a + r • edge Pc a) = (1 - r) • edge Pc a := by
      simp only [edge, sub_smul, one_smul]; abel
    have e2 : Pc (a + 1 + 1) - (Pc a + r • edge Pc a) = edge Pc (a + 1) + (1 - r) • edge Pc a := by
      simp only [edge, sub_smul, one_smul]; abel
    have e3 : Pc (a + 1 + 1) - Pc a = edge Pc (a + 1) + edge Pc a := by simp only [edge]; abel
    show SignType.sign (det (Pc (a + 1) - edgePoint Pc a r) (Pc (a + 1 + 1) - edgePoint Pc a r)) = _
    show SignType.sign (det (Pc (a + 1) - (Pc a + r • edge Pc a)) (Pc (a + 1 + 1) - (Pc a + r • edge Pc a))) = _
    have e0 : Pc (a + 1) - Pc a = edge Pc a := rfl
    rw [e1, e2, e3, e0]
    simp only [det_add_right, det_smul_left, s7fb_det_self, add_zero]
    exact s7fb_sign_smul_pos h1r _
  · -- a vertex `μ_{a+j}` with `j ≠ 0, 1`: both neighbours are carried (for `j = −1` the successor is `μ_M`)
    have hnext : secondHalfIndex M a (j + 1) = secondHalfEdgeIndex M a j + 1 := secondHalfIndex_next M a hj
    have hprev' : secondHalfIndex M a (j - 1) = secondHalfEdgeIndex M a j - 1 := by
      have hj1' : j - 1 ≠ 0 := fun h => hj1 (by linear_combination h)
      have h := secondHalfIndex_next M a hj1'
      rw [sub_add_cancel, secondHalfIndex_nonzero M a hj] at h
      rw [secondHalfIndex_nonzero M a hj1']
      exact eq_sub_of_add_eq h.symm
    show chi (secondHalf Pc M a) (j - 1) j (j + 1) = _
    show SignType.sign (det (Pc (secondHalfIndex M a j) - Pc (secondHalfIndex M a (j - 1)))
      (Pc (secondHalfIndex M a (j + 1)) - Pc (secondHalfIndex M a (j - 1)))) = _
    rw [hnext, hprev', secondHalfIndex_nonzero M a hj]
    rfl

end S7FBTurns

section S7FBWeights

variable {Pc Q : LabelledTuple n} (hQ : Generic Q) (hsep : ContactSeparated M a)
  (hz : pointZeroTriples Pc = {contactSupport M a}) (hm : Pc M ∈ edgeInterior Pc a) {r η : ℝ}
  (hr : Pc M = edgePoint Pc a r) (hr0 : 0 < r) (hr1 : r < 1) (hη : 0 < η)
  (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing Pc s))
  (hw : ContactParameterWindows Pc Q M a r η)
  (hchi : ChirotopesOutsideZerosAgree Pc Q)
  (hg₁ : Generic (firstHalf Pc M a)) (hg₂ : Generic (secondHalf Pc M a))
  (hcx : IsCrossing Q {a, contactLeg false M}) (hcy : IsCrossing Q {a, contactLeg true M})
  (T : Finset (Crossing Q)) (S₁ : Finset (Crossing (firstHalf Pc M a)))
  (S₂ : Finset (Crossing (secondHalf Pc M a)))
  (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))

omit [NeZero n] in
theorem s7fb_hcx' (hcx : IsCrossing Q {a, contactLeg false M}) : IsCrossing Q {a, M - 1} := by
  have h := hcx; rw [s7fb_leg_false] at h; exact h

omit [NeZero n] in
theorem s7fb_hcy' (hcy : IsCrossing Q {a, contactLeg true M}) : IsCrossing Q {a, M} := by
  have h := hcy; rw [s7fb_leg_true] at h; exact h

omit [NeZero n] in
include hr in
/-- `P M − P a = r • E_a` at the centre. -/
theorem s7fb_PcM_sub : Pc M - Pc a = r • edge Pc a := by
  have : Pc M = Pc a + r • edge Pc a := hr
  rw [this]; exact add_sub_cancel_left _ _

omit [NeZero n] in
include hr in
/-- `P_{M+1} − P_a = E_M + r • E_a` at the centre. -/
theorem s7fb_PcM1_sub : Pc (M + 1) - Pc a = edge Pc M + r • edge Pc a := by
  rw [← s7fb_PcM_sub hr, ← sub_add_sub_cancel (Pc (M + 1)) (Pc M) (Pc a)]; rfl

omit [NeZero n] in
include hr in
/-- `P_{a+1} − P_M = (1 − r) • E_a` at the centre. -/
theorem s7fb_Pca1_sub : Pc (a + 1) - Pc M = (1 - r) • edge Pc a := by
  have : Pc M = Pc a + r • edge Pc a := hr
  rw [this, sub_smul, one_smul, sub_add_eq_sub_sub]; rfl

omit [NeZero n] in
include hr in
/-- `P_{a+1} − P_{M−1} = E_{M−1} + (1 − r) • E_a` at the centre. -/
theorem s7fb_Pca1_sub_pred : Pc (a + 1) - Pc (M - 1) = edge Pc (M - 1) + (1 - r) • edge Pc a := by
  have e0 : Pc M - Pc (M - 1) = edge Pc (M - 1) := by simp only [edge, sub_add_cancel]
  rw [← sub_add_sub_cancel (Pc (a + 1)) (Pc M) (Pc (M - 1)), s7fb_Pca1_sub hr, e0, add_comm]

include hn hQ hsep hz hr hr0 hchi in
/-- **The turn at `y_a` on `Q` is `λ₁`'s turn at its vertex `0`**: both are `sgn det(E_a, E_M)` at the
centre (`χ_{a,a+1,M+1}` persists; `P_{M+1} − P_a = E_M + r E_a`). -/
theorem s7fb_markTurn_ya : markTurn Q (Sum.inr (s7e_va hcy)) = turn (firstHalf Pc M a) 0 := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  have hb := (contactHalfSizes_bounds hn hsep).1.1
  have hfact : Fact (1 < firstHalfSize M a) := ⟨by omega⟩
  -- the left side: `crossingSign Q a M = χ_{a,a+1,M+1}(Q) = χ_{a,a+1,M+1}(Pc)`
  have hL : markTurn Q (Sum.inr (s7e_va hcy)) = SignType.sign (det (edge Pc a) (edge Pc M)) := by
    rw [markTurn_inr, s7e_twin_va hcy (s7e_a_ne_leg true hsep), s7e_va_edge, s7fb_yl_edge,
      s7a_crossingSign_eq_chi hn hQ.1 (s7fb_hcy' hcy)]
    have hne1 : a ≠ a + 1 := (next_ne_self a).symm
    have hne2 : a + 1 ≠ M + 1 := fun h => hsep.2.1 (add_right_cancel h).symm
    have hne3 : a ≠ M + 1 := fun h => hsep.1 (by rw [h]; ring)
    have hnot : ({a, a + 1, M + 1} : Finset (ZMod n)) ≠ contactSupport M a := by
      intro heq
      have hm1 : M + 1 ∈ contactSupport M a := by rw [← heq]; simp
      simp only [contactSupport, Finset.mem_insert, Finset.mem_singleton] at hm1
      rcases hm1 with h | h | h
      · exact hne3 h.symm
      · exact hne2 h.symm
      · exact next_ne_self M h
    rw [s7fb_chi_eq hz hchi a (a + 1) (M + 1) hne1 hne2 hne3 hnot, chi_edge, s7fb_PcM1_sub hr]
    simp only [det_add_right, det_smul_right, s7fb_det_self, mul_zero, add_zero]
  -- the right side: `λ₁`'s vertex `0 = P M` between the cut `[μ_a, P M]` and `E_M`
  have hR : turn (firstHalf Pc M a) 0 = SignType.sign (det (edge Pc a) (edge Pc M)) := by
    have h1 : firstHalfIndex M a (0 + 1) = M + 1 := by
      rw [firstHalfIndex_next M a (s7b_zero_ne_neg_one (by omega)), firstHalfIndex_zero]
    show chi (firstHalf Pc M a) (0 - 1) 0 (0 + 1) = _
    rw [zero_sub]
    show SignType.sign (det (Pc (firstHalfIndex M a 0) - Pc (firstHalfIndex M a (-1)))
      (Pc (firstHalfIndex M a (0 + 1)) - Pc (firstHalfIndex M a (-1)))) = _
    rw [firstHalfIndex_zero, firstHalfIndex_last, h1, s7fb_PcM_sub hr, s7fb_PcM1_sub hr]
    simp only [det_add_right, det_smul_left, s7fb_det_self, add_zero]
    exact s7fb_sign_smul_pos hr0 _
  rw [hL, hR]

include hn hQ hsep hz hr hr1 hchi in
/-- **The turn at `x_ℓ` on `Q` is `λ₂`'s turn at its vertex `0`**: both are `sgn det(E_{M−1}, E_a)` at
the centre. -/
theorem s7fb_markTurn_xl : markTurn Q (Sum.inr (s7e_vl hcx)) = turn (secondHalf Pc M a) 0 := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  have hb := (contactHalfSizes_bounds hn hsep).2.1
  have hfact : Fact (1 < secondHalfSize M a) := ⟨by omega⟩
  have h1r : 0 < 1 - r := by linarith
  have e0 : Pc M - Pc (M - 1) = edge Pc (M - 1) := by simp only [edge, sub_add_cancel]
  have hL : markTurn Q (Sum.inr (s7e_vl hcx)) = SignType.sign (det (edge Pc (M - 1)) (edge Pc a)) := by
    have hc' : IsCrossing Q {M - 1, a} := by rw [Finset.pair_comm]; exact s7fb_hcx' hcx
    rw [markTurn_inr, s7e_twin_vl hcx (s7e_a_ne_leg false hsep), s7e_va_edge, s7fb_xl_edge,
      s7a_crossingSign_eq_chi hn hQ.1 hc', sub_add_cancel]
    have hne1 : M - 1 ≠ M := prev_ne_self M
    have hne2 : M ≠ a + 1 := hsep.2.2.1
    have hne3 : M - 1 ≠ a + 1 := fun h => hsep.2.2.2 (by rw [← sub_add_cancel M 1, h]; ring)
    have hnot : ({M - 1, M, a + 1} : Finset (ZMod n)) ≠ contactSupport M a := by
      intro heq
      have hm1 : M - 1 ∈ contactSupport M a := by rw [← heq]; simp
      simp only [contactSupport, Finset.mem_insert, Finset.mem_singleton] at hm1
      rcases hm1 with h | h | h
      · exact hsep.2.2.1 (by rw [← h]; ring)
      · exact hne3 h
      · exact hne1 h
    rw [s7fb_chi_eq hz hchi (M - 1) M (a + 1) hne1 hne2 hne3 hnot]
    show SignType.sign (det (Pc M - Pc (M - 1)) (Pc (a + 1) - Pc (M - 1))) = _
    rw [e0, s7fb_Pca1_sub_pred hr]
    simp only [det_add_right, det_smul_right, s7fb_det_self, zero_add]
    exact s7fb_sign_smul_pos h1r _
  have hR : turn (secondHalf Pc M a) 0 = SignType.sign (det (edge Pc (M - 1)) (edge Pc a)) := by
    have h0 : secondHalfIndex M a 0 = M := by simp [secondHalfIndex]
    have hneg : secondHalfIndex M a (-1) = M - 1 := by
      rw [secondHalfIndex_nonzero M a (neg_ne_zero.mpr one_ne_zero), secondHalfEdgeIndex_last]
    show chi (secondHalf Pc M a) (0 - 1) 0 (0 + 1) = _
    rw [zero_sub, zero_add]
    show SignType.sign (det (Pc (secondHalfIndex M a 0) - Pc (secondHalfIndex M a (-1)))
      (Pc (secondHalfIndex M a 1) - Pc (secondHalfIndex M a (-1)))) = _
    rw [h0, hneg, secondHalfIndex_one hn hsep, e0, s7fb_Pca1_sub_pred hr]
    simp only [det_add_right, det_smul_right, s7fb_det_self, zero_add]
    exact s7fb_sign_smul_pos h1r _
  rw [hL, hR]

namespace s7fb_BigonTransport

variable {hn} {hQ} {hsep} {hm} {hQC} {hg₁} {hg₂} {hcx} {hcy} {T} {S₁} {S₂}
variable (hT : s7fb_BigonTransport hn hQ hsep hm hQC hg₁ hg₂ hcx hcy T S₁ S₂)
include hT

/-- **Mark turns are carried from `λ₁`**: vertices by chirotope persistence, `λ₁`'s vertex `0 ↦ y_a`
by `s7fb_markTurn_ya`, carried visits by `s7fb_crossingSign_centre` and the positive scalings of the
half's edges. -/
theorem markTurn_first (hz : pointZeroTriples Pc = {contactSupport M a}) (hr : Pc M = edgePoint Pc a r)
    (hr0 : 0 < r) (hchi : ChirotopesOutsideZerosAgree Pc Q) (c : Mark (firstHalf Pc M a)) :
    markTurn Q (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl c))) = markTurn (firstHalf Pc M a) c := by
  cases c with
  | inl i =>
    by_cases hi : i = 0
    · subst hi
      rw [s7fb_mark_inl_inl_zero, markTurn_inl]
      exact s7fb_markTurn_ya hn hQ hsep hz hr hr0 hchi hcy
    · rw [s7fb_mark_inl_inl hn hsep hm hQC hcx hcy hi, markTurn_inl, markTurn_inl,
        s7fb_turn_eq hn hsep hz hchi, s7fb_turn_first hn hsep hr hr0 i hi]
  | inr v =>
    rw [s7fb_mark_inl_inr, markTurn_inr, markTurn_inr, ← s7b_firstVisitQ_visitTwin hn hsep hm hQC v,
      s7b_firstVisitQ_edge, s7b_firstVisitQ_edge]
    have hc : IsCrossing Q {firstHalfIndex M a v.2.val, firstHalfIndex M a (visitTwin v).2.val} := by
      have := s7a2_visit_isCrossing (s7b_firstVisitQ hn hsep hm hQC v)
      rwa [← s7b_firstVisitQ_visitTwin hn hsep hm hQC v, s7b_firstVisitQ_edge, s7b_firstVisitQ_edge] at this
    have hnot : ¬ ContactAffected M a {firstHalfIndex M a v.2.val, firstHalfIndex M a (visitTwin v).2.val} := by
      have := s7b_firstCrossingQ_not_affected hn hsep hm hQC v.1
      rwa [← s7b_firstVisitQ_fst hn hsep hm hQC v, visit_crossing_val_eq_pair (s7b_firstVisitQ hn hsep hm hQC v),
        ← s7b_firstVisitQ_visitTwin hn hsep hm hQC v, s7b_firstVisitQ_edge, s7b_firstVisitQ_edge] at this
    rw [s7fb_crossingSign_centre hn hQ hsep hz hchi _ _ hc hnot]
    obtain ⟨c₁, hc₁, he₁⟩ := s7fb_edge_first_smul hr hr0 v.2.val
    obtain ⟨c₂, hc₂, he₂⟩ := s7fb_edge_first_smul hr hr0 (visitTwin v).2.val
    unfold crossingSign
    rw [he₁, he₂, det_smul_left, det_smul_right, s7fb_sign_smul_pos hc₁, s7fb_sign_smul_pos hc₂]

/-- **Mark turns are carried from `λ₂`**. -/
theorem markTurn_second (hz : pointZeroTriples Pc = {contactSupport M a}) (hr : Pc M = edgePoint Pc a r)
    (hr1 : r < 1) (hchi : ChirotopesOutsideZerosAgree Pc Q) (c : Mark (secondHalf Pc M a)) :
    markTurn Q (s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr c))) = markTurn (secondHalf Pc M a) c := by
  cases c with
  | inl j =>
    by_cases hj : j = 0
    · subst hj
      rw [s7fb_mark_inr_inl_zero, markTurn_inl]
      exact s7fb_markTurn_xl hn hQ hsep hz hr hr1 hchi hcx
    · rw [s7fb_mark_inr_inl hn hsep hm hQC hcx hcy hj, markTurn_inl, markTurn_inl,
        s7fb_turn_eq hn hsep hz hchi, secondHalfIndex_nonzero M a hj, s7fb_turn_second hn hsep hr hr1 j hj]
  | inr v =>
    rw [s7fb_mark_inr_inr, markTurn_inr, markTurn_inr, ← s7b_secondVisitQ_visitTwin hn hsep hm hQC v,
      s7b_secondVisitQ_edge, s7b_secondVisitQ_edge]
    have hc : IsCrossing Q {secondHalfEdgeIndex M a v.2.val, secondHalfEdgeIndex M a (visitTwin v).2.val} := by
      have := s7a2_visit_isCrossing (s7b_secondVisitQ hn hsep hm hQC v)
      rwa [← s7b_secondVisitQ_visitTwin hn hsep hm hQC v, s7b_secondVisitQ_edge, s7b_secondVisitQ_edge] at this
    have hnot : ¬ ContactAffected M a
        {secondHalfEdgeIndex M a v.2.val, secondHalfEdgeIndex M a (visitTwin v).2.val} := by
      have := s7b_secondCrossingQ_not_affected hn hsep hm hQC v.1
      rwa [← s7b_secondVisitQ_fst hn hsep hm hQC v, visit_crossing_val_eq_pair (s7b_secondVisitQ hn hsep hm hQC v),
        ← s7b_secondVisitQ_visitTwin hn hsep hm hQC v, s7b_secondVisitQ_edge, s7b_secondVisitQ_edge] at this
    rw [s7fb_crossingSign_centre hn hQ hsep hz hchi _ _ hc hnot]
    obtain ⟨c₁, hc₁, he₁⟩ := s7fb_edge_second_smul hn hsep hr hr1 v.2.val
    obtain ⟨c₂, hc₂, he₂⟩ := s7fb_edge_second_smul hn hsep hr hr1 (visitTwin v).2.val
    unfold crossingSign
    rw [he₁, he₂, det_smul_left, det_smul_right, s7fb_sign_smul_pos hc₁, s7fb_sign_smul_pos hc₂]

/-! #### The carrier weights of the half carriers -/

/-- **`wt(q) = wt(q₁)`** for `q ↔ inl (inl q₁)`: the corner turns correspond along the index shift. -/
theorem carrierWeight_first (hz : pointZeroTriples Pc = {contactSupport M a}) (hr : Pc M = edgePoint Pc a r)
    (hr0 : 0 < r) (hη : 0 < η) (hw : ContactParameterWindows Pc Q M a r η)
    (hchi : ChirotopesOutsideZerosAgree Pc Q)
    (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))
    (hS : IsDecomposition hn hQ T) (hS₁ : IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁)
    (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁) (q : Component hn hQ T)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inl q₁)) :
    carrierWeight hn hQ T q = carrierWeight (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁ := by
  obtain ⟨hk, s, hs⟩ := hT.cornerMark_first_shift hη hw hlt hS hS₁ q₁ q hq
  set f : ZMod (ccpCornerCount hn hQ T q) → ZMod (ccpCornerCount (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁) :=
    fun j => ((j.val + s : ℕ) : ZMod _) with hf
  have hinj : Function.Injective f := by
    intro j j' h
    apply ccpCornerMark_injective hn hQ T q
    rw [hs j, hs j']
    show s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl (ccpCornerMark _ hg₁ S₁ q₁ (f j)))) =
      s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inl (ccpCornerMark _ hg₁ S₁ q₁ (f j'))))
    rw [h]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by rw [ZMod.card, ZMod.card, hk]⟩
  have hturn : ∀ j, turn (ccpCornerPolygon (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁) (f j) =
      turn (ccpCornerPolygon hn hQ T q) j := by
    intro j
    rw [turn_ccpCornerPolygon_eq_markTurn hn hQ hS q j, turn_ccpCornerPolygon_eq_markTurn _ hg₁ hS₁ q₁ (f j),
      hs j]
    exact (hT.markTurn_first hz hr hr0 hchi _).symm
  rw [s7c_carrierWeight_eq_sel, s7c_carrierWeight_eq_sel]
  congr 1
  unfold s7c_turns
  exact s7c_map_univ_eq_of_equiv _ _ (Equiv.ofBijective f hbij) hturn

theorem carrierWeight_second (hz : pointZeroTriples Pc = {contactSupport M a}) (hr : Pc M = edgePoint Pc a r)
    (hr1 : r < 1) (hη : 0 < η) (hw : ContactParameterWindows Pc Q M a r η)
    (hchi : ChirotopesOutsideZerosAgree Pc Q)
    (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))
    (hS : IsDecomposition hn hQ T) (hS₂ : IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂)
    (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂) (q : Component hn hQ T)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inr q₂)) :
    carrierWeight hn hQ T q = carrierWeight (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂ := by
  obtain ⟨hk, s, hs⟩ := hT.cornerMark_second_shift hη hw hlt hS hS₂ q₂ q hq
  set f : ZMod (ccpCornerCount hn hQ T q) → ZMod (ccpCornerCount (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂) :=
    fun j => ((j.val + s : ℕ) : ZMod _) with hf
  have hinj : Function.Injective f := by
    intro j j' h
    apply ccpCornerMark_injective hn hQ T q
    rw [hs j, hs j']
    show s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr (ccpCornerMark _ hg₂ S₂ q₂ (f j)))) =
      s7fb_mark hn hsep hm hQC hcx hcy (Sum.inl (Sum.inr (ccpCornerMark _ hg₂ S₂ q₂ (f j'))))
    rw [h]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by rw [ZMod.card, ZMod.card, hk]⟩
  have hturn : ∀ j, turn (ccpCornerPolygon (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂) (f j) =
      turn (ccpCornerPolygon hn hQ T q) j := by
    intro j
    rw [turn_ccpCornerPolygon_eq_markTurn hn hQ hS q j, turn_ccpCornerPolygon_eq_markTurn _ hg₂ hS₂ q₂ (f j),
      hs j]
    exact (hT.markTurn_second hz hr hr1 hchi _).symm
  rw [s7c_carrierWeight_eq_sel, s7c_carrierWeight_eq_sel]
  congr 1
  unfold s7c_turns
  exact s7c_map_univ_eq_of_equiv _ _ (Equiv.ofBijective f hbij) hturn

/-! #### The contact triangle: three equal turns `χ_{a,a+1,M}(Q)`, weight `−χ_{a,a+1,M}(Q)` -/

/-- The vector identity of the contact triangle `x → μ_M → y → x`:
`(p_{x_a} − p_{y_a}) E_a + (1 − p_{x_ℓ}) E_{M−1} + p_{y_ℓ} E_M = 0`. -/
theorem triangle_sum :
    (visitParameter (s7e_va hcx) - visitParameter (s7e_va hcy)) • edge Q a +
      (1 - visitParameter (s7e_vl hcx)) • edge Q (M - 1) + visitParameter (s7e_vl hcy) • edge Q M = 0 := by
  have hdx : det (edge Q a) (edge Q (M - 1)) ≠ 0 := crossing_edgeParameter_det_ne_zero hn hQ.1 (s7fb_hcx' hcx)
  have hdy : det (edge Q a) (edge Q M) ≠ 0 := crossing_edgeParameter_det_ne_zero hn hQ.1 (s7fb_hcy' hcy)
  have hxa : visitParameter (s7e_va hcx) = edgeParameter Q a (M - 1) :=
    (s7e_va_param hn hQ hcx).trans (by rw [s7fb_leg_false])
  have hxl : visitParameter (s7e_vl hcx) = edgeParameter Q (M - 1) a :=
    (s7e_vl_param hn hQ hcx).trans (by rw [s7fb_leg_false])
  have hya : visitParameter (s7e_va hcy) = edgeParameter Q a M :=
    (s7e_va_param hn hQ hcy).trans (by rw [s7fb_leg_true])
  have hyl : visitParameter (s7e_vl hcy) = edgeParameter Q M a :=
    (s7e_vl_param hn hQ hcy).trans (by rw [s7fb_leg_true])
  -- the crossing points read on both edges
  have hX : edgePoint Q a (visitParameter (s7e_va hcx)) = edgePoint Q (M - 1) (visitParameter (s7e_vl hcx)) := by
    rw [hxa, hxl]; exact s7a2_cramer_symm Q a (M - 1) hdx
  have hY : edgePoint Q a (visitParameter (s7e_va hcy)) = edgePoint Q M (visitParameter (s7e_vl hcy)) := by
    rw [hya, hyl]; exact s7a2_cramer_symm Q a M hdy
  -- the three sides
  have h1 : edgePoint Q a (visitParameter (s7e_va hcx)) - edgePoint Q a (visitParameter (s7e_va hcy)) =
      (visitParameter (s7e_va hcx) - visitParameter (s7e_va hcy)) • edge Q a :=
    edgePoint_sub_edgePoint Q a _ _
  have h2 : Q M - edgePoint Q (M - 1) (visitParameter (s7e_vl hcx)) =
      (1 - visitParameter (s7e_vl hcx)) • edge Q (M - 1) := by
    rw [← edgePoint_sub_edgePoint Q (M - 1), edgePoint_one, sub_add_cancel]
  have h3 : edgePoint Q M (visitParameter (s7e_vl hcy)) - Q M = visitParameter (s7e_vl hcy) • edge Q M := by
    show Q M + visitParameter (s7e_vl hcy) • edge Q M - Q M = _
    exact add_sub_cancel_left _ _
  rw [← h1, ← h2, ← h3, hX, hY]
  abel

/-- Every corner turn of the contact triangle is `χ_{a,a+1,M}(Q) = sgn det(E_a, E_{M−1})`. -/
theorem turn_M (hη : 0 < η) (hw : ContactParameterWindows Pc Q M a r η)
    (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx)) (hS : IsDecomposition hn hQ T)
    (j : ZMod (ccpCornerCount hn hQ T (owner hn hQ T (Sum.inl M)))) :
    turn (ccpCornerPolygon hn hQ T (owner hn hQ T (Sum.inl M))) j = chi Q a (a + 1) M := by
  have hsum := hT.triangle_sum
  -- coordinates
  set α := visitParameter (s7e_va hcx) - visitParameter (s7e_va hcy) with hα
  set β := 1 - visitParameter (s7e_vl hcx) with hβ
  set γ := visitParameter (s7e_vl hcy) with hγ
  have hα0 : 0 < α := by rw [hα]; linarith
  have hβ0 : 0 < β := by rw [hβ]; linarith [s7e_visitParameter_lt_one hn hQ (s7e_vl hcx)]
  have hγ0 : 0 < γ := s7e_visitParameter_pos hn hQ (s7e_vl hcy)
  have h1 := congrArg Prod.fst hsum
  have h2 := congrArg Prod.snd hsum
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_zero,
    Prod.snd_zero] at h1 h2
  -- the two determinant identities
  have hbc : γ * det (edge Q (M - 1)) (edge Q M) = α * det (edge Q a) (edge Q (M - 1)) := by
    simp only [det]; linear_combination (edge Q (M - 1)).1 * h2 - (edge Q (M - 1)).2 * h1
  have hca : γ * det (edge Q M) (edge Q a) = β * det (edge Q a) (edge Q (M - 1)) := by
    simp only [det]; linear_combination (edge Q a).2 * h1 - (edge Q a).1 * h2
  have hσ : chi Q a (a + 1) M = SignType.sign (det (edge Q a) (edge Q (M - 1))) := by
    have h := s7a_crossingSign_eq_chi hn hQ.1 (s7fb_hcx' hcx)
    rw [sub_add_cancel] at h
    exact h.symm
  rw [hσ, turn_ccpCornerPolygon_eq_markTurn hn hQ hS]
  have hmem := (hT.mem_cornerList_M_iff hη hw hlt (ccpCornerMark hn hQ T _ j)).mp
    ((mem_ccpCornerList hn hQ T _ _).mpr (ccpCornerMark_mem hn hQ T _ j))
  rcases hmem with h | h | h <;> rw [h]
  · -- `μ_M`: `sgn det(E_{M−1}, E_M)`
    rw [markTurn_inl]
    show SignType.sign (det (Q M - Q (M - 1)) (Q (M + 1) - Q (M - 1))) = _
    have e0 : Q M - Q (M - 1) = edge Q (M - 1) := by simp only [edge, sub_add_cancel]
    have e1 : Q (M + 1) - Q (M - 1) = edge Q (M - 1) + edge Q M := by simp only [edge, sub_add_cancel]; abel
    rw [e0, e1, det_add_right, s7fb_det_self, zero_add, ← s7fb_sign_smul_pos hγ0, hbc, s7fb_sign_smul_pos hα0]
  · -- `y_ℓ`: `sgn det(E_M, E_a)`
    rw [markTurn_inr, s7e_twin_vl hcy (s7e_a_ne_leg true hsep), s7fb_yl_edge, s7e_va_edge]
    unfold crossingSign
    rw [← s7fb_sign_smul_pos hγ0, hca, s7fb_sign_smul_pos hβ0]
  · -- `x_a`: `sgn det(E_a, E_{M−1})`
    rw [markTurn_inr, s7e_twin_va hcx (s7e_a_ne_leg false hsep), s7fb_xl_edge, s7e_va_edge]
    rfl

/-- **The weight of the contact triangle is `−χ_{a,a+1,M}(Q)`** (eq. s7c:triangle-data:
three corners of turn `−s₀` give `wt = s₀`, here with `s₀ = −χ_{a,a+1,M}(Q)`). -/
theorem carrierWeight_M (hη : 0 < η) (hw : ContactParameterWindows Pc Q M a r η)
    (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx)) (hS : IsDecomposition hn hQ T) :
    carrierWeight hn hQ T (owner hn hQ T (Sum.inl M)) = -((chi Q a (a + 1) M : SignType) : ℤ) := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  have hσ : chi Q a (a + 1) M ≠ 0 :=
    hQ.1 a (a + 1) M (next_ne_self a).symm hsep.2.2.1.symm (s7e_a_ne_M hsep)
  have := s7c_carrierWeight_triangle hn hQ T (owner hn hQ T (Sum.inl M)) (s₀ := -chi Q a (a + 1) M)
    (fun h => hσ (SignType.neg_eq_zero_iff.mp h)) (hT.ccpCornerCount_M hη hw hlt)
    (fun j => by rw [hT.turn_M hη hw hlt hS j, neg_neg])
  rw [this, SignType.coe_neg]

end s7fb_BigonTransport

end S7FBWeights

/-! Part E — the rotation equality `hr` for the half carriers (A2's corner-polygon family through the
wall, `s7a2_cornerFamily`, extended to the two-newborn row): the corner marks of a half carrier of `T`
read on `g.curve u` form a continuous, regular family on `|u| ≤ t`; at the side time it is the carrier's
corner polygon, at the centre it is (a cyclic reindexing of) the half's corner polygon — the special
corner `y_a` (resp. `x_ℓ`) is the Cramer point of `E_a, E_M` (resp. `E_{M−1}, E_a`), which at the
centre is `P M`, the half's vertex `0`.  Transversality of these two edge pairs along the interval is
the one input not in `VertexLocalData`; it is supplied by continuity from the centre (`s7fb_exists_detRadius`). -/

section S7FBFamilyPrelim

omit [NeZero n] in
theorem s7fb_det_sub_left (u w v : Plane) : det (u - w) v = det u v - det w v := by
  simp only [det, Prod.fst_sub, Prod.snd_sub]; ring

omit [NeZero n] in
theorem s7fb_continuous_det : Continuous (fun p : Plane × Plane => det p.1 p.2) := by
  unfold det
  exact (continuous_fst.fst.mul continuous_snd.snd).sub (continuous_fst.snd.mul continuous_snd.fst)

omit [NeZero n] in
/-- `edgeParameter Q i j` is continuous in `Q` where `det(E_i, E_j) ≠ 0`. -/
theorem s7fb_continuousAt_edgeParameter (i j : ZMod n) (Q₀ : LabelledTuple n)
    (hd : det (edge Q₀ i) (edge Q₀ j) ≠ 0) :
    ContinuousAt (fun Q : LabelledTuple n => edgeParameter Q i j) Q₀ := by
  have hnum : Continuous (fun Q : LabelledTuple n => det (Q j - Q i) (edge Q j)) :=
    s7fb_continuous_det.comp (((continuous_apply j).sub (continuous_apply i)).prodMk (continuous_edge j))
  have hden : Continuous (fun Q : LabelledTuple n => det (edge Q i) (edge Q j)) :=
    s7fb_continuous_det.comp ((continuous_edge i).prodMk (continuous_edge j))
  exact ContinuousAt.div hnum.continuousAt hden.continuousAt hd

variable {r η δ : ℝ} (hloc : s7a2_IntervalLocal hn g M a r η δ)
  (hr : g.center M = edgePoint g.center a r) (hr0 : 0 < r) (hr1 : r < 1) (hη : 0 < η)

include hn h hr in
/-- At the centre `E_a` and `E_M` are transverse (`χ_{a,a+1,M+1} ≠ 0`). -/
theorem s7fb_det_aM_center : det (edge g.center a) (edge g.center M) ≠ 0 := by
  have hsep := h.1.1
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.1.2.1
  have hchi := contactNeighbour_chi_nonzero hn hsep hz true
  simp only [contactNeighbour, ↓reduceIte] at hchi
  rw [chi_edge, s7fb_PcM1_sub hr, det_add_right, det_smul_right, s7fb_det_self, mul_zero, add_zero] at hchi
  exact sign_ne_zero.mp hchi

include hn h hloc hr hr1 in
/-- At the centre `E_{M−1}` and `E_a` are transverse (`χ_{M−1,M,a+1} ≠ 0`, a triple off the contact support). -/
theorem s7fb_det_M1a_center (hδ : 0 < δ) : det (edge g.center (M - 1)) (edge g.center a) ≠ 0 := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  have hsep := h.1.1
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.1.2.1
  have h0 : |(g.zeroParameter).val| < δ := by show |(0 : ℝ)| < δ; rw [abs_zero]; exact hδ
  have hne1 : M - 1 ≠ M := prev_ne_self M
  have hne2 : M ≠ a + 1 := hsep.2.2.1
  have hne3 : M - 1 ≠ a + 1 := fun h => hsep.2.2.2 (by rw [← sub_add_cancel M 1, h]; ring)
  have hnot : ({M - 1, M, a + 1} : Finset (ZMod n)) ∉ pointZeroTriples g.center := by
    rw [hz, Finset.mem_singleton]
    intro heq
    have hm1 : M - 1 ∈ contactSupport M a := by rw [← heq]; simp
    simp only [contactSupport, Finset.mem_insert, Finset.mem_singleton] at hm1
    rcases hm1 with h | h | h
    · exact hsep.2.2.1 (by rw [← h]; ring)
    · exact hne3 h
    · exact hne1 h
  have hchi : chi g.center (M - 1) M (a + 1) ≠ 0 :=
    ((hloc g.zeroParameter h0).chirotopes (M - 1) M (a + 1) hne1 hne2 hne3 hnot).2
  have e0 : g.center M - g.center (M - 1) = edge g.center (M - 1) := by simp only [edge, sub_add_cancel]
  have h1r : 0 < 1 - r := by linarith
  change SignType.sign (det (g.center M - g.center (M - 1)) (g.center (a + 1) - g.center (M - 1))) ≠ 0 at hchi
  rw [e0, s7fb_Pca1_sub_pred hr, det_add_right, det_smul_right, s7fb_det_self, zero_add] at hchi
  intro hd
  apply hchi
  rw [hd, mul_zero, sign_zero]

include hn h hloc hr hr1 in
/-- **The transversality radius**: below `δ'` the pairs `(E_a, E_M)` and `(E_{M−1}, E_a)` stay transverse
along the germ (continuity from the centre values). -/
theorem s7fb_exists_detRadius (hδ : 0 < δ) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∀ u : g.Parameter, |u.val| < δ' →
      det (edge (g.curve u) a) (edge (g.curve u) M) ≠ 0 ∧
        det (edge (g.curve u) (M - 1)) (edge (g.curve u) a) ≠ 0 := by
  have hc1 := s7fb_det_aM_center hn g h hr
  have hc2 := s7fb_det_M1a_center hn g h hloc hr hr1 hδ
  have hcont1 : Continuous (fun u : g.Parameter => det (edge (g.curve u) a) (edge (g.curve u) M)) :=
    s7fb_continuous_det.comp (((continuous_edge a).comp g.continuous_curve).prodMk
      ((continuous_edge M).comp g.continuous_curve))
  have hcont2 : Continuous (fun u : g.Parameter => det (edge (g.curve u) (M - 1)) (edge (g.curve u) a)) :=
    s7fb_continuous_det.comp (((continuous_edge (M - 1)).comp g.continuous_curve).prodMk
      ((continuous_edge a).comp g.continuous_curve))
  have hev := (hcont1.continuousAt.eventually_ne (x := g.zeroParameter) hc1).and
    (hcont2.continuousAt.eventually_ne (x := g.zeroParameter) hc2)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, fun u hu => hball ?_⟩
  rw [Subtype.dist_eq, Real.dist_eq]
  show |u.val - 0| < ε
  rw [sub_zero]; exact hu

/-! #### The parameter windows along the germ -/

include hloc in
theorem s7fb_win_aM (u : g.Parameter) (hu : |u.val| < δ) : |edgeParameter (g.curve u) a M - r| < η := by
  have := ((hloc u hu).windows.2.2 true).1
  rwa [s7fb_leg_true] at this

include hloc in
theorem s7fb_win_Ma (u : g.Parameter) (hu : |u.val| < δ) : |edgeParameter (g.curve u) M a| < η := by
  have := ((hloc u hu).windows.2.2 true).2
  rwa [s7fb_leg_true, show contactEndpoint true = 0 by rfl, sub_zero] at this

include hloc in
theorem s7fb_win_aM1 (u : g.Parameter) (hu : |u.val| < δ) :
    |edgeParameter (g.curve u) a (M - 1) - r| < η := by
  have := ((hloc u hu).windows.2.2 false).1
  rwa [s7fb_leg_false] at this

include hloc in
theorem s7fb_win_M1a (u : g.Parameter) (hu : |u.val| < δ) :
    |edgeParameter (g.curve u) (M - 1) a - 1| < η := by
  have := ((hloc u hu).windows.2.2 false).2
  rwa [s7fb_leg_false, show contactEndpoint false = 1 by rfl] at this

include hloc in
/-- A persistent crossing on edge `a` has its parameter `3η` away from `r`, at every `|u| < δ`. -/
theorem s7fb_win_persist_a (u : g.Parameter) (hu : |u.val| < δ) (j : ZMod n)
    (hc : IsCrossing (g.curve u) {a, j}) (hnot : ¬ ContactAffected M a {a, j}) :
    3 * η < |edgeParameter (g.curve u) a j - r| :=
  (hloc u hu).windows.2.1 none j hc hnot

include hloc in
/-- A persistent crossing on edge `M` has its parameter above `3η` in absolute value, at every `|u| < δ`. -/
theorem s7fb_win_persist_M (u : g.Parameter) (hu : |u.val| < δ) (j : ZMod n)
    (hc : IsCrossing (g.curve u) {M, j}) (hnot : ¬ ContactAffected M a {M, j}) :
    3 * η < |edgeParameter (g.curve u) M j| := by
  have := (hloc u hu).windows.2.1 (some true) j (by simpa [contactWindowEdge, contactLeg] using hc)
    (by simpa [contactWindowEdge, contactLeg] using hnot)
  simpa [contactWindowEdge, contactWindowCenter, contactLeg, contactEndpoint] using this

include hloc in
/-- A persistent crossing on edge `M − 1` has its parameter `3η` away from `1`, at every `|u| < δ`. -/
theorem s7fb_win_persist_M1 (u : g.Parameter) (hu : |u.val| < δ) (j : ZMod n)
    (hc : IsCrossing (g.curve u) {M - 1, j}) (hnot : ¬ ContactAffected M a {M - 1, j}) :
    3 * η < |edgeParameter (g.curve u) (M - 1) j - 1| := by
  have := (hloc u hu).windows.2.1 (some false) j (by simpa [contactWindowEdge, contactLeg] using hc)
    (by simpa [contactWindowEdge, contactLeg] using hnot)
  simpa [contactWindowEdge, contactWindowCenter, contactLeg, contactEndpoint] using this

/-! #### The corner points at the centre: the special corners are `P M`, the others the halves' -/

include hn h hr in
/-- At the centre the Cramer parameter of `(E_a, E_M)` is `r`. -/
theorem s7fb_edgeParameter_center_aM : edgeParameter g.center a M = r := by
  have hc1 := s7fb_det_aM_center hn g h hr
  show det (g.center M - g.center a) (edge g.center M) / det (edge g.center a) (edge g.center M) = r
  rw [s7fb_PcM_sub hr, det_smul_left, mul_div_assoc, div_self hc1, mul_one]

include hn h hloc hr hr1 in
/-- At the centre the Cramer parameter of `(E_{M−1}, E_a)` is `1`. -/
theorem s7fb_edgeParameter_center_M1a (hδ : 0 < δ) : edgeParameter g.center (M - 1) a = 1 := by
  have hc2 := s7fb_det_M1a_center hn g h hloc hr hr1 hδ
  show det (g.center a - g.center (M - 1)) (edge g.center a) / det (edge g.center (M - 1)) (edge g.center a) = 1
  have e0 : g.center M - g.center (M - 1) = edge g.center (M - 1) := by simp only [edge, sub_add_cancel]
  have e1 : g.center a - g.center (M - 1) = edge g.center (M - 1) - r • edge g.center a := by
    rw [← sub_add_sub_cancel (g.center a) (g.center M) (g.center (M - 1)), e0, ← neg_sub, s7fb_PcM_sub hr]
    abel
  rw [e1, s7fb_det_sub_left, det_smul_left, s7fb_det_self, mul_zero, sub_zero, div_self hc2]

include hn h hr in
/-- The point of `y_a` read on the centre is `P M`, `λ₁`'s vertex `0`. -/
theorem s7fb_point_ya_center {Q : LabelledTuple n} (hcy : IsCrossing Q {a, contactLeg true M}) :
    s7a2_point g.center (Sum.inr (s7e_va hcy)) = g.center M := by
  rw [s7a2_point_inr, s7e_twin_va hcy (s7e_a_ne_leg true h.1.1), s7e_va_edge, s7fb_yl_edge,
    s7fb_edgeParameter_center_aM hn g h hr]
  exact hr.symm

include hn h hloc hr hr1 in
/-- The point of `x_ℓ` read on the centre is `P M`, `λ₂`'s vertex `0`. -/
theorem s7fb_point_xl_center (hδ : 0 < δ) {Q : LabelledTuple n} (hcx : IsCrossing Q {a, contactLeg false M}) :
    s7a2_point g.center (Sum.inr (s7e_vl hcx)) = g.center M := by
  rw [s7a2_point_inr, s7e_twin_vl hcx (s7e_a_ne_leg false h.1.1), s7fb_xl_edge, s7e_va_edge,
    s7fb_edgeParameter_center_M1a hn g h hloc hr hr1 hδ, edgePoint_one, sub_add_cancel]

include hn h in
/-- The point of a carried visit of `λ₁`, read on the centre, is the half's corner point. -/
theorem s7fb_point_first_visit {Q : LabelledTuple n}
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing g.center s))
    (hg₁ : Generic (firstHalf g.center M a)) (v : Visit (firstHalf g.center M a)) :
    s7a2_point g.center (Sum.inr (s7b_firstVisitQ hn h.1.1 h.1.2.2.2.1 hQC v)) =
      s7a2_point (firstHalf g.center M a) (Sum.inr v) := by
  have hsep := h.1.1
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.1.2.1
  have hm := h.1.2.2.2.1
  have hn₁ := (contactHalfSizes_bounds hn hsep).1.1
  -- the right side is the crossing point of `v`'s crossing on the half, i.e. on the centre
  rw [← s7a2_point_eq_evaluation hn₁ hg₁, markPosition_evaluation_visit hn₁ hg₁.1,
    ← s7b_crossingPoint_firstHalfCrossing hn hsep hz hm v.1]
  -- the carried crossing of the centre
  have hval : (s7b_firstHalfCrossing hn hsep hm v.1).val =
      {firstHalfIndex M a v.2.val, firstHalfIndex M a (visitTwin v).2.val} := by
    rw [s7b_firstHalfCrossing_val, ← Finset.image_singleton, ← Finset.image_insert]
    congr 1
    exact visit_crossing_val_eq_pair v
  have hcross : IsCrossing g.center {firstHalfIndex M a v.2.val, firstHalfIndex M a (visitTwin v).2.val} := by
    have := (s7b_firstHalfCrossing hn hsep hm v.1).property; rwa [hval] at this
  have hnot : ¬ ContactAffected M a {firstHalfIndex M a v.2.val, firstHalfIndex M a (visitTwin v).2.val} := by
    have := s7b_firstHalfCrossing_not_affected hn hsep hm v.1; rwa [hval] at this
  have hcr : s7b_firstHalfCrossing hn hsep hm v.1 = ⟨_, hcross⟩ := Subtype.ext hval
  rw [hcr, (contact_pair_data hn hsep hz hcross hnot).point_eq, s7a2_point_inr,
    ← s7b_firstVisitQ_visitTwin hn hsep hm hQC v, s7b_firstVisitQ_edge, s7b_firstVisitQ_edge]

include hn h in
/-- The point of a carried visit of `λ₂`, read on the centre, is the half's corner point. -/
theorem s7fb_point_second_visit {Q : LabelledTuple n}
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing g.center s))
    (hg₂ : Generic (secondHalf g.center M a)) (v : Visit (secondHalf g.center M a)) :
    s7a2_point g.center (Sum.inr (s7b_secondVisitQ hn h.1.1 h.1.2.2.2.1 hQC v)) =
      s7a2_point (secondHalf g.center M a) (Sum.inr v) := by
  have hsep := h.1.1
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.1.2.1
  have hm := h.1.2.2.2.1
  have hn₂ := (contactHalfSizes_bounds hn hsep).2.1
  rw [← s7a2_point_eq_evaluation hn₂ hg₂, markPosition_evaluation_visit hn₂ hg₂.1,
    ← s7b_crossingPoint_secondHalfCrossing hn hsep hz hm v.1]
  have hval : (s7b_secondHalfCrossing hn hsep hm v.1).val =
      {secondHalfEdgeIndex M a v.2.val, secondHalfEdgeIndex M a (visitTwin v).2.val} := by
    rw [s7b_secondHalfCrossing_val, ← Finset.image_singleton, ← Finset.image_insert]
    congr 1
    exact visit_crossing_val_eq_pair v
  have hcross : IsCrossing g.center {secondHalfEdgeIndex M a v.2.val, secondHalfEdgeIndex M a (visitTwin v).2.val} := by
    have := (s7b_secondHalfCrossing hn hsep hm v.1).property; rwa [hval] at this
  have hnot : ¬ ContactAffected M a {secondHalfEdgeIndex M a v.2.val, secondHalfEdgeIndex M a (visitTwin v).2.val} := by
    have := s7b_secondHalfCrossing_not_affected hn hsep hm v.1; rwa [hval] at this
  have hcr : s7b_secondHalfCrossing hn hsep hm v.1 = ⟨_, hcross⟩ := Subtype.ext hval
  rw [hcr, (contact_pair_data hn hsep hz hcross hnot).point_eq, s7a2_point_inr,
    ← s7b_secondVisitQ_visitTwin hn hsep hm hQC v, s7b_secondVisitQ_edge, s7b_secondVisitQ_edge]

include hn h hr in
/-- **The points of the first-half marks at the centre**: `s7a2_point g.center (ι c) = s7a2_point λ₁ c`. -/
theorem s7fb_point_first {Q : LabelledTuple n}
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing g.center s))
    (hg₁ : Generic (firstHalf g.center M a))
    (hcx : IsCrossing Q {a, contactLeg false M}) (hcy : IsCrossing Q {a, contactLeg true M})
    (c : Mark (firstHalf g.center M a)) :
    s7a2_point g.center (s7fb_mark hn h.1.1 h.1.2.2.2.1 hQC hcx hcy (Sum.inl (Sum.inl c))) =
      s7a2_point (firstHalf g.center M a) c := by
  cases c with
  | inl i =>
    by_cases hi : i = 0
    · subst hi
      rw [s7fb_mark_inl_inl_zero, s7fb_point_ya_center hn g h hr hcy, s7a2_point_inl]
      show g.center M = g.center (firstHalfIndex M a 0)
      rw [firstHalfIndex_zero]
    · rw [s7fb_mark_inl_inl hn h.1.1 h.1.2.2.2.1 hQC hcx hcy hi]; rfl
  | inr v => rw [s7fb_mark_inl_inr]; exact s7fb_point_first_visit hn g h hQC hg₁ v

include hn h hloc hr hr1 in
/-- **The points of the second-half marks at the centre**: `s7a2_point g.center (ι c) = s7a2_point λ₂ c`. -/
theorem s7fb_point_second (hδ : 0 < δ) {Q : LabelledTuple n}
    (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing g.center s))
    (hg₂ : Generic (secondHalf g.center M a))
    (hcx : IsCrossing Q {a, contactLeg false M}) (hcy : IsCrossing Q {a, contactLeg true M})
    (c : Mark (secondHalf g.center M a)) :
    s7a2_point g.center (s7fb_mark hn h.1.1 h.1.2.2.2.1 hQC hcx hcy (Sum.inl (Sum.inr c))) =
      s7a2_point (secondHalf g.center M a) c := by
  cases c with
  | inl j =>
    by_cases hj : j = 0
    · subst hj
      rw [s7fb_mark_inr_inl_zero, s7fb_point_xl_center hn g h hloc hr hr1 hδ hcx, s7a2_point_inl]
      show g.center M = g.center (secondHalfIndex M a 0)
      simp [secondHalfIndex]
    · rw [s7fb_mark_inr_inl hn h.1.1 h.1.2.2.2.1 hQC hcx hcy hj]; rfl
  | inr v => rw [s7fb_mark_inr_inr]; exact s7fb_point_second_visit hn g h hQC hg₂ v

end S7FBFamilyPrelim

section S7FBFamily

variable {r η δ δ' : ℝ} (hloc : s7a2_IntervalLocal hn g M a r η δ) (hδ : 0 < δ)
  (hr : g.center M = edgePoint g.center a r) (hr0 : 0 < r) (hr1 : r < 1) (hη : 0 < η)
  (hηr : 4 * η < r) (hηr1 : 4 * η < 1 - r)
  (hdet : ∀ u : g.Parameter, |u.val| < δ' →
    det (edge (g.curve u) a) (edge (g.curve u) M) ≠ 0 ∧
      det (edge (g.curve u) (M - 1)) (edge (g.curve u) a) ≠ 0)
  {t : g.SideParameter} (ht : t.val < δ) (ht' : t.val < δ') (b : Bool)
  (hcx : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg false M})
  (hcy : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg true M})

variable (M a) in
/-- The kinds of corner mark of a half carrier of a two-newborn row: a vertex, a persistent visit, or
the special visit `sp` (`y_a` for `λ₁`, `x_ℓ` for `λ₂`). -/
def s7fb_Kind (sp : Visit (g.curve (g.sideTime b t))) (m : Mark (g.curve (g.sideTime b t))) : Prop :=
  (∃ i, m = Sum.inl i) ∨ (∃ v, m = Sum.inr v ∧ ¬ ContactAffected M a v.1.val) ∨ m = Sum.inr sp

include hn hloc ht in
/-- A persistent visit of the side carries a persistent crossing of the centre (both edge orders). -/
theorem s7fb_persist_cross (v : Visit (g.curve (g.sideTime b t))) (hv : ¬ ContactAffected M a v.1.val) :
    (IsCrossing g.center {v.2.val, (visitTwin v).2.val} ∧ ¬ ContactAffected M a {v.2.val, (visitTwin v).2.val}) ∧
    (IsCrossing g.center {(visitTwin v).2.val, v.2.val} ∧ ¬ ContactAffected M a {(visitTwin v).2.val, v.2.val}) := by
  have hnot : ¬ ContactAffected M a {v.2.val, (visitTwin v).2.val} := by
    rw [← visit_crossing_val_eq_pair v]; exact hv
  have hc : IsCrossing g.center {v.2.val, (visitTwin v).2.val} :=
    (s7a2_crossing_iff hn g hloc (u := g.sideTime b t) (by rw [g.sideTime_val_abs]; exact ht) _ hnot).mp
      (s7a2_visit_isCrossing v)
  refine ⟨⟨hc, hnot⟩, ?_, ?_⟩
  · rw [Finset.pair_comm]; exact hc
  · rw [Finset.pair_comm]; exact hnot

/-! #### The in/out edges of the special visits -/

omit [NeZero n] in
theorem s7fb_ya_inEdge : s7a2_inEdge (Sum.inr (s7e_va hcy)) = a := s7e_va_edge hcy

include h in
theorem s7fb_ya_outEdge : s7a2_outEdge (Sum.inr (s7e_va hcy)) = M := by
  rw [s7a2_outEdge_inr, s7e_twin_va hcy (s7e_a_ne_leg true h.1.1), s7fb_yl_edge]

omit [NeZero n] in
theorem s7fb_xl_inEdge : s7a2_inEdge (Sum.inr (s7e_vl hcx)) = M - 1 := s7fb_xl_edge hcx

include h in
theorem s7fb_xl_outEdge : s7a2_outEdge (Sum.inr (s7e_vl hcx)) = a := by
  rw [s7a2_outEdge_inr, s7e_twin_vl hcx (s7e_a_ne_leg false h.1.1), s7e_va_edge]

include h in
theorem s7fb_ya_inParam (Qu : LabelledTuple n) : s7a2_inParam Qu (Sum.inr (s7e_va hcy)) = edgeParameter Qu a M := by
  rw [s7a2_inParam_inr, s7e_twin_va hcy (s7e_a_ne_leg true h.1.1), s7e_va_edge, s7fb_yl_edge]

include h in
theorem s7fb_ya_outParam (Qu : LabelledTuple n) : s7a2_outParam Qu (Sum.inr (s7e_va hcy)) = edgeParameter Qu M a := by
  rw [s7a2_outParam_inr, s7e_twin_va hcy (s7e_a_ne_leg true h.1.1), s7e_va_edge, s7fb_yl_edge]

include h in
theorem s7fb_xl_inParam (Qu : LabelledTuple n) :
    s7a2_inParam Qu (Sum.inr (s7e_vl hcx)) = edgeParameter Qu (M - 1) a := by
  rw [s7a2_inParam_inr, s7e_twin_vl hcx (s7e_a_ne_leg false h.1.1), s7fb_xl_edge, s7e_va_edge]

include h in
theorem s7fb_xl_outParam (Qu : LabelledTuple n) :
    s7a2_outParam Qu (Sum.inr (s7e_vl hcx)) = edgeParameter Qu a (M - 1) := by
  rw [s7a2_outParam_inr, s7e_twin_vl hcx (s7e_a_ne_leg false h.1.1), s7fb_xl_edge, s7e_va_edge]

variable (sp : Visit (g.curve (g.sideTime b t))) (hsp : sp = s7e_va hcy ∨ sp = s7e_vl hcx)

include hn h hloc hdet ht hsp in
/-- **Transversality of the two edges of a visit-kind mark** at every `|u| < δ`, `|u| < δ'`. -/
theorem s7fb_kind_visit_det (u : g.Parameter) (hu : |u.val| < δ) (hu' : |u.val| < δ')
    (m : Mark (g.curve (g.sideTime b t))) (hm : s7fb_Kind g M a b sp m) :
    ∀ v, m = Sum.inr v → det (edge (g.curve u) v.2.val) (edge (g.curve u) (visitTwin v).2.val) ≠ 0 := by
  rintro v rfl
  rcases hm with ⟨i, hi⟩ | ⟨v', hv', hpers⟩ | hspm
  · exact absurd hi Sum.inr_ne_inl
  · have hvv : v = v' := Sum.inr.inj hv'
    subst hvv
    obtain ⟨⟨hc, hnot⟩, -⟩ := s7fb_persist_cross hn g hloc ht b v hpers
    exact s7a2_det_ne_zero hn g h.1 hloc hu hc hnot
  · have hvs : v = sp := Sum.inr.inj hspm
    subst hvs
    rcases hsp with rfl | rfl
    · rw [s7e_twin_va hcy (s7e_a_ne_leg true h.1.1), s7e_va_edge, s7fb_yl_edge]
      exact (hdet u hu').1
    · rw [s7e_twin_vl hcx (s7e_a_ne_leg false h.1.1), s7fb_xl_edge, s7e_va_edge]
      exact (hdet u hu').2

include hn h hloc hdet ht hsp in
/-- **Transversality of the incoming and outgoing directions** at every kind of corner mark. -/
theorem s7fb_kind_corner_det (u : g.Parameter) (hu : |u.val| < δ) (hu' : |u.val| < δ')
    (m : Mark (g.curve (g.sideTime b t))) (hm : s7fb_Kind g M a b sp m) :
    det (edge (g.curve u) (s7a2_inEdge m)) (edge (g.curve u) (s7a2_outEdge m)) ≠ 0 := by
  rcases hm with ⟨i, rfl⟩ | ⟨v, rfl, hpers⟩ | rfl
  · exact s7a2_turn_det_ne_zero hn g h.1 hloc hu i
  · rw [s7a2_inEdge_inr, s7a2_outEdge_inr]
    obtain ⟨⟨hc, hnot⟩, -⟩ := s7fb_persist_cross hn g hloc ht b v hpers
    exact s7a2_det_ne_zero hn g h.1 hloc hu hc hnot
  · rcases hsp with rfl | rfl
    · rw [s7fb_ya_inEdge, s7fb_ya_outEdge g h]; exact (hdet u hu').1
    · rw [s7fb_xl_inEdge, s7fb_xl_outEdge g h]; exact (hdet u hu').2

/-! #### The parameter differences of consecutive corners never vanish along the germ -/

include hn h hloc hη hηr hηr1 ht hsp in
/-- **`ψ ≠ 0`**: for two kind marks `m, m'` with `outEdge m = inEdge m'` and `outParam m < inParam m'`
on the side, `inParam m' − outParam m ≠ 0` at every `|u| < δ`. -/
theorem s7fb_kind_psi_ne_zero (u : g.Parameter) (hu : |u.val| < δ)
    (m m' : Mark (g.curve (g.sideTime b t))) (hm : s7fb_Kind g M a b sp m) (hm' : s7fb_Kind g M a b sp m')
    (hε : s7a2_outEdge m = s7a2_inEdge m')
    (hlt : s7a2_outParam (g.curve (g.sideTime b t)) m < s7a2_inParam (g.curve (g.sideTime b t)) m') :
    s7a2_inParam (g.curve u) m' - s7a2_outParam (g.curve u) m ≠ 0 := by
  have hsep := h.1.1
  have hnt : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
  -- the window facts at `u`
  have waM := s7fb_win_aM hn g hloc u hu
  have wMa := s7fb_win_Ma hn g hloc u hu
  have waM1 := s7fb_win_aM1 hn g hloc u hu
  have wM1a := s7fb_win_M1a hn g hloc u hu
  have hab1 := abs_lt.mp waM
  have hab2 := abs_lt.mp wMa
  have hab3 := abs_lt.mp waM1
  have hab4 := abs_lt.mp wM1a
  rcases hm with ⟨i, rfl⟩ | ⟨v, rfl, hpers⟩ | rfl <;>
    rcases hm' with ⟨i', rfl⟩ | ⟨v', rfl, hpers'⟩ | rfl
  · -- vertex, vertex
    simp
  · -- vertex, persistent visit
    simp only [s7a2_inParam_inr, s7a2_outParam_inl, sub_zero]
    obtain ⟨⟨hc, hnot⟩, -⟩ := s7fb_persist_cross hn g hloc ht b v' hpers'
    exact (s7a2_edgeParameter_interior hn g h.1 hloc hu hc hnot).1.ne'
  · -- vertex, special
    simp only [s7a2_outParam_inl, sub_zero]
    rcases hsp with rfl | rfl
    · rw [s7fb_ya_inParam g h]; linarith
    · rw [s7fb_xl_inParam g h]; linarith
  · -- persistent visit, vertex
    simp only [s7a2_inParam_inl, s7a2_outParam_inr]
    obtain ⟨-, hc, hnot⟩ := s7fb_persist_cross hn g hloc ht b v hpers
    exact (sub_pos.mpr (s7a2_edgeParameter_interior hn g h.1 hloc hu hc hnot).2).ne'
  · -- persistent visit, persistent visit
    simp only [s7a2_inParam_inr, s7a2_outParam_inr, s7a2_outEdge_inr, s7a2_inEdge_inr] at hε hlt ⊢
    obtain ⟨-, hc, hnot⟩ := s7fb_persist_cross hn g hloc ht b v hpers
    obtain ⟨⟨hc', hnot'⟩, -⟩ := s7fb_persist_cross hn g hloc ht b v' hpers'
    rw [← hε] at hc' hnot' hlt ⊢
    have hne : (visitTwin v').2.val ≠ v.2.val := by
      intro heq; rw [heq] at hlt; exact lt_irrefl _ hlt
    exact sub_ne_zero.mpr (s7a2_edgeParameters_ne hn g h.1 hloc hu hne hc' hnot' hc hnot)
  · -- persistent visit, special
    simp only [s7a2_outParam_inr, s7a2_outEdge_inr] at hε ⊢
    obtain ⟨-, hc, hnot⟩ := s7fb_persist_cross hn g hloc ht b v hpers
    rcases hsp with rfl | rfl
    · rw [s7fb_ya_inEdge] at hε
      rw [hε] at hc hnot ⊢
      have hcu : IsCrossing (g.curve u) {a, v.2.val} := (s7a2_crossing_iff hn g hloc hu _ hnot).mpr hc
      have hw := s7fb_win_persist_a hn g hloc u hu _ hcu hnot
      rw [s7fb_ya_inParam g h]
      intro h0
      have : edgeParameter (g.curve u) a v.2.val = edgeParameter (g.curve u) a M := by linarith
      rw [this] at hw
      rcases lt_or_ge (edgeParameter (g.curve u) a M) r with hlt' | hge
      · rw [abs_of_neg (by linarith)] at hw; linarith
      · rw [abs_of_nonneg (by linarith)] at hw; linarith
    · rw [s7fb_xl_inEdge] at hε
      rw [hε] at hc hnot ⊢
      have hcu : IsCrossing (g.curve u) {M - 1, v.2.val} := (s7a2_crossing_iff hn g hloc hu _ hnot).mpr hc
      have hw := s7fb_win_persist_M1 hn g hloc u hu _ hcu hnot
      rw [s7fb_xl_inParam g h]
      intro h0
      have : edgeParameter (g.curve u) (M - 1) v.2.val = edgeParameter (g.curve u) (M - 1) a := by linarith
      rw [this] at hw
      rcases lt_or_ge (edgeParameter (g.curve u) (M - 1) a) 1 with hlt' | hge
      · rw [abs_of_neg (by linarith)] at hw; linarith
      · rw [abs_of_nonneg (by linarith)] at hw; linarith
  · -- special, vertex
    simp only [s7a2_inParam_inl]
    rcases hsp with rfl | rfl
    · rw [s7fb_ya_outParam g h]; linarith
    · rw [s7fb_xl_outParam g h]; linarith
  · -- special, persistent visit
    simp only [s7a2_inParam_inr, s7a2_inEdge_inr] at hε ⊢
    obtain ⟨⟨hc', hnot'⟩, -⟩ := s7fb_persist_cross hn g hloc ht b v' hpers'
    rcases hsp with rfl | rfl
    · rw [s7fb_ya_outEdge g h] at hε
      rw [← hε] at hc' hnot' ⊢
      have hcu : IsCrossing (g.curve u) {M, (visitTwin v').2.val} :=
        (s7a2_crossing_iff hn g hloc hu _ hnot').mpr hc'
      have hw := s7fb_win_persist_M hn g hloc u hu _ hcu hnot'
      rw [s7fb_ya_outParam g h]
      intro h0
      have : edgeParameter (g.curve u) M (visitTwin v').2.val = edgeParameter (g.curve u) M a := by linarith
      rw [this] at hw
      rcases lt_or_ge (edgeParameter (g.curve u) M a) 0 with hlt' | hge
      · rw [abs_of_neg hlt'] at hw; linarith
      · rw [abs_of_nonneg hge] at hw; linarith
    · rw [s7fb_xl_outEdge g h] at hε
      rw [← hε] at hc' hnot' ⊢
      have hcu : IsCrossing (g.curve u) {a, (visitTwin v').2.val} :=
        (s7a2_crossing_iff hn g hloc hu _ hnot').mpr hc'
      have hw := s7fb_win_persist_a hn g hloc u hu _ hcu hnot'
      rw [s7fb_xl_outParam g h]
      intro h0
      have : edgeParameter (g.curve u) a (visitTwin v').2.val = edgeParameter (g.curve u) a (M - 1) := by linarith
      rw [this] at hw
      rcases lt_or_ge (edgeParameter (g.curve u) a (M - 1)) r with hlt' | hge
      · rw [abs_of_neg (by linarith)] at hw; linarith
      · rw [abs_of_nonneg (by linarith)] at hw; linarith
  · -- special, special: impossible (`outEdge sp ≠ inEdge sp`)
    exfalso
    rcases hsp with rfl | rfl
    · rw [s7fb_ya_outEdge g h, s7fb_ya_inEdge] at hε; exact s7e_a_ne_M hsep hε.symm
    · rw [s7fb_xl_outEdge g h, s7fb_xl_inEdge] at hε; exact s7e_a_ne_M_sub_one hsep hε

include hn h hloc hdet ht hsp in
/-- The in-parameter of a kind mark is continuous along the germ (on `|u| < δ`, `|u| < δ'`). -/
theorem s7fb_kind_inParam_continuousAt (u : g.Parameter) (hu : |u.val| < δ) (hu' : |u.val| < δ')
    (m : Mark (g.curve (g.sideTime b t))) (hm : s7fb_Kind g M a b sp m) :
    ContinuousAt (fun w : g.Parameter => s7a2_inParam (g.curve w) m) u := by
  rcases hm with ⟨i, rfl⟩ | ⟨v, rfl, hpers⟩ | rfl
  · simp only [s7a2_inParam_inl]; exact continuousAt_const
  · simp only [s7a2_inParam_inr]
    obtain ⟨⟨hc, hnot⟩, -⟩ := s7fb_persist_cross hn g hloc ht b v hpers
    exact s7a2_continuousAt_edgeParameter hn g h.1 hloc hu hc hnot
  · rcases hsp with rfl | rfl
    · simp only [s7fb_ya_inParam g h]
      exact ContinuousAt.comp (f := g.curve) (x := u) (s7fb_continuousAt_edgeParameter a M _ (hdet u hu').1)
        g.continuous_curve.continuousAt
    · simp only [s7fb_xl_inParam g h]
      exact ContinuousAt.comp (f := g.curve) (x := u) (s7fb_continuousAt_edgeParameter (M - 1) a _ (hdet u hu').2)
        g.continuous_curve.continuousAt

include hn h hloc hdet ht hsp in
/-- The out-parameter of a kind mark is continuous along the germ. -/
theorem s7fb_kind_outParam_continuousAt (u : g.Parameter) (hu : |u.val| < δ) (hu' : |u.val| < δ')
    (m : Mark (g.curve (g.sideTime b t))) (hm : s7fb_Kind g M a b sp m) :
    ContinuousAt (fun w : g.Parameter => s7a2_outParam (g.curve w) m) u := by
  rcases hm with ⟨i, rfl⟩ | ⟨v, rfl, hpers⟩ | rfl
  · simp only [s7a2_outParam_inl]; exact continuousAt_const
  · simp only [s7a2_outParam_inr]
    obtain ⟨-, hc, hnot⟩ := s7fb_persist_cross hn g hloc ht b v hpers
    exact s7a2_continuousAt_edgeParameter hn g h.1 hloc hu hc hnot
  · rcases hsp with rfl | rfl
    · simp only [s7fb_ya_outParam g h]
      have hd : det (edge (g.curve u) M) (edge (g.curve u) a) ≠ 0 := by
        rw [det_swap]; exact neg_ne_zero.mpr (hdet u hu').1
      exact ContinuousAt.comp (f := g.curve) (x := u) (s7fb_continuousAt_edgeParameter M a _ hd)
        g.continuous_curve.continuousAt
    · simp only [s7fb_xl_outParam g h]
      have hd : det (edge (g.curve u) a) (edge (g.curve u) (M - 1)) ≠ 0 := by
        rw [det_swap]; exact neg_ne_zero.mpr (hdet u hu').2
      exact ContinuousAt.comp (f := g.curve) (x := u) (s7fb_continuousAt_edgeParameter a (M - 1) _ hd)
        g.continuous_curve.continuousAt

include hn h hloc hdet ht hsp in
/-- The point of a kind mark is continuous along the germ. -/
theorem s7fb_kind_point_continuousAt (u : g.Parameter) (hu : |u.val| < δ) (hu' : |u.val| < δ')
    (m : Mark (g.curve (g.sideTime b t))) (hm : s7fb_Kind g M a b sp m) :
    ContinuousAt (fun w : g.Parameter => s7a2_point (g.curve w) m) u := by
  have hin := s7fb_kind_inParam_continuousAt hn g h hloc hdet ht b hcx hcy sp hsp u hu hu' m hm
  have hpt : ∀ w : g.Parameter, s7a2_point (g.curve w) m =
      (g.curve w) (s7a2_inEdge m) + s7a2_inParam (g.curve w) m • edge (g.curve w) (s7a2_inEdge m) := by
    intro w; rw [s7a2_point_eq_in]; rfl
  simp only [hpt]
  exact (((continuous_apply _).comp g.continuous_curve).continuousAt).add
    (hin.smul ((continuous_edge _).comp g.continuous_curve).continuousAt)

/-! #### The corner-polygon family of a half carrier -/

variable (T : Finset (Crossing (g.curve (g.sideTime b t)))) (hS : IsDecomposition hn (s7a_sideGeneric g b) T)
  (q : Component hn (s7a_sideGeneric g b) T)
  (hkind : ∀ j, s7fb_Kind g M a b sp (ccpCornerMark hn (s7a_sideGeneric g b) T q j))

include hn h hloc hdet ht hsp hS hkind in
/-- The edges of the family: parameter differences times the original edge directions. -/
theorem s7fb_family_edge (u : g.Parameter) (hu : |u.val| < δ) (hu' : |u.val| < δ')
    (j : ZMod (ccpCornerCount hn (s7a_sideGeneric g b) T q)) :
    edge (s7a2_cornerFamily hn g b T q u) j =
      (s7a2_inParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) T q (j + 1)) -
        s7a2_outParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) T q j)) •
        edge (g.curve u) (s7a2_outEdge (ccpCornerMark hn (s7a_sideGeneric g b) T q j)) := by
  show s7a2_point (g.curve u) _ - s7a2_point (g.curve u) _ = _
  exact s7a2_point_sub (g.curve u) _ _ (s7a2_corner_edges hn _ hS q j)
    (s7fb_kind_visit_det hn g h hloc hdet ht b hcx hcy sp hsp u hu hu' _ (hkind j))

include hn h hloc hη hηr hηr1 ht hsp hS hkind in
theorem s7fb_family_psi_ne_zero (u : g.Parameter) (hu : |u.val| < δ)
    (j : ZMod (ccpCornerCount hn (s7a_sideGeneric g b) T q)) :
    s7a2_inParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) T q (j + 1)) -
      s7a2_outParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) T q j) ≠ 0 :=
  s7fb_kind_psi_ne_zero hn g h hloc hη hηr hηr1 ht b hcx hcy sp hsp u hu _ _ (hkind j) (hkind (j + 1))
    (s7a2_corner_edges hn _ hS q j) (s7a2_corner_params_lt hn _ hS q j)

include hn h hloc hdet ht hsp hkind in
theorem s7fb_family_psi_continuousAt (u : g.Parameter) (hu : |u.val| < δ) (hu' : |u.val| < δ')
    (j : ZMod (ccpCornerCount hn (s7a_sideGeneric g b) T q)) :
    ContinuousAt (fun w : g.Parameter =>
      s7a2_inParam (g.curve w) (ccpCornerMark hn (s7a_sideGeneric g b) T q (j + 1)) -
        s7a2_outParam (g.curve w) (ccpCornerMark hn (s7a_sideGeneric g b) T q j)) u :=
  (s7fb_kind_inParam_continuousAt hn g h hloc hdet ht b hcx hcy sp hsp u hu hu' _ (hkind (j + 1))).sub
    (s7fb_kind_outParam_continuousAt hn g h hloc hdet ht b hcx hcy sp hsp u hu hu' _ (hkind j))

include hn h hloc hη hηr hηr1 hdet ht ht' hsp hS hkind in
/-- **Positive edge pieces on `|u| ≤ t`** (sign constancy from the side, `s7a2_pos_of_ne_zero`). -/
theorem s7fb_family_psi_pos (u : g.Parameter) (hu : |u.val| ≤ t.val)
    (j : ZMod (ccpCornerCount hn (s7a_sideGeneric g b) T q)) :
    0 < s7a2_inParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) T q (j + 1)) -
      s7a2_outParam (g.curve u) (ccpCornerMark hn (s7a_sideGeneric g b) T q j) := by
  have htmin : t.val < min δ δ' := lt_min ht ht'
  exact s7a2_pos_of_ne_zero g htmin
    (fun w hw => s7fb_family_psi_continuousAt hn g h hloc hdet ht b hcx hcy sp hsp T q hkind w
      (lt_of_lt_of_le hw (min_le_left _ _)) (lt_of_lt_of_le hw (min_le_right _ _)) j)
    (fun w hw => s7fb_family_psi_ne_zero hn g h hloc hη hηr hηr1 ht b hcx hcy sp hsp T hS q hkind w
      (lt_of_lt_of_le hw (min_le_left _ _)) j)
    b (sub_pos.mpr (s7a2_corner_params_lt hn _ hS q j)) u hu

include hn h hloc hη hηr hηr1 hdet ht ht' hsp hS hkind in
/-- **The family is regular on `|u| ≤ t`**. -/
theorem s7fb_family_regular (u : g.Parameter) (hu : |u.val| ≤ t.val) :
    Regular (s7a2_cornerFamily hn g b T q u) := by
  have hu' : |u.val| < δ := lt_of_le_of_lt hu ht
  have hu'' : |u.val| < δ' := lt_of_le_of_lt hu ht'
  rw [regular_iff_edges]
  intro j
  have hψ := s7fb_family_psi_pos hn g h hloc hη hηr hηr1 hdet ht ht' b hcx hcy sp hsp T hS q hkind u hu j
  have hψ' := s7fb_family_psi_pos hn g h hloc hη hηr hηr1 hdet ht ht' b hcx hcy sp hsp T hS q hkind u hu (j - 1)
  rw [sub_add_cancel] at hψ'
  have he := s7fb_family_edge hn g h hloc hdet ht b hcx hcy sp hsp T hS q hkind u hu' hu'' j
  have he' := s7fb_family_edge hn g h hloc hdet ht b hcx hcy sp hsp T hS q hkind u hu' hu'' (j - 1)
  rw [sub_add_cancel] at he'
  have hε' := s7a2_corner_edges hn _ hS q (j - 1)
  rw [sub_add_cancel] at hε'
  have hdet' : det (edge (s7a2_cornerFamily hn g b T q u) (j - 1))
      (edge (s7a2_cornerFamily hn g b T q u) j) ≠ 0 := by
    rw [he, he', s7a2_det_smul_smul, hε']
    exact mul_ne_zero (mul_ne_zero hψ'.ne' hψ.ne')
      (s7fb_kind_corner_det hn g h hloc hdet ht b hcx hcy sp hsp u hu' hu'' _ (hkind j))
  refine ⟨?_, ?_⟩
  · rw [he]
    exact smul_ne_zero hψ.ne' (s7a2_edge_ne_zero hn g h.1 hloc hu' _)
  · rintro ⟨c, _, hc⟩
    apply hdet'
    rw [hc]
    exact det_smul_self _ c

include hn h hloc hdet ht ht' hsp hkind in
/-- **The family is continuous on `|u| ≤ t`**. -/
theorem s7fb_family_continuousOn :
    ContinuousOn (s7a2_cornerFamily hn g b T q) {u : g.Parameter | |u.val| ≤ t.val} := by
  intro u hu
  apply ContinuousAt.continuousWithinAt
  have hu' : |u.val| < δ := lt_of_le_of_lt hu ht
  have hu'' : |u.val| < δ' := lt_of_le_of_lt hu ht'
  apply continuousAt_pi.mpr
  intro j
  exact s7fb_kind_point_continuousAt hn g h hloc hdet ht b hcx hcy sp hsp u hu' hu'' _ (hkind j)

include hn h hloc hη hηr hηr1 hdet ht ht' hsp hS hkind in
/-- **The rotation number of the family is constant on `|u| ≤ t`.** -/
theorem s7fb_family_rotation (u : g.Parameter) (hu : |u.val| ≤ t.val) :
    rotationNumber (s7a2_cornerFamily hn g b T q u) =
      rotationNumber (s7a2_cornerFamily hn g b T q (g.sideTime b t)) := by
  have hpre : PreconnectedSpace (Set.Icc (-t.val) t.val) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let ι : Set.Icc (-t.val) t.val → g.Parameter := fun w =>
    ⟨w.1, by obtain ⟨h1, h2⟩ := w.2; have := t.property.2; constructor <;> linarith⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hmem : ∀ w, |(ι w).val| ≤ t.val := fun w => abs_le.mpr w.2
  have hF : Continuous (fun w => s7a2_cornerFamily hn g b T q (ι w)) :=
    (s7fb_family_continuousOn hn g h hloc hdet ht ht' b hcx hcy sp hsp T q hkind).comp_continuous hι hmem
  exact rotationNumber_family_constant hF
    (fun w => s7fb_family_regular hn g h hloc hη hηr hηr1 hdet ht ht' b hcx hcy sp hsp T hS q hkind (ι w) (hmem w))
    ⟨u.val, abs_le.mp hu⟩ ⟨(g.sideTime b t).val, abs_le.mp (le_of_eq (g.sideTime_val_abs b t))⟩

end S7FBFamily

section S7FBRotation

variable {r η δ δ' : ℝ} (hloc : s7a2_IntervalLocal hn g M a r η δ) (hδ : 0 < δ)
  (hr : g.center M = edgePoint g.center a r) (hr0 : 0 < r) (hr1 : r < 1) (hη : 0 < η)
  (hηr : 4 * η < r) (hηr1 : 4 * η < 1 - r)
  (hdet : ∀ u : g.Parameter, |u.val| < δ' →
    det (edge (g.curve u) a) (edge (g.curve u) M) ≠ 0 ∧
      det (edge (g.curve u) (M - 1)) (edge (g.curve u) a) ≠ 0)
  {t : g.SideParameter} (ht : t.val < δ) (ht' : t.val < δ') (b : Bool)
  (hcx : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg false M})
  (hcy : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg true M})
  (hw : ContactParameterWindows g.center (g.curve (g.sideTime b t)) M a r η)
  (hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx))
  (T : Finset (Crossing (g.curve (g.sideTime b t)))) (S₁ : Finset (Crossing (firstHalf g.center M a)))
  (S₂ : Finset (Crossing (secondHalf g.center M a)))
  (hT : s7fb_BigonTransport hn (s7a_sideGeneric g b) h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t b) h₁ h₂ hcx hcy T S₁ S₂)
  (hS : IsDecomposition hn (s7a_sideGeneric g b) T)

include hη hw hlt hT in
/-- The corner marks of a first-half carrier are of the three kinds (`sp = y_a`). -/
theorem s7fb_kind_first (q₁ : Component (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁)
    (q : Component hn (s7a_sideGeneric g b) T) (hq : hT.componentEquiv q = Sum.inl (Sum.inl q₁))
    (j : ZMod (ccpCornerCount hn (s7a_sideGeneric g b) T q)) :
    s7fb_Kind g M a b (s7e_va hcy) (ccpCornerMark hn (s7a_sideGeneric g b) T q j) := by
  have hmem := (hT.mem_cornerList_first_iff hη hw hlt q₁ q hq _).mp
    ((mem_ccpCornerList hn _ T q _).mpr (ccpCornerMark_mem hn _ T q j))
  obtain ⟨c, -, hc⟩ := List.mem_map.mp hmem
  rw [← hc]
  rcases c with i | v
  · by_cases hi : i = 0
    · subst hi; right; right; exact s7fb_mark_inl_inl_zero hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t b) hcx hcy
    · left; exact ⟨_, s7fb_mark_inl_inl hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t b) hcx hcy hi⟩
  · right; left
    refine ⟨_, s7fb_mark_inl_inr hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t b) hcx hcy v, ?_⟩
    rw [s7b_firstVisitQ_fst]
    exact s7b_firstCrossingQ_not_affected hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t b) v.1

include hη hw hlt hT in
/-- The corner marks of a second-half carrier are of the three kinds (`sp = x_ℓ`). -/
theorem s7fb_kind_second (q₂ : Component (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂)
    (q : Component hn (s7a_sideGeneric g b) T) (hq : hT.componentEquiv q = Sum.inl (Sum.inr q₂))
    (j : ZMod (ccpCornerCount hn (s7a_sideGeneric g b) T q)) :
    s7fb_Kind g M a b (s7e_vl hcx) (ccpCornerMark hn (s7a_sideGeneric g b) T q j) := by
  have hmem := (hT.mem_cornerList_second_iff hη hw hlt q₂ q hq _).mp
    ((mem_ccpCornerList hn _ T q _).mpr (ccpCornerMark_mem hn _ T q j))
  obtain ⟨c, -, hc⟩ := List.mem_map.mp hmem
  rw [← hc]
  rcases c with j' | v
  · by_cases hj : j' = 0
    · subst hj; right; right; exact s7fb_mark_inr_inl_zero hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t b) hcx hcy
    · left; exact ⟨_, s7fb_mark_inr_inl hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t b) hcx hcy hj⟩
  · right; left
    refine ⟨_, s7fb_mark_inr_inr hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t b) hcx hcy v, ?_⟩
    rw [s7b_secondVisitQ_fst]
    exact s7b_secondCrossingQ_not_affected hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t b) v.1

include hloc hr hη hηr hηr1 hdet ht ht' hw hlt hT hS in
/-- **The rotation equality for a first-half carrier** (eq. s7c:full-rotation on the two-newborn row):
along `s7a2_cornerFamily` from the side to the centre, where it is a cyclic reindexing of `λ₁`'s corner
polygon. -/
theorem s7fb_carrierRotation_first (hS₁ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁)
    (q₁ : Component (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁)
    (q : Component hn (s7a_sideGeneric g b) T) (hq : hT.componentEquiv q = Sum.inl (Sum.inl q₁)) :
    carrierRotation hn (s7a_sideGeneric g b) T q = carrierRotation (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ q₁ := by
  have hkind := s7fb_kind_first hn g h h₁ h₂ hη b hcx hcy hw hlt T S₁ S₂ hT q₁ q hq
  have hrot := s7fb_family_rotation hn g h hloc hη hηr hηr1 hdet ht ht' b hcx hcy (s7e_va hcy) (Or.inl rfl)
    T hS q hkind g.zeroParameter (by show |(0 : ℝ)| ≤ t.val; rw [abs_zero]; exact t.property.1.le)
  rw [s7a2_cornerFamily_side_self] at hrot
  obtain ⟨hk, s, hs⟩ := hT.cornerMark_first_shift hη hw hlt hS hS₁ q₁ q hq
  have hre : Reindexed (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ q₁)
      (s7a2_cornerFamily hn g b T q g.zeroParameter) := by
    refine ⟨hk.symm, s, fun j => ?_⟩
    show s7a2_point g.center (ccpCornerMark hn (s7a_sideGeneric g b) T q j) = _
    rw [hs j, s7fb_point_first hn g h hr (s7f_hQC hn h.1 t b) h₁ hcx hcy,
      ← s7a2_point_eq_evaluation (contactHalfSizes_bounds hn h.1.1).1.1 h₁]
    rfl
  show rotationNumber (ccpCornerPolygon hn (s7a_sideGeneric g b) T q) = rotationNumber _
  rw [← hrot]
  exact rotationNumber_of_reindexed hre

include hloc hδ hr hr1 hη hηr hηr1 hdet ht ht' hw hlt hT hS in
/-- **The rotation equality for a second-half carrier.** -/
theorem s7fb_carrierRotation_second (hS₂ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂)
    (q₂ : Component (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂)
    (q : Component hn (s7a_sideGeneric g b) T) (hq : hT.componentEquiv q = Sum.inl (Sum.inr q₂)) :
    carrierRotation hn (s7a_sideGeneric g b) T q = carrierRotation (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ q₂ := by
  have hkind := s7fb_kind_second hn g h h₁ h₂ hη b hcx hcy hw hlt T S₁ S₂ hT q₂ q hq
  have hrot := s7fb_family_rotation hn g h hloc hη hηr hηr1 hdet ht ht' b hcx hcy (s7e_vl hcx) (Or.inr rfl)
    T hS q hkind g.zeroParameter (by show |(0 : ℝ)| ≤ t.val; rw [abs_zero]; exact t.property.1.le)
  rw [s7a2_cornerFamily_side_self] at hrot
  obtain ⟨hk, s, hs⟩ := hT.cornerMark_second_shift hη hw hlt hS hS₂ q₂ q hq
  have hre : Reindexed (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ q₂)
      (s7a2_cornerFamily hn g b T q g.zeroParameter) := by
    refine ⟨hk.symm, s, fun j => ?_⟩
    show s7a2_point g.center (ccpCornerMark hn (s7a_sideGeneric g b) T q j) = _
    rw [hs j, s7fb_point_second hn g h hloc hr hr1 hδ (s7f_hQC hn h.1 t b) h₂ hcx hcy,
      ← s7a2_point_eq_evaluation (contactHalfSizes_bounds hn h.1.1).2.1 h₂]
    rfl
  show rotationNumber (ccpCornerPolygon hn (s7a_sideGeneric g b) T q) = rotationNumber _
  rw [← hrot]
  exact rotationNumber_of_reindexed hre

end S7FBRotation

/-! Part F — the coefficient transport (U110-D's cut form with ROT's key decoding `s7q_cutFirst_of`),
the assembly `term(T ∪ {x, y}) = s₀ · term(T₁) · term(T₂)` at one side parameter, and the radius. -/

section S7FBCoefficients

variable {Pc Q : LabelledTuple n} (hQ : Generic Q) (hsep : ContactSeparated M a)
  (hz : pointZeroTriples Pc = {contactSupport M a}) (hm : Pc M ∈ edgeInterior Pc a) {r η : ℝ}
  (hr : Pc M = edgePoint Pc a r) (hr0 : 0 < r) (hr1 : r < 1) (hη : 0 < η)
  (hQC : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing Pc s))
  (hw : ContactParameterWindows Pc Q M a r η)
  (hord : ∀ (u u' : Visit Pc) (hu : ¬ ContactAffected M a u.1.val) (hu' : ¬ ContactAffected M a u'.1.val),
    u.2.val = u'.2.val →
    (visitParameter (s7a_visit hQC u hu) < visitParameter (s7a_visit hQC u' hu') ↔
      visitParameter u < visitParameter u'))
  (hchi : ChirotopesOutsideZerosAgree Pc Q)
  (hg₁ : Generic (firstHalf Pc M a)) (hg₂ : Generic (secondHalf Pc M a))
  (hcx : IsCrossing Q {a, contactLeg false M}) (hcy : IsCrossing Q {a, contactLeg true M})
  (T : Finset (Crossing Q)) (S₁ : Finset (Crossing (firstHalf Pc M a)))
  (S₂ : Finset (Crossing (secondHalf Pc M a)))

namespace s7fb_BigonTransport

variable {hn} {hQ} {hsep} {hm} {hQC} {hg₁} {hg₂} {hcx} {hcy} {T} {S₁} {S₂}
variable (hT : s7fb_BigonTransport hn hQ hsep hm hQC hg₁ hg₂ hcx hcy T S₁ S₂)
include hT

/-- **Coefficient transport to `λ₁`** (`s7q_coef_first` for the bigon transport): `hmem` from
`carrierCrossings_eq_img_first`, `htwin` from `s7b_firstVisitQ_visitTwin`, the rest from `s7q_CutFirst`. -/
theorem coef_first
    (hsplit : s7f_BigonSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 hg₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 hg₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) (s7e_va hcx).1 (s7e_va hcy).1)
    (hS : IsDecomposition hn hQ T) (hS₁ : IsDecomposition (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁)
    (q : Component hn hQ T) (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inl q₁))
    (hcut : s7q_CutFirst hn hsep hm hQC hQ hg₁ T S₁ q q₁) :
    cornerCoefficient hn hQ T q hS = cornerCoefficient (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁ hS₁ := by
  obtain ⟨c, hmono, hcut', hbit, hr⟩ := hcut
  symm
  refine s7d_cornerCoefficient_eq_of_cut (contactHalfSizes_bounds hn hsep).1.1 hn hg₁ hQ hS₁ q₁ hS q
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

theorem coef_second
    (hsplit : s7f_BigonSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 hg₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 hg₂) (s7b_firstCrossingQ hn hsep hm hQC)
      (s7b_secondCrossingQ hn hsep hm hQC) (s7e_va hcx).1 (s7e_va hcy).1)
    (hS : IsDecomposition hn hQ T) (hS₂ : IsDecomposition (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂)
    (q : Component hn hQ T) (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂)
    (hq : hT.componentEquiv q = Sum.inl (Sum.inr q₂))
    (hcut : s7q_CutSecond hn hsep hm hQC hQ hg₂ T S₂ q q₂) :
    cornerCoefficient hn hQ T q hS = cornerCoefficient (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂ hS₂ := by
  obtain ⟨c, hmono, hcut', hbit, hr⟩ := hcut
  symm
  refine s7d_cornerCoefficient_eq_of_cut (contactHalfSizes_bounds hn hsep).2.1 hn hg₂ hQ hS₂ q₂ hS q
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

/-- The cut-form data `s7q_CutFirst` for a carrier corresponding to `q₁`: the key decoding from the
same-edge order (`s7r_first_order`), the over bits from the carried crossing signs (`markTurn_first`),
and the rotation equality as an input. -/
theorem cutFirst_of (hz : pointZeroTriples Pc = {contactSupport M a}) (hr : Pc M = edgePoint Pc a r)
    (hr0 : 0 < r) (hchi : ChirotopesOutsideZerosAgree Pc Q)
    (hord : ∀ (u u' : Visit Pc) (hu : ¬ ContactAffected M a u.1.val) (hu' : ¬ ContactAffected M a u'.1.val),
      u.2.val = u'.2.val →
      (visitParameter (s7a_visit hQC u hu) < visitParameter (s7a_visit hQC u' hu') ↔
        visitParameter u < visitParameter u'))
    (q : Component hn hQ T) (q₁ : Component (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁)
    (hrot : carrierRotation (contactHalfSizes_bounds hn hsep).1.1 hg₁ S₁ q₁ = carrierRotation hn hQ T q) :
    s7q_CutFirst hn hsep hm hQC hQ hg₁ T S₁ q q₁ :=
  s7q_cutFirst_of hn hsep hm hQC hQ hg₁ T S₁ q q₁
    (fun v w he => (s7r_first_order hn hsep hz hm hr hr0 hQC hord v w he).symm)
    (fun v _ => s7d_positiveOverBit_eq_of_crossingSign v _ (by
      have := hT.markTurn_first hz hr hr0 hchi (Sum.inr v)
      rwa [s7fb_mark_inl_inr, markTurn_inr, markTurn_inr] at this))
    hrot

theorem cutSecond_of (hz : pointZeroTriples Pc = {contactSupport M a}) (hr : Pc M = edgePoint Pc a r)
    (hr1 : r < 1) (hchi : ChirotopesOutsideZerosAgree Pc Q)
    (hord : ∀ (u u' : Visit Pc) (hu : ¬ ContactAffected M a u.1.val) (hu' : ¬ ContactAffected M a u'.1.val),
      u.2.val = u'.2.val →
      (visitParameter (s7a_visit hQC u hu) < visitParameter (s7a_visit hQC u' hu') ↔
        visitParameter u < visitParameter u'))
    (q : Component hn hQ T) (q₂ : Component (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂)
    (hrot : carrierRotation (contactHalfSizes_bounds hn hsep).2.1 hg₂ S₂ q₂ = carrierRotation hn hQ T q) :
    s7q_CutSecond hn hsep hm hQC hQ hg₂ T S₂ q q₂ :=
  s7q_cutSecond_of hn hsep hm hQC hQ hg₂ T S₂ q q₂
    (fun v w he => (s7r_second_order hn hsep hz hm hr hr1 hQC hord v w he).symm)
    (fun v _ => s7d_positiveOverBit_eq_of_crossingSign v _ (by
      have := hT.markTurn_second hz hr hr1 hchi (Sum.inr v)
      rwa [s7fb_mark_inr_inr, markTurn_inr, markTurn_inr] at this))
    hrot

end s7fb_BigonTransport

end S7FBCoefficients

/-! #### The germ-level inputs for a vertex–edge wall (RET's `s7r_hord`/`s7r_hside` restated on
`VertexEdgeAt`; RET stated them on `SlidingAt` but used only its first component) -/

section S7FBGermInputs

variable {r η δ : ℝ} (hloc : s7a2_IntervalLocal hn g M a r η δ)

include hloc in
/-- The same-edge order law of a side relative to the centre (`VertexLocalData.visit_order`). -/
theorem s7fb_hord (t : g.SideParameter) (ht : t.val < δ) (b : Bool) :
    ∀ (u u' : Visit g.center) (hu : ¬ ContactAffected M a u.1.val) (hu' : ¬ ContactAffected M a u'.1.val),
      u.2.val = u'.2.val →
      (visitParameter (s7a_visit (s7f_hQC hn h.1 t b) u hu) <
          visitParameter (s7a_visit (s7f_hQC hn h.1 t b) u' hu') ↔
        visitParameter u < visitParameter u') :=
  fun u u' hu hu' he =>
    (hloc (g.sideTime b t) (by rw [g.sideTime_val_abs]; exact ht)).visit_order (s7a_sideGeneric g b).1
      ⟨u, hu⟩ ⟨u', hu'⟩ he

include hloc h in
/-- Sign constancy between a side and the centre (RET's `s7r_sign_const_center` on `VertexEdgeAt`). -/
theorem s7fb_sign_const_center (hη : 0 < η) (t : g.SideParameter) (ht : t.val < δ) (b : Bool) (j : ZMod n)
    (hc : IsCrossing g.center {a, j}) (hnot : ¬ ContactAffected M a {a, j}) :
    edgeParameter (g.curve (g.sideTime b t)) a j < r ↔ edgeParameter g.center a j < r := by
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
  have hlt : |(g.sideTime b t).val| < δ := by rw [g.sideTime_val_abs]; exact ht
  have h0 : (g.zeroParameter).val = 0 := rfl
  have h0abs : |(g.zeroParameter).val| ≤ t.val := by rw [h0, abs_zero]; exact t.property.1.le
  have hcenter : g.center = g.curve g.zeroParameter := rfl
  constructor
  · intro h1
    by_contra h2
    have hpos : 0 < -(edgeParameter (g.curve (g.sideTime b t)) a j - r) := by linarith
    have := s7a2_pos_of_ne_zero g ht hcont' hne' b hpos g.zeroParameter h0abs
    rw [← hcenter] at this
    linarith
  · intro h1
    by_contra h2
    have hpos : 0 < edgeParameter (g.curve (g.sideTime b t)) a j - r :=
      lt_of_le_of_ne (by linarith) (hne _ hlt).symm
    have := s7a2_pos_of_ne_zero g ht hcont hne b hpos g.zeroParameter h0abs
    rw [← hcenter] at this
    linarith

include hloc h in
/-- The side-of-`r` law on edge `a` for a side, relative to the centre. -/
theorem s7fb_hside (hη : 0 < η) (t : g.SideParameter) (ht : t.val < δ) (b : Bool) :
    ∀ (u : Visit g.center) (hu : ¬ ContactAffected M a u.1.val), u.2.val = a →
      (visitParameter (s7a_visit (s7f_hQC hn h.1 t b) u hu) < r ↔ visitParameter u < r) := by
  intro u hu he
  obtain ⟨j, -, hj⟩ := crossing_support_partner u.1 u.2.val u.2.property
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.1.2.1
  have h1 : visitParameter u = edgeParameter g.center a j := by
    rw [contact_visitParameter_eq_of_support_pair hn h.1.1 hz u hu j hj, he]
  have h2 : visitParameter (s7a_visit (s7f_hQC hn h.1 t b) u hu) =
      edgeParameter (g.curve (g.sideTime b t)) a j := by
    rw [visitParameter_eq_of_support_pair hn (s7a_sideGeneric g b).1 (s7a_visit (s7f_hQC hn h.1 t b) u hu) j hj,
      s7a_visit_edge, he]
  have hj' : u.1.val = {a, j} := by rw [hj, he]
  have hnot : ¬ ContactAffected M a {a, j} := by rw [← hj']; exact hu
  have hc : IsCrossing g.center {a, j} := by rw [← hj']; exact u.1.property
  rw [h1, h2]
  exact s7fb_sign_const_center hn g h hloc hη t ht b j hc hnot

include h in
/-- `−χ_{a,a+1,M}(P₂) = δ_dir · s = s₀` (eq. s7c:bigon-signs read on the newborn side with
`vertex_contact_signs`). -/
theorem s7fb_neg_chi (t : g.SideParameter) :
    -((chi (g.curve (g.sideTime (s7f_side g M a) t)) a (a + 1) M : SignType) : ℤ) =
      s7f_dirSign g M a * (g.contactSign M a : ℤ) := by
  obtain ⟨-, hm, hp⟩ := g.vertex_contact_signs h.1 t t
  unfold s7f_dirSign
  cases s7f_side g M a
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have : chi (g.curve (g.sideTime false t)) a (a + 1) M = g.contactSign M a := hm
    rw [this]; ring
  · simp only [↓reduceIte, one_mul]
    have : chi (g.curve (g.sideTime true t)) a (a + 1) M = -g.contactSign M a := hp
    rw [this, SignType.coe_neg, neg_neg]

end S7FBGermInputs

/-! #### The two-newborn term identity at one side parameter, and below a radius -/

section S7FBAssembly

variable {r η δ δ' : ℝ} (hloc : s7a2_IntervalLocal hn g M a r η δ) (hδ : 0 < δ)
  (hr : g.center M = edgePoint g.center a r) (hr0 : 0 < r) (hr1 : r < 1) (hη : 0 < η)
  (hηr : 4 * η < r) (hηr1 : 4 * η < 1 - r)
  (hdet : ∀ u : g.Parameter, |u.val| < δ' →
    det (edge (g.curve u) a) (edge (g.curve u) M) ≠ 0 ∧
      det (edge (g.curve u) (M - 1)) (edge (g.curve u) a) ≠ 0)

include hloc hδ hr hr0 hr1 hη hηr hηr1 hdet in
/-- **The `ε = 0` two-newborn term identity at one side parameter** (sm-4:434-447): the smoothing of
`T ∪ {x, y}` is the contact triangle (weight `s₀ = δ_dir · s`, coefficient `1`) together with the
successors of `T₁, T₂` (equal weights by the corner correspondence, equal coefficients by the cut
transport and the rotation equality). -/
theorem s7fb_twoNewbornTerm_at (t : g.SideParameter) (ht : t.val < δ) (ht' : t.val < δ')
    (hsplit : s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t))
    (hI : ¬ s7f_Interlacing hn h t)
    (S₁ : Finset (Crossing (firstHalf g.center M a))) (S₂ : Finset (Crossing (secondHalf g.center M a)))
    (hS₁ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁)
    (hS₂ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂) :
    s7e_term hn (s7f_hP₂ g M a t)
        (insert (s7f_x hn h t) (insert (s7f_y hn h t) (hsplit.split.joinSupport S₁ S₂))) =
      (s7f_dirSign g M a * (g.contactSign M a : ℤ)) *
        (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ *
          s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂) := by
  have hsep := h.1.1
  have hz : pointZeroTriples g.center = {contactSupport M a} := h.1.2.1
  have hm := h.1.2.2.2.1
  set b := s7f_side g M a with hb
  have hQ : Generic (g.curve (g.sideTime b t)) := s7a_sideGeneric g b
  have hcx : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg false M} := by
    rw [s7fb_leg_false]; exact (s7f_pattern hn h t).1
  have hcy : IsCrossing (g.curve (g.sideTime b t)) {a, contactLeg true M} := by
    rw [s7fb_leg_true]; exact (s7f_pattern hn h t).2.1
  have hx : (s7e_va hcx).1 = s7f_x hn h t :=
    Subtype.ext (by rw [s7e_va_fst_val, s7f_x_val, s7fb_leg_false])
  have hy : (s7e_va hcy).1 = s7f_y hn h t :=
    Subtype.ext (by rw [s7e_va_fst_val, s7f_y_val, s7fb_leg_true])
  have hV := hloc (g.sideTime b t) (by rw [g.sideTime_val_abs]; exact ht)
  have hw : ContactParameterWindows g.center (g.curve (g.sideTime b t)) M a r η := hV.windows
  have hchi : ChirotopesOutsideZerosAgree g.center (g.curve (g.sideTime b t)) := hV.chirotopes
  have hord := s7fb_hord hn g h hloc t ht b
  have hside := s7fb_hside hn g h hloc hη t ht b
  -- `¬ε ⟹ y_a < x_a`
  have hI' : ¬ Interlaces hn hQ (s7e_va hcx).1 (s7e_va hcy).1 := by rw [hx, hy]; exact hI
  have hlt : visitParameter (s7e_va hcy) < visitParameter (s7e_va hcx) :=
    s7fb_ya_lt_xa_of_not_interlaces hn hQ hsep hcx hcy hI'
  -- the row and its transport
  set T := insert (s7f_x hn h t) (insert (s7f_y hn h t) (hsplit.split.joinSupport S₁ S₂)) with hTdef
  have hxy : ¬ Interlaces hn hQ (s7f_x hn h t) (s7f_y hn h t) ∧
      ¬ Interlaces hn hQ (s7f_y hn h t) (s7f_x hn h t) :=
    ⟨hI, fun hI2 => hI (interlaces_symm hn hQ hI2)⟩
  have hS : IsDecomposition hn hQ T :=
    (s7b_isDecomposition_iff_indep _ _ _).mpr (hsplit.indep_insert hxy
      ((s7b_isDecomposition_iff_indep _ _ _).mp hS₁) ((s7b_isDecomposition_iff_indep _ _ _).mp hS₂))
  have hxT : (s7e_va hcx).1 ∈ T := by rw [hx]; exact Finset.mem_insert_self _ _
  have hyT : (s7e_va hcy).1 ∈ T := by rw [hy]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hTimg : ∀ z ∈ T, z ≠ (s7e_va hcx).1 → z ≠ (s7e_va hcy).1 →
      z ∈ Set.range (s7b_firstCrossingQ hn hsep hm (s7f_hQC hn h.1 t b)) ∪
        Set.range (s7b_secondCrossingQ hn hsep hm (s7f_hQC hn h.1 t b)) := by
    intro z hz hzx hzy
    rw [hx] at hzx; rw [hy] at hzy
    rcases Finset.mem_insert.mp hz with h1 | h1
    · exact absurd h1 hzx
    rcases Finset.mem_insert.mp h1 with h2 | h2
    · exact absurd h2 hzy
    rcases (hsplit.split.mem_joinSupport S₁ S₂ z).mp h2 with ⟨c, -, hc⟩ | ⟨c, -, hc⟩
    · exact Or.inl ⟨c, hc⟩
    · exact Or.inr ⟨c, hc⟩
  have hT₀ := s7fb_bigonTransport_of hn hQ hsep hz hm hr hr0 hr1 hη (s7f_hQC hn h.1 t b) hw hord hside h₁ h₂
    hcx hcy T hxT hyT hTimg hlt
  have hpre₁ : s7b_pre (s7b_firstCrossingQ hn hsep hm (s7f_hQC hn h.1 t b)) T = S₁ := by
    rw [hsplit.pre₁_insert, hsplit.split.pre₁_joinSupport]
  have hpre₂ : s7b_pre (s7b_secondCrossingQ hn hsep hm (s7f_hQC hn h.1 t b)) T = S₂ := by
    rw [hsplit.pre₂_insert, hsplit.split.pre₂_joinSupport]
  rw [hpre₁, hpre₂] at hT₀
  have hsplit' : s7f_BigonSplit (Interlaces hn hQ) (Interlaces (contactHalfSizes_bounds hn hsep).1.1 h₁)
      (Interlaces (contactHalfSizes_bounds hn hsep).2.1 h₂)
      (s7b_firstCrossingQ hn hsep hm (s7f_hQC hn h.1 t b))
      (s7b_secondCrossingQ hn hsep hm (s7f_hQC hn h.1 t b)) (s7e_va hcx).1 (s7e_va hcy).1 := by
    rw [hx, hy]; exact hsplit
  set e := hT₀.componentEquiv with he
  -- the half carriers: weights and coefficients
  have hrot₁ : ∀ q₁, carrierRotation hn hQ T (e.symm (Sum.inl (Sum.inl q₁))) =
      carrierRotation (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ := fun q₁ =>
    s7fb_carrierRotation_first hn g h h₁ h₂ hloc hr hη hηr hηr1 hdet ht ht' b hcx hcy hw hlt T S₁ S₂
      hT₀ hS hS₁ q₁ _ (e.apply_symm_apply _)
  have hrot₂ : ∀ q₂, carrierRotation hn hQ T (e.symm (Sum.inl (Sum.inr q₂))) =
      carrierRotation (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ := fun q₂ =>
    s7fb_carrierRotation_second hn g h h₁ h₂ hloc hδ hr hr1 hη hηr hηr1 hdet ht ht' b hcx hcy hw hlt T S₁ S₂
      hT₀ hS hS₂ q₂ _ (e.apply_symm_apply _)
  have hwt₁ : ∀ q₁, carrierWeight hn hQ T (e.symm (Sum.inl (Sum.inl q₁))) =
      carrierWeight (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ := fun q₁ =>
    hT₀.carrierWeight_first hz hr hr0 hη hw hchi hlt hS hS₁ q₁ _ (e.apply_symm_apply _)
  have hwt₂ : ∀ q₂, carrierWeight hn hQ T (e.symm (Sum.inl (Sum.inr q₂))) =
      carrierWeight (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ := fun q₂ =>
    hT₀.carrierWeight_second hz hr hr1 hη hw hchi hlt hS hS₂ q₂ _ (e.apply_symm_apply _)
  have hcoef₁ : ∀ q₁, cornerCoefficient hn hQ T (e.symm (Sum.inl (Sum.inl q₁))) hS =
      cornerCoefficient (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ hS₁ := fun q₁ =>
    hT₀.coef_first hsplit' hS hS₁ _ q₁ (e.apply_symm_apply _)
      (hT₀.cutFirst_of hz hr hr0 hchi hord _ q₁ (hrot₁ q₁).symm)
  have hcoef₂ : ∀ q₂, cornerCoefficient hn hQ T (e.symm (Sum.inl (Sum.inr q₂))) hS =
      cornerCoefficient (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ hS₂ := fun q₂ =>
    hT₀.coef_second hsplit' hS hS₂ _ q₂ (e.apply_symm_apply _)
      (hT₀.cutSecond_of hz hr hr1 hchi hord _ q₂ (hrot₂ q₂).symm)
  -- the contact triangle
  have htri : e.symm (Sum.inr (default : Unit)) = owner hn hQ T (Sum.inl M) := hT₀.symm_inr_unit
  have hwt_tri : carrierWeight hn hQ T (e.symm (Sum.inr (default : Unit))) =
      -((chi (g.curve (g.sideTime b t)) a (a + 1) M : SignType) : ℤ) := by
    rw [htri]; exact hT₀.carrierWeight_M hη hw hlt hS
  have hcoef_tri : cornerCoefficient hn hQ T (e.symm (Sum.inr (default : Unit))) hS = 1 := by
    have hnt : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by omega)
    have hσ : chi (g.curve (g.sideTime b t)) a (a + 1) M ≠ 0 :=
      hQ.1 a (a + 1) M (next_ne_self a).symm hsep.2.2.1.symm (s7e_a_ne_M hsep)
    have hwne : carrierWeight hn hQ T (e.symm (Sum.inr (default : Unit))) ≠ 0 := by
      rw [hwt_tri]
      rcases signType_nonzero_cases hσ with h0 | h0 <;> rw [h0] <;> decide
    rw [htri] at hwne ⊢
    exact (corner_values_i hn hQ hS _ (s7c_carrierUniform_of_weight_ne_zero hn hQ T _ hwne)
      (hT₀.carrierCrossingCount_M hη hw hlt)).2.2
  -- the products over the carriers
  have hwind : wind hn hQ T = ((∏ q₁, carrierWeight (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁) *
      ∏ q₂, carrierWeight (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂) *
      (-((chi (g.curve (g.sideTime b t)) a (a + 1) M : SignType) : ℤ)) := by
    unfold wind
    rw [Fintype.prod_equiv e (fun q => carrierWeight hn hQ T q) (fun c => carrierWeight hn hQ T (e.symm c))
      (fun q => by rw [Equiv.symm_apply_apply]), Fintype.prod_sum_type, Fintype.prod_sum_type,
      Fintype.prod_unique (fun u : Unit => carrierWeight hn hQ T (e.symm (Sum.inr u)))]
    simp only [hwt₁, hwt₂]
    rw [hwt_tri]
  have hcp : cornerProduct hn hQ T hS =
      ((∏ q₁, cornerCoefficient (contactHalfSizes_bounds hn hsep).1.1 h₁ S₁ q₁ hS₁) *
        ∏ q₂, cornerCoefficient (contactHalfSizes_bounds hn hsep).2.1 h₂ S₂ q₂ hS₂) * 1 := by
    unfold cornerProduct
    rw [Fintype.prod_equiv e (fun q => cornerCoefficient hn hQ T q hS)
      (fun c => cornerCoefficient hn hQ T (e.symm c) hS) (fun q => by rw [Equiv.symm_apply_apply]),
      Fintype.prod_sum_type, Fintype.prod_sum_type,
      Fintype.prod_unique (fun u : Unit => cornerCoefficient hn hQ T (e.symm (Sum.inr u)) hS)]
    simp only [hcoef₁, hcoef₂]
    rw [hcoef_tri]
  rw [s7e_term_of_decomposition hn (s7f_hP₂ g M a t) hS, s7e_term_of_decomposition _ h₁ hS₁,
    s7e_term_of_decomposition _ h₂ hS₂]
  show wind hn hQ T * cornerProduct hn hQ T hS = _
  rw [hwind, hcp, s7fb_neg_chi g h t]
  unfold wind cornerProduct
  ring

include hn h h₁ h₂ in
/-- **BLACK BOX 2 of unit F, PROVED**: the `ε = 0` two-newborn term identity below a radius. -/
theorem s7fb_exists_twoNewbornTerm :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      ∀ hsplit : s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t),
      ¬ s7f_Interlacing hn h t →
      ∀ (S₁ : Finset (Crossing (firstHalf g.center M a))) (S₂ : Finset (Crossing (secondHalf g.center M a))),
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ →
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ →
        s7e_term hn (s7f_hP₂ g M a t)
            (insert (s7f_x hn h t) (insert (s7f_y hn h t) (hsplit.split.joinSupport S₁ S₂))) =
          (s7f_dirSign g M a * (g.contactSign M a : ℤ)) *
            (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ *
              s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂) := by
  obtain ⟨r, η, hr0, hr1, hr, hη, hηr, hηr1, δ, hδ, -, hloc⟩ := s7a2_exists_intervalLocal hn g M a h.1
  obtain ⟨δ', hδ', hdet⟩ := s7fb_exists_detRadius hn g h hloc hr hr1 hδ
  refine ⟨min δ δ', lt_min hδ hδ', fun t ht hsplit hI S₁ S₂ hS₁ hS₂ => ?_⟩
  exact s7fb_twoNewbornTerm_at hn g h h₁ h₂ hloc hδ hr hr0 hr1 hη hηr hηr1 hdet t
    (lt_of_lt_of_le ht (min_le_left _ _)) (lt_of_lt_of_le ht (min_le_right _ _)) hsplit hI S₁ S₂ hS₁ hS₂

end S7FBAssembly

/-- **BLACK BOX 2 (geometric; sm-4:434-447, the `ε = 0` two-newborn row).**  Below a radius, for
non-interlacing newborns and eligible `T = ι₁ T₁ ∪ ι₂ T₂`, the selector-form term of `T ∪ {x, y}` on
`P₂` is `s₀ · term(T₁) · term(T₂)`, `s₀ = δ_dir · s` (`s7f_s₀_eq_chi`): smoothing the four newborn
visits makes the contact triangle — three corners of turn `−s₀` (`wt = s₀`, `s7c_carrierWeight_triangle`;
crossing-free uniform carrier of coefficient `1`, `corner_values`(i): `|rot| = 1`, `d = 0`, `c = 1`) —
and otherwise exactly the successors of `T₁, T₂` with equal weights and coefficients (U110-B §2.4's
bigon mark map with the two `μ_M`-vertices identified; U110-D's coefficient transport to the halves). -/
theorem s7f_exists_twoNewbornTerm :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      ∀ hsplit : s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t),
      ¬ s7f_Interlacing hn h t →
      ∀ (S₁ : Finset (Crossing (firstHalf g.center M a))) (S₂ : Finset (Crossing (secondHalf g.center M a))),
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ →
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ →
        s7e_term hn (s7f_hP₂ g M a t)
            (insert (s7f_x hn h t) (insert (s7f_y hn h t) (hsplit.split.joinSupport S₁ S₂))) =
          (s7f_dirSign g M a * (g.contactSign M a : ℤ)) *
            (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ *
              s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂) := by
  exact s7fb_exists_twoNewbornTerm hn g h h₁ h₂

/-- sm-4:418-420 on `P₂(t)`: a one- or two-newborn support containing an ineligible old crossing
(outside both half images) is not a decomposition — its term is `0`.  PROVED from the split. -/
theorem s7f_term_eq_zero_of_ineligible (t : g.SideParameter)
    (hsplit : s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t))
    (T : Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))
    (hz : ∃ z ∈ T, z ≠ s7f_x hn h t ∧ z ≠ s7f_y hn h t ∧
      z ∉ Set.range (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) ∪
        Set.range (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))))
    (hmem : s7f_x hn h t ∈ T ∨ s7f_y hn h t ∈ T) :
    s7e_term hn (s7f_hP₂ g M a t) T = 0 := by
  apply s7e_term_of_not
  intro hdec
  rw [s7b_isDecomposition_iff_indep] at hdec
  rcases hmem with hx | hy
  · exact hsplit.not_indep_of_mem_x hz hx hdec
  · exact hsplit.not_indep_of_mem_y hz hy hdec

/-- **`ε = 0`: the directed two-newborn sector is `J = s C(λ₁) C(λ₂)`** (sm-4:441-445 "Finite
distributivity and eq. s7c:bigon-signs show that the directed two-newborn sector is `J` when `ε = 0`"),
from the split and the termwise identity along `s7f_twoNewbornDecompositionEquiv`. -/
theorem s7f_twoNewbornSum_of_split (t : g.SideParameter)
    (hsplit : s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t))
    (hxy : ¬ Interlaces hn (s7f_hP₂ g M a t) (s7f_x hn h t) (s7f_y hn h t) ∧
      ¬ Interlaces hn (s7f_hP₂ g M a t) (s7f_y hn h t) (s7f_x hn h t))
    (hterm : ∀ (S₁ : Finset (Crossing (firstHalf g.center M a)))
        (S₂ : Finset (Crossing (secondHalf g.center M a))),
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ →
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ →
        s7e_term hn (s7f_hP₂ g M a t)
            (insert (s7f_x hn h t) (insert (s7f_y hn h t) (hsplit.split.joinSupport S₁ S₂))) =
          (s7f_dirSign g M a * (g.contactSign M a : ℤ)) *
            (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ *
              s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂)) :
    s7f_dirSign g M a * s7f_twoNewbornSum hn h t =
      (g.contactSign M a : ℤ) *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  classical
  let e := s7f_twoNewbornDecompositionEquiv hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))
    (s7f_hP₂ g M a t) h₁ h₂ (s7f_x hn h t) (s7f_y hn h t) hsplit hxy
  have h1 : ∑ T ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
        (fun T => s7f_x hn h t ∈ T ∧ s7f_y hn h t ∈ T), s7e_term hn (s7f_hP₂ g M a t) T =
      ∑ T ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
        (fun T => IsDecomposition hn (s7f_hP₂ g M a t) T ∧ s7f_x hn h t ∈ T ∧ s7f_y hn h t ∈ T),
        s7e_term hn (s7f_hP₂ g M a t) T := by
    symm
    apply Finset.sum_subset
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
      exact hT.2
    · intro T hT hT'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT hT'
      exact s7e_term_of_not _ _ (fun hd => hT' ⟨hd, hT⟩)
  have h1' : ∑ T ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
        (fun T => IsDecomposition hn (s7f_hP₂ g M a t) T ∧ s7f_x hn h t ∈ T ∧ s7f_y hn h t ∈ T),
        s7e_term hn (s7f_hP₂ g M a t) T =
      ∑ T : {T : Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))) //
        IsDecomposition hn (s7f_hP₂ g M a t) T ∧ s7f_x hn h t ∈ T ∧ s7f_y hn h t ∈ T},
        s7e_term hn (s7f_hP₂ g M a t) T.1 :=
    Finset.sum_subtype _ (fun T => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) _
  have h2 : ∑ T : {T : Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))) //
        IsDecomposition hn (s7f_hP₂ g M a t) T ∧ s7f_x hn h t ∈ T ∧ s7f_y hn h t ∈ T},
        s7e_term hn (s7f_hP₂ g M a t) T.1 =
      ∑ q, s7e_term hn (s7f_hP₂ g M a t) (e.symm q).1 :=
    Fintype.sum_equiv e _ _ (fun S => by rw [Equiv.symm_apply_apply])
  have hq : ∀ q, s7e_term hn (s7f_hP₂ g M a t) (e.symm q).1 =
      (s7f_dirSign g M a * (g.contactSign M a : ℤ)) *
        (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ q.1.1 *
          s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ q.2.1) :=
    fun q => hterm _ _ q.1.2 q.2.2
  have h3 : ∑ q, s7e_term hn (s7f_hP₂ g M a t) (e.symm q).1 =
      (s7f_dirSign g M a * (g.contactSign M a : ℤ)) *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
    simp_rw [hq]
    rw [← Finset.mul_sum, Fintype.sum_prod_type,
      s7e_cornerStateSum_eq_sum_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁,
      s7e_cornerStateSum_eq_sum_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂,
      ← s7e_sum_full_eq_of_zero (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁) (fun S hS => s7e_term_of_not _ _ hS),
      ← s7e_sum_full_eq_of_zero (s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂) (fun S hS => s7e_term_of_not _ _ hS),
      Finset.sum_mul_sum]
  unfold s7f_twoNewbornSum
  rw [h1, h1', h2, h3]
  linear_combination ((g.contactSign M a : ℤ) *
    (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
      cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) * s7f_dirSign_sq g M a

/-- **eq. s7c:sector-split `B = (1 − ε) J` at one side parameter**, from the split and the `ε = 0`
termwise identity. -/
theorem s7f_sector_split_at (t : g.SideParameter)
    (hsplit : s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t))
    (hterm : ¬ s7f_Interlacing hn h t →
      ∀ (S₁ : Finset (Crossing (firstHalf g.center M a)))
        (S₂ : Finset (Crossing (secondHalf g.center M a))),
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ →
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ →
        s7e_term hn (s7f_hP₂ g M a t)
            (insert (s7f_x hn h t) (insert (s7f_y hn h t) (hsplit.split.joinSupport S₁ S₂))) =
          (s7f_dirSign g M a * (g.contactSign M a : ℤ)) *
            (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ *
              s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂)) :
    s7f_dirSign g M a * s7f_twoNewbornSum hn h t =
      (if s7f_Interlacing hn h t then 0 else 1) *
        ((g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) := by
  by_cases hI : s7f_Interlacing hn h t
  · rw [ite_eq_left hI, s7f_twoNewbornSum_eq_zero hn h t hI, mul_zero, zero_mul]
  · rw [ite_eq_right hI, one_mul]
    exact s7f_twoNewbornSum_of_split hn g h h₁ h₂ t hsplit
      ⟨hI, fun hI' => hI (interlaces_symm _ _ hI')⟩ (hterm hI)

/-- **eq. s7c:sector-split `B = (1 − ε) J` below a radius — THE SHAPE FOR U110-K.**  With
`s7f_law_decomposition`, U110-K's remaining obligation is sm-4:448:
`δ_dir · ((Σ_pers(P₂) − C(P₀)) + Σ_one(P₂)) = ε · J` below a radius. -/
theorem s7f_sector_split :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      s7f_dirSign g M a * s7f_twoNewbornSum hn h t =
        (if s7f_Interlacing hn h t then 0 else 1) *
          ((g.contactSign M a : ℤ) *
            (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
              cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) := by
  obtain ⟨δ₁, hδ₁, hsplit⟩ := s7f_exists_bigonSplit hn g h h₁ h₂
  obtain ⟨δ₂, hδ₂, hterm⟩ := s7f_exists_twoNewbornTerm hn g h h₁ h₂
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht => ?_⟩
  exact s7f_sector_split_at hn g h h₁ h₂ t (hsplit t (lt_of_lt_of_le ht (min_le_left _ _)))
    (fun hI => hterm t (lt_of_lt_of_le ht (min_le_right _ _))
      (hsplit t (lt_of_lt_of_le ht (min_le_left _ _))) hI)

end S7FSectorSplit

section S7FSplitOf

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.BigonAt M a)
  (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter)

/-- **The bigon split from its OPEN geometric fields only.**  `inj₁ inj₂ disjoint` and the newborn
exclusions `x_not y_not` are U110-B's (`s7b_firstCrossingQ_injective`, `s7b_firstCrossingQ_ne_secondCrossingQ`,
`s7b_firstCrossingQ_not_affected` against `s7f_x_affected`/`s7f_y_affected`), so BLACK BOX 1
(`s7f_exists_bigonSplit`) reduces to: `rel₁ rel₂` (U_S7B_REPORT §2.2, the halves' interlacement is the
restriction of `P₂`'s), `cross cross'` (no interlacement across the two half images), `x_free y_free`
(the newborn chords interlace no internal label of `A` or `B`) and `x_split y_split` (sm-4:414-416). -/
theorem s7f_bigonSplit_of
    (hrel₁ : ∀ c c', (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c') ↔ (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁) c c')
    (hrel₂ : ∀ c c', (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c') ↔ (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂) c c')
    (hcross : ∀ c₁ c₂, ¬ (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c₁) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c₂))
    (hcross' : ∀ c₁ c₂, ¬ (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c₂) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c₁))
    (hxfree₁ : ∀ c, ¬ (Interlaces hn (s7f_hP₂ g M a t)) (s7f_x hn h t) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) ∧ ¬ (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) (s7f_x hn h t))
    (hxfree₂ : ∀ c, ¬ (Interlaces hn (s7f_hP₂ g M a t)) (s7f_x hn h t) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) ∧ ¬ (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) (s7f_x hn h t))
    (hyfree₁ : ∀ c, ¬ (Interlaces hn (s7f_hP₂ g M a t)) (s7f_y hn h t) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) ∧ ¬ (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) (s7f_y hn h t))
    (hyfree₂ : ∀ c, ¬ (Interlaces hn (s7f_hP₂ g M a t)) (s7f_y hn h t) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) ∧ ¬ (Interlaces hn (s7f_hP₂ g M a t)) ((s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) c) (s7f_y hn h t))
    (hxsplit : ∀ z, z ≠ (s7f_x hn h t) → z ≠ (s7f_y hn h t) → ¬ (Interlaces hn (s7f_hP₂ g M a t)) (s7f_x hn h t) z → ¬ (Interlaces hn (s7f_hP₂ g M a t)) z (s7f_x hn h t) →
      z ∈ Set.range (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) ∪ Set.range (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))))
    (hysplit : ∀ z, z ≠ (s7f_x hn h t) → z ≠ (s7f_y hn h t) → ¬ (Interlaces hn (s7f_hP₂ g M a t)) (s7f_y hn h t) z → ¬ (Interlaces hn (s7f_hP₂ g M a t)) z (s7f_y hn h t) →
      z ∈ Set.range (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) ∪ Set.range (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))) :
    s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t)) (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁) (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂) (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) (s7f_x hn h t) (s7f_y hn h t) where
  split :=
    { inj₁ := s7b_firstCrossingQ_injective hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))
      inj₂ := s7b_secondCrossingQ_injective hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))
      disjoint := fun c₁ c₂ =>
        s7b_firstCrossingQ_ne_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)) c₁ c₂
      rel₁ := hrel₁
      rel₂ := hrel₂
      cross := hcross
      cross' := hcross' }
  x_not₁ := fun c he => s7b_firstCrossingQ_not_affected hn h.1.1 h.1.2.2.2.1
    (s7f_hQC hn h.1 t (s7f_side g M a)) c (by rw [he]; exact s7f_x_affected hn h t)
  x_not₂ := fun c he => s7b_secondCrossingQ_not_affected hn h.1.1 h.1.2.2.2.1
    (s7f_hQC hn h.1 t (s7f_side g M a)) c (by rw [he]; exact s7f_x_affected hn h t)
  y_not₁ := fun c he => s7b_firstCrossingQ_not_affected hn h.1.1 h.1.2.2.2.1
    (s7f_hQC hn h.1 t (s7f_side g M a)) c (by rw [he]; exact s7f_y_affected hn h t)
  y_not₂ := fun c he => s7b_secondCrossingQ_not_affected hn h.1.1 h.1.2.2.2.1
    (s7f_hQC hn h.1 t (s7f_side g M a)) c (by rw [he]; exact s7f_y_affected hn h t)
  x_free₁ := hxfree₁
  x_free₂ := hxfree₂
  y_free₁ := hyfree₁
  y_free₂ := hyfree₂
  x_split := hxsplit
  y_split := hysplit

end S7FSplitOf

section S7FPersistent

/-! #### The persistent sector of `P₂` as the supports of `P₀` (sm-4:418-421): every crossing of
`P₀(t)` is persistent and lifts to `P₂(t)`; the lifts are exactly the newborn-free supports.  The
ineligible rows cancel by the U110-A/A2/D transport (BLACK BOX 3), so the persistent-sector difference
`Σ_pers(P₂) − C(P₀)` reduces to the ELIGIBLE rows — the input of the skein branch (U110-K/G/H/I/J). -/

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.BigonAt M a) (t : g.SideParameter)

include hn h in
/-- Persistent crossings agree between the two sides (both agree with the centre). -/
theorem s7f_hs : ∀ s, ¬ ContactAffected M a s →
    (IsCrossing (g.curve (g.sideTime (s7f_side g M a) t)) s ↔
      IsCrossing (g.curve (g.sideTime (!s7f_side g M a) t)) s) :=
  fun s hs => (s7f_hQC hn h.1 t (s7f_side g M a) s hs).trans (s7f_hQC hn h.1 t (!s7f_side g M a) s hs).symm

include hn h in
/-- A crossing of `P₀(t)` read on `P₂(t)`. -/
noncomputable def s7f_liftCross (z : Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) :
    Crossing (g.curve (g.sideTime (s7f_side g M a) t)) :=
  ⟨z.val, (s7f_hs hn g h t z.val (s7f_P₀_not_affected hn h t z)).mpr z.property⟩

theorem s7f_liftCross_val (z : Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) :
    (s7f_liftCross hn g h t z).val = z.val := rfl

theorem s7f_liftCross_injective : Function.Injective (s7f_liftCross hn g h t) :=
  fun z w he => Subtype.ext (show (s7f_liftCross hn g h t z).val = (s7f_liftCross hn g h t w).val from
    congrArg Subtype.val he)

theorem s7f_liftCross_ne_x (z : Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) :
    s7f_liftCross hn g h t z ≠ s7f_x hn h t := fun he =>
  s7f_P₀_not_affected hn h t z (by rw [← s7f_liftCross_val hn g h t z, he]; exact s7f_x_affected hn h t)

theorem s7f_liftCross_ne_y (z : Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) :
    s7f_liftCross hn g h t z ≠ s7f_y hn h t := fun he =>
  s7f_P₀_not_affected hn h t z (by rw [← s7f_liftCross_val hn g h t z, he]; exact s7f_y_affected hn h t)

/-- A crossing of `P₂(t)` other than the newborns is a lift. -/
theorem s7f_exists_liftCross (z : Crossing (g.curve (g.sideTime (s7f_side g M a) t)))
    (hx : z ≠ s7f_x hn h t) (hy : z ≠ s7f_y hn h t) : ∃ w, s7f_liftCross hn g h t w = z := by
  have hz : ¬ ContactAffected M a z.val := fun ha => by
    rcases s7f_eq_x_or_y_of_affected hn h t z ha with h' | h'
    · exact hx h'
    · exact hy h'
  exact ⟨⟨z.val, (s7f_hs hn g h t z.val hz).mp z.property⟩, Subtype.ext rfl⟩

/-- The lift of a support of `P₀(t)` to `P₂(t)` (the same crossing set). -/
noncomputable def s7f_lift (T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t)))) :
    Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))) :=
  T₀.map ⟨s7f_liftCross hn g h t, s7f_liftCross_injective hn g h t⟩

theorem s7f_mem_lift (T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))
    (z : Crossing (g.curve (g.sideTime (s7f_side g M a) t))) :
    z ∈ s7f_lift hn g h t T₀ ↔ ∃ w ∈ T₀, s7f_liftCross hn g h t w = z := by
  simp only [s7f_lift, Finset.mem_map, Function.Embedding.coeFn_mk]

theorem s7f_liftCross_mem_lift (T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))
    (w : Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) :
    s7f_liftCross hn g h t w ∈ s7f_lift hn g h t T₀ ↔ w ∈ T₀ :=
  Finset.mem_map' _

theorem s7f_x_not_mem_lift (T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t)))) :
    s7f_x hn h t ∉ s7f_lift hn g h t T₀ := fun hx => by
  obtain ⟨w, -, hw⟩ := (s7f_mem_lift hn g h t T₀ _).mp hx
  exact s7f_liftCross_ne_x hn g h t w hw

theorem s7f_y_not_mem_lift (T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t)))) :
    s7f_y hn h t ∉ s7f_lift hn g h t T₀ := fun hy => by
  obtain ⟨w, -, hw⟩ := (s7f_mem_lift hn g h t T₀ _).mp hy
  exact s7f_liftCross_ne_y hn g h t w hw

theorem s7f_lift_injective : Function.Injective (s7f_lift hn g h t) :=
  Finset.map_injective _

/-- Every newborn-free support of `P₂(t)` is the lift of a support of `P₀(t)`. -/
theorem s7f_lift_surj (T : Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))
    (hx : s7f_x hn h t ∉ T) (hy : s7f_y hn h t ∉ T) : ∃ T₀, s7f_lift hn g h t T₀ = T := by
  refine ⟨Finset.univ.filter (fun w => s7f_liftCross hn g h t w ∈ T), ?_⟩
  ext z
  rw [s7f_mem_lift]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (Finset.mem_filter.mp hw).2
  · intro hz
    obtain ⟨w, rfl⟩ := s7f_exists_liftCross hn g h t z (fun he => hx (he ▸ hz)) (fun he => hy (he ▸ hz))
    exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩, rfl⟩

/-- The persistent sector of `P₂(t)` is the sum over the supports of `P₀(t)` of the lifted terms. -/
theorem s7f_persistentSum_eq_sum_lift :
    s7f_persistentSum hn h t =
      ∑ T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))),
        s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) := by
  unfold s7f_persistentSum
  have himg : (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
      (fun T => s7f_x hn h t ∉ T ∧ s7f_y hn h t ∉ T) = Finset.univ.image (s7f_lift hn g h t) := by
    ext T
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hx, hy⟩
      obtain ⟨T₀, hT₀⟩ := s7f_lift_surj hn g h t T hx hy
      exact ⟨T₀, Finset.mem_univ _, hT₀⟩
    · rintro ⟨T₀, -, rfl⟩
      exact ⟨Finset.mem_univ _, s7f_x_not_mem_lift hn g h t T₀, s7f_y_not_mem_lift hn g h t T₀⟩
  rw [himg, Finset.sum_image (fun T₀ _ T₀' _ he => s7f_lift_injective hn g h t he)]

/-- An old support of `P₀(t)` is ELIGIBLE when every crossing lifts into one of the two half images
(`T ∩ N = ∅`, sm-4:416-417). -/
def s7f_Eligible (T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t)))) : Prop :=
  ∀ z ∈ T₀, s7f_liftCross hn g h t z ∈
    Set.range (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a))) ∪ Set.range (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))

/-- **BLACK BOX 3 (geometric; sm-4:418-421 "Deleting their four visits identifies the complete smoothing
successor, owners, corners, rotations, carrier diagrams and coefficient reads. The entire ineligible
returned sector is therefore zero").**  Below a radius, an INELIGIBLE persistent row has equal terms on
the two sides: the support is persistent (U110-A `s7a_sideComponentEquiv`, U110-A2
`s7a2_carrierRotation_eq` for `hr`, U110-D `s7d_cornerCoefficient_eq_of_strictMono` — the exact pattern
of `s7e_term_eq`), and since a smoothed chord of `N` separates the two visits of each newborn, `x, y`
are MIXED crossings of `P₂`'s carriers, never self-crossings — so `hmem` holds with the carrier
crossing sets literally equal (`s7a_side_mem_carrierCrossings` + this separation fact). -/
theorem s7f_exists_ineligible_transport :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      ∀ T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))), ¬ s7f_Eligible hn g h t T₀ →
        s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) = s7e_term hn (s7f_hP₀ g M a t) T₀ := by
  sorry

/-- sm-4:420-421: given the ineligible transport at `t`, the persistent-sector difference is the sum of
the ELIGIBLE row differences. -/
theorem s7f_persistent_difference_of_transport
    (htr : ∀ T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))), ¬ s7f_Eligible hn g h t T₀ →
      s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) = s7e_term hn (s7f_hP₀ g M a t) T₀) :
    s7f_persistentSum hn h t - cornerStateSum hn (s7f_hP₀ g M a t) =
      ∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
          (s7f_Eligible hn g h t),
        (s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) - s7e_term hn (s7f_hP₀ g M a t) T₀) := by
  rw [s7f_persistentSum_eq_sum_lift hn g h t, s7e_cornerStateSum_eq_sum_term, ← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (s7f_Eligible hn g h t)]
  have h0 : ∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
      (fun T₀ => ¬ s7f_Eligible hn g h t T₀),
        (s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) - s7e_term hn (s7f_hP₀ g M a t) T₀) = 0 :=
    Finset.sum_eq_zero fun T₀ hT₀ => by rw [htr T₀ (Finset.mem_filter.mp hT₀).2, sub_self]
  rw [h0, add_zero]

/-- **The residual for U110-K** (sm-4:448 `R_ret = εJ`; with `s7f_sector_split` for `B`): given the
ineligible transport at `t`,
`C(P₊) − C(P₋) = δ_dir · (Σ_(eligible T₀) (term₂(lift T₀) − term₀(T₀)) + Σ_one(P₂) + Σ_two(P₂))`. -/
theorem s7f_law_decomposition_eligible
    (htr : ∀ T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))), ¬ s7f_Eligible hn g h t T₀ →
      s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) = s7e_term hn (s7f_hP₀ g M a t) T₀) :
    cornerStateSum hn (g.sideTuple true t).property - cornerStateSum hn (g.sideTuple false t).property =
      s7f_dirSign g M a *
        (∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
            (s7f_Eligible hn g h t),
          (s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) - s7e_term hn (s7f_hP₀ g M a t) T₀) +
          s7f_oneNewbornSum hn h t + s7f_twoNewbornSum hn h t) := by
  rw [s7f_law_decomposition hn h t, s7f_persistent_difference_of_transport hn g h t htr]

end S7FPersistent

section S7FOneNewborn

/-! #### The one-newborn sector of `P₂` as the supports of `P₀` (sm-4:418-420, 777-783): a one-newborn
support is `T₀ ∪ {x}` or `T₀ ∪ {y}` for a unique support `T₀` of `P₀`, and the ineligible rows vanish
(`s7f_term_eq_zero_of_ineligible`), so `Σ_one(P₂)` is a sum over the ELIGIBLE `T₀` — the input of the
cb:singleton step (U110-K/J). -/

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.BigonAt M a)
  (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter)

theorem s7f_insert_x_lift_injective :
    Function.Injective (fun T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) =>
      insert (s7f_x hn h t) (s7f_lift hn g h t T₀)) := by
  intro T₀ T₀' he
  apply s7f_lift_injective hn g h t
  rw [← Finset.erase_insert (s7f_x_not_mem_lift hn g h t T₀),
    ← Finset.erase_insert (s7f_x_not_mem_lift hn g h t T₀')]
  simp only at he
  rw [he]

theorem s7f_insert_y_lift_injective :
    Function.Injective (fun T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))) =>
      insert (s7f_y hn h t) (s7f_lift hn g h t T₀)) := by
  intro T₀ T₀' he
  apply s7f_lift_injective hn g h t
  rw [← Finset.erase_insert (s7f_y_not_mem_lift hn g h t T₀),
    ← Finset.erase_insert (s7f_y_not_mem_lift hn g h t T₀')]
  simp only at he
  rw [he]

/-- The one-newborn supports of `P₂(t)` are the `T₀ ∪ {x}` and the `T₀ ∪ {y}`. -/
theorem s7f_oneNewborn_filter_eq :
    (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (s7f_side g M a) t))))).filter
        (fun T => (s7f_x hn h t ∈ T ∧ s7f_y hn h t ∉ T) ∨ (s7f_x hn h t ∉ T ∧ s7f_y hn h t ∈ T)) =
      Finset.univ.image (fun T₀ => insert (s7f_x hn h t) (s7f_lift hn g h t T₀)) ∪
        Finset.univ.image (fun T₀ => insert (s7f_y hn h t) (s7f_lift hn g h t T₀)) := by
  ext T
  rw [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨-, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
    · left
      obtain ⟨T₀, hT₀⟩ := s7f_lift_surj hn g h t (T.erase (s7f_x hn h t)) (Finset.notMem_erase _ _)
        (fun hy' => hy (Finset.mem_of_mem_erase hy'))
      exact ⟨T₀, Finset.mem_univ _, by rw [hT₀, Finset.insert_erase hx]⟩
    · right
      obtain ⟨T₀, hT₀⟩ := s7f_lift_surj hn g h t (T.erase (s7f_y hn h t))
        (fun hx' => hx (Finset.mem_of_mem_erase hx')) (Finset.notMem_erase _ _)
      exact ⟨T₀, Finset.mem_univ _, by rw [hT₀, Finset.insert_erase hy]⟩
  · rintro (⟨T₀, -, rfl⟩ | ⟨T₀, -, rfl⟩)
    · refine ⟨Finset.mem_univ _, Or.inl ⟨Finset.mem_insert_self _ _, fun hy => ?_⟩⟩
      rcases Finset.mem_insert.mp hy with h' | h'
      · exact s7f_x_ne_y hn h t h'.symm
      · exact s7f_y_not_mem_lift hn g h t T₀ h'
    · refine ⟨Finset.mem_univ _, Or.inr ⟨fun hx => ?_, Finset.mem_insert_self _ _⟩⟩
      rcases Finset.mem_insert.mp hx with h' | h'
      · exact s7f_x_ne_y hn h t h'
      · exact s7f_x_not_mem_lift hn g h t T₀ h'

theorem s7f_oneNewborn_images_disjoint :
    Disjoint (Finset.univ.image (fun T₀ => insert (s7f_x hn h t) (s7f_lift hn g h t T₀)))
      (Finset.univ.image (fun T₀ => insert (s7f_y hn h t) (s7f_lift hn g h t T₀))) := by
  rw [Finset.disjoint_left]
  intro T hT₁ hT₂
  obtain ⟨T₀, -, rfl⟩ := Finset.mem_image.mp hT₁
  obtain ⟨T₀', -, he⟩ := Finset.mem_image.mp hT₂
  have hx : s7f_x hn h t ∈ insert (s7f_y hn h t) (s7f_lift hn g h t T₀') := by
    rw [he]; exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hx with h' | h'
  · exact s7f_x_ne_y hn h t h'
  · exact s7f_x_not_mem_lift hn g h t T₀' h'

/-- The one-newborn sector of `P₂(t)` as a sum over the supports of `P₀(t)`. -/
theorem s7f_oneNewbornSum_eq_sum_lift :
    s7f_oneNewbornSum hn h t =
      ∑ T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))),
        (s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_x hn h t) (s7f_lift hn g h t T₀)) +
          s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_y hn h t) (s7f_lift hn g h t T₀))) := by
  unfold s7f_oneNewbornSum
  rw [s7f_oneNewborn_filter_eq hn g h t, Finset.sum_union (s7f_oneNewborn_images_disjoint hn g h t),
    Finset.sum_image (fun T₀ _ T₀' _ he => s7f_insert_x_lift_injective hn g h t he),
    Finset.sum_image (fun T₀ _ T₀' _ he => s7f_insert_y_lift_injective hn g h t he),
    ← Finset.sum_add_distrib]

/-- **The one-newborn sector for U110-K** (sm-4:418-420 + 777-783): given the split at `t`, the
ineligible one-newborn rows vanish and `Σ_one(P₂)` is the sum over the ELIGIBLE `T₀` of
`term(T₀ ∪ {x}) + term(T₀ ∪ {y})`. -/
theorem s7f_oneNewbornSum_of_split
    (hsplit : s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t)) :
    s7f_oneNewbornSum hn h t =
      ∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
          (s7f_Eligible hn g h t),
        (s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_x hn h t) (s7f_lift hn g h t T₀)) +
          s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_y hn h t) (s7f_lift hn g h t T₀))) := by
  rw [s7f_oneNewbornSum_eq_sum_lift hn g h t,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (s7f_Eligible hn g h t)]
  have h0 : ∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
      (fun T₀ => ¬ s7f_Eligible hn g h t T₀),
        (s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_x hn h t) (s7f_lift hn g h t T₀)) +
          s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_y hn h t) (s7f_lift hn g h t T₀))) = 0 := by
    apply Finset.sum_eq_zero
    intro T₀ hT₀
    have hne := (Finset.mem_filter.mp hT₀).2
    unfold s7f_Eligible at hne
    push Not at hne
    obtain ⟨z, hz, hzr⟩ := hne
    have hzx := s7f_liftCross_ne_x hn g h t z
    have hzy := s7f_liftCross_ne_y hn g h t z
    have hzl : s7f_liftCross hn g h t z ∈ s7f_lift hn g h t T₀ := (s7f_liftCross_mem_lift hn g h t T₀ z).mpr hz
    rw [s7f_term_eq_zero_of_ineligible hn g h h₁ h₂ t hsplit _
        ⟨_, Finset.mem_insert_of_mem hzl, hzx, hzy, hzr⟩ (Or.inl (Finset.mem_insert_self _ _)),
      s7f_term_eq_zero_of_ineligible hn g h h₁ h₂ t hsplit _
        ⟨_, Finset.mem_insert_of_mem hzl, hzx, hzy, hzr⟩ (Or.inr (Finset.mem_insert_self _ _)), add_zero]
  rw [h0, add_zero]

end S7FOneNewborn

section S7FResidual

variable (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n} (h : g.BigonAt M a)
  (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))

/-- **THE SHAPE FOR U110-K, at one side parameter** (sm-4:396-448 assembled): given the bigon split, the
`ε = 0` termwise identity and the ineligible transport at `t`,
`C(P₊) − C(P₋) = (1 − ε)·J + δ_dir·(Σ_{eligible T₀} (term₂(T₀) − term₀(T₀)) + Σ_{eligible T₀} (term(T₀∪{x}) + term(T₀∪{y})))`,
`J = s·C(λ₁)·C(λ₂)`.  U110-K's obligation is that the second summand is `ε·J` (sm-4:448 onward:
skein extraction, two-component row, rotation ledger, floor and cb:singleton). -/
theorem s7f_law_residual (t : g.SideParameter)
    (hsplit : s7f_BigonSplit (Interlaces hn (s7f_hP₂ g M a t))
        (Interlaces (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
        (Interlaces (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
        (s7b_firstCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7b_secondCrossingQ hn h.1.1 h.1.2.2.2.1 (s7f_hQC hn h.1 t (s7f_side g M a)))
        (s7f_x hn h t) (s7f_y hn h t))
    (hterm : ¬ s7f_Interlacing hn h t →
      ∀ (S₁ : Finset (Crossing (firstHalf g.center M a)))
        (S₂ : Finset (Crossing (secondHalf g.center M a))),
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ →
        IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂ →
        s7e_term hn (s7f_hP₂ g M a t)
            (insert (s7f_x hn h t) (insert (s7f_y hn h t) (hsplit.split.joinSupport S₁ S₂))) =
          (s7f_dirSign g M a * (g.contactSign M a : ℤ)) *
            (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁ *
              s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂))
    (htr : ∀ T₀ : Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))), ¬ s7f_Eligible hn g h t T₀ →
      s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) = s7e_term hn (s7f_hP₀ g M a t) T₀) :
    cornerStateSum hn (g.sideTuple true t).property - cornerStateSum hn (g.sideTuple false t).property =
      (if s7f_Interlacing hn h t then 0 else 1) *
        ((g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) +
      s7f_dirSign g M a *
        (∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
            (s7f_Eligible hn g h t),
          (s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) - s7e_term hn (s7f_hP₀ g M a t) T₀) +
         ∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
            (s7f_Eligible hn g h t),
          (s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_x hn h t) (s7f_lift hn g h t T₀)) +
            s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_y hn h t) (s7f_lift hn g h t T₀)))) := by
  rw [s7f_law_decomposition_eligible hn g h t htr, s7f_oneNewbornSum_of_split hn g h h₁ h₂ t hsplit,
    ← s7f_sector_split_at hn g h h₁ h₂ t hsplit hterm]
  ring

/-- **THE SHAPE FOR U110-K, below a radius**, from the three black boxes `s7f_exists_bigonSplit`,
`s7f_exists_twoNewbornTerm`, `s7f_exists_ineligible_transport`. -/
theorem s7f_exists_law_residual :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property - cornerStateSum hn (g.sideTuple false t).property =
        (if s7f_Interlacing hn h t then 0 else 1) *
          ((g.contactSign M a : ℤ) *
            (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
              cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) +
        s7f_dirSign g M a *
          (∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
              (s7f_Eligible hn g h t),
            (s7e_term hn (s7f_hP₂ g M a t) (s7f_lift hn g h t T₀) - s7e_term hn (s7f_hP₀ g M a t) T₀) +
           ∑ T₀ ∈ (Finset.univ : Finset (Finset (Crossing (g.curve (g.sideTime (!s7f_side g M a) t))))).filter
              (s7f_Eligible hn g h t),
            (s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_x hn h t) (s7f_lift hn g h t T₀)) +
              s7e_term hn (s7f_hP₂ g M a t) (insert (s7f_y hn h t) (s7f_lift hn g h t T₀)))) := by
  obtain ⟨δ₁, hδ₁, hsplit⟩ := s7f_exists_bigonSplit hn g h h₁ h₂
  obtain ⟨δ₂, hδ₂, hterm⟩ := s7f_exists_twoNewbornTerm hn g h h₁ h₂
  obtain ⟨δ₃, hδ₃, htr⟩ := s7f_exists_ineligible_transport hn g h
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), fun t ht => ?_⟩
  have ht₁ : t.val < δ₁ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht₂ : t.val < δ₂ := lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_left _ _))
  have ht₃ : t.val < δ₃ := lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_right _ _))
  exact s7f_law_residual hn g h h₁ h₂ t (hsplit t ht₁) (fun hI => hterm t ht₂ (hsplit t ht₁) hI) (htr t ht₃)

end S7FResidual

/-! ### Unit S7-SITE (I-110; prefix `s7s_`; corner wave 3, audit A-110-1)

The wall bigon site of PLAN_FINAL §3.3 bigon (2) on the ported `SM.BigonDeletion`: on the positive lift
`D_H` of a carrier `q` of a decomposition `S` of the bigon-side polygon `P` that RETAINS the two contact
crossings `x = x_{M−1,a}`, `y = x_{a,M}` (the "full contact carrier" through the vertex `M`), the switch
of `D_H` at (the lift of) `x` carries a `BigonData` whose bigon is `{x, y}` and whose region is the closed
contact triangle `K = conv{x, P M, y}` (`s7s_core`, via `exists_bigonData_of_triangle`).  Pattern: the
landed site `work/drafts/moves/Site_174.lean` (`s174_core`), with the corner at a polygon VERTEX instead of
a selected crossing: the corner index is `j_in + 1` (`hjout`, `hcorner`), the two `a`-visits are adjacent
(`hadj_s`), the contact crossing signs alternate (`hsgn`), and the other carrier edges are clear of `K`
(`hclear`) — these carrier-form facts are the wall data of U110-A/B (window clauses of
`VertexLocalData`, the printed emptiness sm-4:618-620): `hsgn` is PROVED from planar geometry
(`s7s_contact_sign`), `hjout`/`hcorner` from the window clauses by the block argument (`s7s_jout_of_wall`,
`s7s_cornerPolygon_of_wall`), `hclear` for the non-local carrier edges (`s7s_carrier_data_of_wall`); the
black boxes are `s7s_clear_local` (the carrier edges on the three local `P`-edges) and the `P`-level wall
data `s7s_wallTriangleData_of_bigon` (U110-A/B).  Then `s7s_switch_value`: given the record
identification `hrec` (`s7s_hrec_prop`, stated), `P (D_H.switch x) = P D_L` through the proved glue
`s7_switch_value_of_bigon` — exactly the hypothesis of `s7g_switch_value_of_rii` / the input of
`s7g_cornerHomfly_skein`, delivered on the accepted `positiveLift` by `geoPositiveLift_eq_generic`. -/

section S7Site

open GeoCarrier RProof

/-! #### s7s.1 Generic helpers (site-174 pattern; `Shadow.positiveDiagram`, `Diagram.switch`) -/

omit [NeZero n] in
theorem s7s_pos_over_iff {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing) {s t : Γ.Strand}
    (hx : x.val = {s, t}) (hst : s ≠ t) :
    (Γ.positiveDiagram hΓ).overStrand x = s ↔ 0 < det (Γ.dir s) (Γ.dir t) := by
  have hpos : 0 < det (Γ.dir ((Γ.positiveDiagram hΓ).overStrand x))
      (Γ.dir ((Γ.positiveDiagram hΓ).underStrand x)) := Γ.positiveDiagram_det_pos hΓ x
  have hs : s ∈ x.val := by rw [hx]; exact Finset.mem_insert_self _ _
  have ht : t ∈ x.val := by rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hmem : (Γ.positiveDiagram hΓ).overStrand x ∈ ({s, t} : Finset Γ.Strand) := by
    rw [← hx]; exact (Γ.positiveDiagram hΓ).over_mem x
  constructor
  · intro h
    have hu : (Γ.positiveDiagram hΓ).underStrand x = t :=
      ((Γ.positiveDiagram hΓ).eq_under_of_mem_of_ne x ht
        (fun heq => hst.symm (heq.trans h))).symm
    rw [h, hu] at hpos
    exact hpos
  · intro hdet
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · exfalso
      have h' : (Γ.positiveDiagram hΓ).overStrand x = t := Finset.mem_singleton.mp h
      have hu : (Γ.positiveDiagram hΓ).underStrand x = s :=
        ((Γ.positiveDiagram hΓ).eq_under_of_mem_of_ne x hs (fun heq => hst (heq.trans h'))).symm
      rw [h', hu, det_swap] at hpos
      linarith

omit [NeZero n] in
theorem s7s_switch_over_self_iff (D : Diagram) (x : D.Γ.Crossing) {s t : D.Γ.Strand}
    (hx : x.val = {s, t}) (hst : s ≠ t) :
    (D.switch x).overStrand x = s ↔ D.overStrand x = t := by
  have hs : s ∈ x.val := by rw [hx]; exact Finset.mem_insert_self _ _
  have ht : t ∈ x.val := by rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [D.switch_overStrand_self]
  constructor
  · intro h
    exact (D.eq_over_of_mem_of_ne x ht (by rw [h]; exact hst.symm)).symm
  · intro h
    exact (D.eq_under_of_mem_of_ne x hs (by rw [h]; exact hst)).symm

omit [NeZero n] in
/-- the over strand is the second strand iff it is not the first -/
theorem s7s_over_other_iff (D : Diagram) (x : D.Γ.Crossing) {s t : D.Γ.Strand}
    (hx : x.val = {s, t}) (hst : s ≠ t) : D.overStrand x = t ↔ D.overStrand x ≠ s := by
  have hmem : D.overStrand x ∈ ({s, t} : Finset D.Γ.Strand) := by rw [← hx]; exact D.over_mem x
  constructor
  · intro h heq; exact hst (heq.symm.trans h)
  · intro h
    rcases Finset.mem_insert.mp hmem with h' | h'
    · exact absurd h' h
    · exact Finset.mem_singleton.mp h'

omit [NeZero n] in
theorem s7s_pos_iff_of_sign_eq {a b : ℝ} (h : SignType.sign a = SignType.sign b) :
    0 < a ↔ 0 < b := by
  rw [← sign_eq_one_iff, ← sign_eq_one_iff, h]

omit [NeZero n] in
theorem s7s_neg_pos_iff_of_sign_eq {a b : ℝ} (h : SignType.sign a = SignType.sign b) :
    0 < -a ↔ 0 < -b := by
  rw [neg_pos, neg_pos, ← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, h]

omit [NeZero n] in
theorem s7s_not_pos_iff {a : ℝ} (ha : a ≠ 0) : ¬ 0 < a ↔ 0 < -a := by
  rw [not_lt, neg_pos]
  exact ⟨fun h => lt_of_le_of_ne h ha, le_of_lt⟩

omit [NeZero n] in
theorem s7s_det_smul_pos_iff {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (u v : Plane) :
    0 < det (c • u) (d • v) ↔ 0 < det u v := by
  rw [gu2_det_smul_smul]
  exact ⟨fun h => pos_of_mul_pos_right h (mul_pos hc hd).le,
    fun h => mul_pos (mul_pos hc hd) h⟩

theorem s7s_adjacent_zmod3 (i j : ZMod 3) : adjacent i j := by
  unfold adjacent
  have hv : ((j - i).val : ZMod 3) = j - i := ZMod.natCast_zmod_val (j - i)
  have hlt : (j - i).val < 3 := ZMod.val_lt (j - i)
  rw [← hv]
  generalize (j - i).val = d at hlt
  interval_cases d
  · right; left; rfl
  · right; right; rfl
  · left; decide

theorem s7s_four_le {k : ℕ} (hk : 3 ≤ k) (h : ∃ i j : ZMod k, ¬ adjacent i j) : 4 ≤ k := by
  by_contra hlt
  have h3 : k = 3 := by omega
  subst h3
  obtain ⟨i, j, hij⟩ := h
  exact hij (s7s_adjacent_zmod3 i j)

omit [NeZero n] in
/-- two strands of a one-component shadow with non-adjacent labels are distinct -/
theorem s7s_strand_ne_of_not_adjacent {C : PolyComp} {j j' : ZMod C.k} (h : ¬ adjacent j j') :
    (⟨0, j⟩ : (Shadow.single C).Strand) ≠ ⟨0, j'⟩ := by
  intro heq
  apply h
  have hjj : j = j' := eq_of_heq (Sigma.mk.inj heq).2
  rw [hjj]
  exact Or.inr (Or.inl (sub_self _))

/-! #### s7s.2 The lifted crossings of a carrier (site-174 pattern on `geoCarrierCrossingEquiv`) -/

section S7SiteCore

variable {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)

/-- the crossing of the carrier shadow at a retained crossing `c` of the carrier `q` -/
noncomputable def s7s_lift (c : Crossing P) (hc : c ∈ geoCarrierCrossings hG.cg S q) :
    (geoCarrierShadow hn hG hS q).Crossing :=
  (geoCarrierCrossingEquiv hn hG hS q).symm ⟨c, hc⟩

theorem s7s_lift_crossingPoint (c : Crossing P) (hc : c ∈ geoCarrierCrossings hG.cg S q) :
    (geoCarrierShadow hn hG hS q).crossingPoint (s7s_lift hn hG hS q c hc) = crossingPoint c := by
  have h := crossingPoint_geoCarrierCrossingEquiv hn hG hS q (s7s_lift hn hG hS q c hc)
  rw [s7s_lift, Equiv.apply_symm_apply] at h
  exact h.symm

theorem s7s_lift_injective_pt {c c' : Crossing P} (hc : c ∈ geoCarrierCrossings hG.cg S q)
    (hc' : c' ∈ geoCarrierCrossings hG.cg S q) (hne : c ≠ c') :
    s7s_lift hn hG hS q c hc ≠ s7s_lift hn hG hS q c' hc' := by
  intro h
  apply hne
  have := congrArg (geoCarrierShadow hn hG hS q).crossingPoint h
  rw [s7s_lift_crossingPoint, s7s_lift_crossingPoint] at this
  exact crossingPoint_injective_of_geometry hG.cg this

/-- the strands of the lifted crossing are the two carrier edges of the visits of `v.1` -/
theorem s7s_lift_val (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg S q)
    (hv' : (visitTwin v).1 ∈ geoCarrierCrossings hG.cg S q) :
    (s7s_lift hn hG hS q v.1 hv).val =
      {(⟨0, G11_carrierEdge hn hG hS q v hv⟩ : (geoCarrierShadow hn hG hS q).Strand),
       ⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩} := by
  set Γ := geoCarrierShadow hn hG hS q with hΓ
  have hna : ¬ Γ.Adjacent ⟨0, G11_carrierEdge hn hG hS q v hv⟩
      ⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ := by
    rw [Shadow.single_adjacent_iff]
    exact gu1_carrierEdge_remote hn hG hS q v hv hv'
  have hmem1 : crossingPoint v.1 ∈ Γ.seg ⟨0, G11_carrierEdge hn hG hS q v hv⟩ :=
    (G11_carrierEdge_spec hn hG hS q v hv).1
  have hmem2 : crossingPoint v.1 ∈ Γ.seg ⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ := by
    have := (G11_carrierEdge_spec hn hG hS q (visitTwin v) hv').1
    rw [visitTwin_crossing] at this
    exact this
  let y₀ : Γ.Crossing := ⟨_, Γ.isCrossing_pair hna ⟨crossingPoint v.1, hmem1, hmem2⟩⟩
  have hpt : Γ.crossingPoint y₀ = crossingPoint v.1 := by
    symm
    apply (geoCarrierShadow_generic hn hG hS q).common_point_unique
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hmem1
    · rw [Finset.mem_singleton.mp hs]; exact hmem2
  have heq : s7s_lift hn hG hS q v.1 hv = y₀ := by
    apply (geoCarrierShadow_generic hn hG hS q).crossingPoint_injective
    rw [s7s_lift_crossingPoint, hpt]
  rw [heq]

include hn hS in
theorem s7s_four_le_cornerCount (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg S q)
    (hv' : (visitTwin v).1 ∈ geoCarrierCrossings hG.cg S q) :
    4 ≤ geoCornerCount hG.cg S q :=
  s7s_four_le (three_le_geoCornerCount hn hG hS q)
    ⟨_, _, gu1_carrierEdge_remote hn hG hS q v hv hv'⟩

omit [NeZero n] in
theorem s7s_det_ne_zero_of_isCrossing (hP : CrossingGeometry P) {i j : ZMod n}
    (h : IsCrossing P {i, j}) : det (edge P i) (edge P j) ≠ 0 :=
  (hP.2.1 i j (gu2_remote_of_isCrossing h) _ (crossingPoint_mem (xPair h) i (mem_pair_left i j))
    (crossingPoint_mem (xPair h) j (mem_pair_right i j))).2.2

include hn hS in
/-- at a lifted crossing `⟨0, j⟩, ⟨0, j'⟩` of the positive lift, the strand `⟨0, j'⟩` is over iff
`det (edge P e') (edge P e) > 0` for the original edges `e, e'` of the two visits -/
theorem s7s_pos_over_lift_iff (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg S q)
    (hv' : (visitTwin v).1 ∈ geoCarrierCrossings hG.cg S q) :
    (geoPositiveLift hn hG hS q).overStrand (s7s_lift hn hG hS q v.1 hv) =
        (⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
      0 < det (edge P (visitTwin v).2.val) (edge P v.2.val) := by
  have hval := s7s_lift_val hn hG hS q v hv hv'
  rw [Finset.pair_comm] at hval
  have hne : (⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ : (geoCarrierShadow hn hG hS q).Strand) ≠
      ⟨0, G11_carrierEdge hn hG hS q v hv⟩ :=
    (geoCarrierShadow hn hG hS q).ne_of_not_adjacent
      (fun h => gu1_carrierEdge_remote hn hG hS q v hv hv'
        ((Shadow.single_adjacent_iff _ _ _).mp (Shadow.Adjacent.symm _ h)))
  refine (s7s_pos_over_iff (geoCarrierShadow_generic hn hG hS q) _ hval hne).trans ?_
  obtain ⟨-, c, hc, he⟩ := G11_carrierEdge_spec hn hG hS q v hv
  obtain ⟨-, c', hc', he'⟩ := G11_carrierEdge_spec hn hG hS q (visitTwin v) hv'
  show 0 < det (edge (geoCornerPolygon hG.cg S q) _) (edge (geoCornerPolygon hG.cg S q) _) ↔ _
  rw [he, he']
  exact s7s_det_smul_pos_iff hc' hc _ _

/-! #### s7s.3 The wall bigon site: the vertex–edge triangle `conv{x, P M, y}` -/

variable {M a : ZMod n} (hx : IsCrossing P {M - 1, a}) (hy : IsCrossing P {a, M})

omit [NeZero n] in
/-- the closed contact triangle `conv{x, M, y}` (sm-4:618-620 "the isolated contact disc") -/
abbrev s7s_K : Set Plane :=
  convexHull ℝ {crossingPoint (xPair hx), P M, crossingPoint (xPair hy)}

include hn in
/-- **The wall bigon site (I-110; row 110 bigon (2)).**  On the positive lift `D_H = geoPositiveLift` of a
carrier `q` (independent support `S`) of the bigon-side polygon `P` that retains the two contact crossings
`x = x_{M−1,a}` (the visit `G11_vef hx` on the edge `M−1`, its twin `G11_vfe hx` on `a`) and `y = x_{a,M}`
(`G11_vfg hy` on `a`, `G11_vgf hy` on `M`), the switch of `D_H` at (the lift of) `x` or `y` carries a
`BigonData` whose bigon is `{x, y}` and whose region is the closed contact triangle `conv{x, P M, y}`.
Wall data consumed in carrier form (U110-A/B; discharged by `s7s_carrier_data_of_wall`):
`hjout` — the carrier edge of `y`'s `M`-visit is the successor of that of `x`'s `(M−1)`-visit (the block of
`x`'s leg visit ends at the vertex corner `M`, `y`'s leg visit opens the next block); `hcorner` — that corner
is the vertex `P M`; `hadj_s` — no visit lies between the two `a`-visits (window clause); `hsgn` — the two
contact crossing signs alternate (`crossingSign P (M−1) a = crossingSign P a M`, the geometric fact that
`P M` lies on one side of `a` and `P (M−1)`, `P (M+1)` on the other; see `s7s_contact_sign`); `hclear` — every
other edge of the corner polygon misses the closed triangle. -/
theorem s7s_core
    (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q) (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q)
    (hjout : G11_carrierEdge hn hG hS q (G11_vgf hy) hyq = G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1)
    (hcorner : geoCornerPolygon hG.cg S q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1) = P M)
    (hadj_s : ∀ w : Visit P, w.2.val = a →
      ¬ (visitParameter (G11_vfe hx) < visitParameter w ∧ visitParameter w < visitParameter (G11_vfg hy)) ∧
      ¬ (visitParameter (G11_vfg hy) < visitParameter w ∧ visitParameter w < visitParameter (G11_vfe hx)))
    (hsgn : crossingSign P (M - 1) a = crossingSign P a M)
    (hclear : ∀ h : ZMod (geoCornerCount hG.cg S q), h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq →
      h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1 → h ≠ G11_carrierEdge hn hG hS q (G11_vfe hx) hxq →
      Disjoint (edgeSegment (geoCornerPolygon hG.cg S q) h) (s7s_K hx hy))
    (xs : (geoCarrierShadow hn hG hS q).Crossing)
    (hxs : xs = s7s_lift hn hG hS q _ hxq ∨ xs = s7s_lift hn hG hS q _ hyq) :
    ∃ B : BigonData ((geoPositiveLift hn hG hS q).switch xs),
      B.i = ⟨0, Nat.one_pos⟩ ∧ B.y = s7s_lift hn hG hS q _ hxq ∧ B.z = s7s_lift hn hG hS q _ hyq := by
  have hne_in_s : M - 1 ≠ a := P1.ne_of_isCrossing_pair hx
  have hne_s_out : a ≠ M := P1.ne_of_isCrossing_pair hy
  -- the two `a`-visits are adjacent: equal carrier edges
  have hjs : G11_carrierEdge hn hG hS q (G11_vfg hy) hyq =
      G11_carrierEdge hn hG hS q (G11_vfe hx) hxq :=
    G11_carrierEdge_eq_of_adjacent hn hG hS q hyq hxq rfl
      (fun w hw => (hadj_s w hw).symm)
  set jy := G11_carrierEdge hn hG hS q (G11_vef hx) hxq with hjy_def
  set js := G11_carrierEdge hn hG hS q (G11_vfe hx) hxq with hjs_def
  set ys := s7s_lift hn hG hS q _ hxq with hys
  set zs := s7s_lift hn hG hS q _ hyq with hzs
  have htwz : visitTwin (G11_vgf hy) = G11_vfg hy :=
    SEL_visitTwin_visitOn (mem_pair_left a M) (mem_pair_right a M) hne_s_out
  -- the strands of the two lifted crossings
  have hyv : ys.val = {(⟨0, jy⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, js⟩} := by
    have h := s7s_lift_val hn hG hS q (G11_vef hx) hxq hxq
    rw [gu2_carrierEdge_congr hn hG hS q (gu2_visitTwin_vef hx) hxq hxq] at h
    exact h
  have hzv : zs.val = {(⟨0, jy + 1⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, js⟩} := by
    have h := s7s_lift_val hn hG hS q (G11_vgf hy) hyq hyq
    rw [gu2_carrierEdge_congr hn hG hS q htwz hyq hyq, hjs, hjout] at h
    exact h
  have hna_y : ¬ adjacent jy js := by
    have h := gu1_carrierEdge_remote hn hG hS q (G11_vef hx) hxq hxq
    rw [gu2_carrierEdge_congr hn hG hS q (gu2_visitTwin_vef hx) hxq hxq] at h
    exact h
  have hna_z : ¬ adjacent (jy + 1) js := by
    have h := gu1_carrierEdge_remote hn hG hS q (G11_vgf hy) hyq hyq
    rw [gu2_carrierEdge_congr hn hG hS q htwz hyq hyq, hjs, hjout] at h
    exact h
  have hne_y : (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ≠ ⟨0, jy⟩ :=
    s7s_strand_ne_of_not_adjacent (fun h => hna_y (by
      rcases h with h | h | h
      · exact Or.inr (Or.inr (by linear_combination -h))
      · exact Or.inr (Or.inl (by linear_combination -h))
      · exact Or.inl (by linear_combination -h)))
  have hne_z : (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ≠ ⟨0, jy + 1⟩ :=
    s7s_strand_ne_of_not_adjacent (fun h => hna_z (by
      rcases h with h | h | h
      · exact Or.inr (Or.inr (by linear_combination -h))
      · exact Or.inr (Or.inl (by linear_combination -h))
      · exact Or.inl (by linear_combination -h)))
  have hyv' : ys.val = {(⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, jy⟩} := by
    rw [hyv, Finset.pair_comm]
  have hzv' : zs.val = {(⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, jy + 1⟩} := by
    rw [hzv, Finset.pair_comm]
  -- the two contact crossings are distinct
  have hone : (1 : ZMod n) ≠ 0 := by
    intro h
    rw [ZMod.one_eq_zero_iff] at h
    omega
  have hyz_c : xPair hx ≠ xPair hy := by
    intro h
    have hmem : M - 1 ∈ (xPair hy).val := by rw [← h]; exact mem_pair_left _ _
    rcases Finset.mem_insert.mp hmem with h' | h'
    · exact hne_in_s h'
    · have h'' : M - 1 = M := Finset.mem_singleton.mp h'
      exact hone (by linear_combination -h'')
  have hyz : ys ≠ zs := s7s_lift_injective_pt hn hG hS q hxq hyq hyz_c
  -- the over strands of the positive lift at `x` and `y`
  have hA := s7s_det_ne_zero_of_isCrossing hG.cg hx
  have hB := s7s_det_ne_zero_of_isCrossing hG.cg hy
  have hoy : (geoPositiveLift hn hG hS q).overStrand ys =
      (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔ 0 < -det (edge P (M - 1)) (edge P a) := by
    have h := s7s_pos_over_lift_iff hn hG hS q (G11_vef hx) hxq hxq
    rw [gu2_carrierEdge_congr hn hG hS q (gu2_visitTwin_vef hx) hxq hxq, gu2_visitTwin_vef,
      det_swap] at h
    exact h
  have hoz : (geoPositiveLift hn hG hS q).overStrand zs =
      (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔ 0 < det (edge P a) (edge P M) := by
    have h := s7s_pos_over_lift_iff hn hG hS q (G11_vgf hy) hyq hyq
    rw [gu2_carrierEdge_congr hn hG hS q htwz hyq hyq, hjs, htwz] at h
    exact h
  have hsign : (0 < det (edge P (M - 1)) (edge P a) ↔ 0 < det (edge P a) (edge P M)) :=
    s7s_pos_iff_of_sign_eq hsgn
  have hsign' : (0 < -det (edge P (M - 1)) (edge P a) ↔ 0 < -det (edge P a) (edge P M)) :=
    s7s_neg_pos_iff_of_sign_eq hsgn
  -- `same_over` on the switched diagram
  have hsame : (((geoPositiveLift hn hG hS q).switch xs).overStrand ys =
        (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ∧
        ((geoPositiveLift hn hG hS q).switch xs).overStrand zs =
        (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand)) ∨
      (((geoPositiveLift hn hG hS q).switch xs).overStrand ys ≠
        (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ∧
        ((geoPositiveLift hn hG hS q).switch xs).overStrand zs ≠
        (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand)) := by
    rcases hxs with rfl | rfl
    · -- the switch is at `x`
      have e1 : ((geoPositiveLift hn hG hS q).switch ys).overStrand ys =
          (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔ 0 < det (edge P (M - 1)) (edge P a) := by
        refine (s7s_switch_over_self_iff (geoPositiveLift hn hG hS q) ys hyv' hne_y).trans ?_
        refine (s7s_over_other_iff (geoPositiveLift hn hG hS q) ys hyv' hne_y).trans ?_
        refine (not_congr hoy).trans ?_
        rw [s7s_not_pos_iff (neg_ne_zero.mpr hA), neg_neg]
      have e2 : ((geoPositiveLift hn hG hS q).switch ys).overStrand zs =
          (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔ 0 < det (edge P a) (edge P M) := by
        have h := Diagram.switch_overStrand_of_ne (geoPositiveLift hn hG hS q) hyz.symm
        rw [h]
        exact hoz
      by_cases hp : 0 < det (edge P (M - 1)) (edge P a)
      · exact Or.inl ⟨e1.mpr hp, e2.mpr (hsign.mp hp)⟩
      · exact Or.inr ⟨fun h => hp (e1.mp h), fun h => hp (hsign.mpr (e2.mp h))⟩
    · -- the switch is at `y`
      have e1 : ((geoPositiveLift hn hG hS q).switch zs).overStrand ys =
          (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔ 0 < -det (edge P (M - 1)) (edge P a) := by
        have h := Diagram.switch_overStrand_of_ne (geoPositiveLift hn hG hS q) hyz
        rw [h]
        exact hoy
      have e2 : ((geoPositiveLift hn hG hS q).switch zs).overStrand zs =
          (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔ 0 < -det (edge P a) (edge P M) := by
        refine (s7s_switch_over_self_iff (geoPositiveLift hn hG hS q) zs hzv' hne_z).trans ?_
        refine (s7s_over_other_iff (geoPositiveLift hn hG hS q) zs hzv' hne_z).trans ?_
        exact (not_congr hoz).trans (s7s_not_pos_iff hB)
      by_cases hp : 0 < -det (edge P (M - 1)) (edge P a)
      · exact Or.inl ⟨e1.mpr hp, e2.mpr (hsign'.mp hp)⟩
      · exact Or.inr ⟨fun h => hp (e1.mp h), fun h => hp (hsign'.mpr (e2.mp h))⟩
  -- clearance, read on strands
  have hclear' : ∀ u : (geoCarrierShadow hn hG hS q).Strand, u ≠ ⟨0, jy⟩ → u ≠ ⟨0, jy + 1⟩ →
      u ≠ ⟨0, js⟩ → Disjoint ((geoCarrierShadow hn hG hS q).seg u) (s7s_K hx hy) := by
    rintro ⟨i₀, h⟩ h1 h2 h3
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    have h1' : h ≠ jy := fun hh => h1 (by rw [hh])
    have h2' : h ≠ jy + 1 := fun hh => h2 (by rw [hh])
    have h3' : h ≠ js := fun hh => h3 (by rw [hh])
    exact hclear h h1' h2' h3'
  have hk : 4 ≤ geoCornerCount hG.cg S q := s7s_four_le_cornerCount hn hG hS q (G11_vef hx) hxq hxq
  have hpy : (geoCarrierShadow hn hG hS q).crossingPoint ys = crossingPoint (xPair hx) :=
    s7s_lift_crossingPoint hn hG hS q _ hxq
  have hpz : (geoCarrierShadow hn hG hS q).crossingPoint zs = crossingPoint (xPair hy) :=
    s7s_lift_crossingPoint hn hG hS q _ hyq
  have hK : convexHull ℝ {(geoCarrierShadow hn hG hS q).crossingPoint ys, geoCornerPolygon hG.cg S q (jy + 1),
      (geoCarrierShadow hn hG hS q).crossingPoint zs} = s7s_K hx hy := by
    rw [hpy, hpz, hcorner]
  -- the triangle builder
  obtain ⟨B, hBi, hBy, hBz⟩ := exists_bigonData_of_triangle ((geoPositiveLift hn hG hS q).switch xs)
    ⟨0, Nat.one_pos⟩ jy hk (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ys zs hyv hzv hsame (by
      intro u h1 h2 h3
      have hK' : convexHull ℝ {((geoPositiveLift hn hG hS q).switch xs).Γ.crossingPoint ys,
          (((geoPositiveLift hn hG hS q).switch xs).Γ.comp ⟨0, Nat.one_pos⟩).P
            ((jy + 1 : ZMod (geoCornerCount hG.cg S q))),
          ((geoPositiveLift hn hG hS q).switch xs).Γ.crossingPoint zs} = s7s_K hx hy := by
        rw [← hK]; rfl
      exact (hclear' u h1 h2 h3).mono_right (le_of_eq hK'))
  exact ⟨B, hBi, hBy, hBz⟩

end S7SiteCore

/-! #### s7s.4 Glue: the record identification `hrec` (stated), the R-II witnesses, `P (D_H^{sw}) = P D_L` -/

section S7SiteGlue

open GeoCarrier RProof

omit [NeZero n] in
/-- the reduced record of a bigon site with crossings `y₀, z₀`, written without the `BigonData` -/
def s7s_reducedRecordOf (D : Diagram) (y₀ z₀ : D.Γ.Crossing) : Record :=
  D.record.restrictCrossings
    {c | c ≠ D.record.crossingOf (D.overVisit y₀) ∧ c ≠ D.record.crossingOf (D.overVisit z₀)}

omit [NeZero n] in
theorem s7s_reducedRecord_eq {D : Diagram} (B : BigonData D) {y₀ z₀ : D.Γ.Crossing}
    (hBy : B.y = y₀) (hBz : B.z = z₀) : B.reducedRecord = s7s_reducedRecordOf D y₀ z₀ := by
  unfold BigonData.reducedRecord BigonData.keep s7s_reducedRecordOf
  rw [hBy, hBz]

variable {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
  {M a : ZMod n} (hx : IsCrossing P {M - 1, a}) (hy : IsCrossing P {a, M})

/-- **The wall data in carrier form** (the hypotheses of `s7s_core`, bundled): what U110-A/B deliver
about the full contact carrier `q` on the bigon side — see `s7s_core` for the reading of each field. -/
structure s7s_SiteData (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q)
    (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) : Prop where
  jout : G11_carrierEdge hn hG hS q (G11_vgf hy) hyq = G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1
  corner : geoCornerPolygon hG.cg S q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1) = P M
  adj_s : ∀ w : Visit P, w.2.val = a →
    ¬ (visitParameter (G11_vfe hx) < visitParameter w ∧ visitParameter w < visitParameter (G11_vfg hy)) ∧
    ¬ (visitParameter (G11_vfg hy) < visitParameter w ∧ visitParameter w < visitParameter (G11_vfe hx))
  sgn : crossingSign P (M - 1) a = crossingSign P a M
  clear : ∀ h : ZMod (geoCornerCount hG.cg S q), h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq →
    h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1 → h ≠ G11_carrierEdge hn hG hS q (G11_vfe hx) hxq →
    Disjoint (edgeSegment (geoCornerPolygon hG.cg S q) h) (s7s_K hx hy)

/-- the site, from the bundled data: the bigon `{x, y}` on `D_H.switch x` -/
theorem s7s_site (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q)
    (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) (W : s7s_SiteData hn hG hS q hx hy hxq hyq) :
    ∃ B : BigonData ((geoPositiveLift hn hG hS q).switch (s7s_lift hn hG hS q _ hxq)),
      B.i = ⟨0, Nat.one_pos⟩ ∧ B.y = s7s_lift hn hG hS q _ hxq ∧ B.z = s7s_lift hn hG hS q _ hyq :=
  s7s_core hn hG hS q hx hy hxq hyq W.jout W.corner W.adj_s W.sgn W.clear _ (Or.inl rfl)

/-- **`hrec` of PLAN_FINAL §3.3 bigon (2) — STATED, not proved.**  The record of `D_H.switch x` with the
four occurrences of `x, y` deleted is the record of the `L`-side lift `D_L` (the positive lift of the
transported carrier `e q` of `S` on `P_L`, `s7a_componentEquiv`): the retained crossings correspond
through `s7a_cross` (persistent crossings, `s7a_mem_carrierCrossings`), the cyclic order of the
persistent visits is carried (`VertexLocalData.visit_order`, `s7a_between_map`), the over bits agree
(`s7a_side_sgn` + `s7d_positiveOverBit_eq_of_crossingSign`; the switched bit sits on a DELETED
occurrence), and the switched restricted record is `Record.restrictCrossings_switch` (retained case) —
here the switched crossing `x` is deleted, so the needed form is the DELETED-case analogue (Site_174_REPORT
§3 item 1).  Cost estimate in W3_SITE_REPORT.md §3. -/
def s7s_hrec_prop (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q)
    (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) (DL : Diagram) : Prop :=
  Nonempty (RecordIso
    (s7s_reducedRecordOf ((geoPositiveLift hn hG hS q).switch (s7s_lift hn hG hS q _ hxq))
      (s7s_lift hn hG hS q _ hxq) (s7s_lift hn hG hS q _ hyq))
    DL.record)

/-- **The two hypotheses of the accepted glue `s7g_switch_value_of_rii`, PROVED from the site and
`hrec`** (`s7_rii_witnesses`, SM.BigonDeletion): an R-II witness `RII Dred (D_H.switch x)` on the actual
polygonal lifts together with `Dred.record ≅ D_L.record`. -/
theorem s7s_rii_witnesses (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q)
    (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) (W : s7s_SiteData hn hG hS q hx hy hxq hyq)
    (DL : Diagram) (hrec : s7s_hrec_prop hn hG hS q hx hy hxq hyq DL) :
    ∃ Dred : Diagram, RII Dred ((geoPositiveLift hn hG hS q).switch (s7s_lift hn hG hS q _ hxq)) ∧
      Nonempty (RecordIso Dred.record DL.record) := by
  obtain ⟨B, -, hBy, hBz⟩ := s7s_site hn hG hS q hx hy hxq hyq W
  refine s7_rii_witnesses _ _ B DL ?_
  rw [s7s_reducedRecord_eq B hBy hBz]
  exact hrec

/-- **sm-4:600-606 on the geo lift: `P (D_H.switch x) = P D_L`** (`s7g_switch_value_of_rii` with the
witnesses of `s7s_rii_witnesses`; equivalently `s7_switch_value_of_bigon`). -/
theorem s7s_switch_value (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q)
    (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) (W : s7s_SiteData hn hG hS q hx hy hxq hyq)
    (DL : Diagram) (hrec : s7s_hrec_prop hn hG hS q hx hy hxq hyq DL) :
    SM.P ((geoPositiveLift hn hG hS q).switch (s7s_lift hn hG hS q _ hxq)) = SM.P DL := by
  obtain ⟨Dred, hR, hrec'⟩ := s7s_rii_witnesses hn hG hS q hx hy hxq hyq W DL hrec
  exact s7g_switch_value_of_rii _ Dred DL _ hR hrec'

end S7SiteGlue

/-! #### s7s.5 Transport to the accepted `positiveLift` (`cornerHomfly`): `geoPositiveLift_eq_generic` -/

section S7SiteGeneric

open GeoCarrier RProof

omit [NeZero n] in
/-- a crossing carried along an equality of diagrams -/
def s7s_castCrossing {D D' : Diagram} (h : D = D') (x : D.Γ.Crossing) : D'.Γ.Crossing :=
  cast (by rw [h]) x

omit [NeZero n] in
theorem s7s_switch_castCrossing {D D' : Diagram} (h : D = D') (x : D.Γ.Crossing) :
    D'.switch (s7s_castCrossing h x) = D.switch x := by
  subst h; rfl

omit [NeZero n] in
theorem s7s_castCrossing_crossingPoint {D D' : Diagram} (h : D = D') (x : D.Γ.Crossing) :
    D'.Γ.crossingPoint (s7s_castCrossing h x) = D.Γ.crossingPoint x := by
  subst h; rfl

variable {P : LabelledTuple n} (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))
  (hS : IsDecomposition hn hP S) (q : Component hn hP S)

/-- the tier-1 witness of an SM-generic polygon -/
abbrev s7s_cg : CarrierGeometry P := CarrierGeometry.ofGeneric hn hP

include hS in
/-- a decomposition is geo-independent (`geoIndependent_iff_isDecomposition`) -/
theorem s7s_geoIndependent : GeoIndependent (s7s_cg hn hP).cg S :=
  (geoIndependent_iff_isDecomposition hn hP S).mpr hS

/-- the geo carrier corresponding to the accepted carrier `q` -/
abbrev s7s_geoComp : GeoComponent (s7s_cg hn hP).cg S := (geoComponentEquivGeneric hn hP S).symm q

/-- the geo positive lift of `s7s_geoComp q` IS the accepted `positiveLift` of `q` -/
theorem s7s_geoPositiveLift_eq :
    geoPositiveLift hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) =
      positiveLift hn hP S q hS := by
  rw [geoPositiveLift_eq_generic hn hP S _ _ hS]
  simp only [s7s_geoComp, Equiv.apply_symm_apply]

variable {M a : ZMod n} (hx : IsCrossing P {M - 1, a}) (hy : IsCrossing P {a, M})

/-- the crossing of the accepted positive lift `positiveLift hn hP S q hS` at a retained crossing `c` -/
noncomputable def s7s_liftGen (c : Crossing P)
    (hc : c ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q)) :
    (positiveLift hn hP S q hS).Γ.Crossing :=
  s7s_castCrossing (s7s_geoPositiveLift_eq hn hP S hS q)
    (s7s_lift hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) c hc)

theorem s7s_liftGen_crossingPoint (c : Crossing P)
    (hc : c ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q)) :
    (positiveLift hn hP S q hS).Γ.crossingPoint (s7s_liftGen hn hP S hS q c hc) = crossingPoint c := by
  exact (s7s_castCrossing_crossingPoint (s7s_geoPositiveLift_eq hn hP S hS q)
    (s7s_lift hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) c hc)).trans
    (s7s_lift_crossingPoint hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) c hc)

/-- **sm-4:600-606 on the accepted lift: `P ((positiveLift q).switch x) = P D_L`.** -/
theorem s7s_switch_value_positiveLift
    (hxq : xPair hx ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q))
    (hyq : xPair hy ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q))
    (W : s7s_SiteData hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) hx hy hxq hyq)
    (DL : Diagram)
    (hrec : s7s_hrec_prop hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) hx hy hxq hyq DL) :
    SM.P ((positiveLift hn hP S q hS).switch (s7s_liftGen hn hP S hS q _ hxq)) = SM.P DL := by
  exact (congrArg SM.P (s7s_switch_castCrossing (s7s_geoPositiveLift_eq hn hP S hS q)
    (s7s_lift hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) _ hxq))).trans
    (s7s_switch_value hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) hx hy hxq hyq W DL hrec)

/-- **eq. s7c:universal-skein at the contact crossing with the R-II step done** — `s7g_cornerHomfly_skein`
with `P (D_H.switch x)` replaced by `P D_L`: `H⁺_Q = a⁻² P(D_L) + a⁻¹ z P(D_A)`, `D_A` the library
smoothing at `x` with record `D_H.record.smooth v`.  This is the input of U110-H/K (the two-component row
on `D_A`, `s7h_extraction_two_component`). -/
theorem s7s_cornerHomfly_skein
    (hxq : xPair hx ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q))
    (hyq : xPair hy ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q))
    (W : s7s_SiteData hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) hx hy hxq hyq)
    (DL : Diagram)
    (hrec : s7s_hrec_prop hn (s7s_cg hn hP) (s7s_geoIndependent hn hP S hS) (s7s_geoComp hn hP S q) hx hy hxq hyq DL)
    (v : (positiveLift hn hP S q hS).Γ.Visit) (hv : v.1 = s7s_liftGen hn hP S hS q _ hxq) :
    ∃ D₀ : Diagram, IsOrientedSmoothing (positiveLift hn hP S q hS) (s7s_liftGen hn hP S hS q _ hxq) D₀ ∧
      Nonempty (RecordIso D₀.record ((positiveLift hn hP S q hS).record.smooth v)) ∧
      cornerHomfly hn hP S q hS = R.aInv * R.aInv * SM.P DL + R.aInv * R.z * SM.P D₀ := by
  obtain ⟨D₀, -, hsm, hrec₀, hsk⟩ := s7g_cornerHomfly_skein hn hP S q hS _ v hv
  refine ⟨D₀, hsm, hrec₀, ?_⟩
  rw [hsk, s7s_switch_value_positiveLift hn hP S hS q hx hy hxq hyq W DL hrec]

end S7SiteGeneric

/-! #### s7s.7 Towards `hrec`: the record side (Site_174_REPORT §3 item 1) and the `carrierCrossings` reading -/

section S7SiteRecord

open GeoCarrier RProof

omit [NeZero n] in
/-- the bits of the restriction of a switched record agree with the unswitched ones when the switched
occurrence is DELETED (its crossing is not kept): `restrictCrossings` reads `isOver` only at retained
occurrences, none of which is `v` or `pair v` -/
theorem s7s_restrict_switch_deleted_bit (ρ : Record) (S : Set ρ.Crossing) (v : ρ.M)
    (hv : ¬ ρ.CrossKeep S v) (w : (ρ.restrictCrossings S).M) :
    (ρ.restrictCrossings S).isOver w = ((ρ.switch v).restrictCrossings S).isOver w := by
  have hw1 : w.1 ≠ v := fun h => hv (h ▸ w.2)
  have hw2 : w.1 ≠ ρ.pair v := fun h => by
    apply hv
    have h2 := w.2
    rw [h, ρ.crossKeep_pair_iff] at h2
    exact h2
  show ρ.isOver w.1 = (ρ.switch v).isOver w.1
  rw [Record.switch_isOver_of_ne ρ v hw1 hw2]

omit [NeZero n] in
theorem s7s_restrict_switch_deleted_sgn (ρ : Record) (S : Set ρ.Crossing) (v : ρ.M)
    (hv : ¬ ρ.CrossKeep S v) (w : (ρ.restrictCrossings S).M) :
    (ρ.restrictCrossings S).sgn w = ((ρ.switch v).restrictCrossings S).sgn w := by
  have hw1 : w.1 ≠ v := fun h => hv (h ▸ w.2)
  have hw2 : w.1 ≠ ρ.pair v := fun h => by
    apply hv
    have h2 := w.2
    rw [h, ρ.crossKeep_pair_iff] at h2
    exact h2
  show ρ.sgn w.1 = (ρ.switch v).sgn w.1
  rw [Record.switch_sgn_of_ne ρ v hw1 hw2]

omit [NeZero n] in
/-- **The DELETED-case companion of `Record.restrictCrossings_switch`** (Site_174_REPORT §3 item 1): when
the switched occurrence's crossing is not kept, restricting the switched record is restricting the
record — the switch of row 110 sits on the bigon crossing `x`, which the R-II deletion removes, so the
reduced record of `D_H.switch x` is the reduced record of `D_H` itself. -/
theorem s7s_restrictCrossings_switch_deleted (ρ : Record) (S : Set ρ.Crossing) (v : ρ.M)
    (hv : ¬ ρ.CrossKeep S v) :
    Nonempty (RecordIso ((ρ.switch v).restrictCrossings S) (ρ.restrictCrossings S)) :=
  ⟨RecordIso.mk (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun w => s7s_restrict_switch_deleted_bit ρ S v hv w)
    (fun w => s7s_restrict_switch_deleted_sgn ρ S v hv w)⟩

variable {P : LabelledTuple n} (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))
  (hS : IsDecomposition hn hP S) (q : Component hn hP S)

/-- the site's membership hypotheses in the accepted `carrierCrossings` form -/
theorem s7s_mem_geoCarrierCrossings_iff (c : Crossing P) :
    c ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q) ↔
      c ∈ carrierCrossings hn hP S q := by
  rw [geoCarrierCrossings_eq_generic hn hP S]
  simp only [s7s_geoComp, Equiv.apply_symm_apply]

include hS in
/-- the lifted crossing of the accepted lift IS the accepted `carrierCrossingEquiv` inverse at `c` -/
theorem s7s_liftGen_eq_carrierCrossingEquiv (c : Crossing P)
    (hc : c ∈ geoCarrierCrossings (s7s_cg hn hP).cg S (s7s_geoComp hn hP S q)) :
    s7s_liftGen hn hP S hS q c hc =
      (carrierCrossingEquiv hn hP S q hS).symm ⟨c, (s7s_mem_geoCarrierCrossings_iff hn hP S q c).mp hc⟩ := by
  apply (carrierShadow_generic hn hP S q hS).crossingPoint_injective
  refine (s7s_liftGen_crossingPoint hn hP S hS q c hc).trans ?_
  have h := crossingPoint_carrierCrossingEquiv hn hP S q hS
    ((carrierCrossingEquiv hn hP S q hS).symm ⟨c, (s7s_mem_geoCarrierCrossings_iff hn hP S q c).mp hc⟩)
  rw [Equiv.apply_symm_apply] at h
  exact h

end S7SiteRecord

/-! #### s7s.8 `hrec` reduced to the UNSWITCHED record: `D_H.record − {x, y} ≅ D_L.record` -/

section S7SiteHrec

open GeoCarrier RProof

omit [NeZero n] in
/-- the keep set "every crossing but `y₀, z₀`", read on the record of `D` itself -/
def s7s_keepOf (D : Diagram) (y₀ z₀ : D.Γ.Crossing) : Set D.record.Crossing :=
  {c | c ≠ D.record.crossingOf (D.overVisit y₀) ∧ c ≠ D.record.crossingOf (D.overVisit z₀)}

omit [NeZero n] in
/-- an occurrence has the record crossing of `x` iff it is a visit of `x` (U-M6's `key`) -/
theorem s7s_crossingOf_eq_iff_fst (D : Diagram) (x : D.Γ.Crossing) (w : D.Γ.Visit) :
    D.record.crossingOf w = D.record.crossingOf (D.overVisit x) ↔ w.1 = x := by
  rw [Record.crossingOf_eq_iff]
  show w ∈ ({D.overVisit x, D.record.pair (D.overVisit x)} : Finset D.Γ.Visit) ↔ _
  rw [D.record_pair_apply, D.mem_pair_twin_iff]
  rfl

omit [NeZero n] in
/-- **`hrec` needs only the UNSWITCHED identification.**  The reduced record of `D.switch x` (the four
occurrences of `x, y` deleted) is isomorphic to the record of `D` minus `{x, y}`: `Diagram.switchRecordIso`
(the identity on occurrences) transports `restrictCrossings` (`CB.restrictCrossings_iso_of_recordIso`),
and the switch sits on the DELETED crossing `x` (`s7s_restrictCrossings_switch_deleted`).  So the record
identification of row 110 is the persistent-visit transport `D_H.record − {x, y} ≅ D_L.record` of U110-A,
with no switch involved. -/
theorem s7s_hrec_of_unswitched (D : Diagram) (x y : D.Γ.Crossing) (v : D.Γ.Visit) (hv : v.1 = x)
    (DL : Diagram)
    (h : Nonempty (RecordIso (D.record.restrictCrossings (s7s_keepOf D x y)) DL.record)) :
    Nonempty (RecordIso (s7s_reducedRecordOf (D.switch x) x y) DL.record) := by
  obtain ⟨κ⟩ := h
  have hX : ∀ w : (D.switch x).record.M,
      (D.switch x).record.crossingOf w ∈
          ({c | c ≠ (D.switch x).record.crossingOf ((D.switch x).overVisit x) ∧
            c ≠ (D.switch x).record.crossingOf ((D.switch x).overVisit y)} : Set (D.switch x).record.Crossing) ↔
        (D.record.switch v).crossingOf ((Diagram.switchRecordIso D x v hv).Φ w) ∈
          (s7s_keepOf D x y : Set (D.record.switch v).Crossing) := by
    intro w
    show ((D.switch x).record.crossingOf w ≠ (D.switch x).record.crossingOf ((D.switch x).overVisit x) ∧
        (D.switch x).record.crossingOf w ≠ (D.switch x).record.crossingOf ((D.switch x).overVisit y)) ↔
      (D.record.crossingOf w ≠ D.record.crossingOf (D.overVisit x) ∧
        D.record.crossingOf w ≠ D.record.crossingOf (D.overVisit y))
    exact and_congr
      (not_congr ((s7s_crossingOf_eq_iff_fst (D.switch x) x w).trans
        (s7s_crossingOf_eq_iff_fst D x w).symm))
      (not_congr ((s7s_crossingOf_eq_iff_fst (D.switch x) y w).trans
        (s7s_crossingOf_eq_iff_fst D y w).symm))
  obtain ⟨ι₁⟩ := CB.restrictCrossings_iso_of_recordIso (Diagram.switchRecordIso D x v hv) _ _ hX
  have hv' : ¬ D.record.CrossKeep (s7s_keepOf D x y) v := by
    intro hk
    have hk' : D.record.crossingOf v ≠ D.record.crossingOf (D.overVisit x) ∧
        D.record.crossingOf v ≠ D.record.crossingOf (D.overVisit y) := hk
    exact hk'.1 ((s7s_crossingOf_eq_iff_fst D x v).mpr hv)
  obtain ⟨ι₂⟩ := s7s_restrictCrossings_switch_deleted D.record (s7s_keepOf D x y) v hv'
  exact ⟨ι₁.trans (ι₂.trans κ)⟩

variable {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
  {M a : ZMod n} (hx : IsCrossing P {M - 1, a}) (hy : IsCrossing P {a, M})

/-- **`s7s_hrec_prop` from the unswitched identification** `D_H.record − {x, y} ≅ D_L.record`
(the U110-A persistent-visit transport, `s7a_cross` / `s7a_between_map` / `s7a_side_sgn` on the retained
crossings of the full contact carrier — the remaining content of `hrec`, W3_SITE_REPORT.md §3). -/
theorem s7s_hrec_prop_of_unswitched (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q)
    (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) (DL : Diagram)
    (h : Nonempty (RecordIso ((geoPositiveLift hn hG hS q).record.restrictCrossings
      (s7s_keepOf (geoPositiveLift hn hG hS q) (s7s_lift hn hG hS q _ hxq) (s7s_lift hn hG hS q _ hyq)))
      DL.record)) :
    s7s_hrec_prop hn hG hS q hx hy hxq hyq DL :=
  s7s_hrec_of_unswitched (geoPositiveLift hn hG hS q) _ _
    ((geoPositiveLift hn hG hS q).overVisit (s7s_lift hn hG hS q _ hxq))
    ((geoPositiveLift hn hG hS q).overVisit_fst _) DL h

end S7SiteHrec

/-! #### s7s.9 The `corner` field from window clause (2): the block of `x`'s leg visit ends at the vertex `M` -/

section S7SiteBlocks

open GeoCarrier RProof

variable {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
  {M a : ZMod n} (hx : IsCrossing P {M - 1, a})

omit [NeZero n] in
/-- a visit is determined by its crossing and its edge -/
theorem s7s_visit_ext {v w : Visit P} (h1 : v.1 = w.1) (h2 : v.2.val = w.2.val) : v = w := by
  rcases v with ⟨c, i, hi⟩
  rcases w with ⟨c', i', hi'⟩
  change c = c' at h1
  subst h1
  change i = i' at h2
  subst h2
  rfl

/-- the smoothing successor of an UNSELECTED visit is its mark successor -/
theorem s7s_smoothingSuccessor_of_not_mem (hP : CrossingGeometry P) (v : Visit P) (hv : v.1 ∉ S) :
    geoSmoothingSuccessor hP S (Sum.inr v) = geoMarkSuccessor hP (Sum.inr v) := by
  rw [geoSmoothingSuccessor_apply, selectedMarkPerm_visit, selectedVisitTwin_of_not_mem S v hv]

include hn in
/-- the mark successor of the LAST visit on its edge is the next vertex
(`geoMarkSuccessor_position_cases`: the alternative "same edge, larger parameter" is excluded) -/
theorem s7s_markSuccessor_last (hP : CrossingGeometry P) (v : Visit P)
    (hlast : ∀ w : Visit P, w.2.val = v.2.val → w ≠ v → visitParameter w < visitParameter v) :
    geoMarkSuccessor hP (Sum.inr v) = Sum.inl (v.2.val + 1) := by
  rcases geoMarkSuccessor_position_cases hn hP (Sum.inr v) with ⟨hedge, hlt⟩ | h
  · exfalso
    rcases hsucc : geoMarkSuccessor hP (Sum.inr v) with j | w
    · rw [hsucc] at hlt
      have h0 : (geoMarkPosition hP (Sum.inl j)).2.val = 0 := rfl
      have hge : 0 ≤ (geoMarkPosition hP (Sum.inr v)).2.val :=
        (geoMarkPosition hP (Sum.inr v)).2.property.1
      rw [h0] at hlt
      linarith
    · rw [hsucc] at hedge hlt
      have hw_edge : w.2.val = v.2.val := hedge
      have hlt' : visitParameter v < visitParameter w := hlt
      have hwv : w ≠ v := by
        intro h
        subst h
        exact lt_irrefl _ hlt'
      have := hlast w hw_edge hwv
      linarith
  · exact h

include hn in
/-- **`corner` (mark form), PROVED from window clause (2)**: the corner after the carrier edge of `x`'s leg
visit is the vertex mark `inl M`.  The leg visit `v = G11_vef hx` (on `M−1`, unselected) is the `r`-th mark
of the block of its carrier edge `j` (`gu1_carrierEdge_block`); the block ends at the corner `j + 1` after
`m` steps (`geoCornerPolygon_block`); the smoothing successor of `v` is its mark successor
(`s7s_smoothingSuccessor_of_not_mem`), which is the vertex `inl M` because `v` is the last visit on `M−1`
(`s7s_markSuccessor_last`); a vertex is a true corner, so `r + 1 = m`. -/
theorem s7s_cornerMark_of_wall
    (h2 : ∀ w : Visit P, w.2.val = M - 1 → w.1 ≠ xPair hx → visitParameter w < visitParameter (G11_vef hx))
    (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q) :
    geoCornerMark hG.cg S q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1) = Sum.inl M := by
  have hvS : (G11_vef hx).1 ∉ S := ((mem_geoCarrierCrossings hG.cg S q (G11_vef hx).1).mp hxq).1
  obtain ⟨r, hr1, hρr, hbr, -, -⟩ := gu1_carrierEdge_block hn hG hS q (G11_vef hx) hxq
  obtain ⟨m, hm1, hρm, hint, -, -, -, -, -⟩ :=
    geoCornerPolygon_block hn hG.cg hS q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq)
  have hsucc : geoSmoothingSuccessor hG.cg S (Sum.inr (G11_vef hx)) = Sum.inl M := by
    rw [s7s_smoothingSuccessor_of_not_mem hG.cg (G11_vef hx) hvS,
      s7s_markSuccessor_last hn hG.cg (G11_vef hx) ?_]
    · show Sum.inl (M - 1 + 1) = Sum.inl M
      rw [sub_add_cancel]
    · intro w hw hwv
      refine h2 w hw ?_
      intro hw1
      exact hwv (s7s_visit_ext hw1 hw)
  have hρr1 : (geoSmoothingSuccessor hG.cg S ^ (r + 1))
      (geoCornerMark hG.cg S q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq)) = Sum.inl M := by
    rw [pow_succ', Equiv.Perm.mul_apply, hρr, hsucc]
  have hrm : r < m := by
    by_contra hle
    obtain ⟨w, hw, hwS, -⟩ := hbr m hm1 (not_lt.mp hle)
    have hc := isTrueCorner_geoCornerMark hG.cg S q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1)
    rw [← hρm, hw] at hc
    exact hwS ((isTrueCorner_visit S w).mp hc)
  have hr1m : r + 1 = m := by
    by_contra hne
    have hlt : r + 1 < m := by omega
    obtain ⟨w, hw, -, -⟩ := hint (r + 1) (by omega) hlt
    rw [hρr1] at hw
    exact Sum.inl_ne_inr hw
  rw [← hρm, ← hr1m, hρr1]

include hn in
/-- **`corner` of `s7s_SiteData`, PROVED**: `geoCornerPolygon (j_in + 1) = P M`. -/
theorem s7s_cornerPolygon_of_wall
    (h2 : ∀ w : Visit P, w.2.val = M - 1 → w.1 ≠ xPair hx → visitParameter w < visitParameter (G11_vef hx))
    (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q) :
    geoCornerPolygon hG.cg S q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1) = P M := by
  rw [geoCornerPolygon_apply, s7s_cornerMark_of_wall hn hG hS q hx h2 hxq,
    geoMarkPosition_evaluation_vertex]

include hn in
/-- **window clause (3) ⇒ the mark successor of the vertex `M` is `y`'s `M`-visit.**  By
`geoMarkSuccessor_position_cases` the successor is a visit `u` on `M` with parameter `> 0` or the vertex
`M + 1`; in either case, if it is not `y`'s visit `w`, then `w` (parameter in `(0, 1)`, and `< param u`
by (3)) lies strictly between `inl M` and the successor in the traversal order — against
`geoMarkSuccessor_no_mark_between` (key arithmetic, including the wrap `(M+1).val = 0`). -/
theorem s7s_markSuccessor_vertex_first (hy : IsCrossing P {a, M})
    (h3 : ∀ w : Visit P, w.2.val = M → w.1 ≠ xPair hy →
      visitParameter (G11_vgf hy) < visitParameter w) :
    geoMarkSuccessor hG.cg (Sum.inl M) = Sum.inr (G11_vgf hy) := by
  have hw0 : 0 < visitParameter (G11_vgf hy) :=
    (crossingParameter_interior_of_geometry hG.cg (xPair hy) M (mem_pair_right a M)).1
  have hw1 : visitParameter (G11_vgf hy) < 1 :=
    (crossingParameter_interior_of_geometry hG.cg (xPair hy) M (mem_pair_right a M)).2
  have hnb := geoMarkSuccessor_no_mark_between hG.cg (Sum.inl M) (Sum.inr (G11_vgf hy))
  have k0 : traversalKey (geoMarkPosition hG.cg (Sum.inl M)) = (M.val : ℝ) := by
    show ((M.val : ℕ) : ℝ) + 0 = _
    rw [add_zero]
  have kw : traversalKey (geoMarkPosition hG.cg (Sum.inr (G11_vgf hy))) =
      (M.val : ℝ) + visitParameter (G11_vgf hy) := rfl
  rcases geoMarkSuccessor_position_cases hn hG.cg (Sum.inl M) with ⟨hedge, hlt⟩ | h
  · rcases hsucc : geoMarkSuccessor hG.cg (Sum.inl M) with j | u
    · exfalso
      rw [hsucc] at hlt
      have h0 : (geoMarkPosition hG.cg (Sum.inl j)).2.val = 0 := rfl
      have h0' : (geoMarkPosition hG.cg (Sum.inl M)).2.val = 0 := rfl
      rw [h0, h0'] at hlt
      exact lt_irrefl _ hlt
    · rw [hsucc] at hedge hlt hnb
      have hu_edge : u.2.val = M := hedge
      have hu_pos : 0 < visitParameter u := hlt
      by_contra hne
      have hne' : u ≠ G11_vgf hy := fun h => hne (by rw [h])
      have hu1 : u.1 ≠ xPair hy := fun h => hne' (s7s_visit_ext h hu_edge)
      have hlt3 := h3 u hu_edge hu1
      have ku : traversalKey (geoMarkPosition hG.cg (Sum.inr u)) = (M.val : ℝ) + visitParameter u := by
        show ((u.2.val.val : ℕ) : ℝ) + visitParameter u = _
        rw [hu_edge]
      apply hnb
      have hpr : traversalKey (geoMarkPosition hG.cg (Sum.inl M)) <
          traversalKey (geoMarkPosition hG.cg (Sum.inr u)) := by
        rw [k0, ku]; linarith
      rw [traversalBetween_of_key_lt hpr, k0, kw, ku]
      constructor <;> linarith
  · exfalso
    have hM1 : (geoMarkPosition hG.cg (Sum.inl M)).1 = M := rfl
    rw [h, hM1] at hnb
    apply hnb
    have : Fact (1 < n) := ⟨by omega⟩
    have hval : (M + 1).val = (M.val + 1) % n := by rw [ZMod.val_add, ZMod.val_one]
    have hMlt : M.val < n := ZMod.val_lt M
    have k1 : traversalKey (geoMarkPosition hG.cg (Sum.inl (M + 1))) = (((M + 1).val : ℕ) : ℝ) := by
      show (((M + 1).val : ℕ) : ℝ) + 0 = _
      rw [add_zero]
    unfold traversalBetween
    rw [k0, kw, k1]
    by_cases hlt : M.val + 1 < n
    · rw [hval, Nat.mod_eq_of_lt hlt]
      left
      constructor
      · linarith
      · push_cast; linarith
    · have hn' : M.val + 1 = n := by omega
      rw [hval, hn', Nat.mod_self]
      right; right
      have h2M : 2 ≤ M.val := by omega
      have h2M' : (2 : ℝ) ≤ (M.val : ℝ) := by exact_mod_cast h2M
      constructor
      · push_cast; linarith
      · linarith

include hn in
/-- **`jout` of `s7s_SiteData`, PROVED from window clauses (2), (3)**: the carrier edge of `y`'s `M`-visit
is the successor of that of `x`'s `(M−1)`-visit.  The block opening at the corner `j_in + 1 = inl M`
(`s7s_cornerMark_of_wall`) has `y`'s `M`-visit as its first mark (`s7s_markSuccessor_vertex_first`,
unselected, on the out-slot edge `M`), so `GeoBlockInterior (j_in + 1) 1`; block uniqueness
`geo_block_mark_eq` against `gu1_carrierEdge_block` at `y`'s visit gives the edge. -/
theorem s7s_jout_of_wall (hy : IsCrossing P {a, M})
    (h2 : ∀ w : Visit P, w.2.val = M - 1 → w.1 ≠ xPair hx → visitParameter w < visitParameter (G11_vef hx))
    (h3 : ∀ w : Visit P, w.2.val = M → w.1 ≠ xPair hy →
      visitParameter (G11_vgf hy) < visitParameter w)
    (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q) (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) :
    G11_carrierEdge hn hG hS q (G11_vgf hy) hyq = G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1 := by
  have hk := s7s_cornerMark_of_wall hn hG hS q hx h2 hxq
  have hsucc := s7s_markSuccessor_vertex_first hn hG hy h3
  have hwS : (G11_vgf hy).1 ∉ S := ((mem_geoCarrierCrossings hG.cg S q (G11_vgf hy).1).mp hyq).1
  have hbk : GeoBlockInterior hG.cg S q (G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1) 1 := by
    intro i h1 hi
    have hi1 : i = 1 := le_antisymm hi h1
    subst hi1
    refine ⟨G11_vgf hy, ?_, hwS, ?_⟩
    · rw [pow_one, hk, geoSmoothingSuccessor_vertex, hsucc]
    · rw [hk]; rfl
  obtain ⟨r', -, hρ', hb', -, -⟩ := gu1_carrierEdge_block hn hG hS q (G11_vgf hy) hyq
  have h := geo_block_mark_eq hG.cg S q hbk hb'
    (by rw [pow_one, hk, geoSmoothingSuccessor_vertex, hsucc, hρ'])
  exact h.1.symm

end S7SiteBlocks

/-! #### s7s.10 The wall data (U110-A/B): the `P`-level form, the sign condition, the assembly, the two black boxes -/

section S7SiteWall

open GeoCarrier RProof

/-- **The `P`-level wall data of the bigon side** (sm-4:407-447, 618-620; lem:wall-sides (V) window clauses):
(1) every edge other than `M−1`, `M`, `a` misses the closed contact triangle `conv{x, P M, y}`; (2) `x`'s
visit is the LAST visit on the edge `M−1` (the window `(x, M]` is empty); (3) `y`'s visit is the FIRST on
the edge `M` (the window `[M, y)` is empty); (4) no visit lies strictly between the two contact visits on
`a`.  Consumed by `s7s_siteData_of_wall`. -/
def s7s_WallTriangleData (P : LabelledTuple n) (M a : ZMod n) (hx : IsCrossing P {M - 1, a})
    (hy : IsCrossing P {a, M}) : Prop :=
  (∀ e : ZMod n, e ≠ M - 1 → e ≠ M → e ≠ a → Disjoint (edgeSegment P e) (s7s_K hx hy)) ∧
  (∀ w : Visit P, w.2.val = M - 1 → w.1 ≠ xPair hx → visitParameter w < visitParameter (G11_vef hx)) ∧
  (∀ w : Visit P, w.2.val = M → w.1 ≠ xPair hy → visitParameter (G11_vgf hy) < visitParameter w) ∧
  (∀ w : Visit P, w.2.val = a →
    ¬ (visitParameter (G11_vfe hx) < visitParameter w ∧ visitParameter w < visitParameter (G11_vfg hy)) ∧
    ¬ (visitParameter (G11_vfg hy) < visitParameter w ∧ visitParameter w < visitParameter (G11_vfe hx)))

variable {P : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)
  {M a : ZMod n} (hx : IsCrossing P {M - 1, a}) (hy : IsCrossing P {a, M})

omit [NeZero n] in
/-- **The contact sign condition of the site, PROVED from the planar geometry** (no wall data): at a
vertex–edge contact where both edges `M−1`, `M` cross the edge `a`, the vertex `P M` lies on one side of
the line of `a` and `P (M−1)`, `P (M+1)` on the other, so the two contact crossing signs alternate:
`(1 − t_x) det(E_{M−1}, E_a) = t_y det(E_a, E_M)` with `0 < 1 − t_x`, `0 < t_y` (`det(E_a, P M − x) =
det(E_a, P M − y)` since `x, y` lie on the line of `a`). -/
theorem s7s_contact_sign {P : LabelledTuple n} (hP : CrossingGeometry P) {M a : ZMod n}
    (hx : IsCrossing P {M - 1, a}) (hy : IsCrossing P {a, M}) :
    crossingSign P (M - 1) a = crossingSign P a M := by
  have hxin : M - 1 ∈ (xPair hx).val := mem_pair_left _ _
  have hxa : a ∈ (xPair hx).val := mem_pair_right _ _
  have hya : a ∈ (xPair hy).val := mem_pair_left _ _
  have hyM : M ∈ (xPair hy).val := mem_pair_right _ _
  obtain ⟨-, htx1⟩ := crossingParameter_interior_of_geometry hP (xPair hx) (M - 1) hxin
  obtain ⟨hty0, -⟩ := crossingParameter_interior_of_geometry hP (xPair hy) M hyM
  set tx := crossingParameter (xPair hx) (M - 1) hxin with htx
  set ty := crossingParameter (xPair hy) M hyM with hty
  set rx := crossingParameter (xPair hx) a hxa with hrx
  set ry := crossingParameter (xPair hy) a hya with hry
  have ex : crossingPoint (xPair hx) = edgePoint P (M - 1) tx := gu2_xpt _ _ hxin
  have ex' : crossingPoint (xPair hx) = edgePoint P a rx := gu2_xpt _ _ hxa
  have ey : crossingPoint (xPair hy) = edgePoint P M ty := gu2_xpt _ _ hyM
  have ey' : crossingPoint (xPair hy) = edgePoint P a ry := gu2_xpt _ _ hya
  have hM1 : P M = edgePoint P (M - 1) 1 := by rw [edgePoint_one, sub_add_cancel]
  have hM0 : P M = edgePoint P M 0 := (edgePoint_zero P M).symm
  have e1 : P M - crossingPoint (xPair hx) = (1 - tx) • edge P (M - 1) := by
    rw [hM1, ex, gu2_edgePoint_sub]
  have e2 : P M - crossingPoint (xPair hy) = (0 - ty) • edge P M := by
    rw [hM0, ey, gu2_edgePoint_sub]
  have e3 : crossingPoint (xPair hy) - crossingPoint (xPair hx) = (ry - rx) • edge P a := by
    rw [ey', ex', gu2_edgePoint_sub]
  have key : det (edge P a) (P M - crossingPoint (xPair hx)) =
      det (edge P a) (P M - crossingPoint (xPair hy)) := by
    have hsplit : P M - crossingPoint (xPair hx) =
        (P M - crossingPoint (xPair hy)) + (crossingPoint (xPair hy) - crossingPoint (xPair hx)) := by
      abel
    rw [hsplit, det_add_right, e3, det_smul_self, add_zero]
  rw [e1, e2, det_smul_right, det_smul_right] at key
  have h1 : 0 < 1 - tx := by linarith
  have hA : det (edge P (M - 1)) (edge P a) = -det (edge P a) (edge P (M - 1)) :=
    det_swap (edge P a) (edge P (M - 1))
  have key' : (1 - tx) * det (edge P (M - 1)) (edge P a) = ty * det (edge P a) (edge P M) := by
    rw [hA]; linear_combination -key
  unfold crossingSign
  calc SignType.sign (det (edge P (M - 1)) (edge P a))
      = SignType.sign ((1 - tx) * det (edge P (M - 1)) (edge P a)) := by
        rw [sign_mul, sign_pos h1, one_mul]
    _ = SignType.sign (ty * det (edge P a) (edge P M)) := by rw [key']
    _ = SignType.sign (det (edge P a) (edge P M)) := by rw [sign_mul, sign_pos hty0, one_mul]

/-- **BLACK BOX (this unit's own remaining content; NOT proved).**  Clearance of the carrier edges that lie
on one of the three LOCAL `P`-edges `M−1`, `M`, `a` and are not the local piece itself (`jout`, `corner`,
`sgn`, `adj_s` and the non-local part of `clear` are PROVED).  Route, per edge: a point of the carrier edge
`h` in `K` lies on the `P`-edge (`gu2_edgeSegment_sub`) and on a side line of the triangle, hence on that side
(`RProof.gu2_mem_segment_ab_of_line`-type barycentric lemma), i.e. at a parameter in `[t_x, 1]` (edge `M−1`),
`[0, t_y]` (edge `M`), between `r_x, r_y` (edge `a`); the block `h = [c_h, c_{h+1}]` (`geoCornerPolygon_block`:
a positive multiple of `edge P e`, incoming edge `e` at `c_{h+1}`) has true-corner ends that are selected visits
on `e` (the vertex end would force `h = j_in` / `h = j_in + 1` by `geoCornerMark_injective` and
`s7s_cornerMark_of_wall`), whose parameters the window clauses (2)/(3) put below `t_x` / above `t_y`, and
whose parameter range cannot straddle `(r_x, r_y)` without a mark strictly between the two contact visits
(4) or containing them (then `h = j_s` by `geo_block_mark_eq`).  Estimate 300-450 lines (the `a`-edge case is
the long one). -/
theorem s7s_clear_local (hW : s7s_WallTriangleData P M a hx hy)
    (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q) (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q)
    (h : ZMod (geoCornerCount hG.cg S q)) (h1 : h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq)
    (h2 : h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1)
    (h3 : h ≠ G11_carrierEdge hn hG hS q (G11_vfe hx) hxq)
    (he : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = M - 1 ∨
      (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = M ∨
      (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = a) :
    Disjoint (edgeSegment (geoCornerPolygon hG.cg S q) h) (s7s_K hx hy) := by
  sorry

/-- **`clear` of `s7s_SiteData`**: the carrier edges on a NON-local `P`-edge are cleared by the `P`-level
clause (1) through `gu2_edgeSegment_sub` (PROVED); the local ones are the black box `s7s_clear_local`. -/
theorem s7s_carrier_data_of_wall (hW : s7s_WallTriangleData P M a hx hy)
    (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q) (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) :
    ∀ h : ZMod (geoCornerCount hG.cg S q), h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq →
      h ≠ G11_carrierEdge hn hG hS q (G11_vef hx) hxq + 1 → h ≠ G11_carrierEdge hn hG hS q (G11_vfe hx) hxq →
      Disjoint (edgeSegment (geoCornerPolygon hG.cg S q) h) (s7s_K hx hy) := by
  intro h h1 h2 h3
  by_cases he : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = M - 1 ∨
      (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = M ∨
      (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = a
  · exact s7s_clear_local hn hG hS q hx hy hW hxq hyq h h1 h2 h3 he
  · have hne1 : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 ≠ M - 1 := fun h' => he (Or.inl h')
    have hne2 : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 ≠ M := fun h' => he (Or.inr (Or.inl h'))
    have hne3 : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 ≠ a := fun h' => he (Or.inr (Or.inr h'))
    exact (hW.1 _ hne1 hne2 hne3).mono_left (gu2_edgeSegment_sub hn hG hS q h)

/-- The bundled site data from the `P`-level wall data: `adj_s` is the window clause (4) verbatim, `sgn` is
`s7s_contact_sign`, `corner` is `s7s_cornerPolygon_of_wall`, `jout` is `s7s_jout_of_wall`, and `clear` is `s7s_carrier_data_of_wall` (non-local edges proved; local edges = the black box `s7s_clear_local`). -/
theorem s7s_siteData_of_wall (hW : s7s_WallTriangleData P M a hx hy)
    (hxq : xPair hx ∈ geoCarrierCrossings hG.cg S q) (hyq : xPair hy ∈ geoCarrierCrossings hG.cg S q) :
    s7s_SiteData hn hG hS q hx hy hxq hyq := by
  exact ⟨s7s_jout_of_wall hn hG hS q hx hy hW.2.1 hW.2.2.1 hxq hyq,
    s7s_cornerPolygon_of_wall hn hG hS q hx hW.2.1 hxq, hW.2.2.2,
    s7s_contact_sign hG.cg hx hy, s7s_carrier_data_of_wall hn hG hS q hx hy hW hxq hyq⟩

end S7SiteWall

/-- **BLACK BOX (U110-A/B wall data; NOT proved here).**  At a bigon wall (`g.BigonAt M a`), below some
radius, on the side whose polygon carries BOTH contact crossings `{M−1, a}`, `{a, M}` (the `H` side,
`VertexCrossingData`: `X(P₊) ∆ X(P₋) = {{a,M−1},{a,M}}`), the `P`-level wall data holds: (1) the closed
contact triangle is clear of the other edges (the printed emptiness sm-4:618-620, from
`ContactParameterWindows` + `contact_persistent_parameters_approach`), (2)-(4) the window clauses of
`VertexLocalData.visit_windows` / `InContactVisitWindow` (U_S7A_REPORT §1.7 `s7a_exists_sideLocal`).
Estimate 300-500 lines on the accepted `vertex_sides`. -/
theorem s7s_wallTriangleData_of_bigon (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)
    (h : g.BigonAt M a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (b : Bool) (t : g.SideParameter), t.val < δ →
      ∀ (hx : IsCrossing (g.sideTuple b t).1 {M - 1, a}) (hy : IsCrossing (g.sideTuple b t).1 {a, M}),
        s7s_WallTriangleData (g.sideTuple b t).1 M a hx hy := by
  sorry

end S7Site


/-! ### Unit BLOCK (wave 3, prefix `s7k_`; PLAN_FINAL §3.3 bigon (2)-(3); serves U110-K `s7_bigon_law_at`):
the universal skein extraction on the ACTUAL positive lifts through the ported R-II site (SM.BigonDeletion:
`s7_switch_value_of_bigon`, no `RIIData` built here), the reading of the oriented smoothing `D_A` (known only
through the record clause of `exists_smoothing_record_visit`) by the two-component row (`s7h_`), the
identification of `D_A`'s two `knotRestrict`s with the half contact carriers' lifts REDUCED TO ABSTRACT GAUSS
RECORDS (`restrict_record`, `RecordIso.smooth`, `CB.positiveLiftRecordIso`: §K; likewise the R-II reduced record
through `Diagram.switchRecordIso`, `RecordIso.switch`: §L — so U110-A/B owe statements about crossing geometries
only, no geometry of `D_A`), the R-I AVOIDANCE
of the `ε = 0` curl `y` through mp:blocks (`curl_block_value`, `SM.blocks.writhe_additive`: the curl is a
single self crossing block of value `1` and writhe `+1`), the writhe / slot bookkeeping (eq. s7c:interlacing-slot,
s7c:noninterlacing-slot from `positiveLift_writhe_eq_carrierCrossingCount` + the crossing partition + the
rotation identities of `s7i_`), and the two extracted rows with the floor reads (sm-4:638-668 interlacing
`Ω_H − Ω_L = −ω₁ω₂`; 736-769 noninterlacing `Ω_H − Ω_L = 0`).

Design.  Everything is stated on FOUR carriers `q_H, q_L, q₁, q₂` of four generic polygons `P_H, P_L`
(the two side polygons, size `n`) and `P₁, P₂` (the halves, sizes `n₁, n₂`), with the geometric inputs of
units A/B/C/F/I as HYPOTHESES bundled in the Prop `s7k_ContactRowData` (the interface this block consumes;
each field names its supplier).  The smoothing `D_A` is a parameter with its record clause, so the consumer
may produce the `knotRestrict` identifications at the record level; the skein relation is transferred to
that `D_A` from the library's smoothing by `presentations`.  The floor `hF` enters ONLY through
`FloorTheoremData.slot_le_of_signed` at `q₁, q₂` (the printed reads sm-4:655-660, 765-769), the singleton
never (the one-newborn rows are U110-K's, sm-4:777-783).  No frozen statement is touched. -/

section S7KBlock

variable {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]

/-! #### A. The skein triple at the contact crossing, on the actual lifts, through the R-II site -/

/-- sm-4:600-606 on the actual lifts: `P (D_H^{sw x}) = H⁺_{L_L}` from a bigon site on the switched high
lift (`BigonData`, SM.BigonDeletion §1: the isolated contact disc `K`, the common over strand) and the
identification of its reduced record with the low lift's record (U110-A's persistent visit order through
`Record.restrictCrossings_switch`).  The R-II witness is produced by `exists_rii_deletion` inside
`s7_switch_value_of_bigon`; nothing geometric is built here. -/
theorem s7k_switch_value (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH) (hPL : Generic PL)
    {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)} (hSH : IsDecomposition hn hPH SH)
    (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH) (qL : Component hn hPL SL)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing)
    (B : BigonData ((positiveLift hn hPH SH qH hSH).switch x))
    (hrec : Nonempty (RecordIso B.reducedRecord (positiveLift hn hPL SL qL hSL).record)) :
    SM.P ((positiveLift hn hPH SH qH hSH).switch x) = cornerHomfly hn hPL SL qL hSL := by
  rw [s7_switch_value_of_bigon _ x B _ hrec]
  unfold cornerHomfly
  exact P_eq_homfly _

/-- The skein relation at the contact crossing `x` of the high lift, read on ANY diagram `D_A` carrying the
record `D_H.record.smooth v` (the clause of `exists_smoothing_record_visit`): `H⁺_{L_H} = a⁻² P (D_H^{sw x}) +
a⁻¹ z P D_A`.  The library's smoothing `D₀` (`s7g_cornerHomfly_skein`) has the same record, so `P D₀ = P D_A`
by `presentations`. -/
theorem s7k_skein_on (hn : 3 ≤ n) {PH : LabelledTuple n} (hPH : Generic PH) {SH : Finset (Crossing PH)}
    (hSH : IsDecomposition hn hPH SH) (qH : Component hn hPH SH)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing) (v : (positiveLift hn hPH SH qH hSH).Γ.Visit)
    (hv : v.1 = x) (DA : Diagram)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v))) :
    cornerHomfly hn hPH SH qH hSH =
      R.aInv * R.aInv * SM.P ((positiveLift hn hPH SH qH hSH).switch x) + R.aInv * R.z * SM.P DA := by
  obtain ⟨D₀, -, -, ⟨ι₀⟩, hsk⟩ := s7g_cornerHomfly_skein hn hPH SH qH hSH x v hv
  obtain ⟨ιA⟩ := hrecA
  rw [hsk, presentations D₀ DA ⟨ι₀.trans ιA.symm⟩]

/-- **eq. s7c:universal-extraction on the actual lifts** (the shape `s7_universal_extraction` consumes, with
`F_H = H⁺_{L_H}`, `F_L = H⁺_{L_L}`, `F_A = P D_A`): `[a^{k−2} z⁰] H⁺_{L_H} = [a^k z⁰] H⁺_{L_L} + [a^{k−1} z⁻¹] P D_A`. -/
theorem s7k_extraction (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH) (hPL : Generic PL)
    {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)} (hSH : IsDecomposition hn hPH SH)
    (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH) (qL : Component hn hPL SL)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing) (v : (positiveLift hn hPH SH qH hSH).Γ.Visit)
    (hv : v.1 = x) (B : BigonData ((positiveLift hn hPH SH qH hSH).switch x))
    (hrec : Nonempty (RecordIso B.reducedRecord (positiveLift hn hPL SL qL hSL).record))
    (DA : Diagram)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v))) (k : ℤ) :
    coeffAt (k - 2) 0 (cornerHomfly hn hPH SH qH hSH) =
      coeffAt k 0 (cornerHomfly hn hPL SL qL hSL) + coeffAt (k - 1) (-1) (SM.P DA) :=
  s7_universal_extraction _ _ _ k (by
    rw [s7k_skein_on hn hPH hSH qH x v hv DA hrecA, s7k_switch_value hn hPH hPL hSH hSL qH qL x B hrec])

/-- **The crossing partition `m_H = m_L + 2` is encoded in the bigon site** (no separate input): the reduced
record has two crossings fewer than `D_H^{sw x}` (`BigonData.reducedRecord_counts`), the switch keeps the
crossings, and the reduced record is `D_L`'s (`RecordIso.crossingCount_eq`, `card_carrierShadow_crossing`). -/
theorem s7k_count_of_site (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH) (hPL : Generic PL)
    {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)} (hSH : IsDecomposition hn hPH SH)
    (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH) (qL : Component hn hPL SL)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing)
    (B : BigonData ((positiveLift hn hPH SH qH hSH).switch x))
    (hrec : Nonempty (RecordIso B.reducedRecord (positiveLift hn hPL SL qL hSL).record)) :
    carrierCrossingCount hn hPH SH qH = carrierCrossingCount hn hPL SL qL + 2 := by
  obtain ⟨ι⟩ := hrec
  have h1 := B.reducedRecord_counts.1
  rw [ι.crossingCount_eq, Diagram.record_crossingCount, Diagram.record_crossingCount] at h1
  have h2 : Fintype.card (positiveLift hn hPL SL qL hSL).Γ.Crossing = carrierCrossingCount hn hPL SL qL :=
    card_carrierShadow_crossing hn hPL SL qL hSL
  have h3 : Fintype.card ((positiveLift hn hPH SH qH hSH).switch x).Γ.Crossing =
      carrierCrossingCount hn hPH SH qH :=
    card_carrierShadow_crossing hn hPH SH qH hSH
  omega

/-! #### B. The counts on `D_A` (sm-4:496-533): two components, writhe `m_H − 1` -/

/-- `D_A` has two components (`positiveLift_componentCount`, `s7h_componentCount_of_smooth_iso`). -/
theorem s7k_DA_componentCount (hn : 3 ≤ n) {PH : LabelledTuple n} (hPH : Generic PH)
    {SH : Finset (Crossing PH)} (hSH : IsDecomposition hn hPH SH) (qH : Component hn hPH SH)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (DA : Diagram)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v))) :
    DA.componentCount = 2 :=
  s7h_componentCount_of_smooth_iso _ DA (positiveLift_componentCount hn hPH SH qH hSH) v hrecA

/-- "the smoothed crossing `q` contributes one" (sm-4:651): `w(D_A) = m_H − 1` (every crossing of the lift is
positive; `positiveLift_writhe_eq_carrierCrossingCount`). -/
theorem s7k_DA_writhe (hn : 3 ≤ n) {PH : LabelledTuple n} (hPH : Generic PH)
    {SH : Finset (Crossing PH)} (hSH : IsDecomposition hn hPH SH) (qH : Component hn hPH SH)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (DA : Diagram)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v))) :
    DA.writhe = (carrierCrossingCount hn hPH SH qH : ℤ) - 1 := by
  rw [s7h_writhe_of_smooth_iso _ DA v hrecA, positiveLift_sign, SignType.coe_one,
    positiveLift_writhe_eq_carrierCrossingCount]

/-! #### C. Reading a component of `D_A` through a record identification (U110-B's output shape) -/

/-- A record identification of a `knotRestrict` of `D_A` with a diagram `K` gives its value (`presentations`). -/
theorem s7k_component_value (DA : Diagram) (i : Fin DA.Γ.c) (K : Diagram)
    (h : Nonempty (RecordIso (DA.knotRestrict i).record K.record)) :
    SM.P (DA.knotRestrict i) = SM.P K :=
  presentations _ _ h

/-- … and its writhe (`RecordIso.writhe_eq`, `record_writhe`). -/
theorem s7k_component_writhe (DA : Diagram) (i : Fin DA.Γ.c) (K : Diagram)
    (h : Nonempty (RecordIso (DA.knotRestrict i).record K.record)) :
    (DA.knotRestrict i).writhe = K.writhe := by
  obtain ⟨ι⟩ := h
  rw [← (DA.knotRestrict i).record_writhe, ι.writhe_eq, K.record_writhe]

/-- The `ε = 1` reading of a component: its record is the record of the positive lift of a half contact
carrier `L` — value `H⁺_L` and writhe `m_L` (eq. s7c:component-polynomial / s7c:component-data). -/
theorem s7k_component_lift {m : ℕ} [NeZero m] (hm : 3 ≤ m) {Q : LabelledTuple m} (hQ : Generic Q)
    {T : Finset (Crossing Q)} (hT : IsDecomposition hm hQ T) (q : Component hm hQ T) (DA : Diagram)
    (i : Fin DA.Γ.c) (h : Nonempty (RecordIso (DA.knotRestrict i).record (positiveLift hm hQ T q hT).record)) :
    SM.P (DA.knotRestrict i) = cornerHomfly hm hQ T q hT ∧
      (DA.knotRestrict i).writhe = (carrierCrossingCount hm hQ T q : ℤ) := by
  refine ⟨?_, ?_⟩
  · rw [s7k_component_value DA i _ h]
    unfold cornerHomfly
    exact P_eq_homfly _
  · rw [s7k_component_writhe DA i _ h, positiveLift_writhe_eq_carrierCrossingCount]

/-! #### D. The R-I avoidance (sm-4:857-866 read at the record level, WAVE1 §7 / U_S7G §0): the curl `y` of
component 1 at `ε = 0` is a single self crossing BLOCK of the record — value `1` (lc:single-crossing), writhe
`+1` — and the other blocks are the blocks of the half contact carrier's lift.  No `RIData` witness. -/

/-- The value of a diagram whose record has a one-crossing block `H₀` (the curl) equals the value of a
diagram whose record's blocks are the OTHER blocks (`curl_block_value` + `SM.blocks.product`, the block
correspondence `e` with equal block values).  With `D = D_A.knotRestrict 1`, `D' = positiveLift` of the
one-dissent half contact carrier `L₁`, this is `Q₁ = H⁺_{L₁}` (eq. s7c:component-polynomial at `ε = 0`). -/
theorem s7k_curl_component_value (D : Diagram) (ρ : Record) (hD : Nonempty (RecordIso D.record ρ))
    (C : ρ.interlacementGraph.ConnectedComponent → Diagram) (hB : BlockSupply ρ C)
    (H₀ : ρ.interlacementGraph.ConnectedComponent) (x₀ : (C H₀).Γ.Crossing)
    (h1 : (C H₀).Γ.c = 1) (hx : ∀ y : (C H₀).Γ.Crossing, y = x₀)
    (D' : Diagram) (ρ' : Record) (hD' : Nonempty (RecordIso D'.record ρ'))
    (C' : ρ'.interlacementGraph.ConnectedComponent → Diagram) (hB' : BlockSupply ρ' C')
    (e : {H : ρ.interlacementGraph.ConnectedComponent // H ≠ H₀} ≃ ρ'.interlacementGraph.ConnectedComponent)
    (he : ∀ H : {H : ρ.interlacementGraph.ConnectedComponent // H ≠ H₀}, SM.P (C H.1) = SM.P (C' (e H))) :
    SM.P D = SM.P D' := by
  rw [curl_block_value ρ C hB D hD H₀ x₀ h1 hx, SM.blocks.product ρ' C' hB' D' hD']
  rw [Finset.prod_subtype (Finset.univ.erase H₀) (p := fun H => H ≠ H₀) (fun H => by simp)
    (fun H => SM.P (C H))]
  exact Fintype.prod_equiv e _ _ he

/-- The writhe companion: the curl block has writhe `+1` (a positive single crossing), the other blocks
match — `w(D) = w(D') + 1` (eq. s7c:pre-curl-writhe `w(component₁(D_A)) = w₁ + 1`; `SM.blocks.writhe_additive`). -/
theorem s7k_curl_component_writhe (D : Diagram) (ρ : Record) (hD : Nonempty (RecordIso D.record ρ))
    (C : ρ.interlacementGraph.ConnectedComponent → Diagram) (hB : BlockSupply ρ C)
    (H₀ : ρ.interlacementGraph.ConnectedComponent) (hw₀ : (C H₀).writhe = 1)
    (D' : Diagram) (ρ' : Record) (hD' : Nonempty (RecordIso D'.record ρ'))
    (C' : ρ'.interlacementGraph.ConnectedComponent → Diagram) (hB' : BlockSupply ρ' C')
    (e : {H : ρ.interlacementGraph.ConnectedComponent // H ≠ H₀} ≃ ρ'.interlacementGraph.ConnectedComponent)
    (he : ∀ H : {H : ρ.interlacementGraph.ConnectedComponent // H ≠ H₀}, (C H.1).writhe = (C' (e H)).writhe) :
    D.writhe = D'.writhe + 1 := by
  rw [SM.blocks.writhe_additive ρ C hB D hD, SM.blocks.writhe_additive ρ' C' hB' D' hD',
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ H₀), hw₀, add_comm]
  congr 1
  rw [Finset.sum_subtype (Finset.univ.erase H₀) (p := fun H => H ≠ H₀) (fun H => by simp)
    (fun H => (C H).writhe)]
  exact Fintype.sum_equiv e _ _ he

/-! #### E. The slot bookkeeping (def:C `d_Q = 1 − m_Q − |r_Q|`; sm-4:629-632, 665-670, 758-762) -/

/-- `k_H = k_L − 2` from the crossing partition `m_H = m_L + 2` (U110-A/F: `X(P₊) ∆ X(P₋) = {x, y}`) and the
full rotation through the wall `R_H = R_L` (eq. s7c:full-rotation, U110-I `s7i_full_rotation_germ`). -/
theorem s7k_high_slot (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH) (hPL : Generic PL)
    {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)} (qH : Component hn hPH SH)
    (qL : Component hn hPL SL)
    (hm : carrierCrossingCount hn hPH SH qH = carrierCrossingCount hn hPL SL qL + 2)
    (hR : |carrierRotationInt hn hPH SH qH| = |carrierRotationInt hn hPL SL qL|) :
    cornerSlot hn hPH SH qH = cornerSlot hn hPL SL qL - 2 := by
  unfold cornerSlot
  rw [hm, hR]
  push_cast
  ring

/-- **eq. s7c:interlacing-slot** on `D_A`: `k_L + 2ℓ = k₁ + k₂` from `w(D_A) = m_H − 1`, the writhe partition
`w(D_A) = w(D_A|ᵢ) + w(D_A|ⱼ) + 2ℓ`, the component writhes `m₁, m₂`, `m_H = m_L + 2` and `R_L = R₁ + R₂`. -/
theorem s7k_interlacing_slot (DA : Diagram) (i j : Fin DA.Γ.c) (h2 : DA.componentCount = 2) (hij : i ≠ j)
    {mH mL m₁ m₂ : ℕ} {RL R₁ R₂ : ℤ} (hwA : DA.writhe = (mH : ℤ) - 1)
    (hw₁ : (DA.knotRestrict i).writhe = (m₁ : ℤ)) (hw₂ : (DA.knotRestrict j).writhe = (m₂ : ℤ))
    (hm : mH = mL + 2) (hR : RL = R₁ + R₂) :
    (1 - (mL : ℤ) - RL) + twoLinking DA i j = (1 - (m₁ : ℤ) - R₁) + (1 - (m₂ : ℤ) - R₂) := by
  have h := s7h_writhe_two_component DA i j h2 hij
  rw [hwA, hw₁, hw₂] at h
  subst hm
  push_cast at h ⊢
  omega

/-- **eq. s7c:noninterlacing-slot** on `D_A`: `k₁ + k₂ − (k_L + 2ℓ) = 2`, i.e. `k_L + 2ℓ = K − 2`, with component
`i` carrying the curl (`w(D_A|ᵢ) = m₁ + 1`, eq. s7c:pre-curl-writhe) and `R₁ + R₂ − R_L = −1`
(eq. s7c:noninterlacing-rotation). -/
theorem s7k_noninterlacing_slot (DA : Diagram) (i j : Fin DA.Γ.c) (h2 : DA.componentCount = 2) (hij : i ≠ j)
    {mH mL m₁ m₂ : ℕ} {RL R₁ R₂ : ℤ} (hwA : DA.writhe = (mH : ℤ) - 1)
    (hw₁ : (DA.knotRestrict i).writhe = (m₁ : ℤ) + 1) (hw₂ : (DA.knotRestrict j).writhe = (m₂ : ℤ))
    (hm : mH = mL + 2) (hR : R₁ + R₂ - RL = -1) :
    (1 - (m₁ : ℤ) - R₁) + (1 - (m₂ : ℤ) - R₂) - ((1 - (mL : ℤ) - RL) + twoLinking DA i j) = 2 := by
  have h := s7h_writhe_two_component DA i j h2 hij
  rw [hwA, hw₁, hw₂] at h
  subst hm
  push_cast at h ⊢
  omega

/-! #### F. The coefficient difference through the two-component row (sm-4:638-651, 736-742) -/

/-- **The extracted difference `Ω_H − Ω_L` before the slot substitution**, in the carriers' vocabulary
(`cornerCoefficient = [a^{d_Q} z⁰] H⁺_Q`): with `k_H = k_L − 2`, the skein extraction at `k = k_L` and the
two-component row on `D_A` (`s7h_extraction_two_component`) give
`Ω_H − Ω_L = [a^{k_L+2ℓ−2} z⁰](Q₁Q₂) − [a^{k_L+2ℓ} z⁰](Q₁Q₂)` with `Q_i = P (D_A|ᵢ)` read as `f₁, f₂`. -/
theorem s7k_coefficient_difference (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH)
    (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (hv : v.1 = x)
    (B : BigonData ((positiveLift hn hPH SH qH hSH).switch x))
    (hrec : Nonempty (RecordIso B.reducedRecord (positiveLift hn hPL SL qL hSL).record))
    (DA : Diagram)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v)))
    (i j : Fin DA.Γ.c) (hij : i ≠ j) (hslot : cornerSlot hn hPH SH qH = cornerSlot hn hPL SL qL - 2)
    {f₁ f₂ : R} (hf₁ : SM.P (DA.knotRestrict i) = f₁) (hf₂ : SM.P (DA.knotRestrict j) = f₂) :
    cornerCoefficient hn hPH SH qH hSH - cornerCoefficient hn hPL SL qL hSL =
      coeffAt (cornerSlot hn hPL SL qL + twoLinking DA i j - 2) 0 (f₁ * f₂) -
        coeffAt (cornerSlot hn hPL SL qL + twoLinking DA i j) 0 (f₁ * f₂) := by
  have h2 := s7k_DA_componentCount hn hPH hSH qH v DA hrecA
  have hext := s7k_extraction hn hPH hPL hSH hSL qH qL x v hv B hrec DA hrecA (cornerSlot hn hPL SL qL)
  have h := s7h_extraction_two_component DA i j h2 hij hext
  rw [hf₁, hf₂] at h
  rw [cornerCoefficient_eq_coeffAt, cornerCoefficient_eq_coeffAt, hslot]
  exact h

/-! #### G. The floor reads (sm-4:655-668, 765-769) — `hF` enters here and only here -/

/-- `H⁺_L` has no negative `z`-exponent (lp:core `knot_support` on the one-component lift). -/
theorem s7k_cornerHomfly_z_nonneg (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S) (d k : ℤ)
    (h : coeffAt d k (cornerHomfly hn hP S q hS) ≠ 0) : 0 ≤ k := by
  unfold cornerHomfly at h
  rw [← P_eq_homfly] at h
  obtain ⟨j, hj⟩ := P_knot_support _ (positiveLift_componentCount hn hP S q hS) d k h
  omega

/-- **The interlacing floor read** (sm-4:655-668): at the two UNIFORM half contact carriers the floor gives
`k_i ≤ mindeg_a H⁺_{L_i}`, and `s7_corner_product` reads `[a^{K−2}](f₁f₂) = 0`, `[a^K](f₁f₂) = ω₁ω₂`. -/
theorem s7k_interlacing_floor_read (hF : FloorTheoremData) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂)
    {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂)
    {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁)
    (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)) :
    coeffAt (cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 2) 0
        (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) = 0 ∧
      coeffAt (cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂) 0
        (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) =
      cornerCoefficient hn₁ hP₁ S₁ q₁ hS₁ * cornerCoefficient hn₂ hP₂ S₂ q₂ hS₂ :=
  s7_corner_product (cornerHomfly_ne_zero hn₁ hP₁ S₁ q₁ hS₁) (cornerHomfly_ne_zero hn₂ hP₂ S₂ q₂ hS₂)
    (hF.slot_le_of_signed hn₁ P₁ hP₁ S₁ hS₁ q₁ hu₁) (hF.slot_le_of_signed hn₂ P₂ hP₂ S₂ hS₂ q₂ hu₂)
    (s7k_cornerHomfly_z_nonneg hn₁ hP₁ hS₁ q₁) (s7k_cornerHomfly_z_nonneg hn₂ hP₂ hS₂ q₂)

/-- **The noninterlacing floor read** (sm-4:765-769): at the two ONE-DISSENT half contact carriers both reads
`K − 4`, `K − 2` lie below the floor `K = k₁ + k₂` of the product (`coeffAt_mul_eq_zero_of_lt_floor`). -/
theorem s7k_noninterlacing_floor_read (hF : FloorTheoremData) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂)
    {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂)
    {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁)
    (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)) (d : ℤ)
    (hd : d < cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂) :
    coeffAt d 0 (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) = 0 :=
  coeffAt_mul_eq_zero_of_lt_floor (cornerHomfly_ne_zero hn₁ hP₁ S₁ q₁ hS₁)
    (cornerHomfly_ne_zero hn₂ hP₂ S₂ q₂ hS₂) (hF.slot_le_of_signed hn₁ P₁ hP₁ S₁ hS₁ q₁ hu₁)
    (hF.slot_le_of_signed hn₂ P₂ hP₂ S₂ hS₂ q₂ hu₂) hd

/-! #### H. The interface this block consumes (the geometric outputs of units A/B/C/F/I, as hypotheses) and
the two extracted rows -/

/-- **The contact data of one bigon contact carrier pair** — everything the extracted rows need about the
four carriers `L_H, L_L, L₁, L₂` (full contact carriers on the two sides; half contact carriers), per field:
the contact crossing `x` and the bigon site on the switched high lift with the reduced record identified with
the low lift's record (U110-F: the isolated contact disc, `same_over`; U110-A: the persistent visit order —
`s7_switch_value_of_bigon`'s inputs); the smoothing `D_A` with its record clause (produced by
`exists_smoothing_record_visit` / `s7g_cornerHomfly_skein`) and its two component indices; the crossing
partition `m_H = m_L + 2` is NOT a field — it follows from the site (`s7k_count_of_site`); the full rotation through the wall `R_H = R_L`
(U110-I `s7i_full_rotation_germ` on U110-A2's/F's family of the contact carrier).  The branch-dependent
fields (component identifications, `R`-identity, turn patterns) are in the two branch structures below. -/
structure s7k_ContactRowData (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH) (hPL : Generic PL)
    {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)} (hSH : IsDecomposition hn hPH SH)
    (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH) (qL : Component hn hPL SL)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing) : Prop where
  /-- the bigon site `{x, y}` on the switched high lift at the contact crossing `q = x`, whose reduced
  record is the low lift's record (sm-4:602-606; `s7k_reduced_iso_of_gauss` produces the second conjunct
  from its Gauss-record form) -/
  site : ∃ B : BigonData ((positiveLift hn hPH SH qH hSH).switch x),
    Nonempty (RecordIso B.reducedRecord (positiveLift hn hPL SL qL hSL).record)
  /-- eq. s7c:full-rotation `R_H = R_L` -/
  rotation : |carrierRotationInt hn hPH SH qH| = |carrierRotationInt hn hPL SL qL|

/-- **The `ε = 1` (interlacing) branch data** on a smoothing `D_A` of the high lift at `x` (record clause):
component `i` is the positive lift of the half contact carrier `L₁` of the decomposition `T₁` of `λ₁`,
component `j` that of `L₂` (U110-B through `CB.positiveLiftRecordIso`, sm-4:800-835); `R_L = R₁ + R₂`
(U110-I `s7i_carrierRotationInt_interlacing` on U110-C's uniform patterns); both half contact carriers are
uniform (U110-C `s7c_uniform_halves_of_interlacing`, the floor's input). -/
structure s7k_InterlacingData (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH) (hPL : Generic PL)
    {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)} (hSH : IsDecomposition hn hPH SH)
    (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH) (qL : Component hn hPL SL)
    (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁)
    (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)}
    (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₁ : Component hn₁ hP₁ S₁)
    (q₂ : Component hn₂ hP₂ S₂) (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (DA : Diagram)
    (i j : Fin DA.Γ.c) : Prop where
  record : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v))
  ne : i ≠ j
  comp₁ : Nonempty (RecordIso (DA.knotRestrict i).record (positiveLift hn₁ hP₁ S₁ q₁ hS₁).record)
  comp₂ : Nonempty (RecordIso (DA.knotRestrict j).record (positiveLift hn₂ hP₂ S₂ q₂ hS₂).record)
  rotation : |carrierRotationInt hn hPL SL qL| =
    |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂|
  pattern₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁)
  pattern₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)

/-- **The `ε = 0` (noninterlacing) branch data**: component `i` of `D_A` carries the curl `y` — its value is
`H⁺_{L₁}` and its writhe `m₁ + 1` (through `s7k_curl_component_value` / `_writhe`, the block route, no R-I);
component `j` is the lift of `L₂`; `R₁ + R₂ − R_L = −1` (U110-I `s7i_carrierRotationInt_noninterlacing`);
both half contact carriers are one-dissent (U110-C `s7c_dissent_halves_of_noninterlacing`). -/
structure s7k_NoninterlacingData (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH)
    (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂}
    (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)}
    (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₁ : Component hn₁ hP₁ S₁)
    (q₂ : Component hn₂ hP₂ S₂) (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (DA : Diagram)
    (i j : Fin DA.Γ.c) : Prop where
  record : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v))
  ne : i ≠ j
  curl_value : SM.P (DA.knotRestrict i) = cornerHomfly hn₁ hP₁ S₁ q₁ hS₁
  curl_writhe : (DA.knotRestrict i).writhe = (carrierCrossingCount hn₁ hP₁ S₁ q₁ : ℤ) + 1
  comp₂ : Nonempty (RecordIso (DA.knotRestrict j).record (positiveLift hn₂ hP₂ S₂ q₂ hS₂).record)
  rotation : |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| -
    |carrierRotationInt hn hPL SL qL| = -1
  pattern₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁)
  pattern₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)

/-- **eq. s7c:interlacing-coefficient-result** (sm-4:638-668): `Ω_H − Ω_L = −ω₁ω₂` at an interlacing
contact carrier pair, from the contact data, the branch data and the floor. -/
theorem s7k_interlacing_row (hF : FloorTheoremData) (hn : 3 ≤ n) {PH PL : LabelledTuple n}
    (hPH : Generic PH) (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing) (hc : s7k_ContactRowData hn hPH hPL hSH hSL qH qL x)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (hv : v.1 = x) (DA : Diagram) (i j : Fin DA.Γ.c)
    (hb : s7k_InterlacingData hn hPH hPL hSH hSL qH qL hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ v DA i j) :
    cornerCoefficient hn hPH SH qH hSH - cornerCoefficient hn hPL SL qL hSL =
      -(cornerCoefficient hn₁ hP₁ S₁ q₁ hS₁ * cornerCoefficient hn₂ hP₂ S₂ q₂ hS₂) := by
  obtain ⟨B, hrec⟩ := hc.site
  have hcount := s7k_count_of_site hn hPH hPL hSH hSL qH qL x B hrec
  have h2 := s7k_DA_componentCount hn hPH hSH qH v DA hb.record
  obtain ⟨hf₁, hw₁⟩ := s7k_component_lift hn₁ hP₁ hS₁ q₁ DA i hb.comp₁
  obtain ⟨hf₂, hw₂⟩ := s7k_component_lift hn₂ hP₂ hS₂ q₂ DA j hb.comp₂
  have hslot := s7k_high_slot hn hPH hPL qH qL hcount hc.rotation
  have hdiff := s7k_coefficient_difference hn hPH hPL hSH hSL qH qL x v hv B hrec DA
    hb.record i j hb.ne hslot hf₁ hf₂
  have hK := s7k_interlacing_slot DA i j h2 hb.ne (s7k_DA_writhe hn hPH hSH qH v DA hb.record) hw₁ hw₂
    hcount hb.rotation
  have hK' : cornerSlot hn hPL SL qL + twoLinking DA i j =
      cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ := by
    unfold cornerSlot; exact hK
  obtain ⟨h0, hprod⟩ := s7k_interlacing_floor_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hb.pattern₁ hb.pattern₂
  rw [hdiff, hK', h0, hprod, zero_sub]

/-- **eq. s7c:noninterlacing-extraction, every returned row zero** (sm-4:736-769): `Ω_H − Ω_L = 0` at a
noninterlacing contact carrier pair, from the contact data, the branch data and the floor. -/
theorem s7k_noninterlacing_row (hF : FloorTheoremData) (hn : 3 ≤ n) {PH PL : LabelledTuple n}
    (hPH : Generic PH) (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing) (hc : s7k_ContactRowData hn hPH hPL hSH hSL qH qL x)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (hv : v.1 = x) (DA : Diagram) (i j : Fin DA.Γ.c)
    (hb : s7k_NoninterlacingData hn hPH hPL hSH hSL qH qL hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ v DA i j) :
    cornerCoefficient hn hPH SH qH hSH - cornerCoefficient hn hPL SL qL hSL = 0 := by
  obtain ⟨B, hrec⟩ := hc.site
  have hcount := s7k_count_of_site hn hPH hPL hSH hSL qH qL x B hrec
  have h2 := s7k_DA_componentCount hn hPH hSH qH v DA hb.record
  obtain ⟨hf₂, hw₂⟩ := s7k_component_lift hn₂ hP₂ hS₂ q₂ DA j hb.comp₂
  have hslot := s7k_high_slot hn hPH hPL qH qL hcount hc.rotation
  have hdiff := s7k_coefficient_difference hn hPH hPL hSH hSL qH qL x v hv B hrec DA
    hb.record i j hb.ne hslot hb.curl_value hf₂
  have hK := s7k_noninterlacing_slot DA i j h2 hb.ne (s7k_DA_writhe hn hPH hSH qH v DA hb.record)
    hb.curl_writhe hw₂ hcount hb.rotation
  have hK' : cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ -
      (cornerSlot hn hPL SL qL + twoLinking DA i j) = 2 := by
    unfold cornerSlot; exact hK
  rw [hdiff, s7k_noninterlacing_floor_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hb.pattern₁ hb.pattern₂ _
    (by omega), s7k_noninterlacing_floor_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hb.pattern₁ hb.pattern₂ _
    (by omega), sub_zero]

/-! #### K. The component identifications at the RECORD level (what U110-B has to supply, with no geometry of
`D_A`): `D_A.knotRestrict i` has the record-level restriction of `D_A.record` to the circle `i`
(`restrict_record`), and `D_A.record ≅ (record D_H).smooth v ≅ (gaussRecord X_H).smooth (Φ v)` through the CB
record bridge `CB.positiveLiftRecordIso` — so each component of `D_A` is a restriction of the smoothing of the
ABSTRACT Gauss record of the contact carrier's self-crossings, and the identification with a half contact
carrier's lift is `((gaussRecord X_H).smooth w).restrict {c} ≅ gaussRecord X_{L_i}`, a statement about the
two crossing geometries (sm-4:496-533 "component 1 / component 2", 800-835). -/

/-- The record of a `knotRestrict` of `D_A` through any record identification `D_A.record ≅ ρ`: the
record-level restriction of `ρ` to the image circle (`Diagram.restrictRecordIso` + `RecordIso.restrict`). -/
theorem s7k_knotRestrict_record_iso (DA : Diagram) {ρ : Record} (ι : RecordIso DA.record ρ)
    (i : Fin DA.Γ.c) :
    Nonempty (RecordIso (DA.knotRestrict i).record (ρ.restrict {ι.e i})) := by
  refine ⟨(DA.restrictRecordIso {i} (Finset.singleton_nonempty i)).trans
    (ι.restrict {i} {ι.e i} fun c => ?_)⟩
  simp only [Finset.mem_singleton]
  exact ι.e.injective.eq_iff

/-- On the actual high lift `D_H = positiveLift q_H`: every component of `D_A` is a record-level restriction of
the smoothing of the abstract Gauss record `gaussRecord (cg P_H) X(L_H)` at the image occurrence of `v`. -/
theorem s7k_component_record_of_gauss (hn : 3 ≤ n) {PH : LabelledTuple n} (hPH : Generic PH)
    {SH : Finset (Crossing PH)} (hSH : IsDecomposition hn hPH SH) (qH : Component hn hPH SH)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (DA : Diagram)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v)))
    (i : Fin DA.Γ.c) :
    ∃ c, Nonempty (RecordIso (DA.knotRestrict i).record
      (((CB.gaussRecord (CB.cg hn hPH) (carrierCrossings hn hPH SH qH)).smooth
        ((CB.positiveLiftRecordIso hn hPH hSH qH).Φ v)).restrict {c})) := by
  obtain ⟨ι⟩ := hrecA
  exact ⟨_, s7k_knotRestrict_record_iso DA (ι.trans ((CB.positiveLiftRecordIso hn hPH hSH qH).smooth v)) i⟩

/-- **The component identification from its Gauss-record form**: if the restriction of the smoothed Gauss
record of `L_H` to the circle `c` is the Gauss record of the half contact carrier `L` (of the decomposition `T`
of the half `λ`), then `D_A.knotRestrict i` has the record of `L`'s positive lift — the field `comp₁ / comp₂`
of the branch data. -/
theorem s7k_component_iso_of_gauss (hn : 3 ≤ n) {PH : LabelledTuple n} (hPH : Generic PH)
    {SH : Finset (Crossing PH)} (hSH : IsDecomposition hn hPH SH) (qH : Component hn hPH SH)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (DA : Diagram)
    (ι : RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v)) (i : Fin DA.Γ.c)
    {m : ℕ} [NeZero m] (hm : 3 ≤ m) {Q : LabelledTuple m} (hQ : Generic Q) {T : Finset (Crossing Q)}
    (hT : IsDecomposition hm hQ T) (q : Component hm hQ T)
    (hg : Nonempty (RecordIso
      (((CB.gaussRecord (CB.cg hn hPH) (carrierCrossings hn hPH SH qH)).smooth
        ((CB.positiveLiftRecordIso hn hPH hSH qH).Φ v)).restrict
          {(ι.trans ((CB.positiveLiftRecordIso hn hPH hSH qH).smooth v)).e i})
      (CB.gaussRecord (CB.cg hm hQ) (carrierCrossings hm hQ T q)))) :
    Nonempty (RecordIso (DA.knotRestrict i).record (positiveLift hm hQ T q hT).record) := by
  obtain ⟨κ⟩ := s7k_knotRestrict_record_iso DA (ι.trans ((CB.positiveLiftRecordIso hn hPH hSH qH).smooth v)) i
  obtain ⟨γ⟩ := hg
  exact ⟨κ.trans (γ.trans (CB.positiveLiftRecordIso hm hQ hT q).symm)⟩

/-! #### L. The R-II reduced record at the RECORD level (what U110-A has to supply): `B.reducedRecord` is
`(D_H^{sw x}).record.restrictCrossings B.keep`, and `(D_H^{sw x}).record ≅ (record D_H).switch v ≅
(gaussRecord X_H).switch (Φ v)` (`Diagram.switchRecordIso`, `RecordIso.switch`, `CB.positiveLiftRecordIso`), so the
reduced record is the switched abstract Gauss record of the contact carrier minus the image of the two
bigon crossings — and its identification with `D_L`'s record is `((gaussRecord X_H).switch w).restrictCrossings K
≅ gaussRecord X_{L_L}`, U110-A's persistent visit order on abstract Gauss records (sm-4:602-606). -/

/-- The image of a crossing set under a record isomorphism (crossings are occurrence pairs, `Finset.map Φ`). -/
def s7k_crossingImage {ρ ρ' : Record} (ι : RecordIso ρ ρ') (X : Set ρ.Crossing) : Set ρ'.Crossing :=
  {c' | ∃ c ∈ X, c'.1 = c.1.map ι.Φ.toEmbedding}

/-- The occurrence-level condition of `CB.restrictCrossings_iso_of_recordIso` for the image set
(`RecordIso.crossingOf_eq`, `Finset.map_injective`). -/
theorem s7k_mem_crossingImage_iff {ρ ρ' : Record} (ι : RecordIso ρ ρ') (X : Set ρ.Crossing) (v : ρ.M) :
    ρ.crossingOf v ∈ X ↔ ρ'.crossingOf (ι.Φ v) ∈ s7k_crossingImage ι X := by
  constructor
  · intro h
    exact ⟨_, h, by rw [ι.crossingOf_eq]⟩
  · rintro ⟨c, hc, hcv⟩
    rw [ι.crossingOf_eq] at hcv
    have hcv' : (ρ.crossingOf v).1.map ι.Φ.toEmbedding = c.1.map ι.Φ.toEmbedding := hcv
    have h1 : ρ.crossingOf v = c := Subtype.ext (Finset.map_injective _ hcv')
    rw [h1]; exact hc

/-- Restriction to a crossing set transports along a record isomorphism, onto the image set. -/
theorem s7k_restrictCrossings_iso {ρ ρ' : Record} (ι : RecordIso ρ ρ') (X : Set ρ.Crossing) :
    Nonempty (RecordIso (ρ.restrictCrossings X) (ρ'.restrictCrossings (s7k_crossingImage ι X))) :=
  CB.restrictCrossings_iso_of_recordIso ι X _ (s7k_mem_crossingImage_iff ι X)

/-- **The reduced record of a bigon site on the switched high lift is a restriction of the switched Gauss
record of `L_H`.** -/
theorem s7k_reducedRecord_iso_of_gauss (hn : 3 ≤ n) {PH : LabelledTuple n} (hPH : Generic PH)
    {SH : Finset (Crossing PH)} (hSH : IsDecomposition hn hPH SH) (qH : Component hn hPH SH)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing) (v : (positiveLift hn hPH SH qH hSH).Γ.Visit)
    (hv : v.1 = x) (B : BigonData ((positiveLift hn hPH SH qH hSH).switch x)) :
    Nonempty (RecordIso B.reducedRecord
      (((CB.gaussRecord (CB.cg hn hPH) (carrierCrossings hn hPH SH qH)).switch
        ((CB.positiveLiftRecordIso hn hPH hSH qH).Φ v)).restrictCrossings
          (s7k_crossingImage (((positiveLift hn hPH SH qH hSH).switchRecordIso x v hv).trans
            ((CB.positiveLiftRecordIso hn hPH hSH qH).switch v)) B.keep))) :=
  s7k_restrictCrossings_iso _ B.keep

/-- **The field `reduced_iso` from its Gauss-record form**: if the switched Gauss record of `L_H` minus the
bigon crossings is the Gauss record of `L_L` (U110-A), then the reduced record is `D_L`'s record. -/
theorem s7k_reduced_iso_of_gauss (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH)
    (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (hv : v.1 = x)
    (B : BigonData ((positiveLift hn hPH SH qH hSH).switch x))
    (hg : Nonempty (RecordIso
      (((CB.gaussRecord (CB.cg hn hPH) (carrierCrossings hn hPH SH qH)).switch
        ((CB.positiveLiftRecordIso hn hPH hSH qH).Φ v)).restrictCrossings
          (s7k_crossingImage (((positiveLift hn hPH SH qH hSH).switchRecordIso x v hv).trans
            ((CB.positiveLiftRecordIso hn hPH hSH qH).switch v)) B.keep))
      (CB.gaussRecord (CB.cg hn hPL) (carrierCrossings hn hPL SL qL)))) :
    Nonempty (RecordIso B.reducedRecord (positiveLift hn hPL SL qL hSL).record) := by
  obtain ⟨κ⟩ := s7k_reducedRecord_iso_of_gauss hn hPH hSH qH x v hv B
  obtain ⟨γ⟩ := hg
  exact ⟨κ.trans (γ.trans (CB.positiveLiftRecordIso hn hPL hSL qL).symm)⟩

/-! #### I. Constructors for the branch data from the outputs of U110-C/I and the mp:blocks curl route -/

/-- A one-crossing diagram whose crossing is positive has writhe `+1` (the curl block `y`: a positive self
crossing of the positive lift, kept by the smoothing). -/
theorem s7k_single_crossing_writhe (D : Diagram) (x₀ : D.Γ.Crossing) (hx : ∀ y : D.Γ.Crossing, y = x₀)
    (hpos : D.IsPositive x₀) : D.writhe = 1 := by
  unfold Diagram.writhe
  rw [Finset.sum_eq_single x₀ (fun y _ hy => absurd (hx y) hy) (fun h => absurd (Finset.mem_univ _) h),
    (D.isPositive_iff_sign_eq_one x₀).mp hpos, SignType.coe_one]

/-- **The interlacing branch data from U110-B's record identifications and U110-C/I's uniform patterns**:
the principal-turn-preserving corner correspondence `e`/`he` of the three contact carriers (U110-I's `he`,
which U110-B builds from "inherited corner edges are positive multiples", `s7i_principalTurn_eq_of_edges_pos_smul`)
and the three uniform patterns of sign `s₀` (`s7c_uniform_halves_of_interlacing` at a live selector) give
`R_L = R₁ + R₂` (`s7i_carrierRotationInt_interlacing`) and the floor's patterns. -/
theorem s7k_interlacingData_of_patterns (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH)
    (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂) (v : (positiveLift hn hPH SH qH hSH).Γ.Visit)
    (DA : Diagram) (i j : Fin DA.Γ.c)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v)))
    (hij : i ≠ j)
    (h₁ : Nonempty (RecordIso (DA.knotRestrict i).record (positiveLift hn₁ hP₁ S₁ q₁ hS₁).record))
    (h₂ : Nonempty (RecordIso (DA.knotRestrict j).record (positiveLift hn₂ hP₂ S₂ q₂ hS₂).record))
    {j₀ : ZMod (ccpCornerCount hn hPL SL qL)} {j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁)}
    {j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)}
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hPL SL qL) // i ≠ j₀})
    (he : ∀ x, principalTurn (ccpCornerPolygon hn hPL SL qL) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          principalTurn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          principalTurn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hall₁ : ∀ i, turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) i = s₀)
    (hall₂ : ∀ i, turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) i = s₀)
    (hall : ∀ i, turn (ccpCornerPolygon hn hPL SL qL) i = s₀) :
    s7k_InterlacingData hn hPH hPL hSH hSL qH qL hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ v DA i j :=
  ⟨hrecA, hij, h₁, h₂,
    s7i_carrierRotationInt_interlacing hn hPL hSL qL hn₁ hP₁ hS₁ q₁ hn₂ hP₂ hS₂ q₂ e he hs₀ hall₁ hall₂ hall,
    s7c_signedUniformOrOneDissent_of_forall _ hs₀ hall₁, s7c_signedUniformOrOneDissent_of_forall _ hs₀ hall₂⟩

/-- **The noninterlacing branch data through the mp:blocks curl route** (no `RIData`): component `i` of `D_A`
has a record `ρ` with a block supply `C` whose block `H₀` is a positive single crossing (the curl `y`), the
lift of the one-dissent half contact carrier `L₁` has a record `ρ'` with a block supply `C'`, and the other
blocks correspond (`e`, equal block values and writhes — the consumer supplies the same block diagrams on
both sides); component `j` is the lift of `L₂`; the one-dissent patterns and the principal-turn correspondence
give `R₁ + R₂ − R_L = −1` (`s7i_carrierRotationInt_noninterlacing`) and the floor's patterns
(`s7c_signedUniformOrOneDissent_of_dissent`). -/
theorem s7k_noninterlacingData_of_blocks (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH)
    (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂) (v : (positiveLift hn hPH SH qH hSH).Γ.Visit)
    (DA : Diagram) (i j : Fin DA.Γ.c)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v)))
    (hij : i ≠ j)
    -- the curl component through mp:blocks
    (ρ : Record) (hρ : Nonempty (RecordIso (DA.knotRestrict i).record ρ))
    (C : ρ.interlacementGraph.ConnectedComponent → Diagram) (hB : BlockSupply ρ C)
    (H₀ : ρ.interlacementGraph.ConnectedComponent) (x₀ : (C H₀).Γ.Crossing)
    (h1 : (C H₀).Γ.c = 1) (hx : ∀ y : (C H₀).Γ.Crossing, y = x₀) (hpos : (C H₀).IsPositive x₀)
    (ρ' : Record) (hρ' : Nonempty (RecordIso (positiveLift hn₁ hP₁ S₁ q₁ hS₁).record ρ'))
    (C' : ρ'.interlacementGraph.ConnectedComponent → Diagram) (hB' : BlockSupply ρ' C')
    (eB : {H : ρ.interlacementGraph.ConnectedComponent // H ≠ H₀} ≃ ρ'.interlacementGraph.ConnectedComponent)
    (heP : ∀ H : {H : ρ.interlacementGraph.ConnectedComponent // H ≠ H₀}, SM.P (C H.1) = SM.P (C' (eB H)))
    (hew : ∀ H : {H : ρ.interlacementGraph.ConnectedComponent // H ≠ H₀}, (C H.1).writhe = (C' (eB H)).writhe)
    -- the second component
    (h₂ : Nonempty (RecordIso (DA.knotRestrict j).record (positiveLift hn₂ hP₂ S₂ q₂ hS₂).record))
    -- the turn patterns and the corner correspondence
    {j₀ : ZMod (ccpCornerCount hn hPL SL qL)} {j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁)}
    {j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)}
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hPL SL qL) // i ≠ j₀})
    (he : ∀ x, principalTurn (ccpCornerPolygon hn hPL SL qL) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          principalTurn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          principalTurn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj₁ : turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) j₁ = s₀)
    (hrest₁ : ∀ i, i ≠ j₁ → turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) i = -s₀)
    (hj₂ : turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) j₂ = s₀)
    (hrest₂ : ∀ i, i ≠ j₂ → turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) i = -s₀)
    (hall : ∀ i, turn (ccpCornerPolygon hn hPL SL qL) i = -s₀) :
    s7k_NoninterlacingData hn hPH hPL hSH hSL qH qL hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ v DA i j := by
  refine ⟨hrecA, hij, ?_, ?_, h₂,
    s7i_carrierRotationInt_noninterlacing hn hPL hSL qL hn₁ hP₁ hS₁ q₁ hn₂ hP₂ hS₂ q₂ e he hs₀ hj₁ hrest₁
      hj₂ hrest₂ hall,
    s7c_signedUniformOrOneDissent_of_dissent _ (s7c_neg_sign_ne_zero hs₀) j₁ (by rw [hj₁, neg_neg]) hrest₁,
    s7c_signedUniformOrOneDissent_of_dissent _ (s7c_neg_sign_ne_zero hs₀) j₂ (by rw [hj₂, neg_neg]) hrest₂⟩
  · rw [s7k_curl_component_value _ ρ hρ C hB H₀ x₀ h1 hx _ ρ' hρ' C' hB' eB heP]
    unfold cornerHomfly
    exact P_eq_homfly _
  · rw [s7k_curl_component_writhe _ ρ hρ C hB H₀ (s7k_single_crossing_writhe _ x₀ hx hpos) _ ρ' hρ' C' hB'
      eB hew, positiveLift_writhe_eq_carrierCrossingCount]

/-! #### J. The term shape U110-K consumes (eq. s7c:interlacing-selector / s7c:noninterlacing-selector with
the extracted rows; sm-4:669-676, 770-776) -/

/-- The interlacing TERM: with the selector law `wt(L*) = −s₀ wt(L₁) wt(L₂)` (`s7c_carrierWeight_interlacing`,
the same `wt(L*)` on both sides — the contact carrier's turns are constant through the wall) and the row
`Ω_H − Ω_L = −ω₁ω₂`, the contact carrier's contribution changes by `s₀ (wt(L₁) ω₁)(wt(L₂) ω₂)`. -/
theorem s7k_interlacing_term {wt wt₁ wt₂ ΩH ΩL ω₁ ω₂ : ℤ} {s₀ : SignType}
    (hwt : wt = -(s₀ : ℤ) * (wt₁ * wt₂)) (hrow : ΩH - ΩL = -(ω₁ * ω₂)) :
    wt * ΩH - wt * ΩL = (s₀ : ℤ) * ((wt₁ * ω₁) * (wt₂ * ω₂)) := by
  have : wt * ΩH - wt * ΩL = wt * (ΩH - ΩL) := by ring
  rw [this, hrow, hwt]; ring

/-- The noninterlacing TERM: `Ω_H − Ω_L = 0` kills the contact carrier's difference outright (whatever the
selector), and independently `s7c_carrierWeight_noninterlacing`'s `wt(L*) (wt(L₁) wt(L₂)) = 0` kills the
returned product row — both printed readings of "every returned row is zero" (sm-4:770-776). -/
theorem s7k_noninterlacing_term {wt wt₁ wt₂ ΩH ΩL ω₁ ω₂ : ℤ} (hrow : ΩH - ΩL = 0)
    (hwt : wt * (wt₁ * wt₂) = 0) :
    wt * ΩH - wt * ΩL = 0 ∧ wt * ((wt₁ * ω₁) * (wt₂ * ω₂)) = 0 := by
  refine ⟨?_, ?_⟩
  · have : wt * ΩH - wt * ΩL = wt * (ΩH - ΩL) := by ring
    rw [this, hrow, mul_zero]
  · have : wt * ((wt₁ * ω₁) * (wt₂ * ω₂)) = (wt * (wt₁ * wt₂)) * (ω₁ * ω₂) := by ring
    rw [this, hwt, zero_mul]

/-! #### M. Two further rows of the bigon branch in the term shape of eq. C-selector-form
(`wind S * cornerProduct S`, `C_X1.selector_form`): the one-newborn rows (sm-4:777-783, cb:singleton ENTERS)
and the contact triangle at `ε = 0` (sm-4:437-447, `corner_values_i`). -/

/-- **The one-newborn rows** (sm-4:777-783): a support whose carrier `q` owns a crossing `c` interlacing no
other crossing of `q` contributes `0` — if `q` is uniform, `c(q) = 0` by cb:singleton (`hsing.isolated_zero`);
otherwise its selector `wt(q) = 0` (`carrierWeight_eq_zero_of_not_uniform`).  For `T ∪ {x}` with the isolated
block `{y}` this is the printed sentence "the singleton block `{y}` … the row is zero". -/
theorem s7k_one_newborn_term_zero (hsing : CbSingletonData) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (c : Crossing P) (hc : c ∈ carrierCrossings hn hP S q)
    (hiso : ∀ c' ∈ carrierCrossings hn hP S q, c' ≠ c → ¬ Interlaces hn hP c c') :
    wind hn hP S * cornerProduct hn hP S hS = 0 := by
  by_cases hu : CarrierUniform hn hP S q
  · have h0 : cornerCoefficient hn hP S q hS = 0 := hsing.isolated_zero n hn P hP S hS q hu c hc hiso
    unfold cornerProduct
    rw [Finset.prod_eq_zero (Finset.mem_univ q) h0, mul_zero]
  · unfold wind
    rw [Finset.prod_eq_zero (Finset.mem_univ q) (carrierWeight_eq_zero_of_not_uniform hn hP S q hu),
      zero_mul]

/-- **The contact triangle** (sm-4:437-447, eq. s7c:triangle-data): a crossing-free carrier with three
corners all of turn `−s₀` has `wt = s₀` (`s7c_carrierWeight_triangle`) and, being uniform and embedded,
`|rot| = 1`, `d = 0`, `c = 1` (`corner_values_i`, unconditional) — its factor in the `ε = 0` high-side term
is `wt · c = s₀`. -/
theorem s7k_triangle_factor (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S) {s₀ : SignType}
    (hs₀ : s₀ ≠ 0) (h3 : ccpCornerCount hn hP S q = 3)
    (hturn : ∀ j, turn (ccpCornerPolygon hn hP S q) j = -s₀) (hm : carrierCrossingCount hn hP S q = 0) :
    carrierWeight hn hP S q * cornerCoefficient hn hP S q hS = (s₀ : ℤ) ∧
      cornerSlot hn hP S q = 0 ∧ |carrierRotation hn hP S q| = 1 := by
  have hu : CarrierUniform hn hP S q := ⟨-s₀, s7c_neg_sign_ne_zero hs₀, hturn⟩
  obtain ⟨hrot, hslot, hc⟩ := corner_values_i hn hP hS q hu hm
  refine ⟨?_, hslot, hrot⟩
  rw [s7c_carrierWeight_triangle hn hP S q hs₀ h3 hturn, hc, mul_one]

/-- **The different-block alternative** (sm-4:785-813; eqs. s7c:different-low-slot / -high-slot): when both
newborns `x, y` are singleton blocks of the contact carrier, mp:blocks gives `H⁺_{L_H} = H⁺_{L_L} = f₁ f₂` (the
consumer's two hypotheses `hfH`, `hfL`, from `product_of_chain` / `curl_block_value` with the two one-crossing
blocks of value `1`), the writhes are `m_L = m₁ + m₂`, `m_H = m₁ + m₂ + 2`, the rotations `R₁ + R₂ − R_L = −1`,
`R_H = R_L`; then `k_L = K − 2`, `k_H = K − 4` (`s7i_different_slot`) and both reads lie below the floor `K` of
`f₁ f₂` at the one-dissent half contact carriers: `Ω_H = Ω_L = 0`. -/
theorem s7k_different_block_row (hF : FloorTheoremData) (hn : 3 ≤ n) {PH PL : LabelledTuple n}
    (hPH : Generic PH) (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hfH : cornerHomfly hn hPH SH qH hSH = cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂)
    (hfL : cornerHomfly hn hPL SL qL hSL = cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂)
    (hmH : carrierCrossingCount hn hPH SH qH =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂ + 2)
    (hmL : carrierCrossingCount hn hPL SL qL =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂)
    (hR : |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| -
      |carrierRotationInt hn hPL SL qL| = -1)
    (hRH : |carrierRotationInt hn hPH SH qH| = |carrierRotationInt hn hPL SL qL|)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)) :
    cornerCoefficient hn hPH SH qH hSH = 0 ∧ cornerCoefficient hn hPL SL qL hSL = 0 := by
  have hkL : cornerSlot hn hPL SL qL < cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ := by
    unfold cornerSlot; rw [hmL]; push_cast; omega
  have hkH : cornerSlot hn hPH SH qH < cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ := by
    unfold cornerSlot; rw [hmH, hRH]; push_cast; omega
  refine ⟨?_, ?_⟩
  · rw [cornerCoefficient_eq_coeffAt, hfH]
    exact s7k_noninterlacing_floor_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hu₁ hu₂ _ hkH
  · rw [cornerCoefficient_eq_coeffAt, hfL]
    exact s7k_noninterlacing_floor_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hu₁ hu₂ _ hkL

end S7KBlock

/-! ### Unit J (wave 3, prefix `s7j_`; PLAN_FINAL §3.3 bigon (5), sm-4:655-668, 765-769, 777-783, 785-813,
800-835; serves U110-K `s7_bigon_law_at`): **where the floor and cb:singleton ENTER the bigon branch**.
Every theorem takes the EXTRACTED ROWS (the outputs of unit BLOCK: eq. s7c:interlacing-extraction
`Ω_H − Ω_L = [a^{K−2}](f₁f₂) − [a^K](f₁f₂)`, eq. s7c:noninterlacing-extraction with `K−4, K−2`, eq.
s7c:different-polynomials `f_H = f_L = f₁f₂`) as EXPLICIT HYPOTHESES in the vocabulary of the Laurent ring
`R` and of def:C (`cornerHomfly`, `cornerSlot`, `cornerCoefficient`), and returns the printed conclusion.
The floor `hF` enters ONLY through `FloorTheoremData.slot_le_of_signed` (§A); cb:singleton `hsing` ONLY
through `CbSingletonData.isolated_zero` (§E).  §D states the entries at the WALL's own halves
`firstHalf g.center M a`, `secondHalf g.center M a` with the leaf's genericity proofs `h₁ h₂` and sizes
`(contactHalfSizes_bounds hn h.1.1).i.1` — the printed hypothesis discharge (800-835): the half contact
carrier `Lᵢ` is a literal `Component hn'ᵢ hᵢ Tᵢ` of a decomposition `Tᵢ` of the generic half `λᵢ`, the
floor's domain; U110-B supplies `Tᵢ, hTᵢ, Lᵢ`.  The printed case "if either `fᵢ = 0`" is vacuous here:
`cornerHomfly_ne_zero`.  Every `s7j_` declaration is proved; no other wave-3 unit is consumed by name. -/
section S7JFloor

variable {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]

/-! #### A. The floor at one half contact carrier — `hF` enters -/

/-- lp:core `knot_support` on the one-component positive lift: `H⁺_Q` has no negative `z`-exponent
(the `hz` inputs of `s7_corner_product`). -/
theorem s7j_z_nonneg (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S) (d k : ℤ)
    (h : coeffAt d k (cornerHomfly hn hP S q hS) ≠ 0) : 0 ≤ k := by
  unfold cornerHomfly at h
  rw [← P_eq_homfly] at h
  obtain ⟨j, hj⟩ := P_knot_support _ (positiveLift_componentCount hn hP S q hS) d k h
  omega

/-- **thm:floor at a UNIFORM half contact carrier** (the `ε = 1` reads, sm-4:680-684: "both half contact
carriers are uniform, and each is a subpolygon of a decomposition of its generic half … the domain of
Theorem floor, which gives `mindeg_a fᵢ ≥ kᵢ`"). -/
theorem s7j_floor_of_uniform (hF : FloorTheoremData) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (hu : CarrierUniform hn hP S q) :
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS) :=
  hF.slot_le_of_signed hn P hP S hS q (signedUniformOrOneDissent_of_uniform hn hP S q hu)

/-- **thm:floor at a ONE-DISSENT half contact carrier** (the `ε = 0` reads, sm-4:745-748: "every half
inherits its old turns and has exactly one new contact turn of sign `s₀`, hence exactly one dissent"):
turns `τ` everywhere except the contact corner `j₀`, where the turn is `−τ`. -/
theorem s7j_floor_of_dissent (hF : FloorTheoremData) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {τ : SignType} (hτ : τ ≠ 0) (j₀ : ZMod (ccpCornerCount hn hP S q))
    (h0 : turn (ccpCornerPolygon hn hP S q) j₀ = -τ)
    (h : ∀ j, j ≠ j₀ → turn (ccpCornerPolygon hn hP S q) j = τ) :
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS) :=
  hF.slot_le_of_signed hn P hP S hS q
    (s7c_signedUniformOrOneDissent_of_dissent (ccpCornerPolygon hn hP S q) hτ j₀ h0 h)

/-- The floor at a carrier with the signed pattern (the shape units C/I return). -/
theorem s7j_floor_of_signed (hF : FloorTheoremData) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (hu : SignedUniformOrOneDissent (ccpCornerPolygon hn hP S q)) :
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS) :=
  hF.slot_le_of_signed hn P hP S hS q hu

/-! #### B. The entries in the Laurent ring, with the extracted rows as hypotheses -/

/-- eq. s7c:interlacing-slot in pure `ℤ`: `k_L = 1 − w_L − R_L` with `w_L = w₁ + w₂ + 2ℓ − 1` (eq.
s7c:interlacing-writhe-row) and `R_L = R₁ + R₂` (eq. s7c:interlacing-absolute) gives `k_L + 2ℓ = K`. -/
theorem s7j_interlacing_slot_int {kL k₁ k₂ wL w₁ w₂ RL R₁ R₂ ℓ : ℤ} (hkL : kL = 1 - wL - RL)
    (hk₁ : k₁ = 1 - w₁ - R₁) (hk₂ : k₂ = 1 - w₂ - R₂) (hw : wL = w₁ + w₂ + 2 * ℓ - 1)
    (hR : RL = R₁ + R₂) : kL + 2 * ℓ = k₁ + k₂ := by omega

/-- eq. s7c:noninterlacing-slot in pure `ℤ`: with `w_L = w₁ + w₂ + 2ℓ` (eq. s7c:noninterlacing-writhe) and
`R₁ + R₂ − R_L = −1` (eq. s7c:noninterlacing-rotation), `K − k_L = 2ℓ + 2`. -/
theorem s7j_noninterlacing_slot_int {kL k₁ k₂ wL w₁ w₂ RL R₁ R₂ ℓ : ℤ} (hkL : kL = 1 - wL - RL)
    (hk₁ : k₁ = 1 - w₁ - R₁) (hk₂ : k₂ = 1 - w₂ - R₂) (hw : wL = w₁ + w₂ + 2 * ℓ)
    (hR : R₁ + R₂ - RL = -1) : k₁ + k₂ - kL = 2 * ℓ + 2 := by omega

/-- eqs. s7c:different-low-slot / -high-slot in pure `ℤ`: `w_L = w₁ + w₂`, `w_H = w₁ + w₂ + 2`,
`R₁ + R₂ − R_L = −1`, `R_H = R_L` give `k_L = K − 2` and `k_H = K − 4`. -/
theorem s7j_different_slot_int {kH kL k₁ k₂ wH wL w₁ w₂ RH RL R₁ R₂ : ℤ} (hkH : kH = 1 - wH - RH)
    (hkL : kL = 1 - wL - RL) (hk₁ : k₁ = 1 - w₁ - R₁) (hk₂ : k₂ = 1 - w₂ - R₂)
    (hwH : wH = w₁ + w₂ + 2) (hwL : wL = w₁ + w₂) (hR : R₁ + R₂ - RL = -1) (hRH : RH = RL) :
    kL = k₁ + k₂ - 2 ∧ kH = k₁ + k₂ - 4 := by omega

/-- **The interlacing entry** (sm-4:679-690, eq. s7c:interlacing-coefficient-result): from the extracted
row `Ω_H − Ω_L = [a^{K−2}](f₁f₂) − [a^K](f₁f₂)` with `K = k₁ + k₂`, the floors `kᵢ ≤ mindeg_a fᵢ` and no
negative `z`-exponents, `Ω_H − Ω_L = −ω₁ω₂` where `ωᵢ = [a^{kᵢ} z⁰] fᵢ` ("its degree `K − 2` coefficient
is zero; in the degree `K` convolution … the only possible pair is exactly `(k₁, k₂)`"). -/
theorem s7j_interlacing_entry {f₁ f₂ : R} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) {k₁ k₂ K : ℤ}
    (hK : K = k₁ + k₂) (h₁ : k₁ ≤ mindegAZ f₁) (h₂ : k₂ ≤ mindegAZ f₂)
    (hz₁ : ∀ d k, coeffAt d k f₁ ≠ 0 → 0 ≤ k) (hz₂ : ∀ d k, coeffAt d k f₂ ≠ 0 → 0 ≤ k)
    {ΩH ΩL : ℤ} (hrow : ΩH - ΩL = coeffAt (K - 2) 0 (f₁ * f₂) - coeffAt K 0 (f₁ * f₂)) :
    ΩH - ΩL = -(coeffAt k₁ 0 f₁ * coeffAt k₂ 0 f₂) := by
  obtain ⟨h0, hprod⟩ := s7_corner_product hf₁ hf₂ h₁ h₂ hz₁ hz₂
  subst hK
  rw [hrow, h0, hprod, zero_sub]

/-- **One read below the floor** (the device of sm-4:765-769 and 805-811): a row `Ω = [a^d z⁰](f₁f₂)` with
`d < k₁ + k₂` is zero. -/
theorem s7j_below_floor_entry {f₁ f₂ : R} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) {k₁ k₂ d : ℤ}
    (h₁ : k₁ ≤ mindegAZ f₁) (h₂ : k₂ ≤ mindegAZ f₂) (hd : d < k₁ + k₂) {Ω : ℤ}
    (hrow : Ω = coeffAt d 0 (f₁ * f₂)) : Ω = 0 := by
  rw [hrow]
  exact coeffAt_mul_eq_zero_of_lt_floor hf₁ hf₂ h₁ h₂ hd

/-- **The noninterlacing entry** (sm-4:762-769, eq. s7c:noninterlacing-extraction): from the extracted row
`Ω_H − Ω_L = [a^{K−4}](f₁f₂) − [a^{K−2}](f₁f₂)` with `K = k₁ + k₂` and the two one-dissent floors,
"both displayed coefficients are below this floor; thus the returned newborn-free row is zero". -/
theorem s7j_noninterlacing_entry {f₁ f₂ : R} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) {k₁ k₂ K : ℤ}
    (hK : K = k₁ + k₂) (h₁ : k₁ ≤ mindegAZ f₁) (h₂ : k₂ ≤ mindegAZ f₂) {ΩH ΩL : ℤ}
    (hrow : ΩH - ΩL = coeffAt (K - 4) 0 (f₁ * f₂) - coeffAt (K - 2) 0 (f₁ * f₂)) : ΩH - ΩL = 0 := by
  rw [hrow, coeffAt_mul_eq_zero_of_lt_floor hf₁ hf₂ h₁ h₂ (by omega),
    coeffAt_mul_eq_zero_of_lt_floor hf₁ hf₂ h₁ h₂ (by omega), sub_zero]

/-- **The different-block entry** (sm-4:785-813): with `f_H = f_L = f₁f₂` (eq. s7c:different-polynomials)
and the slots `k_L = K − 2`, `k_H = K − 4` (eqs. s7c:different-low/high-slot) below the floor `K` of the
product, "both reads vanish separately": `Ω_H = 0` and `Ω_L = 0`. -/
theorem s7j_different_block_entry {fH fL f₁ f₂ : R} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0)
    (hfH : fH = f₁ * f₂) (hfL : fL = f₁ * f₂) {kH kL k₁ k₂ : ℤ} (hkH : kH = k₁ + k₂ - 4)
    (hkL : kL = k₁ + k₂ - 2) (h₁ : k₁ ≤ mindegAZ f₁) (h₂ : k₂ ≤ mindegAZ f₂) :
    coeffAt kH 0 fH = 0 ∧ coeffAt kL 0 fL = 0 :=
  ⟨by rw [hfH]; exact coeffAt_mul_eq_zero_of_lt_floor hf₁ hf₂ h₁ h₂ (by omega),
   by rw [hfL]; exact coeffAt_mul_eq_zero_of_lt_floor hf₁ hf₂ h₁ h₂ (by omega)⟩

/-! #### C. The entries at carriers (def:C's vocabulary at two half contact carriers `L₁, L₂`) -/

/-- The interlacing entry at two UNIFORM half contact carriers: the extracted row at `K = k₁ + k₂`
(`cornerSlot`s) on `H⁺_{L₁} H⁺_{L₂}` returns `Ω_H − Ω_L = −c(L₁) c(L₂)`. -/
theorem s7j_interlacing_read (hF : FloorTheoremData) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂)
    {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂)
    {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁)
    (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hu₁ : CarrierUniform hn₁ hP₁ S₁ q₁) (hu₂ : CarrierUniform hn₂ hP₂ S₂ q₂) {ΩH ΩL : ℤ}
    (hrow : ΩH - ΩL =
      coeffAt (cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 2) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) -
        coeffAt (cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂)) :
    ΩH - ΩL = -(cornerCoefficient hn₁ hP₁ S₁ q₁ hS₁ * cornerCoefficient hn₂ hP₂ S₂ q₂ hS₂) :=
  s7j_interlacing_entry (cornerHomfly_ne_zero hn₁ hP₁ S₁ q₁ hS₁) (cornerHomfly_ne_zero hn₂ hP₂ S₂ q₂ hS₂)
    rfl (s7j_floor_of_uniform hF hn₁ hP₁ hS₁ q₁ hu₁) (s7j_floor_of_uniform hF hn₂ hP₂ hS₂ q₂ hu₂)
    (s7j_z_nonneg hn₁ hP₁ hS₁ q₁) (s7j_z_nonneg hn₂ hP₂ hS₂ q₂) hrow

/-- The noninterlacing entry at two half contact carriers with the signed (one-dissent) pattern: the
extracted row at `K − 4, K − 2` returns `Ω_H − Ω_L = 0`. -/
theorem s7j_noninterlacing_read (hF : FloorTheoremData) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂)
    {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂)
    {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁)
    (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)) {ΩH ΩL : ℤ}
    (hrow : ΩH - ΩL =
      coeffAt (cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 4) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) -
        coeffAt (cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 2) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂)) :
    ΩH - ΩL = 0 :=
  s7j_noninterlacing_entry (cornerHomfly_ne_zero hn₁ hP₁ S₁ q₁ hS₁)
    (cornerHomfly_ne_zero hn₂ hP₂ S₂ q₂ hS₂) rfl (s7j_floor_of_signed hF hn₁ hP₁ hS₁ q₁ hu₁)
    (s7j_floor_of_signed hF hn₂ hP₂ hS₂ q₂ hu₂) hrow

/-- Any read of `H⁺_{L₁} H⁺_{L₂}` at an `a`-degree below `k₁ + k₂` is zero at signed patterns. -/
theorem s7j_below_floor_read (hF : FloorTheoremData) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂)
    {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂)
    {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁)
    (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)) {d : ℤ}
    (hd : d < cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂) :
    coeffAt d 0 (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) = 0 :=
  coeffAt_mul_eq_zero_of_lt_floor (cornerHomfly_ne_zero hn₁ hP₁ S₁ q₁ hS₁)
    (cornerHomfly_ne_zero hn₂ hP₂ S₂ q₂ hS₂) (s7j_floor_of_signed hF hn₁ hP₁ hS₁ q₁ hu₁)
    (s7j_floor_of_signed hF hn₂ hP₂ hS₂ q₂ hu₂) hd

/-- The different-block entry at carriers: `H⁺_{L_H} = H⁺_{L_L} = H⁺_{L₁} H⁺_{L₂}` (mp:blocks with the two
singleton newborn blocks, sm-4:785-800) and the slots `k_L = K − 2`, `k_H = K − 4` give
`c(L_H) = 0 ∧ c(L_L) = 0`. -/
theorem s7j_different_block_read (hF : FloorTheoremData) (hn : 3 ≤ n) {PH PL : LabelledTuple n}
    (hPH : Generic PH) (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hfH : cornerHomfly hn hPH SH qH hSH = cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂)
    (hfL : cornerHomfly hn hPL SL qL hSL = cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂)
    (hkH : cornerSlot hn hPH SH qH = cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 4)
    (hkL : cornerSlot hn hPL SL qL = cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 2)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)) :
    cornerCoefficient hn hPH SH qH hSH = 0 ∧ cornerCoefficient hn hPL SL qL hSL = 0 := by
  rw [cornerCoefficient_eq_coeffAt, cornerCoefficient_eq_coeffAt]
  exact s7j_different_block_entry (cornerHomfly_ne_zero hn₁ hP₁ S₁ q₁ hS₁)
    (cornerHomfly_ne_zero hn₂ hP₂ S₂ q₂ hS₂) hfH hfL hkH hkL (s7j_floor_of_signed hF hn₁ hP₁ hS₁ q₁ hu₁)
    (s7j_floor_of_signed hF hn₂ hP₂ hS₂ q₂ hu₂)

/-- The slots of the different-block alternative from the printed counts (eq. s7c:different-polynomials'
writhes `m_H = m₁ + m₂ + 2`, `m_L = m₁ + m₂`; eq. s7c:noninterlacing-rotation `R₁ + R₂ − R_L = −1`; eq.
s7c:full-rotation `R_H = R_L`) — the inputs of `s7j_different_block_read`. -/
theorem s7j_different_block_slots (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH)
    (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)} (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hmH : carrierCrossingCount hn hPH SH qH =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂ + 2)
    (hmL : carrierCrossingCount hn hPL SL qL =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂)
    (hR : |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| -
      |carrierRotationInt hn hPL SL qL| = -1)
    (hRH : |carrierRotationInt hn hPH SH qH| = |carrierRotationInt hn hPL SL qL|) :
    cornerSlot hn hPH SH qH = cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 4 ∧
      cornerSlot hn hPL SL qL = cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 2 := by
  unfold cornerSlot
  rw [hmH, hmL, hRH]
  push_cast
  omega

/-- eq. s7c:interlacing-slot at carriers (sm-4:665-670): `k_L + 2ℓ = k₁ + k₂` from the writhe count
`m_L = m₁ + m₂ + 2ℓ − 1` (eq. s7c:interlacing-writhe-row; `tl = 2ℓ = twoLinking D_A`) and
`|R_L| = |R₁| + |R₂|` (eq. s7c:interlacing-absolute). -/
theorem s7j_interlacing_slot (hn : 3 ≤ n) {PL : LabelledTuple n} (hPL : Generic PL)
    {SL : Finset (Crossing PL)} (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂)
    {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂)
    {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)} (q₁ : Component hn₁ hP₁ S₁)
    (q₂ : Component hn₂ hP₂ S₂) (tl : ℤ)
    (hw : (carrierCrossingCount hn hPL SL qL : ℤ) =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂ + tl - 1)
    (hR : |carrierRotationInt hn hPL SL qL| =
      |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂|) :
    cornerSlot hn hPL SL qL + tl = cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ := by
  unfold cornerSlot
  rw [hR]
  omega

/-- eq. s7c:noninterlacing-slot at carriers (sm-4:758-762): `K − (k_L + 2ℓ) = 2` from
`m_L = m₁ + m₂ + 2ℓ` (eq. s7c:noninterlacing-writhe) and `|R₁| + |R₂| − |R_L| = −1`
(eq. s7c:noninterlacing-rotation). -/
theorem s7j_noninterlacing_slot (hn : 3 ≤ n) {PL : LabelledTuple n} (hPL : Generic PL)
    {SL : Finset (Crossing PL)} (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂)
    {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂)
    {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)} (q₁ : Component hn₁ hP₁ S₁)
    (q₂ : Component hn₂ hP₂ S₂) (tl : ℤ)
    (hw : (carrierCrossingCount hn hPL SL qL : ℤ) =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂ + tl)
    (hR : |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| -
      |carrierRotationInt hn hPL SL qL| = -1) :
    cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - (cornerSlot hn hPL SL qL + tl) = 2 := by
  unfold cornerSlot
  omega

/-- **The interlacing row in the printed order** (sm-4:655-690): from the universal extraction on the
two-component row, `c(L_H) − c(L_L) = [a^{k_L+2ℓ−2}](H⁺_{L₁}H⁺_{L₂}) − [a^{k_L+2ℓ}](H⁺_{L₁}H⁺_{L₂})`
(the output shape of the skein/two-component units, `tl = 2ℓ`), the writhe count, the rotation identity
and the two UNIFORM half contact carriers: `c(L_H) − c(L_L) = −c(L₁) c(L₂)`. -/
theorem s7j_interlacing_row (hF : FloorTheoremData) (hn : 3 ≤ n) {PH PL : LabelledTuple n}
    (hPH : Generic PH) (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂) (hu₁ : CarrierUniform hn₁ hP₁ S₁ q₁)
    (hu₂ : CarrierUniform hn₂ hP₂ S₂ q₂) (tl : ℤ)
    (hext : cornerCoefficient hn hPH SH qH hSH - cornerCoefficient hn hPL SL qL hSL =
      coeffAt (cornerSlot hn hPL SL qL + tl - 2) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) -
        coeffAt (cornerSlot hn hPL SL qL + tl) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂))
    (hw : (carrierCrossingCount hn hPL SL qL : ℤ) =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂ + tl - 1)
    (hR : |carrierRotationInt hn hPL SL qL| =
      |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂|) :
    cornerCoefficient hn hPH SH qH hSH - cornerCoefficient hn hPL SL qL hSL =
      -(cornerCoefficient hn₁ hP₁ S₁ q₁ hS₁ * cornerCoefficient hn₂ hP₂ S₂ q₂ hS₂) := by
  have hK := s7j_interlacing_slot hn hPL qL hn₁ hn₂ hP₁ hP₂ q₁ q₂ tl hw hR
  rw [hK] at hext
  exact s7j_interlacing_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hu₁ hu₂ hext

/-- **The noninterlacing row in the printed order** (sm-4:736-769): the same extraction shape at
`k_L + 2ℓ`, the writhe count `m_L = m₁ + m₂ + 2ℓ`, the rotation identity `|R₁| + |R₂| − |R_L| = −1` and
the two ONE-DISSENT half contact carriers: `c(L_H) − c(L_L) = 0`. -/
theorem s7j_noninterlacing_row (hF : FloorTheoremData) (hn : 3 ≤ n) {PH PL : LabelledTuple n}
    (hPH : Generic PH) (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)) (tl : ℤ)
    (hext : cornerCoefficient hn hPH SH qH hSH - cornerCoefficient hn hPL SL qL hSL =
      coeffAt (cornerSlot hn hPL SL qL + tl - 2) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) -
        coeffAt (cornerSlot hn hPL SL qL + tl) 0
          (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂))
    (hw : (carrierCrossingCount hn hPL SL qL : ℤ) =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂ + tl)
    (hR : |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| -
      |carrierRotationInt hn hPL SL qL| = -1) :
    cornerCoefficient hn hPH SH qH hSH - cornerCoefficient hn hPL SL qL hSL = 0 := by
  have hK := s7j_noninterlacing_slot hn hPL qL hn₁ hn₂ hP₁ hP₂ q₁ q₂ tl hw hR
  rw [hext]
  rw [s7j_below_floor_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hu₁ hu₂ (by omega),
    s7j_below_floor_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hu₁ hu₂ (by omega), sub_zero]

/-! #### D. The entries at the WALL's halves — the floor-domain discharge (sm-4:800-835) literally:
`λ₁ = firstHalf g.center M a`, `λ₂ = secondHalf g.center M a` with the leaf's `h₁ h₂ : Generic` and sizes
`(contactHalfSizes_bounds hn h.1.1).1.1 / .2.1`; `Tᵢ` a decomposition of `λᵢ`, `Lᵢ : Component … Tᵢ`. -/

/-- thm:floor at a carrier of a decomposition of the FIRST generic half of a bigon wall. -/
theorem s7j_half₁_floor (hF : FloorTheoremData) (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)
    (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    {T₁ : Finset (Crossing (firstHalf g.center M a))}
    (hT₁ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (L₁ : Component (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (hu : SignedUniformOrOneDissent (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁)) :
    cornerSlot (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ ≤
      mindegAZ (cornerHomfly (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁) :=
  s7j_floor_of_signed hF _ h₁ hT₁ L₁ hu

/-- thm:floor at a carrier of a decomposition of the SECOND generic half of a bigon wall. -/
theorem s7j_half₂_floor (hF : FloorTheoremData) (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)
    (h : g.BigonAt M a) (h₂ : Generic (secondHalf g.center M a))
    {T₂ : Finset (Crossing (secondHalf g.center M a))}
    (hT₂ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (L₂ : Component (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (hu : SignedUniformOrOneDissent (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂)) :
    cornerSlot (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ ≤
      mindegAZ (cornerHomfly (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂) :=
  s7j_floor_of_signed hF _ h₂ hT₂ L₂ hu

/-- **The interlacing entry at the wall's halves** (`ε = 1`): the two UNIFORM half contact carriers
`L₁, L₂`, carriers of decompositions `T₁, T₂` of the generic halves, and the extracted row on
`H⁺_{L₁} H⁺_{L₂}` at `K − 2, K` give `Ω_H − Ω_L = −c(L₁) c(L₂)`. -/
theorem s7j_interlacing_entry_at_halves (hF : FloorTheoremData) (hn : 3 ≤ n) (g : WallGerm n)
    (M a : ZMod n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) {T₁ : Finset (Crossing (firstHalf g.center M a))}
    {T₂ : Finset (Crossing (secondHalf g.center M a))}
    (hT₁ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (hT₂ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (L₁ : Component (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (L₂ : Component (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (hu₁ : CarrierUniform (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁)
    (hu₂ : CarrierUniform (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂) {ΩH ΩL : ℤ}
    (hrow : ΩH - ΩL =
      coeffAt (cornerSlot (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ +
          cornerSlot (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ - 2) 0
          (cornerHomfly (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁ *
            cornerHomfly (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂) -
        coeffAt (cornerSlot (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ +
          cornerSlot (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂) 0
          (cornerHomfly (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁ *
            cornerHomfly (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂)) :
    ΩH - ΩL = -(cornerCoefficient (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁ *
      cornerCoefficient (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂) :=
  s7j_interlacing_read hF _ _ h₁ h₂ hT₁ hT₂ L₁ L₂ hu₁ hu₂ hrow

/-- **The noninterlacing entry at the wall's halves** (`ε = 0`): the two ONE-DISSENT half contact carriers
and the extracted row at `K − 4, K − 2` give `Ω_H − Ω_L = 0`. -/
theorem s7j_noninterlacing_entry_at_halves (hF : FloorTheoremData) (hn : 3 ≤ n) (g : WallGerm n)
    (M a : ZMod n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) {T₁ : Finset (Crossing (firstHalf g.center M a))}
    {T₂ : Finset (Crossing (secondHalf g.center M a))}
    (hT₁ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (hT₂ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (L₁ : Component (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (L₂ : Component (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂))
    {ΩH ΩL : ℤ}
    (hrow : ΩH - ΩL =
      coeffAt (cornerSlot (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ +
          cornerSlot (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ - 4) 0
          (cornerHomfly (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁ *
            cornerHomfly (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂) -
        coeffAt (cornerSlot (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ +
          cornerSlot (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ - 2) 0
          (cornerHomfly (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁ *
            cornerHomfly (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂)) :
    ΩH - ΩL = 0 :=
  s7j_noninterlacing_read hF _ _ h₁ h₂ hT₁ hT₂ L₁ L₂ hu₁ hu₂ hrow

/-- **The different-block entry at the wall's halves**: `H⁺_{L_H} = H⁺_{L_L} = H⁺_{L₁} H⁺_{L₂}` with the
printed counts and rotations at the two one-dissent half contact carriers give `c(L_H) = 0 ∧ c(L_L) = 0`. -/
theorem s7j_different_block_entry_at_halves (hF : FloorTheoremData) (hn : 3 ≤ n) (g : WallGerm n)
    (M a : ZMod n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) {PH PL : LabelledTuple n} (hPH : Generic PH)
    (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) {T₁ : Finset (Crossing (firstHalf g.center M a))}
    {T₂ : Finset (Crossing (secondHalf g.center M a))}
    (hT₁ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (hT₂ : IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (L₁ : Component (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁)
    (L₂ : Component (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂)
    (hfH : cornerHomfly hn hPH SH qH hSH =
      cornerHomfly (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁ *
        cornerHomfly (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂)
    (hfL : cornerHomfly hn hPL SL qL hSL =
      cornerHomfly (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ hT₁ *
        cornerHomfly (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ hT₂)
    (hmH : carrierCrossingCount hn hPH SH qH =
      carrierCrossingCount (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ +
        carrierCrossingCount (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂ + 2)
    (hmL : carrierCrossingCount hn hPL SL qL =
      carrierCrossingCount (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁ +
        carrierCrossingCount (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂)
    (hR : |carrierRotationInt (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁| +
      |carrierRotationInt (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂| -
      |carrierRotationInt hn hPL SL qL| = -1)
    (hRH : |carrierRotationInt hn hPH SH qH| = |carrierRotationInt hn hPL SL qL|)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).1.1 h₁ T₁ L₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon (contactHalfSizes_bounds hn h.1.1).2.1 h₂ T₂ L₂)) :
    cornerCoefficient hn hPH SH qH hSH = 0 ∧ cornerCoefficient hn hPL SL qL hSL = 0 := by
  obtain ⟨hkH, hkL⟩ := s7j_different_block_slots hn hPH hPL qH qL _ _ h₁ h₂ L₁ L₂ hmH hmL hR hRH
  exact s7j_different_block_read hF hn hPH hPL hSH hSL qH qL _ _ h₁ h₂ hT₁ hT₂ L₁ L₂ hfH hfL hkH hkL
    hu₁ hu₂

/-! #### E. The singleton entry (sm-4:777-783) — `hsing` enters -/

/-- The printed sentence "every old neighbour of `y` is also a neighbour of selected `x`, and hence is
dominated; thus `{y}` is an isolated block" in cb:singleton's vocabulary: if every unselected crossing
`c' ≠ y` interlacing `y` interlaces the SELECTED `x`, then `y` interlaces no other self-crossing of its carrier `q`
— a neighbour of a selected crossing has its two visits on different carriers (lem:carriers (iii),
`neighbor_visit_owners_ne`), whereas a self-crossing of `q` has both on `q`. -/
theorem s7j_isolated_of_neighbours_dominated (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {x y : Crossing P} (hx : x ∈ S)
    (hdom : ∀ c' : Crossing P, c' ∉ S → c' ≠ y → Interlaces hn hP y c' → Interlaces hn hP c' x) :
    ∀ c' ∈ carrierCrossings hn hP S q, c' ≠ y → ¬ Interlaces hn hP y c' := by
  intro c' hc' hne hint
  obtain ⟨hc'S, hc'q⟩ := (mem_carrierCrossings hn hP S q c').mp hc'
  have hN : c' ∈ supportNeighbors hn hP S :=
    (mem_supportNeighbors hn hP S c').mpr ⟨x, hx, hdom c' hc'S hne hint⟩
  obtain ⟨i, _, _⟩ := crossing_visits_exist c'
  exact neighbor_visit_owners_ne hn hP hS hN ⟨c', i⟩ rfl
    ((hc'q ⟨c', i⟩ rfl).trans (hc'q (visitTwin ⟨c', i⟩) rfl).symm)

/-- **cb:singleton at the support `T ∪ {x}` with the isolated block `{y}`** (sm-4:777-783): the owner `q`
of the newborn `y` is uniform, `y` is a self-crossing of `q`, and every unselected neighbour of `y` is a
neighbour of the selected `x`; then `c(q) = 0` ("Lemma cb:singleton makes the required coefficient zero,
including the zero-polynomial case"). -/
theorem s7j_singleton_entry (hsing : CbSingletonData) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (hu : CarrierUniform hn hP S q) {x y : Crossing P} (hx : x ∈ S)
    (hy : y ∈ carrierCrossings hn hP S q)
    (hdom : ∀ c' : Crossing P, c' ∉ S → c' ≠ y → Interlaces hn hP y c' → Interlaces hn hP c' x) :
    cornerCoefficient hn hP S q hS = 0 :=
  hsing.isolated_zero n hn P hP S hS q hu y hy (s7j_isolated_of_neighbours_dominated hn hP hS q hx hdom)

/-- **Every one-newborn term is zero** (sm-4:781-783), in the term shape of eq. C-selector-form: "if a
one-newborn selector is zero its term vanishes; otherwise its owner is uniform, and cb:singleton makes the
required coefficient zero". -/
theorem s7j_one_newborn_term_zero (hsing : CbSingletonData) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    {x y : Crossing P} (hx : x ∈ S) (hy : y ∈ carrierCrossings hn hP S q)
    (hdom : ∀ c' : Crossing P, c' ∉ S → c' ≠ y → Interlaces hn hP y c' → Interlaces hn hP c' x) :
    wind hn hP S * cornerProduct hn hP S hS = 0 := by
  by_cases hu : CarrierUniform hn hP S q
  · unfold cornerProduct
    rw [Finset.prod_eq_zero (Finset.mem_univ q) (s7j_singleton_entry hsing hn hP hS q hu hx hy hdom),
      mul_zero]
  · unfold wind
    rw [Finset.prod_eq_zero (Finset.mem_univ q) (carrierWeight_eq_zero_of_not_uniform hn hP S q hu),
      zero_mul]

/-- The one-newborn term at the support `insert x T` literally (sm-4:777: "`T ∪ {x}` is a support since
`x` is adjacent to neither `T` nor `y`"; the support property `hS` is F's output). -/
theorem s7j_one_newborn_term_zero_insert (hsing : CbSingletonData) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (x y : Crossing P)
    (hS : IsDecomposition hn hP (insert x T)) (q : Component hn hP (insert x T))
    (hy : y ∈ carrierCrossings hn hP (insert x T) q)
    (hdom : ∀ c' : Crossing P, c' ∉ insert x T → c' ≠ y → Interlaces hn hP y c' → Interlaces hn hP c' x) :
    wind hn hP (insert x T) * cornerProduct hn hP (insert x T) hS = 0 :=
  s7j_one_newborn_term_zero hsing hn hP hS q (Finset.mem_insert_self x T) hy hdom

end S7JFloor


/-! ### Unit K (wave 3, prefix `s7z_`; PLAN_FINAL §3.3 bigon (6), U110-K, sm-4:874-908): the ASSEMBLY of the
bigon leaf `s7_bigon_law_at`.  Everything geometric is a black box (rule (3)): the outputs of units F (the
eligible bijection eq. s7c:eligible-bijection, the ineligible cancellation, the two-newborn sector
eq. s7c:sector-split `B = (1−ε)J`), SITE + BLOCK + ROT + RET (the newborn-free returned row: the R-II site,
the skein/two-component rows eq. s7c:interlacing-coefficient-result / s7c:noninterlacing-return, the rotation
ledger, the selector laws) and J (the floor entries and cb:singleton at the one-newborn rows) are stated as
the three `s7z_`-Props `s7z_FSector`, `s7z_NewbornFreeRow`, `s7z_OneNewbornRows` (per side parameter, on an
explicit persistent bijection `e₀` and an explicit eligible bijection `e`), bundled in `s7z_RowSector`; their
existence below a radius is the single sorried theorem `s7z_exists_rowSector`.  PROVED here: the state-sum
bookkeeping — the newborn split of the high side's supports into the four classes `T, T∪{x}, T∪{y}, T∪{x,y}`
(`s7z_sum_insert_split`), the row algebra `Σ_H − Σ_L = s₀ Σ_rows` and `B + R_ret = J` (`s7z_law_of_rows`,
eq. s7c:bigon-total), the newborn side and its two newborn crossings from lem:wall-sides
(`s7z_side`, `s7z_pattern`, `s7z_x`, `s7z_y`), the sign `s₀ = χ(P₀)` from `vertex_contact_signs`
(`s7z_s₀_eq_chi`, eq. s7c:bigon-signs), the directed law at one side parameter (`s7z_law_at_of_rowSector`)
and the leaf modulo the sector (`s7z_bigon_law_at_of`). -/

section S7ZBigon

/-! #### A. Pure algebra: the newborn split and the row law (eq. s7c:bigon-total) -/

omit [NeZero n] in
/-- The supports of the high side, split by the two newborns `x ≠ y`: every support is uniquely
`T`, `T ∪ {x}`, `T ∪ {y}` or `T ∪ {x, y}` with `T` newborn-free (sm-4:409-418, the four sectors). -/
theorem s7z_sum_insert_split {κ : Type*} [Fintype κ] [DecidableEq κ] (F : Finset κ → ℤ) (x y : κ)
    (hxy : x ≠ y) :
    ∑ T, F T = ∑ T : {T : Finset κ // x ∉ T ∧ y ∉ T},
      (F T.1 + F (insert x T.1) + F (insert y T.1) + F (insert x (insert y T.1))) := by
  classical
  set s : Finset κ := (Finset.univ.erase x).erase y with hs
  have hy : y ∉ s := Finset.notMem_erase y _
  have hx : x ∉ insert y s := by
    rw [Finset.mem_insert, not_or]
    refine ⟨hxy, ?_⟩
    rw [hs, Finset.mem_erase, Finset.mem_erase]
    tauto
  have huniv : (Finset.univ : Finset κ) = insert x (insert y s) := by
    ext z
    simp only [Finset.mem_univ, Finset.mem_insert, hs, Finset.mem_erase, true_iff]
    by_cases hzx : z = x
    · exact Or.inl hzx
    by_cases hzy : z = y
    · exact Or.inr (Or.inl hzy)
    exact Or.inr (Or.inr ⟨hzy, hzx, trivial⟩)
  have h1 : (Finset.univ : Finset (Finset κ)) = (insert x (insert y s)).powerset := by
    rw [← huniv]
    ext T
    simp only [Finset.mem_univ, Finset.mem_powerset, Finset.subset_univ]
  have hmem : ∀ T : Finset κ, T ∈ s.powerset ↔ (x ∉ T ∧ y ∉ T) := by
    intro T
    rw [Finset.mem_powerset]
    constructor
    · intro hT
      refine ⟨fun hxT => ?_, fun hyT => ?_⟩
      · have := hT hxT
        rw [hs, Finset.mem_erase, Finset.mem_erase] at this
        exact this.2.1 rfl
      · have := hT hyT
        rw [hs, Finset.mem_erase] at this
        exact this.1 rfl
    · intro ⟨hxT, hyT⟩ z hz
      rw [hs, Finset.mem_erase, Finset.mem_erase]
      exact ⟨fun h => hyT (h ▸ hz), fun h => hxT (h ▸ hz), Finset.mem_univ _⟩
  rw [h1, Finset.sum_powerset_insert hx, Finset.sum_powerset_insert hy, Finset.sum_powerset_insert hy,
    ← Finset.sum_subtype s.powerset hmem
      (fun T => F T + F (insert x T) + F (insert y T) + F (insert x (insert y T))),
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

omit [NeZero n] in
/-- **The algebra of the bigon law** (eq. s7c:bigon-total `B + R_ret = J`, sm-4:874-908).  Two state
sums `Σ f` (the low side `P₀`, indexed by all its supports) and `Σ f'` (the high side `P₂`, indexed by
`Finset κ`) are compared through the newborn-free bijection `e₀` (persistent transport) and the ROWS
of the newborn-free supports `T`: `row T = (f' T − f (e₀⁻¹ T)) + f' (T∪{x}) + f' (T∪{y}) + f' (T∪{x,y})`.
Ineligible rows vanish (`hrow0`); the eligible rows are matched with `Ind(λ₁) × Ind(λ₂)` by `e` and
equal `s₀ · g₁ · g₂` termwise (`hrow`); the half terms vanish off the decompositions (`hz₁`, `hz₂`).
Then `Σ f' − Σ f = s₀ (Σ g₁)(Σ g₂)`. -/
theorem s7z_law_of_rows {α κ γ₁ γ₂ : Type*} [Fintype α] [Fintype κ] [DecidableEq κ] [Fintype γ₁]
    [Fintype γ₂] (f : α → ℤ) (f' : Finset κ → ℤ) (g₁ : γ₁ → ℤ) (g₂ : γ₂ → ℤ) (x y : κ) (hxy : x ≠ y)
    (E : Finset κ → Prop) (D₁ : γ₁ → Prop) (D₂ : γ₂ → Prop)
    (hz₁ : ∀ S, ¬ D₁ S → g₁ S = 0) (hz₂ : ∀ S, ¬ D₂ S → g₂ S = 0)
    (e₀ : α ≃ {T : Finset κ // x ∉ T ∧ y ∉ T})
    (e : {T : {T : Finset κ // x ∉ T ∧ y ∉ T} // E T.1} ≃
      {S₁ : γ₁ // D₁ S₁} × {S₂ : γ₂ // D₂ S₂}) (s : ℤ)
    (hrow : ∀ T : {T : {T : Finset κ // x ∉ T ∧ y ∉ T} // E T.1},
      f' T.1.1 - f (e₀.symm T.1) + f' (insert x T.1.1) + f' (insert y T.1.1) +
        f' (insert x (insert y T.1.1)) = s * (g₁ (e T).1.1 * g₂ (e T).2.1))
    (hrow0 : ∀ T : {T : Finset κ // x ∉ T ∧ y ∉ T}, ¬ E T.1 →
      f' T.1 - f (e₀.symm T) + f' (insert x T.1) + f' (insert y T.1) +
        f' (insert x (insert y T.1)) = 0) :
    ∑ T, f' T - ∑ S, f S = s * ((∑ S₁, g₁ S₁) * (∑ S₂, g₂ S₂)) := by
  classical
  set row : {T : Finset κ // x ∉ T ∧ y ∉ T} → ℤ := fun T =>
    f' T.1 - f (e₀.symm T) + f' (insert x T.1) + f' (insert y T.1) +
      f' (insert x (insert y T.1)) with hrowdef
  rw [s7z_sum_insert_split f' x y hxy]
  have hL : ∑ S, f S = ∑ T : {T : Finset κ // x ∉ T ∧ y ∉ T}, f (e₀.symm T) :=
    Fintype.sum_equiv e₀ _ _ (fun S => by rw [Equiv.symm_apply_apply])
  rw [hL, ← Finset.sum_sub_distrib]
  have hsum : ∑ T : {T : Finset κ // x ∉ T ∧ y ∉ T},
      ((f' T.1 + f' (insert x T.1) + f' (insert y T.1) + f' (insert x (insert y T.1))) -
        f (e₀.symm T)) = ∑ T, row T :=
    Finset.sum_congr rfl fun T _ => by simp only [hrowdef]; ring
  rw [hsum, ← s7e_sum_full_eq_of_zero row (fun T => E T.1) hrow0]
  have he : ∑ T : {T : {T : Finset κ // x ∉ T ∧ y ∉ T} // E T.1}, row T.1 =
      ∑ q : {S₁ : γ₁ // D₁ S₁} × {S₂ : γ₂ // D₂ S₂}, s * (g₁ q.1.1 * g₂ q.2.1) :=
    Fintype.sum_equiv e _ _ (fun T => hrow T)
  rw [he, ← Finset.mul_sum, Fintype.sum_prod_type, ← s7e_sum_full_eq_of_zero g₁ D₁ hz₁,
    ← s7e_sum_full_eq_of_zero g₂ D₂ hz₂, Finset.sum_mul_sum]

/-! #### B. The bigon wall: the newborn side, the two newborns, the sign `s₀` (sm-4:396-408) -/

variable {g : WallGerm n} {M a : ZMod n}

/-- The NEWBORN side `P₂` of the bigon wall (sm-4:397-399: "the other side, with two newborn
crossings `x, y`"): `true` if `P₊` carries the crossing `{a, M}` (at the base parameter; constant
along the side, `s7z_pattern`).  The side `!s7z_side` is `P₀`. -/
noncomputable def s7z_side (g : WallGerm n) (M a : ZMod n) : Bool :=
  decide (IsCrossing (g.sideTuple true g.sideBase).val {a, M})

/-- The bigon crossing pattern (lem:wall-sides (V), `vertex_sides`, `BigonCrossingPattern`) read with
`s7z_side`: the newborn side carries BOTH contact crossings `{a, M − 1}`, `{a, M}` and the other side
NEITHER, at every side parameter `t`. -/
theorem s7z_pattern (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    IsCrossing (g.curve (g.sideTime (s7z_side g M a) t)) {a, M - 1} ∧
    IsCrossing (g.curve (g.sideTime (s7z_side g M a) t)) {a, M} ∧
    ¬ IsCrossing (g.curve (g.sideTime (!s7z_side g M a) t)) {a, M - 1} ∧
    ¬ IsCrossing (g.curve (g.sideTime (!s7z_side g M a) t)) {a, M} := by
  have hpat : BigonCrossingPattern (g.curve (g.sideTime true t)) (g.curve (g.sideTime false t)) M a :=
    ((vertex_sides hn g h.1).2.2.2.1 t t).2.1 h.2
  have hbase : BigonCrossingPattern (g.curve (g.sideTime true g.sideBase))
      (g.curve (g.sideTime false t)) M a :=
    ((vertex_sides hn g h.1).2.2.2.1 g.sideBase t).2.1 h.2
  unfold s7z_side
  by_cases hM : IsCrossing (g.sideTuple true g.sideBase).val {a, M}
  · rw [decide_eq_true hM]
    simp only [Bool.not_true]
    rcases hpat with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact ⟨h1, h2, h3, h4⟩
    · exfalso
      rcases hbase with ⟨_, _, b3, _⟩ | ⟨_, b2, _, _⟩
      · exact b3 h3
      · exact b2 hM
  · rw [decide_eq_false hM]
    simp only [Bool.not_false]
    rcases hpat with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exfalso
      rcases hbase with ⟨_, b2, _, _⟩ | ⟨_, _, _, b4⟩
      · exact hM b2
      · exact h4 b4
    · exact ⟨h3, h4, h1, h2⟩

/-- The newborn `x = x_{M−1,a}` of the newborn side (sm-4:398). -/
noncomputable def s7z_x (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    Crossing (g.curve (g.sideTime (s7z_side g M a) t)) :=
  ⟨{a, M - 1}, (s7z_pattern hn h t).1⟩

/-- The newborn `y = x_{a,M}` of the newborn side (sm-4:398). -/
noncomputable def s7z_y (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    Crossing (g.curve (g.sideTime (s7z_side g M a) t)) :=
  ⟨{a, M}, (s7z_pattern hn h t).2.1⟩

theorem s7z_x_ne_y (hn : 3 ≤ n) (h : g.BigonAt M a) (t : g.SideParameter) :
    s7z_x hn h t ≠ s7z_y hn h t := by
  intro hxy
  exact contact_pairs_distinct hn h.1.1 (congrArg Subtype.val hxy)

/-- The sign `s₀ = sgn det(r, m − a)|_{P₀}` of eq. s7c:bigon-signs, expressed through the frozen
`contactSign` (`= χ(P₋)`, `vertex_contact_signs`): `s₀ = χ(P₀)`, and `P₀ = P₋` iff the newborn side is
`P₊`.  So `s = δ_dir s₀ = contactSign` is automatic (`s7z_s₀_eq_chi`). -/
def s7z_s₀ (g : WallGerm n) (M a : ZMod n) (b : Bool) : ℤ :=
  if b then (g.contactSign M a : ℤ) else -(g.contactSign M a : ℤ)

/-- eq. s7c:bigon-signs: `s7z_s₀ g M a (s7z_side g M a)` IS `χ(P₀) = sgn det(r, m − a)|_{P₀}` on the
newborn-free side `P₀ = !s7z_side`, at every side parameter. -/
theorem s7z_s₀_eq_chi (h : g.BigonAt M a) (t : g.SideParameter) (b : Bool) :
    s7z_s₀ g M a b = (chi (g.sideTuple (!b) t).val a (a + 1) M : ℤ) := by
  obtain ⟨-, hm, hp⟩ := g.vertex_contact_signs h.1 t t
  unfold s7z_s₀
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    rw [hp]; push_cast; ring
  · simp only [↓reduceIte, Bool.not_true]
    rw [hm]

/-- `ε = 1` when the newborn chords interlace, `0` otherwise (sm-4:409). -/
def s7z_eps (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (x y : Crossing P) : ℤ :=
  if Interlaces hn hP x y then 1 else 0

/-- An ELIGIBLE support (sm-4:419-421): a decomposition `T` of the newborn side missing the common
old neighbourhood `N` of `x, y` (no selected crossing interlaces both newborns). -/
def s7z_Eligible (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (x y : Crossing P)
    (T : Finset (Crossing P)) : Prop :=
  IsDecomposition hn hP T ∧ ∀ c ∈ T, ¬ (Interlaces hn hP x c ∧ Interlaces hn hP y c)

/-! #### C. The black boxes, as Props on an explicit newborn side `b`, newborns `x y`, persistent
bijection `e₀` and eligible bijection `e` (rule (3); instantiated at `s7z_side`, `s7z_x`, `s7z_y`) -/

/-- **Unit F's output** (PLAN §3.3 bigon (1), sm-4:396-455): (i) `e₀` is the persistent transport
(labels preserved; `s7a_cross` is `⟨x.val, _⟩`); (ii) `e` restricts an eligible support to the
two intervals (eq. s7c:eligible-bijection: the half crossing `c₁` of `λ₁` lies in `T₁` iff its
image label pair under `firstHalfIndex` lies in `T`; `λ₂` through `secondHalfEdgeIndex`); (iii) the
INELIGIBLE rows vanish: an ineligible or non-independent newborn-free `T` has equal terms on the two
sides and none of its newborn extensions is a support (sm-4:421-425); (iv) the TWO-NEWBORN row is
`(1−ε) s₀ · term(T₁) term(T₂)` (eq. s7c:sector-split with eq. s7c:triangle-data: at `ε = 0` the
contact triangle carries `wt · c = s₀`, the other carriers are those of `T₁, T₂`; at `ε = 1`
`T ∪ {x, y}` is not a support). -/
def s7z_FSector (hn : 3 ≤ n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter) (b : Bool)
    (x y : Crossing (g.curve (g.sideTime b t)))
    (e₀ : Finset (Crossing (g.curve (g.sideTime (!b) t))) ≃
      {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T})
    (e : {T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T} //
        s7z_Eligible hn (s7a_sideGeneric g b) x y T.1} ≃
      {S₁ : Finset (Crossing (firstHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}) : Prop :=
  (∀ (S : Finset (Crossing (g.curve (g.sideTime (!b) t)))) (c : Crossing (g.curve (g.sideTime (!b) t))),
      c ∈ S ↔ ∃ c' ∈ (e₀ S).1, c'.val = c.val) ∧
  (∀ (T : {T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T} //
        s7z_Eligible hn (s7a_sideGeneric g b) x y T.1}) (c₁ : Crossing (firstHalf g.center M a)),
      c₁ ∈ (e T).1.1 ↔ ∃ c ∈ T.1.1, c.val = c₁.val.image (firstHalfIndex M a)) ∧
  (∀ (T : {T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T} //
        s7z_Eligible hn (s7a_sideGeneric g b) x y T.1}) (c₂ : Crossing (secondHalf g.center M a)),
      c₂ ∈ (e T).2.1 ↔ ∃ c ∈ T.1.1, c.val = c₂.val.image (secondHalfEdgeIndex M a)) ∧
  (∀ T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T},
      ¬ s7z_Eligible hn (s7a_sideGeneric g b) x y T.1 →
      s7e_term hn (s7a_sideGeneric g b) T.1 = s7e_term hn (s7a_sideGeneric g (!b)) (e₀.symm T) ∧
      s7e_term hn (s7a_sideGeneric g b) (insert x T.1) = 0 ∧
      s7e_term hn (s7a_sideGeneric g b) (insert y T.1) = 0 ∧
      s7e_term hn (s7a_sideGeneric g b) (insert x (insert y T.1)) = 0) ∧
  (∀ T : {T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T} //
        s7z_Eligible hn (s7a_sideGeneric g b) x y T.1},
      s7e_term hn (s7a_sideGeneric g b) (insert x (insert y T.1.1)) =
        (1 - s7z_eps hn (s7a_sideGeneric g b) x y) * s7z_s₀ g M a b *
          (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ (e T).1.1 *
            s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ (e T).2.1))

/-- **The newborn-free returned row** (units SITE + BLOCK + ROT + RET, with the floor entries of J;
PLAN §3.3 bigon (2)-(5), sm-4:456-770, 785-825): for an eligible `T` the difference of the two
newborn-free terms is `ε s₀ · term(T₁) term(T₂)`: interlacing (`ε = 1`) `Ω_H − Ω_L = −ω₁ω₂`
(eq. s7c:interlacing-coefficient-result, `s7k_interlacing_row` + `s7k_interlacing_term`: the R-II
site `P(D_H^{sw}) = P(D_L)`, the skein, the two-component row, the rotation ledger, the floor at the
two uniform half contact carriers); noninterlacing (`ε = 0`) every returned row is zero
(eq. s7c:noninterlacing-return, `s7k_noninterlacing_row` / `s7k_different_block_row` +
`s7k_noninterlacing_term`: the floor at the two one-dissent half contact carriers). -/
def s7z_NewbornFreeRow (hn : 3 ≤ n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter) (b : Bool)
    (x y : Crossing (g.curve (g.sideTime b t)))
    (e₀ : Finset (Crossing (g.curve (g.sideTime (!b) t))) ≃
      {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T})
    (e : {T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T} //
        s7z_Eligible hn (s7a_sideGeneric g b) x y T.1} ≃
      {S₁ : Finset (Crossing (firstHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}) : Prop :=
  ∀ T : {T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T} //
      s7z_Eligible hn (s7a_sideGeneric g b) x y T.1},
    s7e_term hn (s7a_sideGeneric g b) T.1.1 - s7e_term hn (s7a_sideGeneric g (!b)) (e₀.symm T.1) =
      s7z_eps hn (s7a_sideGeneric g b) x y * s7z_s₀ g M a b *
        (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ (e T).1.1 *
          s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ (e T).2.1)

/-- **The one-newborn rows** (unit J with unit C; sm-4:693-723 and 777-788): for an eligible `T`
both one-newborn terms vanish — interlacing by their selectors (the daughter carrying the turn at
`m` also carries the opposite smoothing turn eq. s7c:one-newborn-turns, so it is mixed and its
weight is `0`, `carrierWeight_eq_zero_of_not_uniform`); noninterlacing by cb:singleton
(`hsing.isolated_zero` at `T ∪ {x}` with the isolated block `{y}`, `s7k_one_newborn_term_zero`). -/
def s7z_OneNewbornRows (hn : 3 ≤ n) (t : g.SideParameter) (b : Bool)
    (x y : Crossing (g.curve (g.sideTime b t))) : Prop :=
  ∀ T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T},
    s7z_Eligible hn (s7a_sideGeneric g b) x y T.1 →
    s7e_term hn (s7a_sideGeneric g b) (insert x T.1) = 0 ∧
    s7e_term hn (s7a_sideGeneric g b) (insert y T.1) = 0

/-- The ROW SECTOR at the side parameter `t`: the three black boxes on one persistent bijection
`e₀` and one eligible bijection `e` (the shape the algebra `s7z_law_of_rows` consumes). -/
def s7z_RowSector (hn : 3 ≤ n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter) (b : Bool)
    (x y : Crossing (g.curve (g.sideTime b t))) : Prop :=
  ∃ (e₀ : Finset (Crossing (g.curve (g.sideTime (!b) t))) ≃
      {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T})
    (e : {T : {T : Finset (Crossing (g.curve (g.sideTime b t))) // x ∉ T ∧ y ∉ T} //
        s7z_Eligible hn (s7a_sideGeneric g b) x y T.1} ≃
      {S₁ : Finset (Crossing (firstHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}),
    s7z_FSector hn h h₁ h₂ t b x y e₀ e ∧ s7z_NewbornFreeRow hn h h₁ h₂ t b x y e₀ e ∧
      s7z_OneNewbornRows hn t b x y

/-! #### D. The composition `B + R_ret = J` and the directed law (sm-4:874-908) -/

/-- The undirected law at one side parameter from its row sector: `Σ_{P₂} − Σ_{P₀} = s₀ C(λ₁) C(λ₂)`
(eq. s7c:bigon-total with `B = (1−ε)J`, `R_ret = εJ`, the one-newborn rows zero). -/
theorem s7z_undirected_of_rowSector (hn : 3 ≤ n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (t : g.SideParameter) (b : Bool) (x y : Crossing (g.curve (g.sideTime b t))) (hxy : x ≠ y)
    (hsec : s7z_RowSector hn h h₁ h₂ t b x y) :
    cornerStateSum hn (g.sideTuple b t).property -
        cornerStateSum hn (g.sideTuple (!b) t).property =
      s7z_s₀ g M a b *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  obtain ⟨e₀, e, ⟨-, -, -, hinel, htwo⟩, hret, hone⟩ := hsec
  rw [s7e_cornerStateSum_eq_sum_term, s7e_cornerStateSum_eq_sum_term,
    s7e_cornerStateSum_eq_sum_term, s7e_cornerStateSum_eq_sum_term]
  refine s7z_law_of_rows (s7e_term hn (s7a_sideGeneric g (!b))) (s7e_term hn (s7a_sideGeneric g b))
    (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
    (s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂) x y hxy
    (s7z_Eligible hn (s7a_sideGeneric g b) x y)
    (IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁)
    (IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂)
    (fun S hS => s7e_term_of_not _ _ hS) (fun S hS => s7e_term_of_not _ _ hS) e₀ e
    (s7z_s₀ g M a b) (fun T => ?_) (fun T hT => ?_)
  · -- the eligible row: `(f_H − f_L) + 0 + 0 + (1−ε) s₀ G = ε s₀ G + (1−ε) s₀ G = s₀ G`
    have h1 := hret T
    have h2 := hone T.1 T.2
    have h3 := htwo T
    rw [h2.1, h2.2, h3, h1]
    ring
  · -- the ineligible row: the newborn-free terms cancel, the extensions vanish
    obtain ⟨h0, h1, h2, h3⟩ := hinel T hT
    rw [h0, h1, h2, h3]; ring

/-- The DIRECTED law at one side parameter (eq. s7c:bigon-signs `s = δ_dir s₀`, here automatic from
`s7z_s₀`): `C(P₊) − C(P₋) = contactSign · C(λ₁) C(λ₂)` from the row sector at the newborn side. -/
theorem s7z_law_at_of_rowSector (hn : 3 ≤ n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (t : g.SideParameter)
    (hsec : s7z_RowSector hn h h₁ h₂ t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t)) :
    cornerStateSum hn (g.sideTuple true t).property -
        cornerStateSum hn (g.sideTuple false t).property =
      (g.contactSign M a : ℤ) *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  have key := s7z_undirected_of_rowSector hn h h₁ h₂ t _ _ _ (s7z_x_ne_y hn h t) hsec
  cases hb : s7z_side g M a
  · rw [hb] at key
    simp only [Bool.not_false, s7z_s₀, Bool.false_eq_true, ↓reduceIte] at key
    linear_combination -key
  · rw [hb] at key
    simp only [Bool.not_true, s7z_s₀, ↓reduceIte] at key
    linear_combination key

/-- **The leaf modulo the row sector**: `s7_bigon_law_at`'s statement from the row sector available
below a radius (the bigon analogue of `s7e_sliding_law_at_of_contact`). -/
theorem s7z_bigon_law_at_of (hn : 3 ≤ n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (hsec : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      s7z_RowSector hn h h₁ h₂ t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  obtain ⟨δ, hδ, hs⟩ := hsec
  exact ⟨δ, hδ, fun t ht => s7z_law_at_of_rowSector hn h h₁ h₂ t (hs t ht)⟩

/-! #### E. The black boxes (rule (3)): the three per-unit existence statements, `sorry` -/

/-- **BLACK BOX — unit F** (PLAN §3.3 bigon (1); U110-F, est. 1,500-2,200 lines per W3_BLOCK_REPORT §2.1):
below a radius the persistent bijection `e₀` and the eligible bijection `e` exist with the four
properties of `s7z_FSector`. -/
theorem s7z_F_exists (hn : 3 ≤ n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      ∃ (e₀ : Finset (Crossing (g.curve (g.sideTime (!s7z_side g M a) t))) ≃
          {T : Finset (Crossing (g.curve (g.sideTime (s7z_side g M a) t))) //
            s7z_x hn h t ∉ T ∧ s7z_y hn h t ∉ T})
        (e : {T : {T : Finset (Crossing (g.curve (g.sideTime (s7z_side g M a) t))) //
              s7z_x hn h t ∉ T ∧ s7z_y hn h t ∉ T} //
            s7z_Eligible hn (s7a_sideGeneric g (s7z_side g M a)) (s7z_x hn h t) (s7z_y hn h t) T.1} ≃
          {S₁ : Finset (Crossing (firstHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
            {S₂ : Finset (Crossing (secondHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}),
        s7z_FSector hn h h₁ h₂ t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t) e₀ e := by
  sorry

/-- **BLACK BOX — units SITE + BLOCK + ROT + RET with the floor entries of J** (PLAN §3.3 bigon
(2)-(5)): below a radius, on the persistent and eligible bijections of `s7z_FSector` (which
determine them: labels), every eligible newborn-free row equals `ε s₀ · term(T₁) term(T₂)`.  The
floor `hF` enters at the two half contact carriers (uniform for `ε = 1`, one-dissent for `ε = 0`). -/
theorem s7z_returned_of_FSector (hF : FloorTheoremData) (hn : 3 ≤ n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      ∀ (e₀ : Finset (Crossing (g.curve (g.sideTime (!s7z_side g M a) t))) ≃
          {T : Finset (Crossing (g.curve (g.sideTime (s7z_side g M a) t))) //
            s7z_x hn h t ∉ T ∧ s7z_y hn h t ∉ T})
        (e : {T : {T : Finset (Crossing (g.curve (g.sideTime (s7z_side g M a) t))) //
              s7z_x hn h t ∉ T ∧ s7z_y hn h t ∉ T} //
            s7z_Eligible hn (s7a_sideGeneric g (s7z_side g M a)) (s7z_x hn h t) (s7z_y hn h t) T.1} ≃
          {S₁ : Finset (Crossing (firstHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
            {S₂ : Finset (Crossing (secondHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}),
        s7z_FSector hn h h₁ h₂ t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t) e₀ e →
        s7z_NewbornFreeRow hn h h₁ h₂ t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t) e₀ e := by
  sorry

/-- **BLACK BOX — unit J (cb:singleton) with unit C (the one-newborn selectors)** (sm-4:693-723,
777-788): below a radius both one-newborn terms of every eligible support vanish. -/
theorem s7z_oneNewborn_exists (hsing : CbSingletonData) (hn : 3 ≤ n) (h : g.BigonAt M a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      s7z_OneNewbornRows hn t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t) := by
  sorry

/-- The row sector below a radius, from the three black boxes (the radii intersected). -/
theorem s7z_exists_rowSector (hF : FloorTheoremData) (hsing : CbSingletonData) (hn : 3 ≤ n)
    (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      s7z_RowSector hn h h₁ h₂ t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t) := by
  obtain ⟨δ₁, hδ₁, hFs⟩ := s7z_F_exists hn h h₁ h₂
  obtain ⟨δ₂, hδ₂, hR⟩ := s7z_returned_of_FSector hF hn h h₁ h₂
  obtain ⟨δ₃, hδ₃, hO⟩ := s7z_oneNewborn_exists hsing hn h
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), fun t ht => ?_⟩
  have ht₁ : t.val < δ₁ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht₂ : t.val < δ₂ := lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_left _ _))
  have ht₃ : t.val < δ₃ := lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨e₀, e, hFe⟩ := hFs t ht₁
  exact ⟨e₀, e, hFe, hR t ht₂ e₀ e hFe, hO t ht₃⟩

/-! #### F. The F-ALIGNED assembly (W3_F_REPORT §0/§3): K's obligation on unit F's actual output shape.
Unit F delivers (`s7f_exists_law_residual`, at every `t` below a radius, on the supports `T₀` of the
newborn-free side `P₀` with the persistent lift `lift : Finset (Crossing P₀) → Finset (Crossing P₂)`
and the eligible supports `Elig`):
`C(P₊) − C(P₋) = (if ε then 0 else 1) · J + δ_dir · (Σ_{T₀ ∈ Elig} (term₂(lift T₀) − term₀ T₀)
+ Σ_{T₀ ∈ Elig} (term₂(T₀ ∪ {x}) + term₂(T₀ ∪ {y})))`.  The two theorems below take that identity as a
hypothesis with F's data abstracted (`α`, `lift`, `term₀`, `Elig`, `ε : Prop`, `d = δ_dir` with `d² = 1`
and `s₀ = d · s`, `e` the eligible bijection — `s7b_eligibleDecompositionEquiv` on `P₀`), and reduce the
leaf's law at `t` to exactly K's residual obligation "the second summand is `ε J`": the newborn-free
returned row `hrow` (SITE + BLOCK + ROT + RET + J's floor entries) and the one-newborn rows `hone`
(J's cb:singleton entry with C's selectors), both per eligible `T₀`. -/

omit [NeZero n] in
/-- The eligible rows over a finset `Elig`, matched with `Ind(λ₁) × Ind(λ₂)` by `e`, sum to
`c (Σ g₁)(Σ g₂)` (the half terms vanish off the decompositions). -/
theorem s7z_residual_sum {α γ₁ γ₂ : Type*} [Fintype γ₁] [Fintype γ₂]
    (r : α → ℤ) (g₁ : γ₁ → ℤ) (g₂ : γ₂ → ℤ) (D₁ : γ₁ → Prop) (D₂ : γ₂ → Prop)
    (hz₁ : ∀ S, ¬ D₁ S → g₁ S = 0) (hz₂ : ∀ S, ¬ D₂ S → g₂ S = 0)
    (Elig : Finset α) (e : {T₀ : α // T₀ ∈ Elig} ≃ {S₁ : γ₁ // D₁ S₁} × {S₂ : γ₂ // D₂ S₂}) (c : ℤ)
    (hrow : ∀ T₀ : {T₀ : α // T₀ ∈ Elig}, r T₀.1 = c * (g₁ (e T₀).1.1 * g₂ (e T₀).2.1)) :
    ∑ T₀ ∈ Elig, r T₀ = c * ((∑ S₁, g₁ S₁) * (∑ S₂, g₂ S₂)) := by
  classical
  rw [← Finset.sum_coe_sort Elig r]
  have he : ∑ T₀ : {T₀ : α // T₀ ∈ Elig}, r T₀.1 =
      ∑ q : {S₁ : γ₁ // D₁ S₁} × {S₂ : γ₂ // D₂ S₂}, c * (g₁ q.1.1 * g₂ q.2.1) :=
    Fintype.sum_equiv e _ _ hrow
  rw [he, ← Finset.mul_sum, Fintype.sum_prod_type, ← s7e_sum_full_eq_of_zero g₁ D₁ hz₁,
    ← s7e_sum_full_eq_of_zero g₂ D₂ hz₂, Finset.sum_mul_sum]

/-- `δ_dir` of eq. s7c:bigon-signs: `+1` iff `P₋ = P₀`, i.e. iff the newborn side is `P₊`. -/
def s7z_dirSign (g : WallGerm n) (M a : ZMod n) : ℤ := if s7z_side g M a then 1 else -1

omit [NeZero n] in
theorem s7z_dirSign_sq (g : WallGerm n) (M a : ZMod n) : s7z_dirSign g M a * s7z_dirSign g M a = 1 := by
  unfold s7z_dirSign; split_ifs <;> norm_num

omit [NeZero n] in
/-- `s₀ = δ_dir · s` (eq. s7c:bigon-signs), at the newborn side. -/
theorem s7z_s₀_eq_dirSign_mul (g : WallGerm n) (M a : ZMod n) :
    s7z_s₀ g M a (s7z_side g M a) = s7z_dirSign g M a * (g.contactSign M a : ℤ) := by
  unfold s7z_s₀ s7z_dirSign; split_ifs <;> ring

/-- **The directed law at `t` from unit F's residual identity** (its shape as a hypothesis `hres`) and K's
two residual obligations `hrow` (returned newborn-free rows `= ε s₀ · term(T₁) term(T₂)`) and `hone`
(one-newborn rows `= 0`): eq. s7c:bigon-total `B + R_ret = (1−ε)J + εJ = J`. -/
theorem s7z_law_at_of_residual (hn : 3 ≤ n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (t : g.SideParameter) (b : Bool) (x y : Crossing (g.curve (g.sideTime b t)))
    (d : ℤ) (hd : d * d = 1) (hs₀ : s7z_s₀ g M a b = d * (g.contactSign M a : ℤ)) (ε : Prop)
    {α : Type*} (lift : α → Finset (Crossing (g.curve (g.sideTime b t)))) (term₀ : α → ℤ)
    (Elig : Finset α)
    (e : {T₀ : α // T₀ ∈ Elig} ≃
      {S₁ : Finset (Crossing (firstHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂})
    (hres : cornerStateSum hn (g.sideTuple true t).property -
        cornerStateSum hn (g.sideTuple false t).property =
      (if ε then 0 else 1) *
          ((g.contactSign M a : ℤ) *
            (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
              cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) +
        d * (∑ T₀ ∈ Elig, (s7e_term hn (s7a_sideGeneric g b) (lift T₀) - term₀ T₀) +
          ∑ T₀ ∈ Elig, (s7e_term hn (s7a_sideGeneric g b) (insert x (lift T₀)) +
            s7e_term hn (s7a_sideGeneric g b) (insert y (lift T₀)))))
    (hrow : ∀ T₀ : {T₀ : α // T₀ ∈ Elig},
      s7e_term hn (s7a_sideGeneric g b) (lift T₀.1) - term₀ T₀.1 =
        (if ε then 1 else 0) * s7z_s₀ g M a b *
          (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ (e T₀).1.1 *
            s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ (e T₀).2.1))
    (hone : ∀ T₀ ∈ Elig, s7e_term hn (s7a_sideGeneric g b) (insert x (lift T₀)) = 0 ∧
      s7e_term hn (s7a_sideGeneric g b) (insert y (lift T₀)) = 0) :
    cornerStateSum hn (g.sideTuple true t).property -
        cornerStateSum hn (g.sideTuple false t).property =
      (g.contactSign M a : ℤ) *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  have hone' : ∑ T₀ ∈ Elig, (s7e_term hn (s7a_sideGeneric g b) (insert x (lift T₀)) +
      s7e_term hn (s7a_sideGeneric g b) (insert y (lift T₀))) = 0 :=
    Finset.sum_eq_zero fun T₀ hT => by rw [(hone T₀ hT).1, (hone T₀ hT).2, add_zero]
  have hret : ∑ T₀ ∈ Elig, (s7e_term hn (s7a_sideGeneric g b) (lift T₀) - term₀ T₀) =
      (if ε then 1 else 0) * s7z_s₀ g M a b *
        (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
          cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
    rw [s7e_cornerStateSum_eq_sum_term, s7e_cornerStateSum_eq_sum_term]
    exact s7z_residual_sum _ _ _ _ _ (fun S hS => s7e_term_of_not _ _ hS)
      (fun S hS => s7e_term_of_not _ _ hS) Elig e _ hrow
  rw [hres, hret, hone', hs₀]
  by_cases hε : ε
  · simp only [hε, ↓reduceIte]
    linear_combination ((g.contactSign M a : ℤ) *
      (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
        cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) * hd
  · simp only [hε, ↓reduceIte]
    ring

/-- The per-`t` RESIDUAL DATA in unit F's vocabulary: a newborn side `b` with newborns `x y`, `δ_dir = d`,
`ε`, F's residual identity on some low-side index type `α` with lift, low terms and eligible finset, the
eligible bijection `e`, and K's two residual obligations.  (The assembler instantiates `b := s7f_side`,
`x y := s7f_x, s7f_y`, `d := s7f_dirSign`, `ε := s7f_Interlacing`, `α := Finset (Crossing P₀)`,
`lift := s7f_lift`, `term₀ := s7e_term hn hP₀`, `Elig := filter (s7f_Eligible)`, `e` from
`s7b_eligibleDecompositionEquiv` on `P₀`, `hres := s7f_law_residual`.) -/
def s7z_ResidualData (hn : 3 ≤ n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (t : g.SideParameter) : Prop :=
  ∃ (b : Bool) (x y : Crossing (g.curve (g.sideTime b t))) (d : ℤ) (ε : Prop) (α : Type)
    (lift : α → Finset (Crossing (g.curve (g.sideTime b t)))) (term₀ : α → ℤ) (Elig : Finset α)
    (e : {T₀ : α // T₀ ∈ Elig} ≃
      {S₁ : Finset (Crossing (firstHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
        {S₂ : Finset (Crossing (secondHalf g.center M a)) //
          IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}),
    d * d = 1 ∧ s7z_s₀ g M a b = d * (g.contactSign M a : ℤ) ∧
    (cornerStateSum hn (g.sideTuple true t).property -
        cornerStateSum hn (g.sideTuple false t).property =
      (if ε then 0 else 1) *
          ((g.contactSign M a : ℤ) *
            (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
              cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂)) +
        d * (∑ T₀ ∈ Elig, (s7e_term hn (s7a_sideGeneric g b) (lift T₀) - term₀ T₀) +
          ∑ T₀ ∈ Elig, (s7e_term hn (s7a_sideGeneric g b) (insert x (lift T₀)) +
            s7e_term hn (s7a_sideGeneric g b) (insert y (lift T₀))))) ∧
    (∀ T₀ : {T₀ : α // T₀ ∈ Elig},
      s7e_term hn (s7a_sideGeneric g b) (lift T₀.1) - term₀ T₀.1 =
        (if ε then 1 else 0) * s7z_s₀ g M a b *
          (s7e_term (contactHalfSizes_bounds hn h.1.1).1.1 h₁ (e T₀).1.1 *
            s7e_term (contactHalfSizes_bounds hn h.1.1).2.1 h₂ (e T₀).2.1)) ∧
    (∀ T₀ ∈ Elig, s7e_term hn (s7a_sideGeneric g b) (insert x (lift T₀)) = 0 ∧
      s7e_term hn (s7a_sideGeneric g b) (insert y (lift T₀)) = 0)

/-- **The leaf modulo the residual data** (F-aligned form of `s7z_bigon_law_at_of`). -/
theorem s7z_bigon_law_at_of_residual (hn : 3 ≤ n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a))
    (hres : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ → s7z_ResidualData hn h h₁ h₂ t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  obtain ⟨δ, hδ, hs⟩ := hres
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨b, x, y, d, ε, α, lift, term₀, Elig, e, hd, hs₀, hid, hrow, hone⟩ := hs t ht
  exact s7z_law_at_of_residual hn h h₁ h₂ t b x y d hd hs₀ ε lift term₀ Elig e hid hrow hone

end S7ZBigon


section W3Bigon

/-! ### Wave-3 assembly glue (bigon leaf, prefix `w3_`).  Unit K reduced the leaf to three existence statements
(`s7z_F_exists`, `s7z_returned_of_FSector`, `s7z_oneNewborn_exists`, §E of its block) whose CONCLUSIONS do not
mention `hF`/`hsing`; the three Props below are those conclusions VERBATIM (shape-checked by `w3_Bigon*_of_box`),
and `w3_s7_bigon_law_at_of` is the frozen leaf statement from them (proof = K's `s7z_exists_rowSector` +
`s7z_bigon_law_at_of`).  Units F, SITE, BLOCK, J prove their row/polynomial content on explicit hypotheses
(`s7f_law_residual`, `s7s_siteData_of_wall`, `s7k_*_row`, `s7j_*_entry`); the per-support instantiation on the
actual carriers that would discharge B1-B3 is the open geometry (W3_K_REPORT §2, W3_BLOCK_REPORT §2, W3_F_REPORT).
The F-aligned alternative route `s7z_bigon_law_at_of_residual` consumes F's proved `s7f_law_residual` and needs
`hrow`/`hone` per eligible `T₀` plus the eligible bijection restricted to F's filter (W3_K_REPORT §4(a)); its
bridge (200-400 lines) is not built here. -/

variable {g : WallGerm n} {M a : ZMod n}

/-- **Remaining Prop B1** = the conclusion of `s7z_F_exists` (unit F's output in K's §C shape: persistent bijection `e₀`,
eligible bijection `e`, ineligible cancellation, two-newborn row `(1 − ε) s₀ · term(T₁) term(T₂)`). -/
def w3_BigonFSector (hn : 3 ≤ n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      ∃ (e₀ : Finset (Crossing (g.curve (g.sideTime (!s7z_side g M a) t))) ≃
          {T : Finset (Crossing (g.curve (g.sideTime (s7z_side g M a) t))) //
            s7z_x hn h t ∉ T ∧ s7z_y hn h t ∉ T})
        (e : {T : {T : Finset (Crossing (g.curve (g.sideTime (s7z_side g M a) t))) //
              s7z_x hn h t ∉ T ∧ s7z_y hn h t ∉ T} //
            s7z_Eligible hn (s7a_sideGeneric g (s7z_side g M a)) (s7z_x hn h t) (s7z_y hn h t) T.1} ≃
          {S₁ : Finset (Crossing (firstHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
            {S₂ : Finset (Crossing (secondHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}),
        s7z_FSector hn h h₁ h₂ t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t) e₀ e

/-- **Remaining Prop B2** = the conclusion of `s7z_returned_of_FSector` (SITE + BLOCK + ROT + RET + J's floor entries:
every eligible newborn-free row equals `ε s₀ · term(T₁) term(T₂)`); the floor `hF` is its hypothesis. -/
def w3_BigonReturnedRows (hn : 3 ≤ n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      ∀ (e₀ : Finset (Crossing (g.curve (g.sideTime (!s7z_side g M a) t))) ≃
          {T : Finset (Crossing (g.curve (g.sideTime (s7z_side g M a) t))) //
            s7z_x hn h t ∉ T ∧ s7z_y hn h t ∉ T})
        (e : {T : {T : Finset (Crossing (g.curve (g.sideTime (s7z_side g M a) t))) //
              s7z_x hn h t ∉ T ∧ s7z_y hn h t ∉ T} //
            s7z_Eligible hn (s7a_sideGeneric g (s7z_side g M a)) (s7z_x hn h t) (s7z_y hn h t) T.1} ≃
          {S₁ : Finset (Crossing (firstHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).1.1 h₁ S₁} ×
            {S₂ : Finset (Crossing (secondHalf g.center M a)) //
              IsDecomposition (contactHalfSizes_bounds hn h.1.1).2.1 h₂ S₂}),
        s7z_FSector hn h h₁ h₂ t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t) e₀ e →
        s7z_NewbornFreeRow hn h h₁ h₂ t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t) e₀ e

/-- **Remaining Prop B3** = the conclusion of `s7z_oneNewborn_exists` (J's cb:singleton entry with C's one-newborn
selectors); `hsing` is its hypothesis. -/
def w3_BigonOneNewborn (hn : 3 ≤ n) (h : g.BigonAt M a) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      s7z_OneNewbornRows hn t (s7z_side g M a) (s7z_x hn h t) (s7z_y hn h t)

/-- Shape checks: K's sorried boxes ARE Props B1-B3 (they carry `sorryAx`; not on the path of `w3_s7_bigon_law_at_of`). -/
theorem w3_BigonFSector_of_box (hn : 3 ≤ n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) : w3_BigonFSector hn h h₁ h₂ := s7z_F_exists hn h h₁ h₂

theorem w3_BigonReturnedRows_of_box (hF : FloorTheoremData) (hn : 3 ≤ n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    w3_BigonReturnedRows hn h h₁ h₂ := s7z_returned_of_FSector hF hn h h₁ h₂

theorem w3_BigonOneNewborn_of_box (hsing : CbSingletonData) (hn : 3 ≤ n) (h : g.BigonAt M a) :
    w3_BigonOneNewborn hn h := s7z_oneNewborn_exists hsing hn h

/-- **`w3_s7_bigon_law_at_of`: the frozen leaf statement of `s7_bigon_law_at` from the three remaining Props**
(proof = K's `s7z_exists_rowSector` on the hypotheses, then `s7z_bigon_law_at_of`). -/
theorem w3_s7_bigon_law_at_of (hn : 3 ≤ n) (h : g.BigonAt M a) (h₁ : Generic (firstHalf g.center M a))
    (h₂ : Generic (secondHalf g.center M a)) (hFs : w3_BigonFSector hn h h₁ h₂)
    (hR : w3_BigonReturnedRows hn h h₁ h₂) (hO : w3_BigonOneNewborn hn h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  refine s7z_bigon_law_at_of hn h h₁ h₂ ?_
  obtain ⟨δ₁, hδ₁, hFs⟩ := hFs
  obtain ⟨δ₂, hδ₂, hR⟩ := hR
  obtain ⟨δ₃, hδ₃, hO⟩ := hO
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), fun t ht => ?_⟩
  have ht₁ : t.val < δ₁ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht₂ : t.val < δ₂ := lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_left _ _))
  have ht₃ : t.val < δ₃ := lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨e₀, e, hFe⟩ := hFs t ht₁
  exact ⟨e₀, e, hFe, hR t ht₂ e₀ e hFe, hO t ht₃⟩

end W3Bigon

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
