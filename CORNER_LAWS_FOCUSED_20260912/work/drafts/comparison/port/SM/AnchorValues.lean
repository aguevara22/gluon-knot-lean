-- Ported <HH:MM>Z 2026-09-15 from work/drafts/comparison/Comparison_Assembled.lean lines 188-439 (comparison lane §2, row 122 prop:anchor-values as library material: `AnchorValuesHypotheses`, `UniquenessHypotheses.toAnchorValuesHypotheses`, `AnchorValuesData`, the `av_*` helpers, `cornerPolygon_soft_of`, `cornerPolygon_anchorValuesHypotheses_of`, `anchor_values_of (hs : CSoftData)` and the companions `AnchorValuesData.C_zero/.C_loop/.C_loopZero`) by the pod executor; body verbatim except this header, the import block (SM.CornerPolygon for §1, SM.Uniqueness, and SM.CornerChainStatements whose accepted `CSoftData` replaces the draft's DELETED §0 copy, lines 71-77 — byte-identical declaration block, tools/port_copy_diff.py) and the module docstring (new).  The wrappers `namespace SM` / `open WallGerm SoftDuplication Carrier` / `end SM` (lines 47, 49, 1052) are repeated verbatim.
import SM.CornerPolygon
import SM.Uniqueness
import SM.CornerChainStatements

/-! # Row 122 prop:anchor-values (sm-5:461-476; proof 477-505) — the statement and the abstract argument

Source: work/drafts/comparison/Comparison_Assembled.lean §2 (PLAN_FINAL.md §4 unit U-CM-AV; FR-CM-1..5).  `AnchorValuesData`
is prop:anchor-values as printed, one field per clause; `anchor_values_of (hs : CSoftData) : AnchorValuesData` proves it
modulo thm:C-soft (D-F11/D-F14 pattern: every clause but `C_hypotheses.soft` is unconditional).  The row theorem
`SM.prop_anchor_values : AnchorValuesData := anchor_values_of thm_C_soft` is declared in SM/AnchorValuesRow.lean from the
accepted `SM.thm_C_soft` (SM/CSoft.lean).  `CSoftData` is the corner lane's accepted bundle (SM/CornerChainStatements.lean §5). -/

namespace SM

open WallGerm SoftDuplication Carrier

/-! ## §2 Row 122 prop:anchor-values (sm-5:461-476) — proposed name `SM.prop_anchor_values` -/

/-- The two hypotheses of prop:anchor-values on a function `F` on generic polygons of all arities:
"constant on chambers" (thm:uniqueness (a), first half) and "satisfying the soft theorem in the form of
thm:C-soft at every admissible soft insertion into a generic polygon" (thm:uniqueness (e)) — the fields
`chamber` and `soft` of the accepted `UniquenessHypotheses` (SM/Uniqueness.lean:37-38, 72-76), copied
verbatim (`UniquenessHypotheses.toAnchorValuesHypotheses` is definitional).  FR-CM-1, FR-CM-2. -/
structure AnchorValuesHypotheses (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) : Prop where
  /-- constant on chambers -/
  chamber : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericPolygon n),
    Q ∈ chamber P → F n Q = F n P
  /-- the soft theorem `F(P_ε) = ((χ_- + χ_+)/2) F(P)` for all small `ε` at every admissible soft insertion -/
  soft : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (j : ZMod n) (q : Plane), SoftAdmissible P j q →
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ hQ : Generic (softInsertion P j q ε),
      (F (n + 1) (polygonProjection ⟨softInsertion P j q ε, hQ⟩) : ℚ) =
        softAmplitudeMultiplier P j q * (F n (polygonProjection ⟨P, hP⟩) : ℚ)

/-- thm:uniqueness's hypotheses contain prop:anchor-values' (the consumer thm:uniqueness cites exactly
(a) and (e); sanity). -/
theorem UniquenessHypotheses.toAnchorValuesHypotheses {F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ}
    (hF : UniquenessHypotheses F) : AnchorValuesHypotheses F :=
  ⟨hF.chamber, hF.soft⟩

/-- **prop:anchor-values as printed** (sm-5:461-476), one field per printed clause (FR-CM-1..7).
`F` is a function on generic polygons of all arities (`GenericPolygon n`, as in thm:uniqueness).  Anchors
are the accepted structures of def:anchors (`ZeroAnchor`, `LoopAnchor`, `LoopAnchorZero`, SM/Anchors.lean):
`Z = Y = A.polygon = softInsertion A.parent A.vertex A.vector A.param` at the anchor's OWN parameter
`A.param < A.bound = ε₀`; the parent `P = A.parent`, the insertion vertex `j = A.vertex`,
`τ_j(P) = turn A.parent A.vertex`; the soft edge `A.softEdge` (= `E_j`); a nonsoft anchor root
`a ≠ A.softEdge` corresponds to the unique parent root `g` with `a = softParentEdge A.vertex g`
(thm:A-soft's correspondence); `A_g = treeCoefficient` (def:treesum). -/
structure AnchorValuesData : Prop where
  /-- "F(Z) = 0 for every zero anchor" (case (Z), mixed sector) -/
  zero : ∀ (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) (_hF : AnchorValuesHypotheses F)
    (m : ℕ) [NeZero m] (r : ℤ) (A : ZeroAnchor m r),
    F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) = 0
  /-- "F(Y) = τ_j(P) F(P) for every loop anchor" — case (L) -/
  loop : ∀ (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) (_hF : AnchorValuesHypotheses F)
    (m : ℕ) [NeZero m] (r : ℤ) (A : LoopAnchor m r),
    F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) =
      ((turn A.parent A.vertex : SignType) : ℤ) * F m (polygonProjection ⟨A.parent, A.parent_generic⟩)
  /-- "F(Y) = τ_j(P) F(P) for every loop anchor" — case (L₀) -/
  loopZero : ∀ (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) (_hF : AnchorValuesHypotheses F)
    (m : ℕ) [NeZero m] (A : LoopAnchorZero m),
    F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) =
      ((turn A.parent A.vertex : SignType) : ℤ) * F m (polygonProjection ⟨A.parent, A.parent_generic⟩)
  /-- "In case (L), τ_j(P) = −sgn(r)" -/
  loop_turn : ∀ (m : ℕ) [NeZero m] (r : ℤ) (A : LoopAnchor m r),
    turn A.parent A.vertex = -SignType.sign r
  /-- "in case (L₀), it is the orientation sign of the parent triangle": `τ_j(P)` is nonzero, it is the
  common sign of the three turns of the generic parent triangle (lem:chi-basic (i) / lem:A-small-values (i)),
  and it is the rotation number of the triangle (lem:rot) — both readings of "orientation sign" (FR-CM-3). -/
  loopZero_turn : ∀ (m : ℕ) [NeZero m] (A : LoopAnchorZero m),
    turn A.parent A.vertex ≠ 0 ∧ (∀ i, turn A.parent i = turn A.parent A.vertex) ∧
      rotationNumber A.parent = ((turn A.parent A.vertex : SignType) : ℤ)
  /-- "The function C satisfies these hypotheses" (prop:C-chamber, thm:C-soft), `C` read on the polygon
  space as `cornerPolygon` (FR-CM-5). -/
  C_hypotheses : AnchorValuesHypotheses cornerPolygon
  /-- "The same identities hold for A_g at every anchor root other than the soft edge, with the
  corresponding parent root used on the right-hand side" — zero anchors (FR-CM-4) -/
  A_zero : ∀ (m : ℕ) [NeZero m] (r : ℤ) (A : ZeroAnchor m r) (a : ZMod (m + 1)), a ≠ A.softEdge →
    treeCoefficient A.polygon A.polygon_generic.1 a (by have := A.parent_card; omega) = 0
  /-- — loop anchors, case (L) -/
  A_loop : ∀ (m : ℕ) [NeZero m] (r : ℤ) (A : LoopAnchor m r) (a : ZMod (m + 1)), a ≠ A.softEdge →
    ∃! g : ZMod m, a = softParentEdge A.vertex g ∧
      treeCoefficient A.polygon A.polygon_generic.1 a (by have := A.parent_card; omega) =
        ((turn A.parent A.vertex : SignType) : ℤ) *
          treeCoefficient A.parent A.parent_generic.1 g A.parent_card
  /-- — loop anchors, case (L₀) -/
  A_loopZero : ∀ (m : ℕ) [NeZero m] (A : LoopAnchorZero m) (a : ZMod (m + 1)), a ≠ A.softEdge →
    ∃! g : ZMod m, a = softParentEdge A.vertex g ∧
      treeCoefficient A.polygon A.polygon_generic.1 a (by have := A.parent_card; omega) =
        ((turn A.parent A.vertex : SignType) : ℤ) *
          treeCoefficient A.parent A.parent_generic.1 g A.parent_card

/-! ### The abstract argument (sm-5:477-505), PROVED.  Helpers prefixed `av_`. -/

/-- The printed smaller-parameter argument for an arbitrary `F`: for every anchor datum,
`F(P_ε) = ((χ_- + χ_+)/2) F(P)` in `ℚ` at the anchor's own parameter — the function's threshold `δ_F`
(`hF.soft`), a smaller parameter `ε' < min ε δ_F`, chamber constancy along `(0, ε₀)` (`A.bound_spec` =
lem:soft-generic (i)) and the soft theorem at `ε'`.  The `F`-half of the accepted `unA_softAnchor_delta`
(SM/Uniqueness.lean). -/
theorem av_softAnchor_value (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : AnchorValuesHypotheses F) {m : ℕ} [NeZero m] (A : SoftAnchorData m) :
    (F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) : ℚ) =
      softAmplitudeMultiplier A.parent A.vertex A.vector *
        (F m (polygonProjection ⟨A.parent, A.parent_generic⟩) : ℚ) := by
  have hm := A.parent_card
  have hm1 : 3 ≤ m + 1 := by omega
  obtain ⟨δF, hδF, hsoftF⟩ :=
    hF.soft m hm A.parent A.parent_generic A.vertex A.vector A.admissible
  obtain ⟨ε', hε'pos, hε'param, hε'δ⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' < A.param ∧ ε' < δF := by
    have hmin : 0 < min A.param δF := lt_min A.param_pos hδF
    have h1 : min A.param δF ≤ A.param := min_le_left _ _
    have h2 : min A.param δF ≤ δF := min_le_right _ _
    exact ⟨min A.param δF / 2, by linarith, by linarith, by linarith⟩
  have hε'bound : ε' < A.bound := hε'param.trans A.param_lt
  obtain ⟨B, hB⟩ := A.bound_spec
  obtain ⟨hQ', -, hch'⟩ := hB ε' hε'pos hε'bound
  obtain ⟨hQ, -, hch⟩ := hB A.param A.param_pos A.param_lt
  have hFch : F (m + 1) (polygonProjection ⟨softInsertion A.parent A.vertex A.vector A.param, hQ⟩) =
      F (m + 1) (polygonProjection ⟨softInsertion A.parent A.vertex A.vector ε', hQ'⟩) := by
    rw [hF.chamber (m + 1) hm1 _ _ hch, hF.chamber (m + 1) hm1 _ _ hch']
  have hFs := hsoftF ε' hε'pos hε'δ hQ'
  show (F (m + 1) (polygonProjection ⟨softInsertion A.parent A.vertex A.vector A.param, hQ⟩) : ℚ) = _
  rw [hFch, hFs]

/-- Zero anchors: the multiplier vanishes in the mixed sector (`softAmplitudeMultiplier_mixed`,
SM/SoftAmplitudeSectors.lean). -/
theorem av_zero (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) (hF : AnchorValuesHypotheses F)
    {m : ℕ} [NeZero m] {r : ℤ} (A : ZeroAnchor m r) :
    F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) = 0 := by
  have h := av_softAnchor_value F hF A.toSoftAnchorData
  rw [softAmplitudeMultiplier_mixed _ _ _ A.admissible A.mixed, zero_mul] at h
  exact_mod_cast h

/-- Loop anchors (both kinds): the multiplier is `τ_j(P)` in the loop sector
(`softAmplitudeMultiplier_loop`). -/
theorem av_loop (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) (hF : AnchorValuesHypotheses F)
    {m : ℕ} [NeZero m] (A : SoftAnchorData m)
    (hloop : softAttachmentMinus A.parent A.vertex A.vector = turn A.parent A.vertex ∧
      softAttachmentPlus A.parent A.vertex A.vector = turn A.parent A.vertex) :
    F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) =
      ((turn A.parent A.vertex : SignType) : ℤ) * F m (polygonProjection ⟨A.parent, A.parent_generic⟩) := by
  have h := av_softAnchor_value F hF A
  rw [softAmplitudeMultiplier_loop _ _ _ hloop] at h
  exact_mod_cast h

/-- The `A_g` clause (sm-5:495-505): thm:A-soft (`soft_theorem_treeCoefficient`, SM/SoftTheoremTree.lean)
on an initial interval for the fixed nonsoft root, then constancy along the geometric interval `(0, ε₀)`
(one labelled chamber, `bound_spec`) by prop:A-chamber (`tree_data_labelled_chamber_constant`,
SM/TreeChamber.lean); uniqueness of `g` by `softParentEdge_injective`.  Root independence is NOT used. -/
theorem av_treeCoefficient_anchor {m : ℕ} [NeZero m] (A : SoftAnchorData m) (a : ZMod (m + 1))
    (ha : a ≠ A.softEdge) :
    ∃! g : ZMod m, a = softParentEdge A.vertex g ∧
      (treeCoefficient A.polygon A.polygon_generic.1 a (by have := A.parent_card; omega) : ℚ) =
        softAmplitudeMultiplier A.parent A.vertex A.vector *
          (treeCoefficient A.parent A.parent_generic.1 g A.parent_card : ℚ) := by
  have hm := A.parent_card
  have hm1 : 3 ≤ m + 1 := by omega
  obtain ⟨ε₁, hε₁, -, hlaw⟩ :=
    soft_theorem_treeCoefficient hm A.parent_generic A.vertex A.vector A.admissible A.bound A.bound_pos
  obtain ⟨ε', hε'pos, hε'param, hε'₁⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' < A.param ∧ ε' < ε₁ := by
    have hmin : 0 < min A.param ε₁ := lt_min A.param_pos hε₁
    have h1 : min A.param ε₁ ≤ A.param := min_le_left _ _
    have h2 : min A.param ε₁ ≤ ε₁ := min_le_right _ _
    exact ⟨min A.param ε₁ / 2, by linarith, by linarith, by linarith⟩
  have hε'bound : ε' < A.bound := hε'param.trans A.param_lt
  obtain ⟨B, hB⟩ := A.bound_spec
  obtain ⟨hQ', hch', -⟩ := hB ε' hε'pos hε'bound
  obtain ⟨hQ, hch, -⟩ := hB A.param A.param_pos A.param_lt
  have hconst : treeCoefficient (softInsertion A.parent A.vertex A.vector A.param) hQ.1 a hm1 =
      treeCoefficient (softInsertion A.parent A.vertex A.vector ε') hQ'.1 a hm1 := by
    have h1 := (tree_data_labelled_chamber_constant B ⟨_, hQ⟩ hch a hm1).2.2
    have h2 := (tree_data_labelled_chamber_constant B ⟨_, hQ'⟩ hch' a hm1).2.2
    exact h1.symm.trans h2
  obtain ⟨hQ'', hall⟩ := hlaw ε' hε'pos hε'₁
  obtain ⟨g, ⟨hg, heq, -, -, -⟩, -⟩ := hall a ha
  refine ⟨g, ⟨hg, ?_⟩, fun g' hg' => softParentEdge_injective A.vertex (hg'.1.symm.trans hg)⟩
  show (treeCoefficient (softInsertion A.parent A.vertex A.vector A.param) hQ.1 a hm1 : ℚ) = _
  rw [hconst]
  exact heq

theorem av_A_zero {m : ℕ} [NeZero m] {r : ℤ} (A : ZeroAnchor m r) (a : ZMod (m + 1))
    (ha : a ≠ A.softEdge) :
    treeCoefficient A.polygon A.polygon_generic.1 a (by have := A.parent_card; omega) = 0 := by
  obtain ⟨g, ⟨-, heq⟩, -⟩ := av_treeCoefficient_anchor A.toSoftAnchorData a ha
  rw [softAmplitudeMultiplier_mixed _ _ _ A.admissible A.mixed, zero_mul] at heq
  exact_mod_cast heq

theorem av_A_loop {m : ℕ} [NeZero m] (A : SoftAnchorData m)
    (hloop : softAttachmentMinus A.parent A.vertex A.vector = turn A.parent A.vertex ∧
      softAttachmentPlus A.parent A.vertex A.vector = turn A.parent A.vertex)
    (a : ZMod (m + 1)) (ha : a ≠ A.softEdge) :
    ∃! g : ZMod m, a = softParentEdge A.vertex g ∧
      treeCoefficient A.polygon A.polygon_generic.1 a (by have := A.parent_card; omega) =
        ((turn A.parent A.vertex : SignType) : ℤ) *
          treeCoefficient A.parent A.parent_generic.1 g A.parent_card := by
  obtain ⟨g, ⟨hg, heq⟩, -⟩ := av_treeCoefficient_anchor A a ha
  rw [softAmplitudeMultiplier_loop _ _ _ hloop] at heq
  refine ⟨g, ⟨hg, by exact_mod_cast heq⟩, fun g' hg' => softParentEdge_injective A.vertex (hg'.1.symm.trans hg)⟩

/-- (L₀): the parent is a generic triangle; its turns share one nonzero sign (`A_small_values_i`,
SM/SmallValues.lean), which is its rotation number (`rotationNumber_triangle`, SM/RotationTriangle.lean). -/
theorem av_loopZero_turn {m : ℕ} [NeZero m] (A : LoopAnchorZero m) :
    turn A.parent A.vertex ≠ 0 ∧ (∀ i, turn A.parent i = turn A.parent A.vertex) ∧
      rotationNumber A.parent = ((turn A.parent A.vertex : SignType) : ℤ) := by
  have h3 := A.triangle
  subst h3
  obtain ⟨τ, hτ, hall, -⟩ := A_small_values_i A.parent A.parent_generic.1
  refine ⟨by rw [hall]; exact hτ, fun i => by rw [hall i, hall A.vertex], ?_⟩
  have hreg : Regular A.parent := generic_regular le_rfl A.parent_generic
  rw [(rotationNumber_triangle hreg).1 A.vertex]
  simp

/-! ### "The function C satisfies these hypotheses" — where thm:C-soft enters (conditional, D-F11/D-F14). -/

theorem cornerPolygon_soft_of (hs : CSoftData) :
    ∀ (n : ℕ) [NeZero n] (_hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
      (j : ZMod n) (q : Plane), SoftAdmissible P j q →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ hQ : Generic (softInsertion P j q ε),
        (cornerPolygon (n + 1) (polygonProjection ⟨softInsertion P j q ε, hQ⟩) : ℚ) =
          softAmplitudeMultiplier P j q * (cornerPolygon n (polygonProjection ⟨P, hP⟩) : ℚ) := by
  intro n _ hn P hP j q hq
  obtain ⟨ε₁, hε₁, hall⟩ := hs.soft_theorem n hn P hP j q hq
  refine ⟨ε₁, hε₁, fun ε hε hε' hQ => ?_⟩
  rw [cornerPolygon_projection (by omega : 3 ≤ n + 1), cornerPolygon_projection hn]
  exact hall ε hε hε' hQ

theorem cornerPolygon_anchorValuesHypotheses_of (hs : CSoftData) :
    AnchorValuesHypotheses cornerPolygon :=
  ⟨cornerPolygon_chamber, cornerPolygon_soft_of hs⟩

/-- **Row 122 modulo thm:C-soft** (library, D-F11/D-F14 pattern): every clause but `C_hypotheses.soft`
is unconditional. -/
theorem anchor_values_of (hs : CSoftData) : AnchorValuesData where
  zero := fun F hF _ _ _ A => av_zero F hF A
  loop := fun F hF _ _ _ A => av_loop F hF A.toSoftAnchorData A.loop
  loopZero := fun F hF _ _ A => av_loop F hF A.toSoftAnchorData A.loop
  loop_turn := fun _ _ _ A => A.parent_turn
  loopZero_turn := fun _ _ A => av_loopZero_turn A
  C_hypotheses := cornerPolygon_anchorValuesHypotheses_of hs
  A_zero := fun _ _ _ A a ha => av_A_zero A a ha
  A_loop := fun _ _ _ A a ha => av_A_loop A.toSoftAnchorData A.loop a ha
  A_loopZero := fun _ _ A a ha => av_A_loop A.toSoftAnchorData A.loop a ha

/-- Companion: the printed identities for `C` at the anchors in labelled form ("The function C satisfies
these hypotheses" made explicit): `C(Z) = 0`. -/
theorem AnchorValuesData.C_zero (hD : AnchorValuesData) {m : ℕ} [NeZero m] {r : ℤ}
    (A : ZeroAnchor m r) :
    cornerStateSum (by have := A.parent_card; omega) A.polygon_generic = 0 := by
  have h := hD.zero cornerPolygon hD.C_hypotheses m r A
  rwa [cornerPolygon_projection' (by have := A.parent_card; omega)] at h

/-- Companion: `C(Y) = τ_j(P) C(P)` at a loop anchor (case (L)). -/
theorem AnchorValuesData.C_loop (hD : AnchorValuesData) {m : ℕ} [NeZero m] {r : ℤ}
    (A : LoopAnchor m r) :
    cornerStateSum (by have := A.parent_card; omega) A.polygon_generic =
      ((turn A.parent A.vertex : SignType) : ℤ) * cornerStateSum A.parent_card A.parent_generic := by
  have h := hD.loop cornerPolygon hD.C_hypotheses m r A
  rwa [cornerPolygon_projection' (by have := A.parent_card; omega),
    cornerPolygon_projection' A.parent_card] at h

/-- Companion: `C(Y) = τ_j(P) C(P)` at a loop anchor over a triangle (case (L₀)). -/
theorem AnchorValuesData.C_loopZero (hD : AnchorValuesData) {m : ℕ} [NeZero m]
    (A : LoopAnchorZero m) :
    cornerStateSum (by have := A.parent_card; omega) A.polygon_generic =
      ((turn A.parent A.vertex : SignType) : ℤ) * cornerStateSum A.parent_card A.parent_generic := by
  have h := hD.loopZero cornerPolygon hD.C_hypotheses m A
  rwa [cornerPolygon_projection' (by have := A.parent_card; omega),
    cornerPolygon_projection' A.parent_card] at h

end SM
