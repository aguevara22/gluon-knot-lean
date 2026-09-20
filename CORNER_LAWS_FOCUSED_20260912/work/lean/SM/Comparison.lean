-- Ported 20:26Z 2026-09-15 from work/drafts/comparison/Comparison_Assembled.lean lines 441-677 (comparison lane §3, row 127 thm:comparison as library material: `TrianglesC` (this lane owns the CV/R tail's Prop, PLAN_FINAL.md §6), the `tri_*` helpers and `trianglesC` (UNCONDITIONAL), the `cs3_*` bridge, `uniquenessHypotheses_C_of`, `thm_comparison_of (hR) (h7) (hs)` and the companions `thm_comparison_root_of`, `thm_comparison_polygon_of`) by the pod executor; body verbatim except this header, the import block (SM.AnchorValues for §1-§2, SM.CornerChainUnits whose accepted `corner_values_i` replaces the draft's DELETED §0 copies of `cvl_embedded_of_no_crossings` / `corner_values_i`, lines 78-127, byte-identical declaration blocks, tools/port_copy_diff.py; SM.CS3, SM.CSilent, SM.HypR; `CS7Data` resolves to the accepted SM/CornerChainStatements.lean declaration, replacing the deleted copy at lines 59-69) and the module docstring (new).  Wrappers `namespace SM` / `open WallGerm SoftDuplication Carrier` / `end SM` repeated verbatim.  The row theorem `SM.thm_comparison (hR : hyp_R)` is NOT declared here: it needs `SM.thm_C_S7` (row 110), see port/PORT_REPORT.md §5.
import SM.AnchorValues
import SM.CornerChainUnits
import SM.CS3
import SM.CSilent
import SM.HypR

/-! # Row 127 thm:comparison (sm-6:299-303; proof 304-311) — the conditional theorem and its ingredients

Source: work/drafts/comparison/Comparison_Assembled.lean §3 (PLAN_FINAL.md §4 units U-CM-TRI, U-CM-CS3, U-CM-CMP; FR-CM-6,
FR-CM-7, FR-CM-10..12).  `thm_comparison_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData)` is "Assume Hypothesis R.  Then
C(P) = A(P) for every generic polygon P" modulo rows 110 thm:C-S7 and 112 thm:C-soft (D-F11/D-F14 pattern): the accepted
`SM.uniqueness` (SM/Uniqueness.lean) at `cornerPolygon` with (a) prop:C-chamber + prop:C-silent, (b) thm:C-S3 through the
`cs3_*` bridge, (c) `h7`, (d) `hR`, (e) `hs`, (f) the UNCONDITIONAL `trianglesC` from the accepted `corner_values_i`
(SM/CornerChainUnits.lean §3).  The row theorem `SM.thm_comparison (hR : hyp_R)` (FIXED name) is declared when `SM.thm_C_S7`
exists, as `thm_comparison_of hR thm_C_S7 thm_C_soft`. -/

namespace SM

open WallGerm SoftDuplication Carrier

/-! ## §3 Row 127 thm:comparison (sm-6:299-311) — FIXED name `SM.thm_comparison` -/

/-- cor:A-lawful's normalizations for `C` (the CV/R tail's `TrianglesC`, VERBATIM): `C(K₁) = −1`,
`C(K₋₁) = +1` — hypothesis (f) of thm:uniqueness for `C` (sm-6:308-311). -/
def TrianglesC : Prop :=
  cornerStateSum (by norm_num) (star_generic_law le_rfl).1.2.2.2.1 = -1 ∧
  cornerStateSum (by norm_num) (star_generic_law le_rfl).1.2.2.2.2.1 = 1

/-! ### The triangle values — where lem:corner-values (i) enters (`corner_values_i`, PROVED).
Prefix `tri_`.  PROVED. -/

/-- A generic polygon without crossings and with all turns of one sign has exactly one decomposition
(`∅`), it is uniform, its one carrier is embedded, and def:C gives `C(P) = (−1)^{ℓ(P)} · c(Q) = (−1)^{ℓ(P)}`
with `c(Q) = 1` by lem:corner-values (i) ("Its only decomposition is empty", sm-6:309-310). -/
theorem tri_cornerStateSum_crossingFree {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {P : LabelledTuple n} (hP : Generic P) (hcr : IsEmpty (Crossing P))
    (τ : SignType) (hτ : τ ≠ 0) (hall : ∀ i, turn P i = τ) :
    cornerStateSum hn hP = (-1) ^ leftTurns P := by
  have hSe : (∅ : Finset (Crossing P)) ∈ independentSupports hn hP :=
    empty_mem_independentSupports hn hP
  -- every carrier of the empty decomposition is uniform: all its corners are vertex marks of `P`
  have huni : UniformDecomposition hn hP ∅ := by
    intro q
    refine ⟨τ, hτ, fun k => ?_⟩
    have hmem : ccpCornerMark hn hP ∅ q k ∈ ccpCornerList hn hP ∅ q := List.getElem_mem _
    obtain ⟨-, hcorner⟩ := (mem_ccpCornerList hn hP ∅ q _).mp hmem
    rcases hmk : ccpCornerMark hn hP ∅ q k with i | v
    · rw [ccpCornerPolygon_turn_vertex hn hP hSe q k i hmk, hall]
    · rw [hmk] at hcorner
      simp [IsTrueCorner] at hcorner
  -- the carriers are embedded: no crossings at all
  have hcount : ∀ q : Component hn hP (∅ : Finset (Crossing P)), carrierCrossingCount hn hP ∅ q = 0 := by
    intro q
    unfold carrierCrossingCount
    rw [Finset.card_eq_zero]
    exact Finset.eq_empty_of_isEmpty _
  have hmemU : (∅ : Finset (Crossing P)) ∈ uniformDecompositions hn hP :=
    (mem_uniformDecompositions hn hP ∅).mpr ⟨hSe, huni⟩
  -- the only decomposition is `∅`
  unfold cornerStateSum
  rw [Finset.sum_eq_single_of_mem (⟨∅, hmemU⟩ : {S // S ∈ uniformDecompositions hn hP})
    (Finset.mem_attach _ _)]
  · rw [Finset.card_empty, pow_zero, one_mul]
    unfold cornerProduct
    rw [Finset.prod_eq_one, mul_one]
    intro q _
    exact (corner_values_i hn hP hSe q (huni q) (hcount q)).2.2
  · intro b _ hb
    exact absurd (Subtype.ext (Finset.eq_empty_of_isEmpty b.1)) hb

/-- A triangle has no crossings (no two of its three edges are remote). -/
theorem tri_triangle_no_crossing (P : LabelledTuple 3) : IsEmpty (Crossing P) := by
  refine ⟨fun c => ?_⟩
  obtain ⟨i, j, -, hrem, -⟩ := c.property
  have h3 : ∀ d : ZMod 3, d = -1 ∨ d = 0 ∨ d = 1 := by decide
  exact hrem (h3 (j - i))

/-- `ℓ(K₁) = 3` (all turns left, lem:star-generic (i)). -/
theorem tri_leftTurns_star_one : leftTurns (star 1) = 3 := by
  have h : ∀ i, turn (star 1) i = 1 := (star_generic_law le_rfl).1.2.1.2.2.2.1
  unfold leftTurns
  rw [Finset.filter_true_of_mem (fun i _ => h i)]
  simp

/-- `ℓ(K₋₁) = 0` (all turns right, lem:star-generic (iii)). -/
theorem tri_leftTurns_starNeg_one : leftTurns (starNeg 1) = 0 := by
  have h : ∀ i, turn (starNeg 1) i = -1 := (star_generic_law le_rfl).1.2.2.2.2.2.1
  unfold leftTurns
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  rw [h i]
  decide

/-- Companion (the shape of lem:A-small-values (i) for `C`): `C(T) = −τ` for every generic triangle with
common turn sign `τ`. -/
theorem tri_triangle_value (T : LabelledTuple 3) (hT : Generic T) (τ : SignType) (hτ : ∀ i, turn T i = τ) :
    cornerStateSum (by norm_num) hT = -(τ : ℤ) := by
  obtain ⟨τ', hτ', hall, -⟩ := A_small_values_i T hT.1
  have hττ' : τ = τ' := by rw [← hτ 0, hall 0]
  have hτ0 : τ ≠ 0 := by rw [hττ']; exact hτ'
  rw [tri_cornerStateSum_crossingFree (by norm_num) hT (tri_triangle_no_crossing T) τ hτ0 hτ]
  rcases τ with _ | _ | _
  · exact absurd rfl hτ0
  · have hl : leftTurns T = 0 := by
      unfold leftTurns
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _
      rw [hτ i]; decide
    rw [hl]; decide
  · have hl : leftTurns T = 3 := by
      unfold leftTurns
      rw [Finset.filter_true_of_mem (fun i _ => (hτ i).trans (by decide))]
      simp
    rw [hl]; decide

/-- **(f) for `C`, UNCONDITIONAL**: "lem:corner-values (i) gives corner coefficient 1 for either oriented
triangle.  Its only decomposition is empty, so def:C gives −1 when ℓ = 3 and +1 when ℓ = 0". -/
theorem trianglesC : TrianglesC := by
  constructor
  · have h := tri_cornerStateSum_crossingFree (n := 3) (by norm_num) (P := star 1)
      (star_generic_law le_rfl).1.2.2.2.1 (tri_triangle_no_crossing _) 1 (by decide)
      (star_generic_law le_rfl).1.2.1.2.2.2.1
    rw [h, tri_leftTurns_star_one]
    norm_num
  · have h := tri_cornerStateSum_crossingFree (n := 3) (by norm_num) (P := starNeg 1)
      (star_generic_law le_rfl).1.2.2.2.2.1 (tri_triangle_no_crossing _) (-1) (by decide)
      (star_generic_law le_rfl).1.2.2.2.2.2.1
    rw [h, tri_leftTurns_starNeg_one]
    norm_num

/-! ### The flat law (b) for `C` from the accepted thm:C-S3 (PROVED): side parameters below the radius δ,
`IsRightSide`/`IsLeftSide` and the `Bool` sides are translated into thm:uniqueness's `w.Parameter` form
through `ri_sideTuple_*_val` (SM/RootIndependence.lean), `side_turn_constant` (SM/GermTurnSigns.lean) and
`cornerStateSum_side_eq` (SM/HypR.lean, prop:C-chamber along a side).  FR-CM-11.  Prefix `cs3_`. -/

/-- Every nonzero germ parameter is a side point. -/
theorem cs3_param_side {n : ℕ} (w : WallGerm n) (s : w.Parameter) (hs : s.val ≠ 0) :
    ∃ (b : Bool) (t : w.SideParameter), (w.sideTuple b t).val = w.curve s := by
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · exact ⟨false, ⟨-s.val, by linarith, by linarith [s.property.1]⟩, w.ri_sideTuple_false_val s hneg⟩
  · exact ⟨true, ⟨s.val, hpos, s.property.2⟩, w.ri_sideTuple_true_val s hpos⟩

theorem cs3_flat_bridge (h3 : CS3Data) {n : ℕ} [NeZero n] (hn : 3 ≤ n) (w : WallGerm (n + 1))
    (j : ZMod (n + 1)) (hf : w.FlatAt j) (hdel : Generic (deleteVertex w.center j))
    (sRight sLeft : w.Parameter) (hRight0 : sRight.val ≠ 0) (hLeft0 : sLeft.val ≠ 0)
    (hR : turn (w.curve sRight) j = -1) (hL : turn (w.curve sLeft) j = 1) :
    cornerStateSum (by omega) (w.generic_punctured sRight hRight0) -
      cornerStateSum (by omega) (w.generic_punctured sLeft hLeft0) = cornerStateSum hn hdel := by
  have hn1 : 3 ≤ n + 1 := by omega
  obtain ⟨-, hz, hc, hb, hsc⟩ := hf
  obtain ⟨δ, hδ, hδr, hlaw⟩ := h3.flat_law n hn w j hz hb hc hsc
  obtain ⟨bR, tR, eR⟩ := cs3_param_side w sRight hRight0
  obtain ⟨bL, tL, eL⟩ := cs3_param_side w sLeft hLeft0
  -- a common small side parameter below δ
  let t' : w.SideParameter := ⟨δ / 2, by constructor <;> linarith [w.radius_pos]⟩
  have ht' : t'.val < δ := by show δ / 2 < δ; linarith
  have hR' : IsRightSide w j bR t' := by
    show turn (w.sideTuple bR t').val j = -1
    rw [w.side_turn_constant bR t' tR j, eR]; exact hR
  have hL' : IsLeftSide w j bL t' := by
    show turn (w.sideTuple bL t').val j = 1
    rw [w.side_turn_constant bL t' tL j, eL]; exact hL
  have key := hlaw bR bL t' t' ht' ht' hR' hL'
  have eR' : cornerStateSum hn1 (w.sideTuple bR t').property =
      cornerStateSum hn1 (w.generic_punctured sRight hRight0) :=
    (cornerStateSum_side_eq hn1 w bR t' tR).trans
      (cp_cornerStateSum_congr hn1 eR _ _)
  have eL' : cornerStateSum hn1 (w.sideTuple bL t').property =
      cornerStateSum hn1 (w.generic_punctured sLeft hLeft0) :=
    (cornerStateSum_side_eq hn1 w bL t' tL).trans
      (cp_cornerStateSum_congr hn1 eL _ _)
  have key' : cornerStateSum hn1 (w.sideTuple bR t').property -
      cornerStateSum hn1 (w.sideTuple bL t').property = cornerStateSum hn hdel := key
  rw [eR', eL'] at key'
  exact key'

/-- The flat law of `C` in cor:A-lawful's shape (the deletion generic by lem:children (i),
`generic_deleteVertex`, SM/DeletionGeneric.lean). -/
theorem cs3_flat_law_C (h3 : CS3Data) {n : ℕ} [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hf : w.FlatAt j) :
    ∃ hQ : Generic (deleteVertex w.center j),
    ∀ (sRight sLeft : w.Parameter) (hRight0 : sRight.val ≠ 0) (hLeft0 : sLeft.val ≠ 0),
      turn (w.curve sRight) j = -1 → turn (w.curve sLeft) j = 1 →
      cornerStateSum (by have := hf.1; omega) (w.generic_punctured sRight hRight0) -
        cornerStateSum (by have := hf.1; omega) (w.generic_punctured sLeft hLeft0) =
        cornerStateSum (by have := hf.1; omega) hQ := by
  have hn : 3 ≤ n := by have := hf.1; omega
  refine ⟨generic_deleteVertex hn hf.2.1 hf.2.2.2.1 hf.2.2.1, ?_⟩
  intro sRight sLeft hRight0 hLeft0 hR hL
  exact cs3_flat_bridge h3 hn w j hf _ sRight sLeft hRight0 hLeft0 hR hL

/-! ### thm:uniqueness's hypotheses (a)–(f) for `C` (sm-6:304-311) — the assembly of the row -/

/-- (a) prop:C-chamber, prop:C-silent; (b) thm:C-S3; (c) thm:C-S7 (`h7`); (d) Hypothesis R (`hR`);
(e) thm:C-soft (`hs`); (f) lem:corner-values (i) (`trianglesC`, unconditional).  FR-CM-10. -/
theorem uniquenessHypotheses_C_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) :
    UniquenessHypotheses cornerPolygon where
  chamber := cornerPolygon_chamber
  silent := by
    intro n _ hn w
    refine ⟨fun M a hE s t => ?_, fun i j k hC s t => ?_⟩
    · rw [cornerPolygon_projection hn, cornerPolygon_projection hn]
      exact prop_C_silent.extension n hn w M a hE t s
    · rw [cornerPolygon_projection hn, cornerPolygon_projection hn]
      exact prop_C_silent.cut n hn w i j k hC t s
  flat := by
    intro n _ w j hf hdel sRight sLeft hRight0 hLeft0 hR hL
    have hn : 3 ≤ n := by have := hf.1; omega
    have hn1 : 3 ≤ n + 1 := by omega
    rw [cornerPolygon_projection hn1, cornerPolygon_projection hn1, cornerPolygon_projection hn]
    exact cs3_flat_bridge thm_C_S3 hn w j hf hdel sRight sLeft hRight0 hLeft0 hR hL
  vertex_edge := by
    intro n _ hn w M a hc h₁ h₂ s t
    rw [cornerPolygon_projection hn, cornerPolygon_projection hn,
      cornerPolygon_projection (contactHalfSizes_bounds hn hc.1).1.1,
      cornerPolygon_projection (contactHalfSizes_bounds hn hc.1).2.1]
    exact h7.vertex_edge_law n hn w M a hc h₁ h₂ t s
  triple := by
    intro n _ hn w e f k hT s t
    rw [cornerPolygon_projection hn, cornerPolygon_projection hn]
    exact hR n hn w e f k hT t s
  soft := cornerPolygon_soft_of hs
  triangles := by
    rw [cornerPolygon_projection (by norm_num), cornerPolygon_projection (by norm_num)]
    exact trianglesC

/-- **thm:comparison modulo rows 110, 112** (D-F11/D-F14 pattern): "Assume Hypothesis R.  Then
C(P) = A(P) for every generic polygon P" — `hR : hyp_R` an explicit parameter (policy mode
`explicit_parameter`, FR-CM-7), `C` = def:C's `cornerStateSum`, `A(P) = amplitude P hP.1 hn`
(cor:A-lawful's `A(P) := A_g(P)`, root 0), every arity `n ≥ 3`, every generic labelled tuple (FR-CM-6).
PROVED: the accepted `SM.uniqueness` (SM/Uniqueness.lean:454) at `cornerPolygon`. -/
theorem thm_comparison_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) :
    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
      cornerStateSum hn hP = amplitude P hP.1 hn := by
  intro n _ hn P hP
  have h := uniqueness cornerPolygon (uniquenessHypotheses_C_of hR h7 hs) n hn P hP
  rw [cornerPolygon_projection hn] at h
  exact h

/-- Companion (FR-CM-6): `C(P) = A_g(P)` for every root `g` (thm:root-indep-proof through
`A_lawful.root_independent`). -/
theorem thm_comparison_root_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData)
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) (g : ZMod n) :
    cornerStateSum hn hP = treeCoefficient P hP.1 g hn := by
  rw [thm_comparison_of hR h7 hs n hn P hP]
  exact A_lawful.root_independent n hn P hP g

/-- Companion (FR-CM-6): the polygon-level form `C = A` on the space of generic polygons
(`alA_polygonAmplitude` is cor:A-lawful's descended `A`). -/
theorem thm_comparison_polygon_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData)
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (Q : GenericPolygon n) :
    cornerPolygonSum hn Q = alA_polygonAmplitude hn Q := by
  induction Q using Quotient.inductionOn with
  | h P =>
    show cornerPolygonSum hn (polygonProjection P) = alA_polygonAmplitude hn (polygonProjection P)
    rw [cornerPolygonSum_projection, alA_polygonAmplitude_projection]
    exact thm_comparison_of hR h7 hs n hn P.val P.property

end SM
