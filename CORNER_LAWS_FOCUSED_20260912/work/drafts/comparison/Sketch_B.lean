import SM.Uniqueness
import SM.HypR
import SM.CS3
import SM.CS5
import SM.CSilent
import SM.CChamber
import SM.AnchorsDefinition
import SM.SoftGenericLemma
import SM.GermSides

/-! # Sketch_B — comparison lane: rows 122 prop:anchor-values, 127 thm:comparison, 128 cor:C-inherits
(architect B, proof-feasibility emphasis; 2026-09-15).  Companion of work/drafts/comparison/DESIGN_B.md.
Check: `cd work/lean && lake env lean ../drafts/comparison/Sketch_B.lean`.

Sources (frame SM15): reference/SM/sm-5-transport.tex 461-476 (122; proof 477-505);
reference/SM/sm-6-comparison.tex 299-303 (127; proof 304-311), 313-319 (128; proof 320-372).
Dependencies (tools/claims.py): 122 ← thm:C-soft; 127 ← lem:corner-values, thm:C-S7, thm:C-soft; 128 ← thm:comparison.
Fixed target names (work/lean/axiom-policy.json): `SM.thm_comparison`, `SM.cor_C_inherits`; hyp:R policy mode
`explicit_parameter` (`SM.hyp_R`, SM/HypR.lean).  Proposed: `SM.prop_anchor_values : AnchorValuesData`.

Every `sorry` is (a) a LEAF of DESIGN_B.md §4 (frozen statement) or (b) one of the three ROW THEOREMS of §6, which
become one-liners once rows 105/110/112 land (D-F11/D-F14).  Everything else is PROVED from accepted declarations. -/

namespace SM

open WallGerm SoftDuplication Carrier

/-! ## §0 Interfaces of the corner lane — VERBATIM copies of work/drafts/corner/Statements_FINAL.lean §3-§5
("to be unified": deleted when that lane's module lands; the names then resolve to the accepted ones). -/

section CornerInterfaces

attribute [local instance] Classical.propDecidable

/-- (corner lane, row 105) **lem:corner-values as printed** — VERBATIM. -/
structure CornerValuesData : Prop where
  embedded_value : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    CarrierUniform hn hP S q → carrierCrossingCount hn hP S q = 0 →
      |carrierRotation hn hP S q| = 1 ∧ cornerSlot hn hP S q = 0 ∧ cornerCoefficient hn hP S q hS = 1
  isolated_zero : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    CarrierUniform hn hP S q →
    ∀ y ∈ carrierCrossings hn hP S q,
      (∀ y' ∈ carrierCrossings hn hP S q, y' ≠ y → ¬ Interlaces hn hP y y') →
      cornerCoefficient hn hP S q hS = 0

/-- (corner lane, row 110) **thm:C-S7 as printed** — VERBATIM (fixed name `SM.thm_C_S7 : CS7Data`). -/
structure CS7Data : Prop where
  vertex_edge_law : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)
    (h : g.VertexEdgeAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)),
    ∀ tp tm : g.SideParameter,
      cornerStateSum hn (g.sideTuple true tp).property -
          cornerStateSum hn (g.sideTuple false tm).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1).2.1 h₂)

/-- (corner lane, row 112) **thm:C-soft as printed** — VERBATIM (fixed name `SM.thm_C_soft : CSoftData`). -/
structure CSoftData : Prop where
  soft_theorem : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (j : ZMod n) (q : Plane), SoftAdmissible P j q →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
      (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
        softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ)

end CornerInterfaces

/-! ## §1 The corner state sum as a function on the polygon space (PROVED; def:C's cyclic quotient,
accepted `cornerStateSum_genericShift`).  This is the object the printed "C" of sm-5/sm-6 denotes when it is
compared with thm:uniqueness's `F : ∀ n, GenericPolygon n → ℤ`.  Helpers prefixed `cp_`. -/

/-- `C` descended to `GenericPolygon n` (zero below arity 3, where def:C assigns nothing). -/
noncomputable def cornerPolygon (n : ℕ) [NeZero n] : GenericPolygon n → ℤ :=
  if hn : 3 ≤ n then
    Quotient.lift (s := genericCyclicSetoid n)
      (fun P : GenericTuple n => cornerStateSum hn P.property)
      (fun P Q h => by
        obtain ⟨k, hk⟩ : ∃ k : ZMod n, Q.val = shift k P.val := h
        have hQ : Q = genericShift k P := Subtype.ext hk
        subst hQ
        exact (cornerStateSum_genericShift hn k P).symm)
  else fun _ => 0

theorem cornerPolygon_projection {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : GenericTuple n) :
    cornerPolygon n (polygonProjection P) = cornerStateSum hn P.property := by
  unfold cornerPolygon
  rw [dif_pos hn]
  rfl

/-- Transport of `cornerStateSum` along an equality of tuples. -/
theorem cp_cornerStateSum_congr {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P Q : LabelledTuple n} (h : P = Q)
    (hP : Generic P) (hQ : Generic Q) : cornerStateSum hn hP = cornerStateSum hn hQ := by
  subst h; rfl

/-- Chamber constancy of `cornerPolygon` (prop:C-chamber on the quotient). -/
theorem cornerPolygon_chamber : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericPolygon n),
    Q ∈ chamber P → cornerPolygon n Q = cornerPolygon n P := by
  intro n _ hn P Q
  refine Quotient.inductionOn₂ P Q ?_
  intro P' Q' hQ
  show cornerPolygon n (polygonProjection Q') = cornerPolygon n (polygonProjection P')
  rw [cornerPolygon_projection hn, cornerPolygon_projection hn]
  exact (prop_C_chamber.constant n hn P' Q' hQ).symm

/-! ## §2 Row 122 prop:anchor-values (sm-5:461-476) -/

/-- The two hypotheses of prop:anchor-values on a function `F` on generic polygons of all arities:
"constant on chambers" and "satisfying the soft theorem in the form of thm:C-soft at every admissible soft
insertion into a generic polygon" — the fields (a-chamber) and (e) of the accepted `UniquenessHypotheses`
(SM/Uniqueness.lean), copied verbatim. -/
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

theorem UniquenessHypotheses.toAnchorValuesHypotheses {F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ}
    (hF : UniquenessHypotheses F) : AnchorValuesHypotheses F :=
  ⟨hF.chamber, hF.soft⟩

/-- **prop:anchor-values as printed** (sm-5:461-476), one field per printed clause.  `F` is a function on
generic polygons of all arities (`GenericPolygon n`, as in thm:uniqueness); an anchor is `A.polygon =
softInsertion A.parent A.vertex A.vector A.param` (def:anchors, `SoftAnchorData`/`ZeroAnchor`/`LoopAnchor`/
`LoopAnchorZero`), its parent `P = A.parent`, its insertion vertex `j = A.vertex`, `τ_j(P) = turn A.parent
A.vertex`; the soft edge is `A.softEdge`, a nonsoft root `a ≠ A.softEdge` of the anchor corresponds to the
parent root `g` with `a = softParentEdge A.vertex g` (thm:A-soft's correspondence); `A_g = treeCoefficient`. -/
structure AnchorValuesData : Prop where
  /-- "F(Z) = 0 for every zero anchor" -/
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
  /-- "in case (L₀), it is the orientation sign of the parent triangle": the common sign of the three turns
  of the generic parent triangle (lem:chi-basic (i) / lem:A-small-values (i)). -/
  loopZero_turn : ∀ (m : ℕ) [NeZero m] (A : LoopAnchorZero m),
    ∃ τ : SignType, τ ≠ 0 ∧ (∀ i, turn A.parent i = τ) ∧ turn A.parent A.vertex = τ
  /-- "The function C satisfies these hypotheses" (prop:C-chamber, thm:C-soft), `C` read on the polygon
  space as `cornerPolygon`. -/
  C_hypotheses : AnchorValuesHypotheses cornerPolygon
  /-- "The same identities hold for A_g at every anchor root other than the soft edge, with the
  corresponding parent root used on the right-hand side" — zero anchors -/
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

/-! ### The abstract argument (sm-5:477-490), PROVED.  Helpers prefixed `av_`. -/

/-- The printed smaller-parameter argument for an arbitrary `F`: for every anchor datum,
`F(P_ε) = ((χ_- + χ_+)/2) F(P)` in `ℚ` (chamber constancy along `(0, ε₀)` + the soft theorem at `ε' < δ_F`). -/
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

theorem av_zero (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) (hF : AnchorValuesHypotheses F)
    {m : ℕ} [NeZero m] {r : ℤ} (A : ZeroAnchor m r) :
    F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) = 0 := by
  have h := av_softAnchor_value F hF A.toSoftAnchorData
  rw [softAmplitudeMultiplier_mixed _ _ _ A.admissible A.mixed, zero_mul] at h
  exact_mod_cast h

theorem av_loop (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) (hF : AnchorValuesHypotheses F)
    {m : ℕ} [NeZero m] (A : SoftAnchorData m)
    (hloop : softAttachmentMinus A.parent A.vertex A.vector = turn A.parent A.vertex ∧
      softAttachmentPlus A.parent A.vertex A.vector = turn A.parent A.vertex) :
    F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) =
      ((turn A.parent A.vertex : SignType) : ℤ) * F m (polygonProjection ⟨A.parent, A.parent_generic⟩) := by
  have h := av_softAnchor_value F hF A
  rw [softAmplitudeMultiplier_loop _ _ _ hloop] at h
  exact_mod_cast h

/-- The `A_g` clause (sm-5:495-505): thm:A-soft on an initial interval for the fixed nonsoft root, then
constancy along the geometric interval `(0, ε₀)` (one labelled chamber, `bound_spec`) by prop:A-chamber. -/
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

/-- "in case (L₀), it is the orientation sign of the parent triangle" (lem:A-small-values (i)). -/
theorem av_loopZero_turn (m : ℕ) [NeZero m] (A : LoopAnchorZero m) :
    ∃ τ : SignType, τ ≠ 0 ∧ (∀ i, turn A.parent i = τ) ∧ turn A.parent A.vertex = τ := by
  have h3 := A.triangle
  subst h3
  obtain ⟨τ, hτ, hall, -⟩ := A_small_values_i A.parent A.parent_generic.1
  exact ⟨τ, hτ, hall, hall _⟩

/-! ### "The function C satisfies these hypotheses" — where thm:C-soft enters (conditional, D-F11/D-F14). -/

theorem cornerPolygon_soft_of (hs : CSoftData) :
    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
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

/-- Row 122 modulo thm:C-soft (D-F11/D-F14 pattern): every clause but `C_hypotheses` is unconditional. -/
theorem anchor_values_of (hs : CSoftData) : AnchorValuesData where
  zero := fun F hF _ _ _ A => av_zero F hF A
  loop := fun F hF _ _ _ A => av_loop F hF A.toSoftAnchorData A.loop
  loopZero := fun F hF _ _ A => av_loop F hF A.toSoftAnchorData A.loop
  loop_turn := fun _ _ _ A => A.parent_turn
  loopZero_turn := av_loopZero_turn
  C_hypotheses := cornerPolygon_anchorValuesHypotheses_of hs
  A_zero := fun _ _ _ A a ha => av_A_zero A a ha
  A_loop := fun _ _ _ A a ha => av_A_loop A.toSoftAnchorData A.loop a ha
  A_loopZero := fun _ _ A a ha => av_A_loop A.toSoftAnchorData A.loop a ha

/-- Companion: the printed identities for `C` at the anchors (labelled form). -/
theorem cornerStateSum_zeroAnchor_of (hs : CSoftData) {m : ℕ} [NeZero m] {r : ℤ} (A : ZeroAnchor m r) :
    cornerStateSum (by have := A.parent_card; omega) A.polygon_generic = 0 := by
  have h := av_zero cornerPolygon (cornerPolygon_anchorValuesHypotheses_of hs) A
  rw [cornerPolygon_projection (by have := A.parent_card; omega)] at h
  exact h

theorem cornerStateSum_loopAnchor_of (hs : CSoftData) {m : ℕ} [NeZero m] {r : ℤ} (A : LoopAnchor m r) :
    cornerStateSum (by have := A.parent_card; omega) A.polygon_generic =
      ((turn A.parent A.vertex : SignType) : ℤ) * cornerStateSum A.parent_card A.parent_generic := by
  have h := av_loop cornerPolygon (cornerPolygon_anchorValuesHypotheses_of hs) A.toSoftAnchorData A.loop
  rw [cornerPolygon_projection (by have := A.parent_card; omega), cornerPolygon_projection A.parent_card] at h
  exact h

/-! ## §3 Row 127 thm:comparison (sm-6:299-311): `C = A` on generic polygons, under Hypothesis R -/

/-- cor:A-lawful's normalizations for `C` (the CV/R tail's `TrianglesC`, VERBATIM): `C(K₁) = −1`,
`C(K₋₁) = +1` — hypothesis (f) of thm:uniqueness for `C`, from lem:corner-values (i) (sm-6:308-311). -/
def TrianglesC : Prop :=
  cornerStateSum (by norm_num) (star_generic_law le_rfl).1.2.2.2.1 = -1 ∧
  cornerStateSum (by norm_num) (star_generic_law le_rfl).1.2.2.2.2.1 = 1

/-! ### The triangle values — where lem:corner-values (i) enters.  LEAVES (unit U-TRI), prefix `tri_`. -/

/-- LEAF (U-TRI-A). A generic polygon without crossings and with all turns of one sign has exactly one
decomposition (`∅`), it is uniform, its one carrier is embedded, and def:C gives `C(P) = (−1)^{ℓ(P)} · c(Q) =
(−1)^{ℓ(P)}` with `c(Q) = 1` by lem:corner-values (i) ("Its only decomposition is empty", sm-6:309-310). -/
theorem tri_cornerStateSum_crossingFree (hCV : CornerValuesData) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
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
    exact (hCV.embedded_value n hn P hP ∅ hSe q (huni q) (hcount q)).2.2
  · intro b _ hb
    exact absurd (Subtype.ext (Finset.eq_empty_of_isEmpty b.1)) hb

/-- LEAF (U-TRI-B). A triangle has no crossings (no two of its three edges are remote). -/
theorem tri_triangle_no_crossing (P : LabelledTuple 3) : IsEmpty (Crossing P) := by
  refine ⟨fun c => ?_⟩
  obtain ⟨i, j, -, hrem, -⟩ := c.property
  have h3 : ∀ d : ZMod 3, d = -1 ∨ d = 0 ∨ d = 1 := by decide
  exact hrem (h3 (j - i))

/-- LEAF (U-TRI-C). `ℓ(K₁) = 3` (all turns left, lem:star-generic (i)). -/
theorem tri_leftTurns_star_one : leftTurns (star 1) = 3 := by
  have h : ∀ i, turn (star 1) i = 1 := (star_generic_law le_rfl).1.2.1.2.2.2.1
  unfold leftTurns
  rw [Finset.filter_true_of_mem (fun i _ => h i)]
  simp

/-- LEAF (U-TRI-C). `ℓ(K₋₁) = 0` (all turns right, lem:star-generic (iii)). -/
theorem tri_leftTurns_starNeg_one : leftTurns (starNeg 1) = 0 := by
  have h : ∀ i, turn (starNeg 1) i = -1 := (star_generic_law le_rfl).1.2.2.2.2.2.1
  unfold leftTurns
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  rw [h i]
  decide

/-- Assembly (PROVED from the leaves): "(f) lem:corner-values (i) gives corner coefficient 1 for either
oriented triangle. Its only decomposition is empty, so def:C gives −1 when ℓ = 3 and +1 when ℓ = 0". -/
theorem trianglesC_of (hCV : CornerValuesData) : TrianglesC := by
  constructor
  · have h := tri_cornerStateSum_crossingFree hCV (n := 3) (by norm_num) (P := star 1)
      (star_generic_law le_rfl).1.2.2.2.1 (tri_triangle_no_crossing _) 1 (by decide)
      (star_generic_law le_rfl).1.2.1.2.2.2.1
    rw [h, tri_leftTurns_star_one]
    norm_num
  · have h := tri_cornerStateSum_crossingFree hCV (n := 3) (by norm_num) (P := starNeg 1)
      (star_generic_law le_rfl).1.2.2.2.2.1 (tri_triangle_no_crossing _) (-1) (by decide)
      (star_generic_law le_rfl).1.2.2.2.2.2.1
    rw [h, tri_leftTurns_starNeg_one]
    norm_num

/-! ### The flat law (b) for `C` from the accepted thm:C-S3 (PROVED): side parameters below the radius δ,
`IsRightSide`/`IsLeftSide` and the `Bool` sides are translated into thm:uniqueness's `w.Parameter` form
through `ri_sideTuple_*_val`, `side_turn_constant` and `cornerStateSum_side_eq` (prop:C-chamber along a side).
Prefix `cs3_`. -/

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

/-- The flat law of `C` in cor:A-lawful's shape (the deletion generic by lem:children (i)). -/
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

/-- (a) prop:C-chamber, prop:C-silent; (b) thm:C-S3; (c) thm:C-S7; (d) Hypothesis R; (e) thm:C-soft;
(f) lem:corner-values (i). -/
theorem uniquenessHypotheses_C_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) (htri : TrianglesC) :
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
    exact htri

/-- **thm:comparison modulo rows 105, 110, 112** (D-F11/D-F14 pattern): under Hypothesis R (explicit
parameter, policy mode `explicit_parameter`), `C(P) = A(P)` for every generic polygon `P` — `C` is def:C's
`cornerStateSum`, `A` is cor:A-lawful's `amplitude` (root-independent, shift-invariant). -/
theorem thm_comparison_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) (hCV : CornerValuesData) :
    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
      cornerStateSum hn hP = amplitude P hP.1 hn := by
  intro n _ hn P hP
  have h := uniqueness cornerPolygon (uniquenessHypotheses_C_of hR h7 hs (trianglesC_of hCV)) n hn P hP
  rw [cornerPolygon_projection hn] at h
  exact h

/-- Companion: the same on the polygon space (`alA_polygonAmplitude` is cor:A-lawful's descended `A`). -/
theorem thm_comparison_polygon_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) (hCV : CornerValuesData)
    (n : ℕ) [NeZero n] (hn : 3 ≤ n) (Q : GenericPolygon n) :
    cornerPolygon n Q = alA_polygonAmplitude hn Q := by
  induction Q using Quotient.inductionOn with
  | h P =>
    show cornerPolygon n (polygonProjection P) = alA_polygonAmplitude hn (polygonProjection P)
    rw [cornerPolygon_projection hn, alA_polygonAmplitude_projection]
    exact thm_comparison_of hR h7 hs hCV n hn P.val P.property

/-! ## §4 Row 128 cor:C-inherits (sm-6:313-372): every identity of cor:A-lawful for `C`, under Hypothesis R -/

/-- cor:C-inherits' cusp law (the CV/R tail's `CuspLawC`, VERBATIM): "C(P_loop) − C(P_no) = −κ C(P(0) ∖ j)"
on cor:A-lawful's domain ("when the deletion satisfies (G1)"), the deletion generic (the printed domain check
sm-6:335-359, existential), including threaded cusps (no emptiness hypothesis). -/
def CuspLawC : Prop :=
  ∀ (n : ℕ) [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1)) (hf : w.CuspAt j),
    G1 (deleteVertex w.center j) →
    ∃ hQ : Generic (deleteVertex w.center j),
    ∃ b : Bool, CuspCase w.center j b ∧ (∀ b' : Bool, CuspCase w.center j b' → b' = b) ∧
      ∃ κ : ℤ, (κ = -1 ∨ κ = 1) ∧
        ∀ s t : w.SideParameter,
          (rotationNumber (w.sideTuple (w.cuspLoopSide b j) s).val -
            rotationNumber (w.sideTuple (!(w.cuspLoopSide b j)) t).val = (κ : ℝ)) ∧
          cornerStateSum (by have := hf.1; omega) (w.sideTuple (w.cuspLoopSide b j) s).property -
              cornerStateSum (by have := hf.1; omega) (w.sideTuple (!(w.cuspLoopSide b j)) t).property =
            -κ * cornerStateSum (by have := hf.1; omega) hQ

/-- cor:A-lawful's reversal identity for `C` (the CV/R tail's `ReversalLawC`, VERBATIM). -/
def ReversalLawC : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
    cornerStateSum hn ((generic_reversal P).mpr hP) = (-1) ^ n * cornerStateSum hn hP

/-- **cor:C-inherits as printed** (sm-6:313-319): "Under Hypothesis R, C satisfies every identity of
cor:A-lawful on the domains stated there, in particular the cusp law" — the accepted `ALawfulData`
(SM/ALawful.lean) field for field with `cornerStateSum` for `amplitude`, minus `root_independent` (A-specific:
C has no root) and minus the A-specific per-induced-root sub-clause of the cusp law; the deletion / halves /
`P_ε` carry `Generic` witnesses because `C` is defined on generic polygons only (the printed domain checks). -/
structure CInheritsData : Prop where
  /-- "well defined on generic polygons": invariance under the cyclic shift (def:C's quotient) -/
  shift_invariant : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (k : ZMod n), cornerStateSum hn ((generic_shift k P).mpr hP) = cornerStateSum hn hP
  /-- descent to the polygon space -/
  descends : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n), ∃ C' : GenericPolygon n → ℤ,
    ∀ P : GenericTuple n, C' (polygonProjection P) = cornerStateSum hn P.property
  /-- chamber constancy (prop:C-chamber) -/
  chamber_constant : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericTuple n),
    (Q ∈ labelledChamber P → cornerStateSum hn Q.property = cornerStateSum hn P.property) ∧
    (polygonProjection Q ∈ chamber (polygonProjection P) →
      cornerStateSum hn Q.property = cornerStateSum hn P.property)
  /-- silence (prop:C-silent) -/
  silent : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (w : WallGerm n),
    (∀ M a : ZMod n, w.ExtensionAt M a → ∀ s t : w.SideParameter,
      cornerStateSum hn (w.sideTuple true t).property = cornerStateSum hn (w.sideTuple false s).property) ∧
    (∀ i j k : ZMod n, w.PureCutAt i j k → ∀ s t : w.SideParameter,
      cornerStateSum hn (w.sideTuple true t).property = cornerStateSum hn (w.sideTuple false s).property)
  /-- the flat law `C(P_right) − C(P_left) = C(P(0) ∖ j)` (thm:C-S3; the deletion generic, lem:children (i)) -/
  flat_law : ∀ (n : ℕ) [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1)) (hf : w.FlatAt j),
    ∃ hQ : Generic (deleteVertex w.center j),
    ∀ (sRight sLeft : w.Parameter) (hRight0 : sRight.val ≠ 0) (hLeft0 : sLeft.val ≠ 0),
      turn (w.curve sRight) j = -1 → turn (w.curve sLeft) j = 1 →
      cornerStateSum (by have := hf.1; omega) (w.generic_punctured sRight hRight0) -
        cornerStateSum (by have := hf.1; omega) (w.generic_punctured sLeft hLeft0) =
        cornerStateSum (by have := hf.1; omega) hQ
  /-- the cusp law `C(P_loop) − C(P_no) = −κ C(P(0) ∖ j)` when the deletion satisfies (G1) -/
  cusp_law : CuspLawC
  /-- the vertex–edge law `C(P₊) − C(P₋) = s C(λ₁) C(λ₂)` (thm:C-S7; the halves generic, lem:children (ii)) -/
  vertex_edge_law : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (w : WallGerm n) (M a : ZMod n)
    (hc : w.VertexEdgeAt M a),
    Generic (firstHalf w.center M a) ∧ Generic (secondHalf w.center M a) ∧
    ∀ s t : w.SideParameter,
      cornerStateSum hn (w.sideTuple true t).property -
        cornerStateSum hn (w.sideTuple false s).property =
        (w.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn hc.1).1.1 (vertex_halves_children hn w hc).1 *
            cornerStateSum (contactHalfSizes_bounds hn hc.1).2.1 (vertex_halves_children hn w hc).2.1)
  /-- the triple law `C(P₊) = C(P₋)` (Hypothesis R) -/
  triple_law : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (w : WallGerm n) (e f k : ZMod n),
    w.TripleAt e f k → ∀ s t : w.SideParameter,
      cornerStateSum hn (w.sideTuple true t).property = cornerStateSum hn (w.sideTuple false s).property
  /-- the soft theorem `C(P_ε) = ((χ_- + χ_+)/2) C(P)` in every sector, for all small `ε` (thm:C-soft;
  `P_ε` generic by lem:soft-generic) -/
  soft_theorem : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (j : ZMod n) (q : Plane), SoftAdmissible P j q →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ hQ : Generic (softInsertion P j q ε),
        (cornerStateSum (by omega) hQ : ℚ) = softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ)
  /-- reversal `C(P̄) = (−1)^n C(P)` -/
  reversal_law : ReversalLawC
  /-- `C(K₁) = −1` and `C(K₋₁) = +1` -/
  triangles : TrianglesC

/-! ### The cusp law — where the genuinely new geometry sits.  Prefix `cu_`. -/

/-- LEAF (U-CUSPGEN, sm-6:335-359): at a simple cusp wall whose deletion `Q = P(0) ∖ j` satisfies (G1), `Q` is
generic ((G2): the fused edge `[A, B]` lies in the longer cusp edge; three pairwise remote edges of `Q` with a
common relative-interior point would give three pairwise remote edges of the centre with a common point,
contrary to `Z_c = ∅` of def:walls (K)). -/
theorem cu_cusp_deletion_generic {n : ℕ} [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hf : w.CuspAt j) (hQ1 : G1 (deleteVertex w.center j)) : Generic (deleteVertex w.center j) := by
  sorry

/-- The cusp law for `C` from `C = A` (thm:comparison) and thm:A-S4 via cor:A-lawful, PROVED given the
domain check. -/
theorem cu_cuspLawC_of
    (hcmp : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
      cornerStateSum hn hP = amplitude P hP.1 hn) : CuspLawC := by
  intro n _ w j hf hQ1
  have hQ : Generic (deleteVertex w.center j) := cu_cusp_deletion_generic w j hf hQ1
  obtain ⟨b, hb, huniq, κ, hκ, hlaw⟩ := A_lawful.cusp_law n w j hf hQ1
  refine ⟨hQ, b, hb, huniq, κ, hκ, fun s t => ⟨(hlaw s t).1, ?_⟩⟩
  have hn1 : 3 ≤ n + 1 := by have := hf.1; omega
  have hn : 3 ≤ n := by have := hf.1; omega
  have e1 := hcmp (n + 1) hn1 _ (w.sideTuple (w.cuspLoopSide b j) s).property
  have e2 := hcmp (n + 1) hn1 _ (w.sideTuple (!(w.cuspLoopSide b j)) t).property
  have e3 := hcmp n hn _ hQ
  show cornerStateSum hn1 (w.sideTuple (w.cuspLoopSide b j) s).property -
      cornerStateSum hn1 (w.sideTuple (!(w.cuspLoopSide b j)) t).property =
      -κ * cornerStateSum hn hQ
  rw [e1, e2, e3]
  exact (hlaw s t).2.2 hQ

/-- **cor:C-inherits modulo rows 105, 110, 112** (D-F11/D-F14 pattern; hyp:R an explicit parameter). -/
theorem cor_C_inherits_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) (hCV : CornerValuesData) :
    CInheritsData := by
  have hcmp := thm_comparison_of hR h7 hs hCV
  refine
    { shift_invariant := ?_, descends := ?_, chamber_constant := ?_, silent := ?_, flat_law := ?_,
      cusp_law := cu_cuspLawC_of hcmp, vertex_edge_law := ?_, triple_law := ?_, soft_theorem := ?_,
      reversal_law := ?_, triangles := trianglesC_of hCV }
  · intro n _ hn P hP k
    exact cornerStateSum_genericShift hn k ⟨P, hP⟩
  · intro n _ hn
    exact ⟨cornerPolygon n, fun P => cornerPolygon_projection hn P⟩
  · intro n _ hn P Q
    exact ⟨fun h => (cornerStateSum_eq_of_mem_labelledChamber hn h).symm,
      fun h => (prop_C_chamber.constant n hn P Q h).symm⟩
  · intro n _ hn w
    exact ⟨fun M a hE s t => prop_C_silent.extension n hn w M a hE t s,
      fun i j k hC s t => prop_C_silent.cut n hn w i j k hC t s⟩
  · intro n _ w j hf
    exact cs3_flat_law_C thm_C_S3 w j hf
  · intro n _ hn w M a hc
    exact ⟨(vertex_halves_children hn w hc).1, (vertex_halves_children hn w hc).2.1,
      fun s t => h7.vertex_edge_law n hn w M a hc _ _ t s⟩
  · intro n _ hn w e f k hT s t
    exact hR n hn w e f k hT t s
  · intro n _ hn P hP j q hq
    obtain ⟨ε₁, hε₁, hall⟩ := hs.soft_theorem n hn P hP j q hq
    obtain ⟨δ, hδ, B, hgen⟩ := (soft_family_generic hn hP j q hq).2.2.2.2.2
    refine ⟨min ε₁ δ, lt_min hε₁ hδ, fun ε hε hlt => ?_⟩
    obtain ⟨hQ, -⟩ := hgen ε hε (lt_of_lt_of_le hlt (min_le_right _ _))
    exact ⟨hQ, hall ε hε (lt_of_lt_of_le hlt (min_le_left _ _)) hQ⟩
  · intro n _ hn P hP
    rw [hcmp n hn _ ((generic_reversal P).mpr hP), hcmp n hn P hP]
    exact A_lawful.reversal_law n hn P hP

/-! ## §5 The row theorems (`sorry` until rows 105 cb/lem:corner-values, 110 thm:C-S7, 112 thm:C-soft land;
D-F11/D-F14: declared and mapped only then). -/

/-- Row 122 prop:anchor-values (proposed name).  Body once row 112 lands: `anchor_values_of thm_C_soft`. -/
theorem prop_anchor_values : AnchorValuesData := by
  sorry

/-- Row 127 thm:comparison (FIXED name; hyp:R explicit).  Body once rows 105/110/112 land:
`thm_comparison_of hR thm_C_S7 thm_C_soft corner_values`. -/
theorem thm_comparison (hR : hyp_R) :
    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
      cornerStateSum hn hP = amplitude P hP.1 hn := by
  sorry

/-- Row 128 cor:C-inherits (FIXED name; hyp:R explicit).  Body once rows 105/110/112 land:
`cor_C_inherits_of hR thm_C_S7 thm_C_soft corner_values`. -/
theorem cor_C_inherits (hR : hyp_R) : CInheritsData := by
  sorry

/-! ## §6 Consumer shape checks -/

/-- The CV/R tail's `corner_laws_and_soft_of` reads exactly these three fields at these types
(work/drafts/cvtail/Statements_FINAL.lean:973-987): no change there. -/
example (hinh : CInheritsData) : CuspLawC ∧ ReversalLawC ∧ TrianglesC :=
  ⟨hinh.cusp_law, hinh.reversal_law, hinh.triangles⟩

/-- thm:uniqueness's hypotheses restrict to prop:anchor-values' hypotheses. -/
example (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) (hF : UniquenessHypotheses F) :
    AnchorValuesHypotheses F := hF.toAnchorValuesHypotheses

end SM
