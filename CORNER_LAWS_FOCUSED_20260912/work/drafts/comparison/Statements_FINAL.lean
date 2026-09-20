import SM.Uniqueness
import SM.HypR
import SM.CS3
import SM.CS5
import SM.CSilent
import SM.CChamber
import SM.AnchorsDefinition
import SM.SoftGenericLemma
import SM.GermSides
import SM.Children
import SM.EmbeddedRotation
import SM.LinkPositiveLift
import SM.UniformRotation
import SM.CBProducts

/-! # Statements_FINAL — comparison lane: rows 122 prop:anchor-values, 127 thm:comparison,
128 cor:C-inherits (judge's decision, 2026-09-15)

Companion of work/drafts/comparison/PLAN_FINAL.md (winner: DESIGN_B's skeleton, with DESIGN_A's grafts
and ONE judge's graft from the corner lane).  Check: `cd work/lean && lake env lean ../drafts/comparison/Statements_FINAL.lean`.

Every `sorry` is either (a) the ONE LEAF of PLAN_FINAL.md §4 (`cusp_deletion_generic`, sm-6:335-359,
frozen statement, unit U-CM-CUSPGEN), or (b) one of the three ROW THEOREMS of §5, which become one-liners
once rows 110 (`SM.thm_C_S7 : CS7Data`) and 112 (`SM.thm_C_soft : CSoftData`) land (D-F11/D-F14: declared
and mapped only then).  Everything else is PROVED from accepted declarations: the whole of row 122 modulo
thm:C-soft (`anchor_values_of`), the descent `cornerPolygon`, the triangle values `trianglesC`
(UNCONDITIONAL — lem:corner-values (i) is the corner lane's proved `corner_values_i`, grafted VERBATIM in
§0), the flat bridge CS3 → thm:uniqueness (b), the assemblies `uniquenessHypotheses_C_of`,
`thm_comparison_of`, `cor_C_inherits_of`, and the companions.

Sources (frame SM15): reference/SM/sm-5-transport.tex 461-476 (122; proof 477-505);
reference/SM/sm-6-comparison.tex 299-303 (127; proof 304-311), 313-319 (128; proof 320-372).
Dependencies (tools/claims.py): 122 ← thm:C-soft; 127 ← lem:corner-values, thm:C-S7, thm:C-soft;
128 ← thm:comparison.  Fixed target names (work/lean/axiom-policy.json): `SM.thm_comparison`,
`SM.cor_C_inherits`; hyp:R policy mode `explicit_parameter` (`SM.hyp_R : Prop`, SM/HypR.lean:83; every
consumer takes `(hR : hyp_R)`).  Proposed: `SM.prop_anchor_values : AnchorValuesData`.

§0 copies VERBATIM from work/drafts/corner/Statements_FINAL.lean: the row bundles `CS7Data` (§4),
`CSoftData` (§5) and row 105 clause (i) `corner_values_i` with its helper `cvl_embedded_of_no_crossings`
(§3, PROVED, unconditional) — TO BE UNIFIED: deleted when the corner lane's modules land (the names then
resolve to the accepted ones).  `CuspLawC`, `ReversalLawC`, `TrianglesC` are the CV/R tail's row-184 Props
(work/drafts/cvtail/Statements_FINAL.lean §5) VERBATIM — this lane OWNS row 128's bundle `CInheritsData`;
the tail's copy is to be replaced by §4's (PLAN_FINAL.md §6). -/

namespace SM

open WallGerm SoftDuplication Carrier

/-! ## §0 Interfaces of the corner lane — VERBATIM copies (TO BE UNIFIED) -/

section CornerInterfaces

open Link

variable {n : ℕ} [NeZero n]

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

/-- (corner lane, row 105 (i), PROVED, unconditional) — VERBATIM copy of
work/drafts/corner/Statements_FINAL.lean §3 (`cvl_embedded_of_no_crossings`): `m_Q = 0` ⇒ the corner
polygon is an embedded polygon in the sense of row 104. -/
theorem cvl_embedded_of_no_crossings (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (h0 : carrierCrossings hn hP S q = ∅) : Embedded (ccpCornerPolygon hn hP S q) := by
  refine ⟨fun j => ((carriers_lemma hn hP hS).corner_polygons.2.1 q j).1, ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    obtain ⟨c, hc, -⟩ := nonadjacent_meet_crossing hn hP S q hS hij hxi hxj
    rw [h0] at hc
    exact Finset.notMem_empty _ hc
  · intro i
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      exact consecutive_meet hn hP S q hS i hx hx'
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨⟨1, by norm_num, le_refl 1, (edgePoint_one _ _).symm⟩,
        ⟨0, le_refl 0, by norm_num, (edgePoint_zero _ _).symm⟩⟩

/-- (corner lane, row 105 (i), PROVED, unconditional) — VERBATIM copy of
work/drafts/corner/Statements_FINAL.lean §3 (`corner_values_i`): lem:corner-values (i), "if `Q` is uniform
and embedded (`m_Q = 0`) then `|r_Q| = 1`, `d_Q = 0` and `c(Q) = 1`". -/
theorem corner_values_i (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (_hu : CarrierUniform hn hP S q) (hm : carrierCrossingCount hn hP S q = 0) :
    |carrierRotation hn hP S q| = 1 ∧ cornerSlot hn hP S q = 0 ∧ cornerCoefficient hn hP S q hS = 1 := by
  have h0 : carrierCrossings hn hP S q = ∅ := Finset.card_eq_zero.mp hm
  have hreg : Regular (ccpCornerPolygon hn hP S q) := ccpCornerPolygon_regular hn hP hS q
  have h3 : 3 ≤ ccpCornerCount hn hP S q := (carriers_lemma hn hP hS).corner_polygons.2.2.1 q
  have hpm := (cb_embedded_rotation h3 (ccpCornerPolygon hn hP S q) hreg
    (cvl_embedded_of_no_crossings hn hP hS q h0)).pm_one
  have hrot : |carrierRotation hn hP S q| = 1 := by
    unfold carrierRotation; rcases hpm with h | h <;> rw [h] <;> simp
  have hrotZ : |carrierRotationInt hn hP S q| = 1 := by
    have := carrierRotationInt_cast hn hP hS q
    have h' : |((carrierRotationInt hn hP S q : ℤ) : ℝ)| = 1 := by rw [this]; exact hrot
    exact_mod_cast h'
  refine ⟨hrot, ?_, ?_⟩
  · simp only [cornerSlot, hm, hrotZ]; ring
  · have hslot : cornerSlot hn hP S q = 0 := by simp only [cornerSlot, hm, hrotZ]; ring
    rw [cornerCoefficient_eq_coeffAt, hslot]
    show coeffAt 0 0 (homfly _) = 1
    rw [← P_eq_homfly, P_circle (positiveLift_isCrossingFreeCircle hn hP S q hS h0), coeffAt_one]
    simp

end CornerInterfaces

/-! ## §1 The descent of `C` to the polygon space (library; helpers prefixed `cp_`).
def:C defines `C` on labelled generic tuples; sm-5/sm-6 compare it with thm:uniqueness's
`F : ∀ n [NeZero n], GenericPolygon n → ℤ`.  The descent is along def:C's cyclic quotient by the accepted
`cornerStateSum_genericShift` (SM/CChamber.lean:1362); the same construction as the accepted
`alA_polygonAmplitude` (SM/ALawful.lean).  FR-CM-5. -/

section Descent
variable {n : ℕ} [NeZero n]

theorem cp_cornerStateSum_compat (hn : 3 ≤ n) (P Q : GenericTuple n)
    (h : (genericCyclicSetoid n) P Q) :
    cornerStateSum hn P.property = cornerStateSum hn Q.property := by
  obtain ⟨k, hk⟩ : ∃ k : ZMod n, Q.val = shift k P.val := h
  have hQ : Q = genericShift k P := Subtype.ext hk
  rw [hQ]
  exact (cornerStateSum_genericShift hn k P).symm

/-- `C` on the space of generic polygons of arity `n ≥ 3` (the `Quotient.lift` of `cornerStateSum`). -/
noncomputable def cornerPolygonSum (hn : 3 ≤ n) : GenericPolygon n → ℤ :=
  Quotient.lift (s := genericCyclicSetoid n) (fun P : GenericTuple n => cornerStateSum hn P.property)
    (fun P Q h => cp_cornerStateSum_compat hn P Q h)

theorem cornerPolygonSum_projection (hn : 3 ≤ n) (P : GenericTuple n) :
    cornerPolygonSum hn (polygonProjection P) = cornerStateSum hn P.property := rfl

/-- Transport of `cornerStateSum` along an equality of tuples (proof-irrelevant witnesses). -/
theorem cp_cornerStateSum_congr (hn : 3 ≤ n) {P Q : LabelledTuple n} (h : P = Q)
    (hP : Generic P) (hQ : Generic Q) : cornerStateSum hn hP = cornerStateSum hn hQ := by
  subst h; rfl

end Descent

/-- `C` as a function on generic polygons of every arity — the object thm:uniqueness and
prop:anchor-values quantify over ("a function on generic polygons of all arities"); `0` below arity 3,
where def:C defines nothing (irrelevant: every clause quantifies `3 ≤ n`; FR-CM-5). -/
noncomputable def cornerPolygon : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ :=
  fun n _ Q => if hn : 3 ≤ n then cornerPolygonSum hn Q else 0

theorem cornerPolygon_projection {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : GenericTuple n) :
    cornerPolygon n (polygonProjection P) = cornerStateSum hn P.property := by
  simp only [cornerPolygon, hn, ↓reduceDIte, cornerPolygonSum_projection]

theorem cornerPolygon_projection' {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Generic P) : cornerPolygon n (polygonProjection ⟨P, hP⟩) = cornerStateSum hn hP :=
  cornerPolygon_projection hn ⟨P, hP⟩

/-- Chamber constancy of `cornerPolygon` (prop:C-chamber on the quotient; accepted
`prop_C_chamber.constant`, SM/CChamber.lean). -/
theorem cornerPolygon_chamber : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericPolygon n),
    Q ∈ chamber P → cornerPolygon n Q = cornerPolygon n P := by
  intro n _ hn P Q
  refine Quotient.inductionOn₂ P Q ?_
  intro P' Q' hQ
  show cornerPolygon n (polygonProjection Q') = cornerPolygon n (polygonProjection P')
  rw [cornerPolygon_projection hn, cornerPolygon_projection hn]
  exact (prop_C_chamber.constant n hn P' Q' hQ).symm

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

/-! ## §4 Row 128 cor:C-inherits (sm-6:313-372) — FIXED name `SM.cor_C_inherits` -/

/-- cor:C-inherits' cusp law (the CV/R tail's `CuspLawC`, VERBATIM): "C(P_loop) − C(P_no) = −κ C(P(0) ∖ j)"
on cor:A-lawful's domain ("when the deletion satisfies (G1)"), the deletion generic (the printed domain check
sm-6:335-359, existential), including threaded cusps (no emptiness hypothesis).  FR-CM-9. -/
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

/-- cor:A-lawful's reversal identity for `C` (the CV/R tail's `ReversalLawC`, VERBATIM;
`generic_reversal`, SM/GenericReversal.lean: reversal preserves (G1), (G2)).  FR-CM-12. -/
def ReversalLawC : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
    cornerStateSum hn ((generic_reversal P).mpr hP) = (-1) ^ n * cornerStateSum hn hP

/-- **cor:C-inherits as printed** (sm-6:313-319): "Under Hypothesis R, C satisfies every identity of
cor:A-lawful on the domains stated there, in particular the cusp law C(P_loop) − C(P_no) = −κ C(P(0)∖j)."
The accepted `ALawfulData` (SM/ALawful.lean:37-131) FIELD FOR FIELD with `cornerStateSum` for
`amplitude` (same binders, same sides, same signs; FR-CM-8), the deletions / halves / `P_ε` carrying
`Generic` witnesses because `C` is defined on generic polygons only (the printed domain checks); the
A-specific `root_independent` becomes `root_values` (`C = A` substituted into `A(P) := A_g(P)`,
FR-CM-13); the A-specific per-induced-root sub-clause of the cusp law has no `C` analogue (FR-CM-9).
`CuspLawC`, `ReversalLawC`, `TrianglesC` are the CV/R tail's Props (row 184 reads exactly these three
fields; `corner_laws_and_soft_of` needs no change). -/
structure CInheritsData : Prop where
  /-- `A(P) := A_g(P)` (any `g`) with `C = A`: `C(P) = A_g(P)` for every root `g`. -/
  root_values : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (g : ZMod n), cornerStateSum hn hP = treeCoefficient P hP.1 g hn
  /-- "well defined on generic polygons": invariance under the cyclic shift (def:C's quotient) -/
  shift_invariant : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (k : ZMod n), cornerStateSum hn ((generic_shift k P).mpr hP) = cornerStateSum hn hP
  /-- descent to the polygon space -/
  descends : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n), ∃ C' : GenericPolygon n → ℤ,
    ∀ P : GenericTuple n, C' (polygonProjection P) = cornerStateSum hn P.property
  /-- chamber constancy (prop:C-chamber), labelled and polygon-space chambers -/
  chamber_constant : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericTuple n),
    (Q ∈ labelledChamber P → cornerStateSum hn Q.property = cornerStateSum hn P.property) ∧
    (polygonProjection Q ∈ chamber (polygonProjection P) →
      cornerStateSum hn Q.property = cornerStateSum hn P.property)
  /-- silence (prop:C-silent) at simple extension and pure-cut walls -/
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
  /-- the cusp law `C(P_loop) − C(P_no) = −κ C(P(0) ∖ j)` when the deletion satisfies (G1) — with the
  deletion proved generic (sm-6:335-359), threaded cusps included -/
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
  `P_ε` generic by lem:soft-generic (i)) -/
  soft_theorem : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (j : ZMod n) (q : Plane), SoftAdmissible P j q →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ hQ : Generic (softInsertion P j q ε),
        (cornerStateSum (by omega) hQ : ℚ) = softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ)
  /-- reversal `C(P̄) = (−1)^n C(P)` -/
  reversal_law : ReversalLawC
  /-- `C(K₁) = −1` and `C(K₋₁) = +1` -/
  triangles : TrianglesC

/-! ### The cusp law — the ONE open leaf of the lane.  Prefix `cu_`. -/

/-- LEAF (unit U-CM-CUSPGEN; sm-6:335-359): at a simple cusp wall whose deletion `Q = P(0) ∖ j`
satisfies (G1), `Q` is generic.  (G2): `CuspAt` gives `A = μ_{j−1}(0)`, `M = μ_j(0)`, `B = μ_{j+1}(0)`
collinear with `M` outside `[A, B]` (`collinear_exterior_cases`, SM/CuspBetweenness.lean), so the fused
edge `[A, B]` lies in the longer of `E_{j−1}(0) = [A, M]`, `E_j(0) = [M, B]` and its relative interior in
that edge's; three pairwise remote edges of `Q` with a common relative-interior point lift injectively to
three pairwise remote edges of the centre with a common point, contrary to `Z_c = ∅`
(`concurrences = ∅`).  Frozen statement.  The domain is NOT narrowed (TARGETS: "the deletion satisfies
G1", threaded cusps included). -/
theorem cusp_deletion_generic {n : ℕ} [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hf : w.CuspAt j) (hQ1 : G1 (deleteVertex w.center j)) : Generic (deleteVertex w.center j) := by
  sorry

/-- The cusp law for `C` from `C = A` (thm:comparison) and thm:A-S4 via cor:A-lawful
(`A_lawful.cusp_law`, SM/ALawful.lean), PROVED given the domain check. -/
theorem cu_cuspLawC_of
    (hcmp : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
      cornerStateSum hn hP = amplitude P hP.1 hn) : CuspLawC := by
  intro n _ w j hf hQ1
  have hQ : Generic (deleteVertex w.center j) := cusp_deletion_generic w j hf hQ1
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

/-- **cor:C-inherits modulo rows 110, 112** (D-F11/D-F14 pattern; hyp:R an explicit parameter): every
field is the corresponding `A_lawful` field with `C = A` substituted at every argument
(`thm_comparison_of`), the deletions / halves / `P_ε` generic as checked (lem:children,
lem:soft-generic, `cusp_deletion_generic`); the vertex–edge / triple / soft fields are the accepted
C rows and the corner bundles reshaped.  PROVED modulo the leaf. -/
theorem cor_C_inherits_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) : CInheritsData := by
  have hcmp := thm_comparison_of hR h7 hs
  refine
    { root_values := ?_, shift_invariant := ?_, descends := ?_, chamber_constant := ?_, silent := ?_,
      flat_law := ?_, cusp_law := cu_cuspLawC_of hcmp, vertex_edge_law := ?_, triple_law := ?_,
      soft_theorem := ?_, reversal_law := ?_, triangles := trianglesC }
  · intro n _ hn P hP g
    rw [hcmp n hn P hP]
    exact A_lawful.root_independent n hn P hP g
  · intro n _ hn P hP k
    exact cornerStateSum_genericShift hn k ⟨P, hP⟩
  · intro n _ hn
    exact ⟨cornerPolygonSum hn, fun P => rfl⟩
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

/-! ## §5 The row theorems (UNCONDITIONAL statements; `sorry` until rows 110 thm:C-S7 and 112 thm:C-soft
land; D-F11/D-F14: declared and mapped only then).  Bodies: `anchor_values_of thm_C_soft`;
`thm_comparison_of hR thm_C_S7 thm_C_soft`; `cor_C_inherits_of hR thm_C_S7 thm_C_soft`. -/

/-- Row 122 prop:anchor-values (proposed name).  Body once row 112 lands: `anchor_values_of thm_C_soft`. -/
theorem prop_anchor_values : AnchorValuesData := by
  sorry

/-- Row 127 thm:comparison (FIXED name; hyp:R explicit).  "Assume Hypothesis R.  Then C(P) = A(P) for
every generic polygon P."  Body once rows 110/112 land: `thm_comparison_of hR thm_C_S7 thm_C_soft`. -/
theorem thm_comparison (hR : hyp_R) :
    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
      cornerStateSum hn hP = amplitude P hP.1 hn := by
  sorry

/-- Row 128 cor:C-inherits (FIXED name; hyp:R explicit).  Body once rows 110/112 land:
`cor_C_inherits_of hR thm_C_S7 thm_C_soft`. -/
theorem cor_C_inherits (hR : hyp_R) : CInheritsData := by
  sorry

/-! ## §6 Consumer and equivalence shape checks (all PROVED) -/

/-- The CV/R tail's `corner_laws_and_soft_of (hR) (h7) (hs) (hinh : CInheritsData)` reads exactly these
three fields at these types (work/drafts/cvtail/Statements_FINAL.lean:973-987): no change there. -/
example (hinh : CInheritsData) : CuspLawC ∧ ReversalLawC ∧ TrianglesC :=
  ⟨hinh.cusp_law, hinh.reversal_law, hinh.triangles⟩

/-- thm:uniqueness's hypotheses restrict to prop:anchor-values' hypotheses. -/
example (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) (hF : UniquenessHypotheses F) :
    AnchorValuesHypotheses F := hF.toAnchorValuesHypotheses

/-- FR-CM-15: the `ALawfulData`-shaped fields of `CInheritsData` are the C-row bundles (DESIGN_A's
nesting) — `triple_law` IS Hypothesis R (argument order only). -/
example (hinh : CInheritsData) : hyp_R :=
  fun n _ hn g e f k hT tp tm => hinh.triple_law n hn g e f k hT tm tp

/-- FR-CM-15: `vertex_edge_law` gives thm:C-S7's bundle (the genericity witnesses are proof-irrelevant). -/
example (hinh : CInheritsData) : CS7Data :=
  ⟨fun n _ hn g M a h _ _ tp tm => (hinh.vertex_edge_law n hn g M a h).2.2 tm tp⟩

/-- FR-CM-15: `soft_theorem` (the `∃ hQ` form of cor:A-lawful) gives thm:C-soft's bundle (`∀ hQ`). -/
example (hinh : CInheritsData) : CSoftData := by
  refine ⟨fun n _ hn P hP j q hq => ?_⟩
  obtain ⟨ε₁, hε₁, hall⟩ := hinh.soft_theorem n hn P hP j q hq
  refine ⟨ε₁, hε₁, fun ε hε hlt _ => ?_⟩
  obtain ⟨_, e⟩ := hall ε hε hlt
  exact e

/-- The row-128 bundle yields the comparison itself back (`root_values` at `g = 0`). -/
example (hinh : CInheritsData) : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Generic P), cornerStateSum hn hP = amplitude P hP.1 hn :=
  fun n _ hn P hP => hinh.root_values n hn P hP 0

end SM
