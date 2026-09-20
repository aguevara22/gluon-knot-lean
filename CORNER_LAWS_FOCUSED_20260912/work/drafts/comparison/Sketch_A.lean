import SM.Uniqueness
import SM.HypR
import SM.CSilent
import SM.CS3
import SM.CS5
import SM.AnchorsDefinition
import SM.CyclicChambers
import SM.GermSides
import SM.NamedWallPredicates
import SM.NamedWallSides
import SM.UniformDefinition
import SM.CarrierCrossings
import SM.SoftAmplitudeSectors
import SM.DeletionHalvesDefinition
import SM.FlatCarriersDefs

/-! # Sketch_A — comparison lane: rows 122 prop:anchor-values, 127 thm:comparison, 128 cor:C-inherits
(architect A, fidelity emphasis, 2026-09-15). Companion: work/drafts/comparison/DESIGN_A.md.
Check: `cd work/lean && lake env lean ../drafts/comparison/Sketch_A.lean`.

Sources (frame SM15): reference/SM/sm-5-transport.tex:461-476 (122; proof 477-501);
reference/SM/sm-6-comparison.tex:299-303 (127; proof 304-311), 313-319 (128; proof 320-368).
Fixed names (work/lean/axiom-policy.json): `SM.thm_comparison`, `SM.cor_C_inherits`. Proposed:
`SM.prop_anchor_values : AnchorValuesData`. hyp:R policy mode `explicit_parameter`: `(hR : hyp_R)`.

§0 copies the corner lane's FINAL bundles `CornerValuesData`, `CS7Data`, `CSoftData` VERBATIM
(work/drafts/corner/Statements_FINAL.lean §3-§5) — TO BE UNIFIED (deleted when SM/CornerValues,
SM/CS7, SM/CSoft land) — and the CV/R tail's row-184 Props `CuspLawC`, `ReversalLawC`, `TrianglesC`
(work/drafts/cvtail/Statements_FINAL.lean §5) — TO BE UNIFIED (this lane ADOPTS them; §4 adopts
`CInheritsData` with one added field `root_values`, see DESIGN_A.md §3).

Every `sorry` is a LEAF of DESIGN_A.md §4 (frozen statement) or one of the three ROW THEOREMS of §5
(one-liners once rows 105/110/112 land; D-F11/D-F14: declared and mapped only then). Everything else
is PROVED from accepted declarations. -/

namespace SM

open WallGerm SoftDuplication Carrier

/-! ## §0 Interfaces copied VERBATIM — TO BE UNIFIED -/

section CornerInterfaces
variable {n : ℕ} [NeZero n]

/-- VERBATIM corner/Statements_FINAL.lean §3 — TO BE UNIFIED. -/
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

/-- VERBATIM corner/Statements_FINAL.lean §4 — TO BE UNIFIED (fixed name `SM.thm_C_S7 : CS7Data`). -/
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

/-- VERBATIM corner/Statements_FINAL.lean §5 — TO BE UNIFIED (fixed name `SM.thm_C_soft : CSoftData`). -/
structure CSoftData : Prop where
  soft_theorem : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (j : ZMod n) (q : Plane), SoftAdmissible P j q →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
      (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
        softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ)

end CornerInterfaces

/-- VERBATIM cvtail/Statements_FINAL.lean §5 — TO BE UNIFIED (adopted by this lane, FR-CM-13). -/
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

/-- VERBATIM cvtail/Statements_FINAL.lean §5 — TO BE UNIFIED (adopted). -/
def ReversalLawC : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
    cornerStateSum hn ((generic_reversal P).mpr hP) = (-1) ^ n * cornerStateSum hn hP

/-- VERBATIM cvtail/Statements_FINAL.lean §5 — TO BE UNIFIED (adopted). -/
def TrianglesC : Prop :=
  cornerStateSum (by norm_num) (star_generic_law le_rfl).1.2.2.2.1 = -1 ∧
  cornerStateSum (by norm_num) (star_generic_law le_rfl).1.2.2.2.2.1 = 1

/-! ## §1 The descent of `C` to the polygon space (library; prefix `cmp_`).
def:C defines `C` on labelled generic polygons; the rows of sm-5/sm-6 read functions "on generic
polygons" as `∀ n [NeZero n], GenericPolygon n → ℤ` (thm:uniqueness, accepted). The descent is by
the accepted shift invariance `cornerStateSum_genericShift` (prop:C-chamber's module, def:C row). -/

section Descent
variable {n : ℕ} [NeZero n]

theorem cmp_cornerStateSum_compat (hn : 3 ≤ n) (P Q : GenericTuple n)
    (h : (genericCyclicSetoid n) P Q) :
    cornerStateSum hn P.property = cornerStateSum hn Q.property := by
  obtain ⟨k, hk⟩ : ∃ k : ZMod n, Q.val = shift k P.val := h
  have hQ : Q = genericShift k P := Subtype.ext hk
  rw [hQ]
  exact (cornerStateSum_genericShift hn k P).symm

/-- `C` on the space of generic polygons (arity `n ≥ 3`). -/
noncomputable def cmp_polygonSum (hn : 3 ≤ n) : GenericPolygon n → ℤ :=
  Quotient.lift (s := genericCyclicSetoid n) (fun P : GenericTuple n => cornerStateSum hn P.property)
    (fun P Q h => cmp_cornerStateSum_compat hn P Q h)

theorem cmp_polygonSum_projection (hn : 3 ≤ n) (P : GenericTuple n) :
    cmp_polygonSum hn (polygonProjection P) = cornerStateSum hn P.property := rfl

end Descent

/-- `C` as a function on generic polygons of every arity (the object of thm:uniqueness and of
prop:anchor-values' "function on generic polygons of all arities"); `0` below arity 3, where def:C
defines nothing (the same convention as the accepted thm:uniqueness' `F`, unconstrained there). -/
noncomputable def cmp_C : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ :=
  fun n _ Q => if hn : 3 ≤ n then cmp_polygonSum hn Q else 0

theorem cmp_C_projection {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : GenericTuple n) :
    cmp_C n (polygonProjection P) = cornerStateSum hn P.property := by
  simp only [cmp_C, dif_pos hn, cmp_polygonSum_projection]

theorem cmp_C_projection' {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) :
    cmp_C n (polygonProjection ⟨P, hP⟩) = cornerStateSum hn hP :=
  cmp_C_projection hn ⟨P, hP⟩

/-! ## §2 Row 122 prop:anchor-values (sm-5:461-476) — proposed name `SM.prop_anchor_values` -/

/-- The two hypotheses of prop:anchor-values on a function `F` on generic polygons of all arities:
"constant on chambers" (thm:uniqueness (a), first half, `UniquenessHypotheses.chamber` verbatim) and
"satisfying the soft theorem in the form of thm:C-soft at every admissible soft insertion into a
generic polygon" (thm:uniqueness (e), `UniquenessHypotheses.soft` verbatim = `CSoftData.soft_theorem`
with `F` for `C`; FR-CM-1, FR-CM-2). -/
structure AnchorValuesHypotheses (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) : Prop where
  chamber : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericPolygon n),
    Q ∈ chamber P → F n Q = F n P
  soft : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (j : ZMod n) (q : Plane), SoftAdmissible P j q →
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ∀ hQ : Generic (softInsertion P j q ε),
      (F (n + 1) (polygonProjection ⟨softInsertion P j q ε, hQ⟩) : ℚ) =
        softAmplitudeMultiplier P j q * (F n (polygonProjection ⟨P, hP⟩) : ℚ)

/-- thm:uniqueness' hypotheses contain prop:anchor-values' (sanity; the consumer thm:uniqueness cites
(a) and (e) exactly). -/
theorem AnchorValuesHypotheses.of_uniqueness {F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ}
    (hF : UniquenessHypotheses F) : AnchorValuesHypotheses F :=
  ⟨hF.chamber, hF.soft⟩

/-- **prop:anchor-values as printed**, one field per printed clause (FR-CM-1..7).
Anchors are the accepted structures of def:anchors (`ZeroAnchor`, `LoopAnchor`, `LoopAnchorZero`);
`Z = Y = A.polygon = P^{(j,q)}_ε` at the anchor's OWN parameter `A.param < A.bound = ε₀`; the parent
`P = A.parent`, the insertion vertex `j = A.vertex`, `τ_j(P) = turn A.parent A.vertex`. -/
structure AnchorValuesData : Prop where
  /-- "F(Z) = 0 for every zero anchor" (case (Z), mixed sector). -/
  zero : ∀ (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ), AnchorValuesHypotheses F →
    ∀ (m : ℕ) [NeZero m] (r : ℤ) (A : ZeroAnchor m r),
      F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) = 0
  /-- "F(Y) = τ_j(P) F(P) for every loop anchor" — case (L). -/
  loop : ∀ (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ), AnchorValuesHypotheses F →
    ∀ (m : ℕ) [NeZero m] (r : ℤ) (A : LoopAnchor m r),
      F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) =
        ((turn A.parent A.vertex : SignType) : ℤ) *
          F m (polygonProjection ⟨A.parent, A.parent_generic⟩)
  /-- "F(Y) = τ_j(P) F(P) for every loop anchor" — case (L₀). -/
  loop_triangle : ∀ (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ), AnchorValuesHypotheses F →
    ∀ (m : ℕ) [NeZero m] (A : LoopAnchorZero m),
      F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) =
        ((turn A.parent A.vertex : SignType) : ℤ) *
          F m (polygonProjection ⟨A.parent, A.parent_generic⟩)
  /-- "In case (L), τ_j(P) = −sgn(r)". -/
  loop_turn : ∀ (m : ℕ) [NeZero m] (r : ℤ) (A : LoopAnchor m r),
    turn A.parent A.vertex = -SignType.sign r
  /-- "in case (L₀), it is the orientation sign of the parent triangle": the common turn sign of the
  generic triangle (lem:chi-basic (i) / lem:A-small-values (i)), which is its rotation number (lem:rot;
  FR-CM-5). -/
  loop_triangle_turn : ∀ (m : ℕ) [NeZero m] (A : LoopAnchorZero m),
    turn A.parent A.vertex ≠ 0 ∧ (∀ i, turn A.parent i = turn A.parent A.vertex) ∧
      rotationNumber A.parent = ((turn A.parent A.vertex : SignType) : ℤ)
  /-- "The function C satisfies these hypotheses" — `C` read on the polygon space through its
  cyclic descent `cmp_C` (FR-CM-6): prop:C-chamber and thm:C-soft. -/
  C_hypotheses : AnchorValuesHypotheses cmp_C
  /-- "The same identities hold for A_g at every anchor root other than the soft edge, with the
  corresponding parent root used on the right-hand side" — zero anchors (FR-CM-7). -/
  A_zero : ∀ (m : ℕ) [NeZero m] (r : ℤ) (A : ZeroAnchor m r) (a : ZMod (m + 1)),
    a ≠ A.softEdge →
      treeCoefficient A.polygon A.polygon_generic.1 a (by have := A.parent_card; omega) = 0
  /-- — loop anchors (L): the anchor root `a ≠ E_j` corresponds to the unique parent root `g` with
  `a = softParentEdge j g` (thm:A-soft's correspondence, the return edge ↔ `E_j`). -/
  A_loop : ∀ (m : ℕ) [NeZero m] (r : ℤ) (A : LoopAnchor m r) (a : ZMod (m + 1)),
    a ≠ A.softEdge → ∃! g : ZMod m, a = softParentEdge A.vertex g ∧
      treeCoefficient A.polygon A.polygon_generic.1 a (by have := A.parent_card; omega) =
        ((turn A.parent A.vertex : SignType) : ℤ) *
          treeCoefficient A.parent A.parent_generic.1 g A.parent_card
  /-- — loop anchors (L₀). -/
  A_loop_triangle : ∀ (m : ℕ) [NeZero m] (A : LoopAnchorZero m) (a : ZMod (m + 1)),
    a ≠ A.softEdge → ∃! g : ZMod m, a = softParentEdge A.vertex g ∧
      treeCoefficient A.polygon A.polygon_generic.1 a (by have := A.parent_card; omega) =
        ((turn A.parent A.vertex : SignType) : ℤ) *
          treeCoefficient A.parent A.parent_generic.1 g A.parent_card

/-! ### Leaves and proofs of §2 (prefix `av_`) -/

section AnchorValuesProofs
variable {m : ℕ} [NeZero m]

/-- The printed proof (sm-5:477-490) for an arbitrary soft anchor: `F(P_ε) = ((χ₋+χ₊)/2) F(P)` at the
anchor's own parameter, by the function's threshold `δ_F`, a smaller parameter `ε' < min ε δ_F`,
chamber constancy along `(0, ε₀)` (`bound_spec`) and the soft theorem at `ε'`. (The `F`-half of the
accepted `unA_softAnchor_delta`, SM/Uniqueness.lean.) PROVED. -/
theorem av_softAnchor_value (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : AnchorValuesHypotheses F) (A : SoftAnchorData m) :
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
    {r : ℤ} (A : ZeroAnchor m r) :
    F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) = 0 := by
  have h := av_softAnchor_value F hF A.toSoftAnchorData
  rw [softAmplitudeMultiplier_mixed _ _ _ A.admissible A.mixed, zero_mul] at h
  exact_mod_cast h

theorem av_loop_of_sector (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ)
    (hF : AnchorValuesHypotheses F) (A : SoftAnchorData m)
    (hloop : softAttachmentMinus A.parent A.vertex A.vector = turn A.parent A.vertex ∧
      softAttachmentPlus A.parent A.vertex A.vector = turn A.parent A.vertex) :
    F (m + 1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) =
      ((turn A.parent A.vertex : SignType) : ℤ) *
        F m (polygonProjection ⟨A.parent, A.parent_generic⟩) := by
  have h := av_softAnchor_value F hF A
  rw [softAmplitudeMultiplier_loop _ _ _ hloop] at h
  exact_mod_cast h

/-- The rooted clause for a soft anchor in a given sector (thm:A-soft at a smaller parameter and
prop:A-chamber's labelled-chamber constancy at the fixed root `a`, sm-5:492-501). PROVED. -/
theorem av_rooted (A : SoftAnchorData m) (a : ZMod (m + 1)) (ha : a ≠ A.softEdge) :
    ∃! g : ZMod m, a = softParentEdge A.vertex g ∧
      (treeCoefficient A.polygon A.polygon_generic.1 a (by have := A.parent_card; omega) : ℚ) =
        softAmplitudeMultiplier A.parent A.vertex A.vector *
          (treeCoefficient A.parent A.parent_generic.1 g A.parent_card : ℚ) := by
  have hm := A.parent_card
  have hm1 : 3 ≤ m + 1 := by omega
  obtain ⟨ε₁, hε₁, -, hlaw⟩ := soft_theorem_treeCoefficient hm A.parent_generic A.vertex A.vector
    A.admissible A.bound A.bound_pos
  obtain ⟨ε', hε'pos, hε'param, hε'ε₁⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' < A.param ∧ ε' < ε₁ := by
    have hmin : 0 < min A.param ε₁ := lt_min A.param_pos hε₁
    have h1 : min A.param ε₁ ≤ A.param := min_le_left _ _
    have h2 : min A.param ε₁ ≤ ε₁ := min_le_right _ _
    exact ⟨min A.param ε₁ / 2, by linarith, by linarith, by linarith⟩
  have hε'bound : ε' < A.bound := hε'param.trans A.param_lt
  obtain ⟨B, hB⟩ := A.bound_spec
  obtain ⟨hQ', hch', -⟩ := hB ε' hε'pos hε'bound
  obtain ⟨hQ, hch, -⟩ := hB A.param A.param_pos A.param_lt
  obtain ⟨hQ'', hall⟩ := hlaw ε' hε'pos hε'ε₁
  have ha' : a ≠ softOldIndex A.vertex A.vertex := ha
  obtain ⟨g, ⟨hag, heq, -, -, -⟩, -⟩ := hall a ha'
  -- prop:A-chamber at the fixed root `a`: both members of the family lie in the labelled chamber of `B`
  have h1 := ((A_chamber hm1).2.1 B ⟨_, hQ'⟩ hch' a).2.2
  have h2 := ((A_chamber hm1).2.1 B ⟨_, hQ⟩ hch a).2.2
  have hval : treeCoefficient A.polygon A.polygon_generic.1 a hm1 =
      treeCoefficient (softInsertion A.parent A.vertex A.vector ε') hQ''.1 a hm1 := by
    show treeCoefficient (softInsertion A.parent A.vertex A.vector A.param) _ a hm1 = _
    rw [← h2, h1]
  refine ⟨g, ⟨hag, ?_⟩, fun g' hg' => ?_⟩
  · rw [hval]; exact heq
  · exact (softParentEdge_injective A.vertex (hag.symm.trans hg'.1)).symm

theorem av_A_zero {r : ℤ} (A : ZeroAnchor m r) (a : ZMod (m + 1)) (ha : a ≠ A.softEdge) :
    treeCoefficient A.polygon A.polygon_generic.1 a (by have := A.parent_card; omega) = 0 := by
  obtain ⟨g, ⟨-, hg⟩, -⟩ := av_rooted A.toSoftAnchorData a ha
  rw [softAmplitudeMultiplier_mixed _ _ _ A.admissible A.mixed, zero_mul] at hg
  exact_mod_cast hg

theorem av_A_loop_of_sector (A : SoftAnchorData m)
    (hloop : softAttachmentMinus A.parent A.vertex A.vector = turn A.parent A.vertex ∧
      softAttachmentPlus A.parent A.vertex A.vector = turn A.parent A.vertex)
    (a : ZMod (m + 1)) (ha : a ≠ A.softEdge) :
    ∃! g : ZMod m, a = softParentEdge A.vertex g ∧
      treeCoefficient A.polygon A.polygon_generic.1 a (by have := A.parent_card; omega) =
        ((turn A.parent A.vertex : SignType) : ℤ) *
          treeCoefficient A.parent A.parent_generic.1 g A.parent_card := by
  obtain ⟨g, ⟨hag, hg⟩, huniq⟩ := av_rooted A a ha
  refine ⟨g, ⟨hag, ?_⟩, fun g' hg' => huniq g' ⟨hg'.1, ?_⟩⟩
  · rw [softAmplitudeMultiplier_loop _ _ _ hloop] at hg
    exact_mod_cast hg
  · rw [softAmplitudeMultiplier_loop _ _ _ hloop]
    exact_mod_cast hg'.2

/-- (L₀): the parent is a generic triangle; its turns share one nonzero sign, equal to its rotation
number (lem:A-small-values (i), lem:rot). PROVED. -/
theorem av_loop_triangle_turn (A : LoopAnchorZero m) :
    turn A.parent A.vertex ≠ 0 ∧ (∀ i, turn A.parent i = turn A.parent A.vertex) ∧
      rotationNumber A.parent = ((turn A.parent A.vertex : SignType) : ℤ) := by
  have h3 := A.triangle
  subst h3
  obtain ⟨τ, hτ, hall, -⟩ := A_small_values_i A.parent A.parent_generic.1
  refine ⟨by rw [hall]; exact hτ, fun i => by rw [hall i, hall A.vertex], ?_⟩
  have hreg : Regular A.parent := generic_regular le_rfl A.parent_generic
  rw [(rotationNumber_triangle hreg).1 A.vertex]
  simp

/-- "C satisfies these hypotheses": chamber constancy is prop:C-chamber (accepted), PROVED here; the
soft theorem is thm:C-soft — explicit hypothesis `hs : CSoftData` (D-F11/D-F14). -/
theorem av_C_chamber : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericPolygon n),
    Q ∈ chamber P → cmp_C n Q = cmp_C n P := by
  intro n _ hn P Q
  refine Quotient.inductionOn₂ P Q ?_
  intro P' Q' h
  have hc : cornerStateSum hn P'.property = cornerStateSum hn Q'.property :=
    prop_C_chamber.constant n hn P' Q' h
  show cmp_C n (polygonProjection Q') = cmp_C n (polygonProjection P')
  rw [cmp_C_projection hn, cmp_C_projection hn, hc]

theorem av_C_hypotheses_of (hs : CSoftData) : AnchorValuesHypotheses cmp_C where
  chamber := av_C_chamber
  soft := by
    intro n _ hn P hP j q hq
    obtain ⟨ε₁, hε₁, hall⟩ := hs.soft_theorem n hn P hP j q hq
    refine ⟨ε₁, hε₁, fun ε hε hlt hQ => ?_⟩
    rw [cmp_C_projection' (by omega) _ hQ, cmp_C_projection' hn P hP]
    exact hall ε hε hlt hQ

end AnchorValuesProofs

/-- **Row 122, conditional on thm:C-soft** (library, D-F11/D-F14 pattern; never mapped). Every clause
but `C_hypotheses.soft` is unconditional. -/
theorem anchor_values_of (hs : CSoftData) : AnchorValuesData where
  zero := fun F hF _ _ _ A => av_zero F hF A
  loop := fun F hF _ _ _ A => av_loop_of_sector F hF A.toSoftAnchorData A.loop
  loop_triangle := fun F hF _ _ A => av_loop_of_sector F hF A.toSoftAnchorData A.loop
  loop_turn := fun _ _ _ A => A.parent_turn
  loop_triangle_turn := fun _ _ A => av_loop_triangle_turn A
  C_hypotheses := av_C_hypotheses_of hs
  A_zero := fun _ _ _ A a ha => av_A_zero A a ha
  A_loop := fun _ _ _ A a ha => av_A_loop_of_sector A.toSoftAnchorData A.loop a ha
  A_loop_triangle := fun _ _ A a ha => av_A_loop_of_sector A.toSoftAnchorData A.loop a ha

/-- Companion: the values of `C` at the anchors (the printed "The function C satisfies these
hypotheses" made explicit), labelled form. -/
theorem AnchorValuesData.C_zero (hD : AnchorValuesData) {m : ℕ} [NeZero m] {r : ℤ}
    (A : ZeroAnchor m r) :
    cornerStateSum (by have := A.parent_card; omega) A.polygon_generic = 0 := by
  have h := hD.zero cmp_C hD.C_hypotheses m r A
  rwa [cmp_C_projection' (by have := A.parent_card; omega)] at h

theorem AnchorValuesData.C_loop (hD : AnchorValuesData) {m : ℕ} [NeZero m] {r : ℤ}
    (A : LoopAnchor m r) :
    cornerStateSum (by have := A.parent_card; omega) A.polygon_generic =
      ((turn A.parent A.vertex : SignType) : ℤ) * cornerStateSum A.parent_card A.parent_generic := by
  have h := hD.loop cmp_C hD.C_hypotheses m r A
  rwa [cmp_C_projection' (by have := A.parent_card; omega), cmp_C_projection' A.parent_card] at h

/-! ## §3 Row 127 thm:comparison (sm-6:299-303) — FIXED name `SM.thm_comparison` -/

section Comparison
variable {n : ℕ} [NeZero n]

/-- Transport of `cornerStateSum` along an equality of tuples (proof-irrelevant witnesses). -/
theorem cmp_congr {P Q : LabelledTuple n} (hPQ : P = Q) (hn : 3 ≤ n) (hP : Generic P)
    (hQ : Generic Q) : cornerStateSum hn hP = cornerStateSum hn hQ := by
  subst hPQ; rfl

/-- LEAF (unit U-CM-TRI): `C` of a generic triangle is minus its common turn sign — the printed (f)
sentence "Its only decomposition is empty, so def:C gives −1 when ℓ = 3 and +1 when ℓ = 0" together
with lem:corner-values (i) (corner coefficient 1 of the embedded uniform carrier). The 3-gon has no
remote edge pair, hence no crossing; `Ind(G_P) = {∅}`; the single carrier of `∅` (lem:carriers (ii),
`component_card_independent`) has `m_Q = 0` and is uniform. Frozen statement. -/
theorem cmp_triangle_value (hCV : CornerValuesData) (T : LabelledTuple 3) (hT : Generic T)
    (τ : SignType) (hτ : ∀ i, turn T i = τ) :
    cornerStateSum (by norm_num) hT = -(τ : ℤ) := by
  sorry

/-- (f) for `C`: `C(K₁) = −1`, `C(K₋₁) = +1` (from the leaf and lem:star-generic's turns). PROVED
modulo the leaf. -/
theorem cmp_triangles (hCV : CornerValuesData) : TrianglesC := by
  refine ⟨?_, ?_⟩
  · have h := cmp_triangle_value hCV (star 1) (star_generic_law le_rfl).1.2.2.2.1 1
      (star_generic_law le_rfl).1.2.1.2.2.2.1
    simpa using h
  · have h := cmp_triangle_value hCV (starNeg 1) (star_generic_law le_rfl).1.2.2.2.2.1 (-1)
      (star_generic_law le_rfl).1.2.2.2.2.2.1
    simpa using h

/-- Every punctured parameter of a wall germ is a side parameter of one of the two sides
(`ri_sideTuple_true_val` / `ri_sideTuple_false_val`, accepted). -/
theorem cmp_side_repr (w : WallGerm n) (s : w.Parameter) (hs : s.val ≠ 0) :
    ∃ (b : Bool) (t : w.SideParameter), (w.sideTuple b t).val = w.curve s := by
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · exact ⟨false, ⟨-s.val, by linarith, by linarith [s.property.1]⟩, w.ri_sideTuple_false_val s hneg⟩
  · exact ⟨true, ⟨s.val, hpos, s.property.2⟩, w.ri_sideTuple_true_val s hpos⟩

/-- thm:C-S3's flat law (`CS3Data.flat_law`: sides named by the turn at `j`
at side parameters below its radius `δ`) in the all-parameters shape of thm:uniqueness (b) — the side
values are moved to small parameters by prop:C-chamber's side constancy (`cornerStateSum_side_eq`,
SM/HypR.lean) and the sides are identified by `flat_named_sides` (lem:flat-sides); the deletion's
genericity witness is quantified (FR-CM-11). PROVED. -/
theorem cmp_flat_bridge (w : WallGerm (n + 1)) (j : ZMod (n + 1)) (hf : w.FlatAt j)
    (hdel : Generic (deleteVertex w.center j))
    (sRight sLeft : w.Parameter) (hRight0 : sRight.val ≠ 0) (hLeft0 : sLeft.val ≠ 0)
    (hR : turn (w.curve sRight) j = -1) (hL : turn (w.curve sLeft) j = 1) :
    cornerStateSum (by have := hf.1; omega) (w.generic_punctured sRight hRight0) -
      cornerStateSum (by have := hf.1; omega) (w.generic_punctured sLeft hLeft0) =
      cornerStateSum (by have := hf.1; omega) hdel := by
  have hn : 3 ≤ n := by have := hf.1; omega
  have hn1 : 3 ≤ n + 1 := by omega
  obtain ⟨δ, hδ, hδr, hlaw⟩ := thm_C_S3.flat_law n hn w j hf.2.1 hf.2.2.2.1 hf.2.2.1 hf.2.2.2.2
  obtain ⟨bR, tR, eR⟩ := cmp_side_repr w sRight hRight0
  obtain ⟨bL, tL, eL⟩ := cmp_side_repr w sLeft hLeft0
  let t0 : w.SideParameter := ⟨δ / 2, by constructor <;> linarith [w.radius_pos]⟩
  have ht0 : t0.val < δ := by show δ / 2 < δ; linarith
  have hRside : IsRightSide w j bR t0 := by
    show turn (w.sideTuple bR t0).val j = -1
    rw [side_turn_constant w bR t0 tR j, eR]; exact hR
  have hLside : IsLeftSide w j bL t0 := by
    show turn (w.sideTuple bL t0).val j = 1
    rw [side_turn_constant w bL t0 tL j, eL]; exact hL
  have key := hlaw bR bL t0 t0 ht0 ht0 hRside hLside
  have e1 : cornerStateSum hn1 (w.generic_punctured sRight hRight0) =
      cornerStateSum hn1 (w.sideTuple bR t0).property := by
    rw [cmp_congr eR.symm hn1 _ (w.sideTuple bR tR).property]
    exact cornerStateSum_side_eq hn1 w bR tR t0
  have e2 : cornerStateSum hn1 (w.generic_punctured sLeft hLeft0) =
      cornerStateSum hn1 (w.sideTuple bL t0).property := by
    rw [cmp_congr eL.symm hn1 _ (w.sideTuple bL tL).property]
    exact cornerStateSum_side_eq hn1 w bL tL t0
  rw [e1, e2]
  exact key

end Comparison

/-- **thm:uniqueness (a)–(f) for `C`** from the accepted C-rows and the explicit corner bundles:
(a) prop:C-chamber, prop:C-silent; (b) thm:C-S3 (through `cmp_flat_bridge`); (c) thm:C-S7 (`h7`);
(d) Hypothesis R (`hR`); (e) thm:C-soft (`hs`); (f) lem:corner-values (i) (`hCV`, through
`cmp_triangle_value`). PROVED modulo the two leaves. -/
theorem cmp_uniqueness_hypotheses_of (hCV : CornerValuesData) (h7 : CS7Data) (hs : CSoftData)
    (hR : hyp_R) : UniquenessHypotheses cmp_C where
  chamber := av_C_chamber
  silent := by
    intro n _ hn w
    refine ⟨fun M a hE s t => ?_, fun i j k hC s t => ?_⟩
    · rw [cmp_C_projection hn, cmp_C_projection hn]
      exact prop_C_silent.extension n hn w M a hE t s
    · rw [cmp_C_projection hn, cmp_C_projection hn]
      exact prop_C_silent.cut n hn w i j k hC t s
  flat := by
    intro n _ w j hf hdel sRight sLeft hRight0 hLeft0 hR' hL'
    have hn : 3 ≤ n := by have := hf.1; omega
    rw [cmp_C_projection' (by omega), cmp_C_projection' (by omega), cmp_C_projection' hn]
    exact cmp_flat_bridge w j hf hdel sRight sLeft hRight0 hLeft0 hR' hL'
  vertex_edge := by
    intro n _ hn w M a hc h₁ h₂ s t
    rw [cmp_C_projection hn, cmp_C_projection hn,
      cmp_C_projection' (contactHalfSizes_bounds hn hc.1).1.1,
      cmp_C_projection' (contactHalfSizes_bounds hn hc.1).2.1]
    exact h7.vertex_edge_law n hn w M a hc h₁ h₂ t s
  triple := by
    intro n _ hn w e f k hT s t
    rw [cmp_C_projection hn, cmp_C_projection hn]
    exact hR n hn w e f k hT t s
  soft := (av_C_hypotheses_of hs).soft
  triangles := by
    obtain ⟨h1, h2⟩ := cmp_triangles hCV
    exact ⟨by rw [cmp_C_projection (by norm_num)]; exact h1,
      by rw [cmp_C_projection (by norm_num)]; exact h2⟩

/-- **Row 127, conditional on lem:corner-values, thm:C-S7, thm:C-soft** (library, D-F11/D-F14
pattern; the printed dependency list of thm:comparison): "Assume Hypothesis R. Then C(P) = A(P) for
every generic polygon P" — with `hR : hyp_R` an explicit parameter (policy `explicit_parameter`),
`A(P) = amplitude P hP.1 hn` (cor:A-lawful's `A(P) := A_g(P)`, root 0), every arity `n ≥ 3`, every
generic labelled tuple (FR-CM-8, FR-CM-9). PROVED modulo the leaves: `SM.uniqueness` at `cmp_C`. -/
theorem thm_comparison_of (hCV : CornerValuesData) (h7 : CS7Data) (hs : CSoftData) (hR : hyp_R) :
    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
      cornerStateSum hn hP = amplitude P hP.1 hn := by
  intro n _ hn P hP
  have h := uniqueness cmp_C (cmp_uniqueness_hypotheses_of hCV h7 hs hR) n hn P hP
  rwa [cmp_C_projection' hn P hP] at h

/-- Companion (FR-CM-9): `C(P) = A_g(P)` for every root `g` (thm:root-indep-proof). -/
theorem thm_comparison_root_of (hCV : CornerValuesData) (h7 : CS7Data) (hs : CSoftData)
    (hR : hyp_R) {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (g : ZMod n) : cornerStateSum hn hP = treeCoefficient P hP.1 g hn := by
  rw [thm_comparison_of hCV h7 hs hR n hn P hP]
  exact A_lawful.root_independent n hn P hP g

/-- Companion (FR-CM-9): the polygon-level form `C = A` on the space of generic polygons. -/
theorem thm_comparison_polygon_of (hCV : CornerValuesData) (h7 : CS7Data) (hs : CSoftData)
    (hR : hyp_R) {n : ℕ} [NeZero n] (hn : 3 ≤ n) (Q : GenericPolygon n) :
    cmp_polygonSum hn Q = alA_polygonAmplitude hn Q := by
  refine Quotient.inductionOn Q ?_
  intro P
  show cmp_polygonSum hn (polygonProjection P) = alA_polygonAmplitude hn (polygonProjection P)
  rw [cmp_polygonSum_projection, alA_polygonAmplitude_projection]
  exact thm_comparison_of hCV h7 hs hR n hn P.val P.property

/-! ## §4 Row 128 cor:C-inherits (sm-6:313-319) — FIXED name `SM.cor_C_inherits` -/

/-- **cor:C-inherits as printed**: "Under Hypothesis R, C satisfies every identity of cor:A-lawful on
the domains stated there, in particular the cusp law C(P_loop) − C(P_no) = −κ C(P(0)∖j)." One field per
field of the accepted `ALawfulData` (SM/ALawful.lean) with `cornerStateSum` for `amplitude`
(FR-CM-12); ADOPTED from the CV/R tail's proposal (cvtail/Statements_FINAL.lean §5) with ONE added
field `root_values` (the substitution of `C = A` into cor:A-lawful's defining clause `A(P) := A_g(P)`,
any `g`). The vertex–edge, triple and soft fields are the C-row bundles themselves (`CS7Data`, `hyp_R`,
`CSoftData`; FR-CM-14); the cusp law asserts the deletion's genericity (the printed domain check,
FR-CM-13). Row 184's `corner_laws_and_soft_of` reads `.cusp_law`, `.reversal_law`, `.triangles` and needs
no change. -/
structure CInheritsData : Prop where
  /-- `A(P) := A_g(P)` (any `g`) with `C = A`: `C(P) = A_g(P)` for every root `g`. -/
  root_values : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (g : ZMod n), cornerStateSum hn hP = treeCoefficient P hP.1 g hn
  /-- cyclic invariance: `C` is a function of the polygon (def:C's `cornerStateSum_shift`). -/
  shift_invariant : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (k : ZMod n), cornerStateSum hn ((generic_shift k P).mpr hP) = cornerStateSum hn hP
  /-- `C` descends to the polygon space. -/
  descends : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n), ∃ C' : GenericPolygon n → ℤ,
    ∀ P : GenericTuple n, C' (polygonProjection P) = cornerStateSum hn P.property
  /-- chamber constancy (labelled and polygon-space chambers). -/
  chamber_constant : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericTuple n),
    (Q ∈ labelledChamber P → cornerStateSum hn Q.property = cornerStateSum hn P.property) ∧
    (polygonProjection Q ∈ chamber (polygonProjection P) →
      cornerStateSum hn Q.property = cornerStateSum hn P.property)
  /-- silence at simple extension and pure-cut walls. -/
  silent : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (w : WallGerm n),
    (∀ M a : ZMod n, w.ExtensionAt M a → ∀ s t : w.SideParameter,
      cornerStateSum hn (w.sideTuple true t).property = cornerStateSum hn (w.sideTuple false s).property) ∧
    (∀ i j k : ZMod n, w.PureCutAt i j k → ∀ s t : w.SideParameter,
      cornerStateSum hn (w.sideTuple true t).property = cornerStateSum hn (w.sideTuple false s).property)
  /-- the flat law `C(P_right) − C(P_left) = C(P(0)∖j)`, the deletion generic (lem:children (i)). -/
  flat_law : ∀ (n : ℕ) [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1)) (hf : w.FlatAt j),
    ∃ hQ : Generic (deleteVertex w.center j),
    ∀ (sRight sLeft : w.Parameter) (hRight0 : sRight.val ≠ 0) (hLeft0 : sLeft.val ≠ 0),
      turn (w.curve sRight) j = -1 → turn (w.curve sLeft) j = 1 →
      cornerStateSum (by have := hf.1; omega) (w.generic_punctured sRight hRight0) -
        cornerStateSum (by have := hf.1; omega) (w.generic_punctured sLeft hLeft0) =
        cornerStateSum (by have := hf.1; omega) hQ
  /-- the cusp law `C(P_loop) − C(P_no) = −κ C(P(0)∖j)` when the deletion satisfies (G1) — with the
  deletion proved generic (sm-6:335-359), threaded cusps included. -/
  cusp_law : CuspLawC
  /-- the vertex–edge law `C(P₊) − C(P₋) = s C(λ₁) C(λ₂)`, both branches (thm:C-S7's bundle). -/
  vertex_edge_law : CS7Data
  /-- the triple law `C(P₊) = C(P₋)` — Hypothesis R itself. -/
  triple_law : hyp_R
  /-- the soft theorem in every sector (thm:C-soft's bundle). -/
  soft_theorem : CSoftData
  /-- reversal `C(P̄) = (−1)^n C(P)`. -/
  reversal_law : ReversalLawC
  /-- `C(K₁) = −1`, `C(K₋₁) = +1`. -/
  triangles : TrianglesC

/-- LEAF (unit U-CM-CUSPGEN): the printed domain check of cor:C-inherits (sm-6:335-359): at a simple
cusp wall the deletion `P(0)∖j`, if it satisfies (G1), is generic — its (G2) from `Z_c = ∅` of
def:walls (K): three pairwise remote edges of `Q` with a common interior point lift injectively (the
fused edge `[A,B]` to the longer of `E_{j−1}(0)`, `E_j(0)`, which contains it since `M` lies outside
`[A,B]`) to three pairwise remote edges of the centre with a common interior point. Frozen statement.
RISKIEST step of the lane. -/
theorem cmp_cusp_deletion_generic {n : ℕ} [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hf : w.CuspAt j) (hG1 : G1 (deleteVertex w.center j)) : Generic (deleteVertex w.center j) := by
  sorry

/-- **Row 128, conditional on lem:corner-values, thm:C-S7, thm:C-soft** (library, D-F11/D-F14): every
field is the corresponding `A_lawful` field with `C = A` substituted at every argument
(`thm_comparison_of`), the deletions/halves generic as checked (lem:children; `cmp_cusp_deletion_generic`
for the cusp); the vertex–edge/triple/soft fields are the C rows themselves. PROVED modulo the leaves. -/
theorem cor_C_inherits_of (hCV : CornerValuesData) (h7 : CS7Data) (hs : CSoftData) (hR : hyp_R) :
    CInheritsData := by
  have hcmp := thm_comparison_of hCV h7 hs hR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h7, hR, hs, ?_, cmp_triangles hCV⟩
  · intro n _ hn P hP g
    rw [hcmp n hn P hP]
    exact A_lawful.root_independent n hn P hP g
  · intro n _ hn P hP k
    exact cornerStateSum_genericShift hn k ⟨P, hP⟩
  · intro n _ hn
    exact ⟨cmp_polygonSum hn, fun P => rfl⟩
  · intro n _ hn P Q
    exact ⟨fun h => (cornerStateSum_eq_of_mem_labelledChamber hn h).symm,
      fun h => (prop_C_chamber.constant n hn P Q h).symm⟩
  · intro n _ hn w
    exact ⟨fun M a hE s t => prop_C_silent.extension n hn w M a hE t s,
      fun i j k hC s t => prop_C_silent.cut n hn w i j k hC t s⟩
  · intro n _ w j hf
    obtain ⟨hg, hlaw⟩ := A_lawful.flat_law n w j hf
    refine ⟨hg, fun sRight sLeft hRight0 hLeft0 hR' hL' => ?_⟩
    have hn1 : 3 ≤ n + 1 := by have := hf.1; omega
    have hn : 3 ≤ n := by have := hf.1; omega
    rw [hcmp (n + 1) hn1 _ (w.generic_punctured sRight hRight0),
      hcmp (n + 1) hn1 _ (w.generic_punctured sLeft hLeft0), hcmp n hn _ hg]
    exact hlaw sRight sLeft hRight0 hLeft0 hR' hL'
  · intro n _ w j hf hG1
    have hQ := cmp_cusp_deletion_generic w j hf hG1
    obtain ⟨b, hb, huniq, κ, hκ, hlaw⟩ := A_lawful.cusp_law n w j hf hG1
    refine ⟨hQ, b, hb, huniq, κ, hκ, fun s t => ⟨(hlaw s t).1, ?_⟩⟩
    have hn1 : 3 ≤ n + 1 := by have := hf.1; omega
    have hn : 3 ≤ n := by have := hf.1; omega
    rw [hcmp (n + 1) hn1 _ (w.sideTuple (w.cuspLoopSide b j) s).property,
      hcmp (n + 1) hn1 _ (w.sideTuple (!(w.cuspLoopSide b j)) t).property, hcmp n hn _ hQ]
    exact (hlaw s t).2.2 hQ
  · intro n _ hn P hP
    rw [hcmp n hn _ ((generic_reversal P).mpr hP), hcmp n hn P hP]
    exact A_lawful.reversal_law n hn P hP

/-! ## §5 The row theorems (UNCONDITIONAL statements; `sorry` until rows 105/110/112 land; D-F11/D-F14:
declared and mapped only then). Bodies: `anchor_values_of thm_C_soft`;
`thm_comparison_of corner_values thm_C_S7 thm_C_soft hR`; `cor_C_inherits_of corner_values thm_C_S7 thm_C_soft hR`. -/

/-- Row 122 prop:anchor-values (proposed name). -/
theorem prop_anchor_values : AnchorValuesData := by
  sorry

/-- Row 127 thm:comparison (FIXED name). "Assume Hypothesis R. Then C(P) = A(P) for every generic
polygon P." -/
theorem thm_comparison (hR : hyp_R) :
    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
      cornerStateSum hn hP = amplitude P hP.1 hn := by
  sorry

/-- Row 128 cor:C-inherits (FIXED name; hyp:R in `explicit_parameter` mode). -/
theorem cor_C_inherits (hR : hyp_R) : CInheritsData := by
  sorry

/-! ## §6 Consumer shape checks -/

/-- Row 184's `corner_laws_and_soft_of (hR) (h7) (hs) (hinh : CInheritsData)` reads exactly these three
fields; the bundle above supplies them (shape check). -/
example (hinh : CInheritsData) : CuspLawC ∧ ReversalLawC ∧ TrianglesC :=
  ⟨hinh.cusp_law, hinh.reversal_law, hinh.triangles⟩

/-- thm:uniqueness' anchor step uses exactly (a) and (e): `AnchorValuesHypotheses` is what the accepted
proof consumes (shape check). -/
example (F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ) (hF : UniquenessHypotheses F) :
    AnchorValuesHypotheses F := AnchorValuesHypotheses.of_uniqueness hF

end SM
