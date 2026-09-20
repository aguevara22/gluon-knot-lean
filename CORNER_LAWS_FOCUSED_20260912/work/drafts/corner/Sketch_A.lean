import SM.CornerStateSum
import SM.CBProducts
import SM.EmbeddedRotation
import SM.Children
import SM.NamedWallSides
import SM.SoftGenericLemma
import SM.SoftAmplitudeSectors
import SM.UniformRotation
import SM.SingleCrossing
import SM.LinkPositiveLift
import SM.CX1
import SM.CChamber
import SM.GermSides

/-! # Rows 103 cb:singleton, 105 lem:corner-values, 110 thm:C-S7, 112 thm:C-soft — design sketch A
(fidelity-first), 2026-09-15

Companion of work/drafts/corner/DESIGN_A.md.  Check: `cd work/lean && lake env lean ../drafts/corner/Sketch_A.lean`.
The STATEMENTS (§0-§4) have no sorry; the conditional forms (§5) are assembled from proof-route LEAVES
that are `sorry` (`cs_split`, `s7_sliding`, `s7_bigon`, `so_soft_law`) — a design sketch, not a proof;
row 105 clause (i) (`corner_values_embedded`) and the degree extraction of row 103
(`cs_coeff_product_zero`) are PROVED outright.  Nothing here is to be ported before the rows'
statement reviews.  No `axiom`.

Sources (frame SM15): reference/SM/sm-3-statesum.tex 4697-4702 (row 103 statement; proof 4703-4759),
4801-4809 (row 105; proof 4810-4819); reference/SM/sm-4-knotlaws.tex 267-274 (row 110; proof 275-905),
984-991 (row 112; proof 992-1128).  Accepted inputs: def:C (SM/CornerStateSum.lean), def:uniform,
def:smoothing, lem:carriers (SM/CarriersLemma.lean), cb:blocks / cb:products (SM/CBBlocks.lean,
SM/CBProducts.lean, incl. `greedy_independent`, `greedy_step`), cb:embedded-rotation
(SM/EmbeddedRotation.lean), lem:uniformrot (SM/UniformRotation.lean), lc:single-crossing, lp:core,
def:walls (V) predicates (SM/NamedWallPredicates.lean), lem:wall-sides (V) (SM/VertexSides.lean),
def:deletion-halves + lem:children (SM/DeletionHalvesDefinition.lean, SM/Children.lean), the accepted
contact sign `WallGerm.contactSign` (SM/NamedWallSides.lean, used by the accepted thm:A-S7), def:soft +
lem:soft-generic (SM/SoftInsertionDefinition.lean, SM/SoftGenericLemma.lean), the accepted multiplier
`SoftDuplication.softAmplitudeMultiplier = (χ₋ + χ₊)/2` (used by the accepted thm:A-soft),
lem:C-X1, prop:C-chamber, lem:homflyrows (SM/MarkedProducts.lean). -/

namespace SM

open Link Carrier

noncomputable section
open Classical

variable {n : ℕ} [NeZero n]

/-! ## 0. Assumed interface — row 100 thm:floor, TO BE UNIFIED WITH THE FLOOR LANE

Copied verbatim from work/drafts/gap2/Gap2Statements.lean §8 (= work/drafts/floor/Sketch_B.lean §2).
Only `a_floor` is consumed below (rows 103 and 110); `z_parity` is not used by this lane (the printed
proofs' `[z⁰]`-row bookkeeping is replaced by the `a`-degree bound on the whole product, FR-CC-8). -/

/-- "after possibly reversing its orientation either all turns are left, or exactly one turn is right"
(floor lane's reading, FR-FL-10). -/
def CarrierUniformOrOneDissent (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : Prop :=
  CarrierUniform hn hP S q ∨
  ∃ τ : SignType, τ ≠ 0 ∧ ∃ j₀, turn (ccpCornerPolygon hn hP S q) j₀ = -τ ∧
    ∀ j, j ≠ j₀ → turn (ccpCornerPolygon hn hP S q) j = τ

/-- thm:floor (row 100), the floor lane's bundle; the row theorem `SM.thm_floor : FloorTheoremData`
is that lane's. -/
structure FloorTheoremData : Prop where
  a_floor : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    CarrierUniformOrOneDissent hn hP S q →
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS)
  z_parity : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    InSupportM 1 (cornerHomfly hn hP S q hS) ∧ 0 ≤ mindegZZ (cornerHomfly hn hP S q hS)

/-! ## 1. Row 103 cb:singleton (sm-3:4697-4702) -/

/-- **cb:singleton as printed**: "Let `A` be a uniform carrier of `S`, and suppose one of its
self-crossing labels `c` interlaces no other self-crossing of `A`. Then `c(A) = 0`."
Binder (cb:blocks, sm-3:4624-4625): a generic polygon `P` (`hn`, `hP`) and an independent support `S`
(`hS`); `A : Component hn hP S` a carrier of `S` (def:smoothing); "uniform" = `CarrierUniform`
(def:uniform); "self-crossing labels of `A`" = `carrierCrossings hn hP S A` (def:smoothing: the
unselected crossings both of whose visits lie on `A`); "interlaces" = `Interlaces hn hP` of `G_P`
(def:interlace); `c(A) = cornerCoefficient hn hP S A hS` (def:C). -/
structure CbSingletonData : Prop where
  /-- the one printed sentence -/
  isolated_zero : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (A : Component hn hP S),
    CarrierUniform hn hP S A →
    ∀ c ∈ carrierCrossings hn hP S A,
      (∀ c' ∈ carrierCrossings hn hP S A, c' ≠ c → ¬ Interlaces hn hP c c') →
      cornerCoefficient hn hP S A hS = 0

/-! ## 2. Row 105 lem:corner-values (sm-3:4801-4809) -/

/-- **lem:corner-values as printed**, one field per printed clause.  `Q` is a subpolygon of a
decomposition `S` of the generic polygon `P` (def:C's binder), `m_Q = carrierCrossingCount`,
`r_Q = carrierRotation` (real, def:uniform), `d_Q = cornerSlot`, `c(Q) = cornerCoefficient`. -/
structure CornerValuesData : Prop where
  /-- (i) "If `Q` is uniform and embedded (`m_Q = 0`) then `|r_Q| = 1`, `d_Q = 0` and `c(Q) = 1`."
  The hypothesis is read as the printed gloss `m_Q = 0` (FR-CV-1; embeddedness of the corner polygon
  is then a theorem, `cv_embedded_of_crossingFree`). -/
  embedded : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    CarrierUniform hn hP S q → carrierCrossingCount hn hP S q = 0 →
    |carrierRotation hn hP S q| = 1 ∧ cornerSlot hn hP S q = 0 ∧ cornerCoefficient hn hP S q hS = 1
  /-- (ii) "If `Q` is uniform and `{y}` is a crossing of `Q` interlacing no other crossing of `Q`,
  then `c(Q) = 0`." -/
  isolated : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    CarrierUniform hn hP S q →
    ∀ y ∈ carrierCrossings hn hP S q,
      (∀ y' ∈ carrierCrossings hn hP S q, y' ≠ y → ¬ Interlaces hn hP y y') →
      cornerCoefficient hn hP S q hS = 0

/-! ## 3. Row 110 thm:C-S7 (sm-4:267-274) -/

namespace WallGerm

/-- `|λ₁| ≥ 3` (lem:children (ii), accepted `contactHalfSizes_bounds`). -/
theorem three_le_firstHalfSize (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n}
    (h : g.VertexEdgeAt M a) : 3 ≤ firstHalfSize M a :=
  (contactHalfSizes_bounds hn h.1).1.1

theorem three_le_secondHalfSize (hn : 3 ≤ n) (g : WallGerm n) {M a : ZMod n}
    (h : g.VertexEdgeAt M a) : 3 ≤ secondHalfSize M a :=
  (contactHalfSizes_bounds hn h.1).2.1

/-- **`C(λ₁)`**: the corner state sum (def:C) of the first half `λ₁ = firstHalf g.center M a`
(def:deletion-halves), generic with `≥ 3` vertices by lem:children (ii) (`vertex_halves_children`). -/
def firstHalfStateSum (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (h : g.VertexEdgeAt M a) : ℤ :=
  haveI : NeZero (firstHalfSize M a) := ⟨by have := g.three_le_firstHalfSize hn h; omega⟩
  cornerStateSum (g.three_le_firstHalfSize hn h) (vertex_halves_children hn g h).1

/-- **`C(λ₂)`**: the corner state sum of the second half `λ₂ = secondHalf g.center M a`. -/
def secondHalfStateSum (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (h : g.VertexEdgeAt M a) : ℤ :=
  haveI : NeZero (secondHalfSize M a) := ⟨by have := g.three_le_secondHalfSize hn h; omega⟩
  cornerStateSum (g.three_le_secondHalfSize hn h) (vertex_halves_children hn g h).2.1

end WallGerm

/-- **thm:C-S7 as printed**: "At a simple vertex–edge wall at `(M; a)`, of bigon or sliding type, with
halves `λ₁, λ₂` (Definition def:deletion-halves) and contact sign `s = χ_{a,a+1,M}(P₋)`,
`C(P₊) − C(P₋) = s C(λ₁) C(λ₂)`."  Rendering (the accepted thm:A-S7's, SM/VertexEdgeLawTree.lean):
the wall is `g : WallGerm n` with `g.BigonAt M a` / `g.SlidingAt M a` (def:walls (V) + the type clause);
`P₊`, `P₋` are the sides `g.sideTuple true tp`, `g.sideTuple false tm` at all side parameters (the
accepted C-row convention of prop:C-silent / hyp:R, equivalent to the chamber values by
prop:C-chamber); `s = g.contactSign M a` (accepted: `χ_{a,a+1,M}` on `P₋`, constant there,
`contactSign_eq_at`); `C(λᵢ)` = `firstHalfStateSum` / `secondHalfStateSum`. -/
structure CS7Data : Prop where
  /-- the vertex–edge law at a wall of bigon type -/
  bigon : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (h : g.BigonAt M a),
    ∀ tp tm : g.SideParameter,
      cornerStateSum hn (g.sideTuple true tp).property -
          cornerStateSum hn (g.sideTuple false tm).property =
        (g.contactSign M a : ℤ) * g.firstHalfStateSum hn M a h.1 * g.secondHalfStateSum hn M a h.1
  /-- the vertex–edge law at a wall of sliding type -/
  sliding : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (h : g.SlidingAt M a),
    ∀ tp tm : g.SideParameter,
      cornerStateSum hn (g.sideTuple true tp).property -
          cornerStateSum hn (g.sideTuple false tm).property =
        (g.contactSign M a : ℤ) * g.firstHalfStateSum hn M a h.1 * g.secondHalfStateSum hn M a h.1

/-- Consumer form: at every simple vertex–edge wall (the type dichotomy `vertexEdge_bigon_or_sliding`
is a theorem of def:walls (V)). -/
theorem CS7Data.vertex_edge_law (hD : CS7Data) (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)
    (h : g.VertexEdgeAt M a) (tp tm : g.SideParameter) :
    cornerStateSum hn (g.sideTuple true tp).property -
        cornerStateSum hn (g.sideTuple false tm).property =
      (g.contactSign M a : ℤ) * g.firstHalfStateSum hn M a h * g.secondHalfStateSum hn M a h := by
  rcases g.vertexEdge_bigon_or_sliding h with hb | hs
  · exact hD.bigon n hn g M a hb tp tm
  · exact hD.sliding n hn g M a hs tp tm

/-- Sanity (FR-CC-12): the contact sign in the bundle IS `χ_{a,a+1,M}` evaluated on `P₋`, at the very
parameter `tm` of the `C(P₋)` term (accepted `contactSign_eq_at`). -/
theorem CS7Data.contactSign_literal (g : WallGerm n) (M a : ZMod n) (tm : g.SideParameter) :
    (g.contactSign M a : ℤ) = ((chi (g.sideTuple false tm).val a (a + 1) M : SignType) : ℤ) := by
  rw [g.contactSign_eq_at M a tm]

/-! ## 4. Row 112 thm:C-soft (sm-4:984-991) -/

/-- **thm:C-soft as printed**: "Let `P` be generic, `j` a vertex, `q` admissible, and `P_ε` the soft
insertion of Definition def:soft, with attachment signs `χ_±`. Then for all sufficiently small
`ε > 0`, `C(P_ε) = (χ₋ + χ₊)/2 · C(P)`."  Rendering (the accepted thm:A-soft's,
SM/SoftTheoremTree.lean): `P_ε = softInsertion P j q ε` (def:soft), admissible = `SoftAdmissible`,
`(χ₋ + χ₊)/2 = SoftDuplication.softAmplitudeMultiplier P j q : ℚ` with
`χ₋ = softAttachmentMinus`, `χ₊ = softAttachmentPlus`; "for all sufficiently small `ε > 0`" =
`∃ ε₁ > 0, ∀ ε ∈ (0, ε₁)`; `P_ε` generic (lem:soft-generic (i)) is part of the conclusion (`∃ hQ`), so
that `C(P_ε)` is formed as in def:C; the identity is read in `ℚ` as printed (FR-CS-3). -/
structure CSoftData : Prop where
  /-- the one printed identity -/
  soft_law : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) (j : ZMod n)
    (q : Plane), SoftAdmissible P j q →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ hQ : Generic (softInsertion P j q ε),
        (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
          SoftDuplication.softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ)

/-- Companion (the printed proof's three sector multipliers, sm-4:1123-1127): in `ℤ`,
`2 C(P_ε) = (χ₋ + χ₊) C(P)`. -/
theorem CSoftData.doubled (hD : CSoftData) (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ hQ : Generic (softInsertion P j q ε),
        2 * cornerStateSum (by omega : 3 ≤ n + 1) hQ =
          ((softAttachmentMinus P j q : ℤ) + (softAttachmentPlus P j q : ℤ)) * cornerStateSum hn hP := by
  obtain ⟨ε₁, hε₁, hall⟩ := hD.soft_law n hn P hP j q hq
  refine ⟨ε₁, hε₁, fun ε hε hε' => ?_⟩
  obtain ⟨hQ, heq⟩ := hall ε hε hε'
  refine ⟨hQ, ?_⟩
  have h2 : (2 : ℚ) * (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
      (((softAttachmentMinus P j q : ℤ) : ℚ) + ((softAttachmentPlus P j q : ℤ) : ℚ)) *
        (cornerStateSum hn hP : ℚ) := by
    rw [heq, SoftDuplication.softAmplitudeMultiplier]; ring
  exact_mod_cast h2

/-! ## 5. Conditional forms (D-F11/D-F14 pattern: library material, never mapped; the row theorems
`SM.cb_singleton`, `SM.corner_values`, `SM.thm_C_S7`, `SM.thm_C_soft` are assembled once row 100
lands as `… (thm_floor)`) -/

/-! ### 5.1 Leaves of row 103 (unit prefix `cs_`) -/

/-- the `a`-degree extraction (sm-3:4748-4757) — PROVED here from the Laurent-ring layer:
`f g ≠ 0`, `k₁ ≤ mindeg_a f`, `k₂ ≤ mindeg_a g` ⇒ `[a^{k₁+k₂-2} z⁰](f g) = 0`. -/
theorem cs_coeff_product_zero {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) {k₁ k₂ : ℤ}
    (h₁ : k₁ ≤ mindegAZ f) (h₂ : k₂ ≤ mindegAZ g) :
    coeffAt (k₁ + k₂ - 2) 0 (f * g) = 0 := by
  apply coeffAt_eq_zero_of_lt_mindegA
  rw [mindegA_eq_mindegAZ (mul_ne_zero hf hg), mindegAZ_mul hf hg]
  exact_mod_cast (by omega : k₁ + k₂ - 2 < mindegAZ f + mindegAZ g)

/-- the split at `c` (sm-3:4704-4741), packaged: `S' = S ∪ {c}` is a decomposition, the two daughters
`Λ₁ Λ₂` of `A`, the products/counts/rotations of eqs. cb:singleton-products, cb:singleton-rotations,
and the daughters' turn patterns (uniform + one dissent) — the geometric heart of row 103. -/
theorem cs_split (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) {S : Finset (Crossing P)}
    (hS : IsDecomposition hn hP S) (A : Component hn hP S) (hA : CarrierUniform hn hP S A)
    (c : Crossing P) (hc : c ∈ carrierCrossings hn hP S A)
    (hiso : ∀ c' ∈ carrierCrossings hn hP S A, c' ≠ c → ¬ Interlaces hn hP c c') :
    ∃ hS' : IsDecomposition hn hP (insert c S),
    ∃ Λ₁ Λ₂ : Component hn hP (insert c S),
      cornerHomfly hn hP S A hS =
        cornerHomfly hn hP (insert c S) Λ₁ hS' * cornerHomfly hn hP (insert c S) Λ₂ hS' ∧
      carrierCrossingCount hn hP S A =
        carrierCrossingCount hn hP (insert c S) Λ₁ + carrierCrossingCount hn hP (insert c S) Λ₂ + 1 ∧
      |carrierRotationInt hn hP S A| =
        |carrierRotationInt hn hP (insert c S) Λ₁| + |carrierRotationInt hn hP (insert c S) Λ₂| ∧
      CarrierUniformOrOneDissent hn hP (insert c S) Λ₁ ∧
      CarrierUniformOrOneDissent hn hP (insert c S) Λ₂ := by
  sorry

/-- **Row 103 conditional on thm:floor** (`a_floor` at the two daughters, sm-3:4750-4753). -/
theorem cb_singleton_of_floor (hF : FloorTheoremData) : CbSingletonData where
  isolated_zero := by
    intro n _ hn P hP S hS A hA c hc hiso
    obtain ⟨hS', Λ₁, Λ₂, hprod, hcount, hrot, h₁, h₂⟩ := cs_split hn hP hS A hA c hc hiso
    have hf := hF.a_floor hn P hP _ hS' Λ₁ h₁
    have hg := hF.a_floor hn P hP _ hS' Λ₂ h₂
    have hne₁ : cornerHomfly hn hP (insert c S) Λ₁ hS' ≠ 0 := by
      show homfly _ ≠ 0; rw [← P_eq_homfly]; exact P_ne_zero _
    have hne₂ : cornerHomfly hn hP (insert c S) Λ₂ hS' ≠ 0 := by
      show homfly _ ≠ 0; rw [← P_eq_homfly]; exact P_ne_zero _
    rw [cornerCoefficient_eq_coeffAt, hprod]
    have hslot : cornerSlot hn hP S A =
        cornerSlot hn hP (insert c S) Λ₁ + cornerSlot hn hP (insert c S) Λ₂ - 2 := by
      simp only [cornerSlot]; rw [hrot]; push_cast [hcount]; ring
    rw [hslot]
    exact cs_coeff_product_zero hne₁ hne₂ hf hg

/-! ### 5.2 Leaves of row 105 (unit prefix `cv_`) -/

/-- `m_Q = 0` ⇒ the corner polygon is an embedded polygon in the sense of row 104
(`Embedded`: nonzero edges, remote edges disjoint, consecutive edges meet in the shared corner) —
PROVED from lem:carriers (ii) and the accepted `nonadjacent_meet_crossing`, `consecutive_meet`
(SM/LinkPositiveLift.lean); this is the bridge behind the reading FR-CV-1. -/
theorem cv_embedded_of_crossingFree (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
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

/-- (i) unconditionally (no floor): `|r_Q| = 1` by row 104 on the embedded regular corner polygon,
`d_Q = 1 − 0 − 1 = 0`, `c(Q) = [a⁰z⁰] 1 = 1` by lp:core's `P_○ = 1` on the crossing-free positive lift. -/
theorem corner_values_embedded (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (_hu : CarrierUniform hn hP S q) (hm : carrierCrossingCount hn hP S q = 0) :
    |carrierRotation hn hP S q| = 1 ∧ cornerSlot hn hP S q = 0 ∧ cornerCoefficient hn hP S q hS = 1 := by
  have h0 : carrierCrossings hn hP S q = ∅ := Finset.card_eq_zero.mp hm
  have hreg : Regular (ccpCornerPolygon hn hP S q) := ccpCornerPolygon_regular hn hP hS q
  have h3 : 3 ≤ ccpCornerCount hn hP S q := (carriers_lemma hn hP hS).corner_polygons.2.2.1 q
  have hpm := (cb_embedded_rotation h3 (ccpCornerPolygon hn hP S q) hreg
    (cv_embedded_of_crossingFree hn hP hS q h0)).pm_one
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

/-- **Row 105 from row 103** ((ii) is cb:singleton at `Q, y`; (i) needs no floor). -/
theorem corner_values_of_singleton (hsing : CbSingletonData) : CornerValuesData where
  embedded := fun _ _ hn _ hP _ hS q hu hm => corner_values_embedded hn hP hS q hu hm
  isolated := fun n _ hn P hP S hS q hu y hy hiso => hsing.isolated_zero n hn P hP S hS q hu y hy hiso

theorem corner_values_of_floor (hF : FloorTheoremData) : CornerValuesData :=
  corner_values_of_singleton (cb_singleton_of_floor hF)

/-! ### 5.3 Leaves of row 110 (unit prefix `s7_`) — statements of the two branches -/

/-- the sliding branch (sm-4:291-372): no floor, no singleton — relocation bijection + selector table. -/
theorem s7_sliding (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (h : g.SlidingAt M a)
    (tp tm : g.SideParameter) :
    cornerStateSum hn (g.sideTuple true tp).property -
        cornerStateSum hn (g.sideTuple false tm).property =
      (g.contactSign M a : ℤ) * g.firstHalfStateSum hn M a h.1 * g.secondHalfStateSum hn M a h.1 := by
  sorry

/-- the bigon branch (sm-4:374-905): consumes `a_floor` at the two half contact carriers (uniform when
the newborns interlace, one-dissent otherwise) and cb:singleton at the one-newborn rows. -/
theorem s7_bigon (hF : FloorTheoremData) (hsing : CbSingletonData) (hn : 3 ≤ n) (g : WallGerm n)
    (M a : ZMod n) (h : g.BigonAt M a) (tp tm : g.SideParameter) :
    cornerStateSum hn (g.sideTuple true tp).property -
        cornerStateSum hn (g.sideTuple false tm).property =
      (g.contactSign M a : ℤ) * g.firstHalfStateSum hn M a h.1 * g.secondHalfStateSum hn M a h.1 := by
  sorry

/-- **Row 110 conditional on thm:floor and cb:singleton** (the printed dependencies, claims.py). -/
theorem thm_C_S7_of (hF : FloorTheoremData) (hsing : CbSingletonData) : CS7Data where
  bigon := fun _ _ hn g M a h tp tm => s7_bigon hF hsing hn g M a h tp tm
  sliding := fun _ _ hn g M a h tp tm => s7_sliding hn g M a h tp tm

theorem thm_C_S7_of_floor (hF : FloorTheoremData) : CS7Data :=
  thm_C_S7_of hF (cb_singleton_of_floor hF)

/-! ### 5.4 Leaves of row 112 (unit prefix `so_`) -/

/-- **Row 112 from row 105** (the printed proof consumes lem:corner-values (i) at the loop triangle and
(ii) at the supports omitting the newborn `y`; the same-sign and mixed sectors use neither). -/
theorem so_soft_law (hcv : CornerValuesData) (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ hQ : Generic (softInsertion P j q ε),
        (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
          SoftDuplication.softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ) := by
  sorry

theorem thm_C_soft_of_corner_values (hcv : CornerValuesData) : CSoftData where
  soft_law := fun _ _ hn _ hP j q hq => so_soft_law hcv hn hP j q hq

theorem thm_C_soft_of_floor (hF : FloorTheoremData) : CSoftData :=
  thm_C_soft_of_corner_values (corner_values_of_floor hF)

/-! ## 6. Shape checks: the fixed-name row theorems will be these one-liners once `SM.thm_floor :
FloorTheoremData` exists (row 100, floor lane): `theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor`,
`theorem thm_C_soft : CSoftData := thm_C_soft_of_floor thm_floor`, `theorem cb_singleton : CbSingletonData :=
cb_singleton_of_floor thm_floor`, `theorem corner_values : CornerValuesData := corner_values_of_floor thm_floor`. -/
example (hF : FloorTheoremData) : CS7Data ∧ CSoftData ∧ CbSingletonData ∧ CornerValuesData :=
  ⟨thm_C_S7_of_floor hF, thm_C_soft_of_floor hF, cb_singleton_of_floor hF, corner_values_of_floor hF⟩

end

end SM
