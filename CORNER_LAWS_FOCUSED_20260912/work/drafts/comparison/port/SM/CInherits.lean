-- Ported <HH:MM>Z 2026-09-15 from work/drafts/comparison/Comparison_Assembled.lean lines 679-768, 938-997, 1019-1050 (comparison lane §4 and §6, row 128 cor:C-inherits as library material: `CuspLawC`, `ReversalLawC`, `CInheritsData` (this lane owns the row-128 bundle and the CV/R tail's three Props, PLAN_FINAL.md §6), `cu_cuspLawC_of`, `cor_C_inherits_of (hR) (h7) (hs)`, and the six §6 consumer / equivalence `example`s) by the pod executor; body verbatim except this header, the import block (SM.Comparison, SM.CuspDeletionGeneric) and the module docstring (new); the three ranges are the draft's §4 minus the unit block 770-936 (now SM/CuspDeletionGeneric.lean) and §6, each verbatim.  Wrappers `namespace SM` / `open WallGerm SoftDuplication Carrier` / `end SM` repeated verbatim.  The row theorem `SM.cor_C_inherits (hR : hyp_R)` is NOT declared here: it needs `SM.thm_C_S7` (row 110), see port/PORT_REPORT.md §5.
import SM.Comparison
import SM.CuspDeletionGeneric

/-! # Row 128 cor:C-inherits (sm-6:313-319; proof 320-372) — the bundle, the conditional theorem, the shape checks

Source: work/drafts/comparison/Comparison_Assembled.lean §4, §6 (PLAN_FINAL.md §4 unit U-CM-INH; FR-CM-8, FR-CM-9, FR-CM-13..17).
`CInheritsData` is the accepted `ALawfulData` field for field with `cornerStateSum` for `amplitude`, plus `root_values`;
`CuspLawC`, `ReversalLawC` (here) and `TrianglesC` (SM/Comparison.lean) are the Props the CV/R tail's row 184 reads
(`corner_laws_and_soft_of`: `hinh.cusp_law`, `hinh.reversal_law`, `hinh.triangles`).  `cor_C_inherits_of (hR : hyp_R)
(h7 : CS7Data) (hs : CSoftData) : CInheritsData` is proved from `thm_comparison_of`, the accepted `A_lawful` and the
genericity checks (lem:children, lem:soft-generic, `cusp_deletion_generic`).  The row theorem `SM.cor_C_inherits (hR : hyp_R)`
(FIXED name) is declared when `SM.thm_C_S7` exists, as `cor_C_inherits_of hR thm_C_S7 thm_C_soft`. -/

namespace SM

open WallGerm SoftDuplication Carrier

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
