# PLAN FINAL — rows 122 prop:anchor-values, 127 thm:comparison, 128 cor:C-inherits: judge's decision, fixed statements, route, units

Rows 122 (reference/SM/sm-5-transport.tex:461-476 statement, 477-505 proof), 127 (reference/SM/sm-6-comparison.tex:299-303,
304-311), 128 (313-319, 320-372). Judge (subagent), 2026-09-15 ~17:35Z / 1:35pm ET. Inputs: DESIGN_A.md / Sketch_A.lean
(fidelity-first) and DESIGN_B.md / Sketch_B.lean (feasibility-first). Both re-checked with `cd work/lean && lake env lean <file>`:
Sketch_A 0 errors, 5 `sorry` (2 leaves `cmp_triangle_value`, `cmp_cusp_deletion_generic` + 3 row theorems); Sketch_B 0 errors,
4 `sorry` (1 leaf `cu_cusp_deletion_generic` + 3 row theorems; the triangle leaf PROVED in 75 lines). Also read: the three printed
statements and proofs; cor:A-lawful (sm-6:105-127); def:anchors (sm-5:373-399); lem:A-small-values (sm-6:5-16); lem:children
(sm-1:1269-1279); the accepted siblings `SM.uniqueness` / `UniquenessHypotheses` (SM/Uniqueness.lean:35-95, 454), `A_lawful :
ALawfulData` (SM/ALawful.lean:37-131, 201), `hyp_R` (SM/HypR.lean:83), `anchors_definition` (SM/AnchorsDefinition.lean),
`thm_C_S3 : CS3Data` (SM/CS3.lean:2478-2510); the CV/R tail's row-184 proposal (work/drafts/cvtail/Statements_FINAL.lean:854-990,
PLAN_FINAL.md FR-F-184-4, PREREVIEW.md item 8); the corner lane's FINAL (work/drafts/corner/Statements_FINAL.lean §3-§6, PREREVIEW.md);
axiom-policy.json (`targets`, hyp:R mode `explicit_parameter`); TARGETS.md; the cusp/deletion library (CuspDefinition, CuspBetweenness,
DeletedTuple, DeletionIndices, DeletionInteriors, DeletionGeneric, FlatAdjacent, GenericTopology, ZeroTriples).

Deliverables (this directory; nothing written under work/lean):
- `Statements_FINAL.lean` (896 lines) — the fixed statements, the ONE frozen leaf, the proved assemblies and companions.
  `cd work/lean && lake env lean ../drafts/comparison/Statements_FINAL.lean`: 0 errors, 20 s warm; 4 declarations use `sorry` =
  the leaf `cusp_deletion_generic` (§4, unit U-CM-CUSPGEN) + the 3 row theorems of §5 (`prop_anchor_values`, `thm_comparison`,
  `cor_C_inherits`; bodies `anchor_values_of thm_C_soft`, `thm_comparison_of hR thm_C_S7 thm_C_soft`, `cor_C_inherits_of hR
  thm_C_S7 thm_C_soft` once rows 110/112 land). PROVED: `cornerPolygon` + projections + chamber constancy (§1); the whole of
  row 122 modulo thm:C-soft (`anchor_values_of`, §2) and the companions `AnchorValuesData.C_zero/.C_loop/.C_loopZero`;
  `trianglesC : TrianglesC` UNCONDITIONAL and `tri_triangle_value` (`C(T) = −τ`, §3); `cs3_flat_bridge`/`cs3_flat_law_C`;
  `uniquenessHypotheses_C_of`, `thm_comparison_of`, `thm_comparison_root_of`, `thm_comparison_polygon_of` (§3);
  `cu_cuspLawC_of`, `cor_C_inherits_of` (§4, modulo the leaf); six §6 shape checks.
  `#print axioms` (probe copy, scratchpad): `anchor_values_of` = [propext, Classical.choice, Quot.sound, SM.lit_homfly];
  `corner_values_i`, `trianglesC`, `tri_triangle_value`, `thm_comparison_of` = standard + [SM.lit_homfly, SM.lp_lm,
  SM.lp_lm_uniqueness] (def:C's `homfly` and lp:core's `P`, the policy literature interfaces — sorry-free);
  `cor_C_inherits_of` adds `sorryAx` only through the leaf.
- this file.

## 0. Verdict: **B wins** (one open leaf instead of two — its 75-line proof of the triangle values closes A's 250-line/4 h unit
U-CM-TRI outright; `CInheritsData` field-for-field `ALawfulData`; the same PROVED row-122 argument and CS3 bridge; honest
estimates), with A's grafts (the two-reading (L₀) turn clause, `root_values`, the two-step descent `cornerPolygonSum`/`cornerPolygon`,
the companions `thm_comparison_root_of` and `AnchorValuesData.C_zero/C_loop`, the `tri_triangle_value` companion in the shape of
lem:A-small-values (i), the fallback analysis "a `Generic` hypothesis on the cusp law narrows TARGETS' domain — the leaf is
mandatory"), and ONE judge's graft neither candidate has (§2.1): the corner lane's PROVED, UNCONDITIONAL `corner_values_i`
(row 105 clause (i)) copied verbatim into §0, which makes (f) unconditional and drops `hCV : CornerValuesData` from
`thm_comparison_of` / `cor_C_inherits_of` — rows 127/128 are now conditional on rows 110/112 ONLY (A's risk 4, realised).

| criterion | A | B | decision |
|---|---|---|---|
| 122 hypotheses bundle | `AnchorValuesHypotheses F` = `UniquenessHypotheses.chamber/.soft` verbatim | identical | equal (adopt) |
| 122 anchor clauses | `zero/loop/loop_triangle` at `A.param`, ℤ-valued, `polygonProjection ⟨A.polygon, _⟩` | `zero/loop/loopZero`, identical content | equal; **B's names** (`loopZero` = the accepted `LoopAnchorZero` / `AnchorsDefinitionData.loopZero`) |
| 122 (L₀) turn clause | `τ_j ≠ 0 ∧ (∀ i, τ_i = τ_j) ∧ rot(P) = τ_j` (both readings of "orientation sign") | `∃ τ ≠ 0, (∀ i, τ_i = τ) ∧ τ_j = τ` (common sign only) | **A** (strictly stronger; covers the lem:rot reading a reviewer may want; PROVED by `rotationNumber_triangle`) |
| 122 `A_g` clauses | `∃! g, a = softParentEdge j g ∧ A_a(Y) = τ_j A_g(P)` at `a ≠ A.softEdge` | identical | equal (adopt) |
| descent of `C` | `cmp_polygonSum hn` (lift, no arity test) + `cmp_C n := if 3 ≤ n then … else 0` | one `cornerPolygon n` with the `if` inside (`dif_pos` deprecation) | **A's two steps, B's name**: `cornerPolygonSum hn` (the `descends` witness, the object of `thm_comparison_polygon_of`) + `cornerPolygon` |
| 127 statement | plain theorem `(hR : hyp_R) : ∀ n [NeZero n] hn P hP, cornerStateSum hn hP = amplitude P hP.1 hn` | identical | equal (adopt; the shape of the sibling `SM.uniqueness`) |
| 127 conditional form | `thm_comparison_of hCV h7 hs hR` | `thm_comparison_of hR h7 hs hCV` | **judge**: `thm_comparison_of hR h7 hs` — `hCV` dropped (§2.1) |
| (f) triangle values | LEAF `cmp_triangle_value hCV T hT τ hτ : C(T) = −τ` (250 lines, 4 h) | PROVED `tri_cornerStateSum_crossingFree` (∅ the only decomposition, uniform, `m_Q = 0`, `embedded_value`), `tri_triangle_no_crossing` (`decide` on ZMod 3), `ℓ` counts | **B's proof**, now against `corner_values_i` (unconditional); A's general statement kept as the PROVED companion `tri_triangle_value` |
| (b) flat bridge | `cmp_flat_bridge` PROVED (`cmp_side_repr`, `side_turn_constant`, `cornerStateSum_side_eq`) | `cs3_flat_bridge` PROVED, identical route, + `cs3_flat_law_C` in cor:A-lawful's `∃ hQ` shape | equal; **B** (the `∃ hQ` packaging is what `CInheritsData.flat_law` needs) |
| 128 bundle | cvtail's 11 fields adopted verbatim (`vertex_edge_law : CS7Data`, `triple_law : hyp_R`, `soft_theorem : CSoftData`) + `root_values` | `ALawfulData` field for field with `cornerStateSum` (11 fields; `Generic λ₁ ∧ Generic λ₂ ∧ ∀ s t`, `∀ … TripleAt → ∀ s t`, `∃ hQ`), no `root_values` | **B's field types + A's `root_values`** (12 fields; §2.2, FR-CM-8/13/15); A's nesting is PROVED equivalent by the §6 checks |
| cusp law | `CuspLawC` verbatim (cvtail), leaf `cmp_cusp_deletion_generic` | identical, leaf `cu_cusp_deletion_generic` | equal; name `cusp_deletion_generic` (a library lemma, not a helper) |
| cusp fallback | recorded, NOT adopted: a `Generic` hypothesis would narrow TARGETS' domain | "fallback = add Generic(deletion) as hypothesis … weaker than printed, disclosed" | **A's reading**: the leaf is mandatory for row 184; the fallback is only an honest intermediate state (§7) |
| FR notes | FR-CM-1..17 (thorough; both readings of (L₀) recorded) | FR-CM-1..11 | **A's list**, renumbered and merged (§5) |
| estimates | ≈ 1,250 lines, 14 prover-h (TRI 4 h + CUSPGEN 8 h) | ≈ 1,200 lines, 8-14 h (CUSPGEN only) | **B's** (TRI is closed; remaining = the leaf) |

Scores (1-10). FIDELITY A 8 / B 8 — A: the stronger (L₀) clause, `root_values`, seventeen recorded readings, but the row-128
fields nest the C-row bundles (`∀ h₁ h₂`, `∀ hQ`) instead of the printed cor:A-lawful shapes (equivalent, disclosed as FR-CM-15);
B: `CInheritsData` literally `ALawfulData` with `C` for `A` (a reviewer compares the two structures line by line), but the (L₀)
clause records one reading only and the defining clause of cor:A-lawful has no field. FEASIBILITY A 7 / B 9 — both typecheck with
the assemblies PROVED; A leaves two leaves and estimates the triangle values at 250 lines; B proves them in 75 and leaves only the
cusp geometry, with a concrete route through `g2_deleteVertex`'s vocabulary. REUSE A 8 / B 9 — both reuse `uniqueness`, `A_lawful`,
`unA_softAnchor_delta`'s argument, `soft_theorem_treeCoefficient`, `cornerStateSum_side_eq`; B additionally drives the carrier API
(`empty_mem_independentSupports`, `mem_ccpCornerList`, `ccpCornerPolygon_turn_vertex`, `mem_uniformDecompositions`) to close a
unit now, and `soft_family_generic` for the `∃ hQ` field. Totals A 23 / B 26.

## 1. Clause map (printed → Lean; Statements_FINAL.lean)

Conventions shared with every accepted sibling: `C(P) = cornerStateSum hn hP : ℤ` on a generic labelled tuple (def:C,
SM/CornerStateSum.lean); `A(P) = amplitude P hP.1 hn` (cor:A-lawful, root 0; SM/ALawful.lean:37); "a function on generic polygons
of all arities" is `F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ` (thm:uniqueness's reviewed reading); walls, sides, deletion,
halves, soft insertion, stars exactly as in `UniquenessHypotheses` / `ALawfulData`.

### Row 122 (sm-5:461-476) → `AnchorValuesHypotheses F` + `AnchorValuesData` (§2), 9 fields

| printed | Lean | status |
|---|---|---|
| "Let F be a function on generic polygons of all arities, constant on chambers and satisfying the soft theorem in the form of thm:C-soft at every admissible soft insertion into a generic polygon" | `AnchorValuesHypotheses F` = `UniquenessHypotheses.chamber` and `.soft` byte-identical (SM/Uniqueness.lean:37-38, 72-76); `UniquenessHypotheses.toAnchorValuesHypotheses` PROVED | stated |
| "F(Z) = 0 for every zero anchor" | `zero : ∀ F (_ : AnchorValuesHypotheses F) m [NeZero m] r (A : ZeroAnchor m r), F (m+1) (polygonProjection ⟨A.polygon, A.polygon_generic⟩) = 0` | PROVED `av_zero` |
| "F(Y) = τ_j(P) F(P) for every loop anchor" | `loop` (case (L), `LoopAnchor m r`) and `loopZero` (case (L₀), `LoopAnchorZero m`): `F (m+1) ⟦Y⟧ = ((turn A.parent A.vertex : SignType) : ℤ) * F m ⟦A.parent⟧` | PROVED `av_loop` |
| "In case (L), τ_j(P) = −sgn(r)" | `loop_turn : turn A.parent A.vertex = -SignType.sign r` | PROVED (`LoopAnchor.parent_turn`) |
| "in case (L₀), it is the orientation sign of the parent triangle" | `loopZero_turn : turn A.parent A.vertex ≠ 0 ∧ (∀ i, turn A.parent i = turn A.parent A.vertex) ∧ rotationNumber A.parent = τ_j` | PROVED `av_loopZero_turn` |
| "The function C satisfies these hypotheses" | `C_hypotheses : AnchorValuesHypotheses cornerPolygon` | chamber PROVED; soft = `hs : CSoftData` |
| "The same identities hold for A_g at every anchor root other than the soft edge, with the corresponding parent root used on the right-hand side" | `A_zero : ∀ A a, a ≠ A.softEdge → treeCoefficient A.polygon _ a _ = 0`; `A_loop`, `A_loopZero : a ≠ A.softEdge → ∃! g, a = softParentEdge A.vertex g ∧ A_a(Y) = τ_j · A_g(P)` | PROVED `av_A_zero`, `av_A_loop` |

Row theorem: `prop_anchor_values : AnchorValuesData := anchor_values_of thm_C_soft` (declared when row 112 lands). Companions
PROVED: `AnchorValuesData.C_zero/.C_loop/.C_loopZero` (the `C` identities in labelled form, from the bundle).

### Row 127 (sm-6:299-303) → `thm_comparison (hR : hyp_R) : ∀ n [NeZero n] (hn : 3 ≤ n) (P) (hP : Generic P), cornerStateSum hn hP = amplitude P hP.1 hn` (§3, §5)

One printed clause, one plain theorem (the shape of `SM.uniqueness`); `hR` explicit. Library form `thm_comparison_of (hR) (h7 : CS7Data)
(hs : CSoftData)` PROVED (sorry-free). Companions PROVED: `thm_comparison_root_of` (`C(P) = A_g(P)` ∀ g), `thm_comparison_polygon_of`
(`cornerPolygonSum hn Q = alA_polygonAmplitude hn Q` on `GenericPolygon n`). Row theorem := `thm_comparison_of hR thm_C_S7 thm_C_soft`.

### Row 128 (sm-6:313-319) → `cor_C_inherits (hR : hyp_R) : CInheritsData` (§4, §5), 12 fields

| cor:A-lawful (sm-6:105-116) / `ALawfulData` field | `CInheritsData` field | proof source (in `cor_C_inherits_of`) |
|---|---|---|
| "A(P) := A_g(P) (any g) is well defined" / `root_independent` | `root_values : C(P) = treeCoefficient P hP.1 g hn` ∀ g (FR-CM-13) | `thm_comparison_of` + `A_lawful.root_independent` |
| "well defined on generic polygons" / `shift_invariant`, `descends` | same with `(generic_shift k P).mpr hP`; `C' = cornerPolygonSum hn` | `cornerStateSum_genericShift` (CChamber.lean:1362), `rfl` |
| "chamber constancy" / `chamber_constant` | same (labelled and polygon chambers) | `cornerStateSum_eq_of_mem_labelledChamber` (:1366), `prop_C_chamber.constant` (:1378) |
| "silence" / `silent` | same, (E) and (C) | `prop_C_silent.extension/.cut` (CSilent.lean:1854) |
| flat law / `flat_law` (`Generic (deletion) ∧ ∀ …`) | `∃ hQ : Generic (deletion), ∀ sRight sLeft …` (the witness is an argument of `C`) | `cs3_flat_law_C thm_C_S3` (CS3.lean:2495) + `generic_deleteVertex` (DeletionGeneric.lean:31) |
| cusp law "when the deletion satisfies (G1)" / `cusp_law` | `cusp_law : CuspLawC` (cvtail VERBATIM): hyp `G1 (deleteVertex w.center j)`, conclusion `∃ hQ : Generic (deletion), ∃ b, CuspCase ∧ unique ∧ ∃ κ = ±1, ∀ s t, rot jump ∧ C-law` | `cu_cuspLawC_of` ← `A_lawful.cusp_law` (ALawful.lean:201) + LEAF `cusp_deletion_generic` |
| vertex–edge law / `vertex_edge_law` (`Generic λ₁ ∧ Generic λ₂ ∧ ∀ s t …`) | same, witnesses `vertex_halves_children hn w hc` (Children.lean:12) | `CS7Data.vertex_edge_law` at `(tp, tm) = (t, s)` |
| triple law / `triple_law` | same (`∀ n hn w e f k, TripleAt → ∀ s t, C(P₊) = C(P₋)`) = `hyp_R` up to argument order | `hR` |
| soft theorem / `soft_theorem` (`∃ ε₁ > 0, ∀ ε < ε₁, ∃ hQ, … ℚ`) | same | `CSoftData.soft_theorem` + `soft_family_generic` (SoftGenericLemma.lean:37) |
| reversal / `reversal_law` | `reversal_law : ReversalLawC` (cvtail VERBATIM; witness `(generic_reversal P).mpr hP`, GenericReversal.lean:64) | `A_lawful.reversal_law` + `thm_comparison_of` at `P`, `P̄` |
| `A(K₁) = −1, A(K₋₁) = +1` / `triangles` | `triangles : TrianglesC` (cvtail VERBATIM) | `trianglesC` (unconditional) |

Row theorem := `cor_C_inherits_of hR thm_C_S7 thm_C_soft`.

## 2. Model decisions

### 2.1 The judge's graft: lem:corner-values (i) is PROVED — (f) is unconditional

Both designs took `hCV : CornerValuesData` as an interface hypothesis for (f), though only clause (i) (`embedded_value`) is consumed,
and the corner lane's FINAL PROVES clause (i) unconditionally (`corner_values_i`, work/drafts/corner/Statements_FINAL.lean:350-372,
axioms standard + lit_homfly/lp_lm/lp_lm_uniqueness; A's risk 4 anticipated exactly this). §0 copies `cvl_embedded_of_no_crossings`
and `corner_values_i` VERBATIM (TO BE UNIFIED), so `trianglesC : TrianglesC` is an unconditional theorem NOW, `tri_triangle_value`
(`C(T) = −τ` for every generic triangle) likewise, and `thm_comparison_of (hR) (h7) (hs)` / `cor_C_inherits_of (hR) (h7) (hs)` take
ONLY the two pending rows. Cost: the imports SM.EmbeddedRotation, SM.LinkPositiveLift, SM.UniformRotation, SM.CBProducts (20 s
compile). Consequences: (i) FINAL_REVIEW's honest intermediate sentence becomes "122 conditional on 112; 127/128 conditional on
110/112" (not on 105); (ii) the CV/R tail's `CornerLawsAndSoftData.triangles` could be discharged by `trianglesC` directly, without
row 128 — not needed (`corner_laws_and_soft_of` keeps reading `hinh.triangles`), but it removes the tail's PREREVIEW item 8 worry
("the comparison lane may drop reversal_law/triangles"): both fields stay, `triangles` even unconditional. Port order: whichever lane
ports first carries `corner_values_i` as library (the corner lane's names, its module); the other imports it.

### 2.2 Row 128's bundle: B's field types + A's `root_values` (FR-CM-8, FR-CM-13, FR-CM-15)

"C satisfies every identity of cor:A-lawful on the domains stated there" — the reviewer's yardstick is `ALawfulData`. B's fields are
`ALawfulData`'s with `cornerStateSum` for `amplitude` (the genericity of the halves and of `P_ε` ASSERTED as in cor:A-lawful, `∧` / `∃`,
never assumed). A's nesting of `CS7Data` / `hyp_R` / `CSoftData` (the C-row bundles, `∀ h₁ h₂` / `∀ hQ`) is equivalent by lem:children
(ii) and lem:soft-generic (i) — PROVED as the three §6 `example`s (`CInheritsData → hyp_R`, `→ CS7Data`, `→ CSoftData`), so nothing
is lost by choosing the literal shape. A's `root_values` is added as the first field: cor:A-lawful's first clause "A(P) := A_g(P)
(any g) is well defined" has, with `C = A` substituted, the content `C(P) = A_g(P)` for every root — true, PROVED, and it forestalls
"where is the defining clause?"; dropping it costs one line (`thm_comparison_root_of` stays as the companion). The A-specific
per-induced-root sub-clause of `ALawfulData.cusp_law` (`∀ g, … = −κ treeCoefficient (deletion) hQ (deletionRoot j g)`) has no
`C` analogue and is not repeated (under the proved genericity it is the generic clause by root independence).

### 2.3 Retained from B
The skeleton (§1-§4 order, `cp_`/`av_`/`tri_`/`cs3_`/`cu_` prefixes), `cornerPolygon` as the name of the descended `C`, the proved
triangle values, `cs3_flat_law_C`, the `∃ hQ` soft field discharged through `soft_family_generic`, `uniquenessHypotheses_C_of` with
the (f) argument now a theorem, the §5/§6 layout, the unit table's honest sizes.

### 2.4 Grafted from A
`cornerPolygonSum hn` as a separate `Quotient.lift` (the `descends` witness; `thm_comparison_polygon_of` states `cornerPolygonSum hn Q
= alA_polygonAmplitude hn Q` with no arity `if`); `loopZero_turn` with the rotation-number conjunct; `root_values`;
`thm_comparison_root_of`; `AnchorValuesData.C_zero/.C_loop` (+ `.C_loopZero`); the general `tri_triangle_value`; the reading that the
cusp fallback narrows TARGETS' domain; the FR list; the verdict that the leaf is the whole remaining risk.

### 2.5 Names
Fixed (axiom-policy.json `targets`): `SM.thm_comparison`, `SM.cor_C_inherits`. Proposed: `SM.prop_anchor_values : AnchorValuesData`.
Library: `SM.cornerPolygonSum`, `SM.cornerPolygon`, `SM.AnchorValuesHypotheses`, `SM.AnchorValuesData`, `SM.anchor_values_of`,
`SM.TrianglesC` / `SM.CuspLawC` / `SM.ReversalLawC` (the CV/R tail's, this lane's module becomes their home), `SM.trianglesC`,
`SM.CInheritsData`, `SM.thm_comparison_of`, `SM.cor_C_inherits_of`, `SM.cusp_deletion_generic`. Modules at port: SM/CornerPolygon.lean
(§1), SM/AnchorValues.lean (§2), SM/Comparison.lean (§3), SM/CInherits.lean (§4); the row theorems in the last two when rows 110/112
land.

## 3. Proof routes (accepted lemmas by file:line, grep-verified 2026-09-15; where the pending rows enter)

### 3.1 Row 122 (sm-5:477-505) — PROVED (`av_*`)
1. `av_softAnchor_value F hF A` (any `SoftAnchorData m`, SM/Anchors.lean:40): `(F(P_ε) : ℚ) = mult · F(P)` at `ε = A.param`.
   `hF.soft` at the parent gives `δ_F`; `ε' := min(A.param, δ_F)/2`; `A.bound_spec` (def:anchors' `ε₀` = lem:soft-generic (i)) puts
   `P_ε` and `P_ε'` in one chamber of the polygon space; `hF.chamber` equates the values; `hF.soft` at `ε'`. The `F`-half of the
   accepted `unA_softAnchor_delta` (SM/Uniqueness.lean:333). The printed "not a bound uniform over the functions" is honoured: two
   bounds, `A.bound` (data) and `δ_F` (existential).
2. Zero anchors: `softAmplitudeMultiplier_mixed` (SM/SoftAmplitudeSectors.lean:110) at `A.admissible`, `A.mixed`; loop anchors:
   `softAmplitudeMultiplier_loop` (:120) at `A.loop`; `exact_mod_cast` back to ℤ.
3. `loop_turn := A.parent_turn` (SM/Anchors.lean, `LoopAnchor`); `loopZero_turn`: `subst A.triangle`, `A_small_values_i`
   (SM/SmallValues.lean:260), `rotationNumber_triangle (generic_regular le_rfl _)` (SM/RotationTriangle.lean:25, SM/RegularLocus.lean:38).
4. `A_g`: `av_treeCoefficient_anchor A a ha` — `soft_theorem_treeCoefficient hm A.parent_generic j q A.admissible A.bound A.bound_pos`
   (SM/SoftTheoremTree.lean:28) gives `ε₁` and, at `ε' = min(A.param, ε₁)/2`, the unique `g` with `a = softParentEdge j g` and the
   ℚ-identity at root `a`; `tree_data_labelled_chamber_constant B ⟨_, hQ⟩ hch a hm1` twice (SM/TreeChamber.lean:29, prop:A-chamber at
   the FIXED root — "without using root independence") transports `A_a` from `P_ε'` to `P_param` through `bound_spec`'s labelled
   chamber `B`; uniqueness by `softParentEdge_injective` (SM/SoftParentEdges.lean:49). Then the sector lemmas as in 2.
5. `C_hypotheses`: `cornerPolygon_chamber` by `Quotient.inductionOn₂` + `prop_C_chamber.constant` (SM/CChamber.lean:1378);
   `cornerPolygon_soft_of hs` by `hs.soft_theorem` rewritten through `cornerPolygon_projection`. **thm:C-soft enters here and only here.**

### 3.2 Row 127 (sm-6:304-311) — PROVED (`thm_comparison_of hR h7 hs`)
`uniqueness cornerPolygon (uniquenessHypotheses_C_of hR h7 hs) n hn P hP` (SM/Uniqueness.lean:454), then `cornerPolygon_projection`.
The hypotheses (a)–(f) for `cornerPolygon`:
- (a) `cornerPolygon_chamber`; `silent` := `prop_C_silent.extension/.cut` (SM/CSilent.lean:1854) with `(s, t) ↦ (t, s)`.
- (b) `cs3_flat_bridge thm_C_S3` (SM/CS3.lean:2478 `CS3Data.flat_law`, :2495 `thm_C_S3`): destructure `FlatAt` (SM/NamedWallPredicates.lean:14
  = `4 ≤ n ∧ pointZeros ∧ concurrences ∧ StrictBetween ∧ SignChanges`) → `δ ≤ radius`; `cs3_param_side` writes `w.curve s` as
  `(w.sideTuple b t).val` (`ri_sideTuple_true_val/false_val`, SM/RootIndependence.lean:122/125); `side_turn_constant` (SM/GermTurnSigns.lean:27)
  gives `IsRightSide/IsLeftSide` at `t' = δ/2`; `cornerStateSum_side_eq` (SM/HypR.lean:119) moves the two side values; the deletion
  witness is proof-irrelevant (`cp_cornerStateSum_congr`). FR-CM-11.
- (c) `h7.vertex_edge_law n hn w M a hc h₁ h₂ t s` — the shapes coincide literally (the corner lane's FR-CC-13). **thm:C-S7 enters here.**
- (d) `hR n hn w e f k hT t s` (SM/HypR.lean:83). **hyp:R enters here.**
- (e) `cornerPolygon_soft_of hs`. **thm:C-soft enters here.**
- (f) `trianglesC`: `tri_cornerStateSum_crossingFree`: for crossing-free generic `P` with all turns `τ ≠ 0`, `∅ ∈ independentSupports`
  (`empty_mem_independentSupports`, SM/InterlaceSupports.lean:44), every corner mark of every carrier is a vertex mark
  (`mem_ccpCornerList` SM/CarrierCornerPolygon.lean:329, `IsTrueCorner` SM/CarrierTrueCorners.lean:44, `ccpCornerPolygon_turn_vertex` :598)
  so `∅` is uniform (`mem_uniformDecompositions`, SM/CornerStateSum.lean:140), `carrierCrossingCount = 0`, `c(Q) = 1` by
  `corner_values_i` (§0), and every decomposition is `∅` (`Finset.eq_empty_of_isEmpty`), so `cornerStateSum = (−1)^{ℓ(P)}`;
  `tri_triangle_no_crossing` (`remote` = `¬ adjacent`, SM/Polygon.lean:63-66; `decide` on `ZMod 3`); `ℓ(K₁) = 3`, `ℓ(K₋₁) = 0` from
  `star_generic_law le_rfl` (SM/StarGenericLaw.lean:21). The printed "Its only decomposition is empty, so def:C gives −1 when ℓ = 3
  and +1 when ℓ = 0" made literal. **lem:corner-values (i) enters here and only here — as a theorem.**

### 3.3 Row 128 (sm-6:320-372) — PROVED modulo the leaf (`cor_C_inherits_of hR h7 hs`)
`hcmp := thm_comparison_of hR h7 hs`; then field by field (table in §1): `root_values` (`A_lawful.root_independent`);
`shift_invariant` (`cornerStateSum_genericShift hn k ⟨P, hP⟩`); `descends` (`cornerPolygonSum hn`, `rfl`); `chamber_constant`
(`cornerStateSum_eq_of_mem_labelledChamber`, `prop_C_chamber.constant`); `silent` (prop:C-silent); `flat_law` (`cs3_flat_law_C thm_C_S3`);
`cusp_law` (`cu_cuspLawC_of hcmp`: LEAF `cusp_deletion_generic w j hf hQ1`, then `A_lawful.cusp_law n w j hf hQ1` — `b`, uniqueness,
`κ`, the rotation jump, its `Generic → −κ·A(Q)` clause — with `hcmp` at the two sides and at `Q`); `vertex_edge_law`
(`vertex_halves_children hn w hc` + `h7.vertex_edge_law … t s`); `triple_law` (`hR … t s`); `soft_theorem` (`hs.soft_theorem` +
`soft_family_generic hn hP j q hq` for `∃ hQ` on `(0, min ε₁ δ)`); `reversal_law` (`A_lawful.reversal_law`, witnesses
`(generic_reversal P).mpr hP` vs `g1_reversal_forward hP.1` proof-irrelevant); `triangles := trianglesC`. This is the printed
"apply each identity of cor:A-lawful to its stated arguments and substitute C = A at every one of them, including the deletions
and halves just checked".

### 3.4 The leaf `cusp_deletion_generic` (sm-6:335-359) — unit U-CM-CUSPGEN, the ONLY open step
Statement: `(w : WallGerm (n+1)) (j) (hf : w.CuspAt j) (hQ1 : G1 (deleteVertex w.center j)) : Generic (deleteVertex w.center j)`.
`Generic = G1 ∧ G2` (SM/Generic.lean:11-19); G1 is `hQ1`. G2 (`¬ ∃ a b c x, distinct ∧ x ∈ edgeInterior Q a ∩ … b ∩ … c`), the printed
argument with the accepted vocabulary, template `g2_deleteVertex` (SM/DeletionGeneric.lean:11-29, the flat case) and `flat_center_g2`
(SM/FlatAdjacent.lean:79):
1. Geometry of the centre `P = w.center`: `hf : CuspAt j` (SM/CuspDefinition.lean:41-45) = `4 ≤ n+1 ∧ pointZeros = {turnSupport j} ∧
   concurrences = ∅ ∧ (¬ ∃ t ∈ [0,1], M = A + t(B − A)) ∧ SignChanges`, with `A = P (j−1)`, `M = P j`, `B = P (j+1)`. Collinearity:
   `singlePointTriple_turn_zero hf.2.1` (SM/TurnSupports.lean:58) → `det (M − A) (B − A) = 0`; `A ≠ B` by `singlePointTriple_vertices_injective`
   (SM/SinglePointTriple.lean:29) + `prev_ne_next`. `collinear_exterior_cases` (SM/CuspBetweenness.lean:40; already used in
   `cusp_cases` :52) gives `StrictBetween A B M ∨ StrictBetween M A B` (= `CuspCase … true/false`, :12): the fused edge `[A, B]` lies
   in `E_{j−1}(0) = [A, M]` (case true) or in `E_j(0) = [M, B]` (case false).
2. NEW lemma `cu_fused_interior_subset` (≈ 60 lines): `x ∈ edgeInterior Q (−1)` → `x ∈ edgeInterior P (j−1)` (case true) /
   `x ∈ edgeInterior P j` (case false). `edgeInterior Q (−1)` unfolds (SM/Polygon.lean:57, `edgePoint`, `deleteVertex_last`
   SM/DeletedTuple.lean:23, `edge_deleteVertex_last` :32) to `x = A + q (B − A)`, `0 < q < 1`; with `B = A + t (M − A)`, `0 < t < 1`
   (`StrictBetween`, SM/StrictBetween.lean:9) this is `x = A + (qt)(M − A)`, `0 < qt < 1` — an affine parameter computation (the cusp
   analogue of `fused_interior_lift`, SM/DeletionInteriors.lean:22, whose `affine_interior_subdivision` is replaced by a product of
   parameters; no case `x = M` arises). Case false symmetric with `A = M + t (B − M)`: `x = M + (t + q(1−t))(B − M)`.
3. Unchanged edges lift to themselves: `edgeInterior_deleteVertex P j hi` (SM/DeletedTuple.lean:41) for `i ≠ −1`, index `deletionIndex j i`
   (SM/DeletionIndices.lean:11-58: `_injective`, `_ne_deleted`, `_ne_prev`, `_next`, `_not_incident`, `_last`, `_zero`).
   Define the lift `cu_lift b : ZMod n → ZMod (n+1)` (`−1 ↦ j−1` or `j` by the case, else `deletionIndex j`) — a function, simpler than
   the relation `DeletionEdgeLift` (:39), so injectivity (≈ 30 lines) is `deletionIndex_injective` + `deletionIndex_ne_prev` /
   `deletionIndex_ne_deleted` ("neither `E_{j−1}(0)` nor `E_j(0)` is an edge of `Q`").
4. Remoteness transfer (≈ 150 lines, the bulk): from `hQ1` and the common point, `g1_common_interiors_remote hn hQ1` (SM/GenericTopology.lean:47)
   makes `a, b, c` pairwise remote in `Q` (needs `[Nontrivial (ZMod n)]`, from `3 ≤ n`). For the lifted edges in `P`:
   (i) two unchanged edges: `adjacent (deletionIndex j a) (deletionIndex j b) ↔ adjacent a b` when `a, b ≠ −1` (`deletionIndex_next`;
   note `deletionIndex j (i+1) = deletionIndex j i + 1` for `i ≠ −1`, and `−1 ≠ i` excludes the wrap through `j`) — a `ZMod` index lemma;
   (ii) the longer cusp edge vs an unchanged edge `k = deletionIndex j i`: its neighbours in `P` are `j−1 ± 1` / `j ± 1`; `j` and `j−1`
   are not in the image (`deletionIndex_ne_deleted/_ne_prev`); `j−2 = deletionIndex j (−2)` and `j+1 = deletionIndex j 0` are the two
   edges of `Q` adjacent to the fused edge `−1` (`deletionIndex_last`, `deletionIndex_zero`), excluded by remoteness of `i` and `−1` in `Q`.
   So the three lifted edges are pairwise remote in `P`.
5. Conclude: `ConcurrenceTriple P {ka, kb, kc}` (SM/ZeroTriples.lean:61, `concurrenceTriple_iff` :74 with the three remoteness facts and
   the common point) ∈ `concurrenceTriples P = w.concurrences` (`mem_concurrenceTriples` :70, `WallGerm.concurrences` SM/GermDefinition.lean:14),
   contradicting `hf.2.2.1 : concurrences = ∅` — exactly `flat_center_g2`'s last three lines.
Size 300-450 lines, 6-10 h; the index bookkeeping (step 4) is the part to budget for. Reassessment rule (2 attempts / 60 min per
sub-step) applies. TRUTH: the printed argument is complete and the Lean vocabulary covers every step; no new definition is needed.

## 4. Unit decomposition (byte-identical copies of Statements_FINAL.lean; statements frozen; helpers prefixed)

Check per unit: `cd work/lean && lake env lean ../drafts/comparison/U_<unit>.lean` (20 s warm). Assembly: the FINAL file IS the
skeleton — replace the leaf's `sorry` by the unit's proof (helpers `cu_*` inserted before it), clash scan, `#print axioms` (expected
standard + `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness` through def:C; `SM.lit_homfly_descent` / `SM.src_contact` only when the
corner rows are plugged in); statement review (3 lenses + 2 refuters; the readings FR-CM-* of §5 are the brief); port after the review
as library material (D-F11/D-F14), §0 deleted when the corner modules land, §5 declared and mapped only then.

| unit | prefix | content | status | lines | hours |
|---|---|---|---|---|---|
| U-CM-CPOLY | `cp_` | `cornerPolygonSum`, `cornerPolygon`, projections, `cornerPolygon_chamber` (§1) | DONE | 60 | review 0.5 |
| U-CM-AV | `av_` | row 122: `AnchorValuesHypotheses/Data`, `av_softAnchor_value`, `av_zero/loop`, `av_treeCoefficient_anchor`, `av_A_*`, `av_loopZero_turn`, `anchor_values_of`, companions (§2) | DONE | 230 | review 1 |
| U-CM-TRI | `tri_` | `trianglesC` UNCONDITIONAL, `tri_cornerStateSum_crossingFree`, `tri_triangle_no_crossing`, `tri_leftTurns_*`, `tri_triangle_value` (§3), against `corner_values_i` (§0) | DONE | 110 (+55 graft) | review 0.5 |
| U-CM-CS3 | `cs3_` | `cs3_param_side`, `cs3_flat_bridge`, `cs3_flat_law_C` (§3) | DONE | 60 | review 0.5 |
| U-CM-CMP | — | `uniquenessHypotheses_C_of`, `thm_comparison_of`, `thm_comparison_root_of`, `thm_comparison_polygon_of` (§3) | DONE (sorry-free) | 70 | review 0.5 |
| **U-CM-CUSPGEN** | `cu_` | LEAF `cusp_deletion_generic` (§3.4, steps 1-5) | **OPEN — launch now** | 300-450 | 6-10 |
| U-CM-INH | `cu_`/— | `CInheritsData`, `cu_cuspLawC_of`, `cor_C_inherits_of` (§4) | DONE modulo U-CM-CUSPGEN | 130 | review 0.5 |
| U-CM-ROWS | — | §5 one-liners at `thm_C_S7`, `thm_C_soft`; port SM/CornerPolygon, SM/AnchorValues, SM/Comparison, SM/CInherits; map rows 122/127/128; delete §0 | after rows 110/112 | 30 | 1 |
| total | | 1 leaf open | **≈ 1,250 (FINAL 896 + 300-450 leaf lines)** | ≈ 6-10 prover-h + 4.5 h review/port; 1 wave; critical path U-CM-CUSPGEN → statement review → port → the corner rows |

Launch NOW: U-CM-CUSPGEN (floor-free, corner-free, R-free — pure accepted geometry) and, in parallel, the independent statement review
of Statements_FINAL.lean (the brief: this file's §1 and §5, the printed statements, the accepted `ALawfulData` / `UniquenessHypotheses`).
Until rows 110/112 land, the conditional theorems are library material and FINAL_REVIEW should say "122 conditional-complete on row
112; 127/128 conditional-complete on rows 110/112" (or "…, one lemma leaf open (cusp deletion genericity)" if U-CM-CUSPGEN stalls).

## 5. Fidelity risks FR-CM-* — the executor writes these into AUTHOR_NOTES BEFORE the rows are stated

Row 122 (sm-5:461-476).
- **FR-CM-1 (F's domain; "constant on chambers").** `F : ∀ n [NeZero n], GenericPolygon n → ℤ` — thm:uniqueness's reviewed reading (a
  function on the orbit space `𝓤_n/(ℤ/n)`, unconstrained below arity 3; integer-valued: thm:uniqueness "assigning an integer").
  "Constant on chambers" = constancy on the chambers of the POLYGON space (def:chamber), `UniquenessHypotheses.chamber` verbatim — not
  labelled-chamber constancy and NOT silence (the printed hypothesis names chambers only; thm:uniqueness's (a) also contains silence,
  unused here — `UniquenessHypotheses.toAnchorValuesHypotheses` records that (a)+(e) ⊇ these hypotheses).
- **FR-CM-2 (the soft hypothesis and the two bounds).** "Satisfying the soft theorem in the form of thm:C-soft at every admissible soft
  insertion into a generic polygon" = `UniquenessHypotheses.soft` verbatim = `CSoftData.soft_theorem` with `F` for `C`: `∃ δ > 0,
  ∀ ε ∈ (0, δ), ∀ hQ : Generic (P_ε), (F(P_ε) : ℚ) = softAmplitudeMultiplier P j q · F(P)`. The function-dependent threshold `δ_F` is the
  existential; the anchor's geometric bound `ε₀` is the DATA `A.bound` with `A.bound_spec` (def:anchors, "part of the anchor data;
  not a bound uniform over the functions"). The identities are asserted at the anchor's OWN parameter `A.param` ("at the original ε").
- **FR-CM-3 (anchors as data; the loop clause as two fields; the (L₀) turn).** Anchors are the accepted def:anchors structures
  `ZeroAnchor m r`, `LoopAnchor m r`, `LoopAnchorZero m` (SM/Anchors.lean:40-98; `Z = Y = A.polygon = softInsertion A.parent A.vertex
  A.vector A.param`, parent `A.parent`, insertion vertex `A.vertex`, `τ_j(P) = turn A.parent A.vertex : SignType` cast to ℤ, the
  polygon presented as `polygonProjection ⟨A.polygon, A.polygon_generic⟩`). "For every loop anchor" is ONE printed sentence over TWO
  Lean types, hence `loop` (case (L)) and `loopZero` (case (L₀)). "In case (L), τ_j(P) = −sgn(r)" is `LoopAnchor.parent_turn` restated
  (a consequence of the definition, printed). "In case (L₀), the orientation sign of the parent triangle": "orientation sign" is not a
  defined term of SM15; BOTH readings are asserted — the common sign of the three turns of the generic triangle (lem:chi-basic (i),
  lem:A-small-values (i)) and its rotation number (lem:rot, `rotationNumber_triangle`) — so `loopZero_turn` is at least as strong as
  either reading.
- **FR-CM-4 (the A_g clause).** "Every anchor root other than the soft edge" = `a : ZMod (m+1)`, `a ≠ A.softEdge` (`= softOldIndex
  A.vertex A.vertex`, def:anchors' `E_j`); "the corresponding parent root" = the unique `g` with `a = softParentEdge A.vertex g`
  (thm:A-soft's correspondence: unchanged edges to themselves, the return edge to `E_j`; `∃!` exactly as the accepted
  `soft_theorem_treeCoefficient`); `A_g = treeCoefficient` at the (G1) witnesses `A.polygon_generic.1`, `A.parent_generic.1`.
  "Without using root independence": the proof uses prop:A-chamber's labelled-chamber constancy at the fixed root
  (`tree_data_labelled_chamber_constant`), not thm:root-indep-proof.
- **FR-CM-5 (C on the polygon space).** "The function C" is `cornerPolygon n : GenericPolygon n → ℤ`, the `Quotient.lift` of
  `cornerStateSum` along def:C's cyclic quotient (compatibility = the accepted `cornerStateSum_genericShift`), `0` below arity 3 where
  def:C assigns nothing (irrelevant: every clause quantifies `3 ≤ n`); `cornerPolygon_projection` identifies it with `cornerStateSum` on
  every labelled representative, and the companions `AnchorValuesData.C_zero/.C_loop/.C_loopZero` state the labelled identities. The
  chamber half is prop:C-chamber (accepted), the soft half is thm:C-soft (`hs`, explicit until row 112).

Row 127 (sm-6:299-303).
- **FR-CM-6 (generic polygon; A).** "C(P) = A(P) for every generic polygon P" is stated on generic labelled representatives for every
  arity `n ≥ 3` (every accepted C row's convention; `[NeZero n]`, `hn : 3 ≤ n` are def:C's presupposition binders), with
  `A(P) = amplitude P hP.1 hn` = cor:A-lawful's `A(P) := A_g(P)` at root 0 (SM/ALawful.lean:37). Both sides descend (`descends`,
  `cornerStateSum_genericShift`), so the labelled equality IS the polygon equality: companion `thm_comparison_polygon_of`; every root:
  companion `thm_comparison_root_of`. A plain theorem, not a one-field bundle (the shape of `SM.uniqueness`).
- **FR-CM-7 (hyp:R).** "Assume Hypothesis R" = the explicit parameter `(hR : hyp_R)` (policy mode `explicit_parameter`; the printed
  round-5 status "hypothesis (d) discharged by citing Hypothesis R by label"); it is consumed exactly as thm:uniqueness's (d)
  (`UniquenessHypotheses.triple`, `hyp_R`'s two-parameter side form IS that field with `(tp, tm) = (t, s)`) and, in row 128, as
  `triple_law` and through `thm_comparison_of`. No `Bridge.sm_R` inside the rows (rem:conditional, sm-6: rows 127/128 "do use it";
  row 184 discharges it). Row 122 does not mention R.
- **FR-CM-10 (the proof is the printed one; where the pending rows enter).** thm:uniqueness at `cornerPolygon` with (a) prop:C-chamber +
  prop:C-silent, (b) thm:C-S3, (c) thm:C-S7 (`h7`), (d) hyp:R (`hR`), (e) thm:C-soft (`hs`), (f) lem:corner-values (i) — the last as the
  PROVED `corner_values_i` (clause (ii), `isolated_zero`, is not used, as printed). Only rows 110/112 remain hypotheses.
- **FR-CM-11 ((b), the CS3 bridge).** `CS3Data.flat_law` is stated for side parameters below its own radius `δ` with sides named by
  `IsRightSide/IsLeftSide` (turn at `j`); thm:uniqueness (b) wants all nonzero parameters with the named turn. The bridge moves each side
  value to `δ/2` by prop:C-chamber's side constancy (`cornerStateSum_side_eq`) and identifies the sides by `side_turn_constant`; the
  deletion's genericity witness is quantified (lem:children (i) supplies it). Same proposition, no strengthening.
- **FR-CM-12 ((f), the triangle sentences).** "Its only decomposition is empty, so def:C gives −1 when ℓ = 3 and +1 when ℓ = 0" is the
  theorem `tri_cornerStateSum_crossingFree` (crossing-free + all turns one sign ⇒ `C = (−1)^ℓ`), specialised to `star 1`, `starNeg 1`
  (lem:star-generic (iii) for their genericity and turns); `TrianglesC` is the CV/R tail's Prop (the two projections are `Generic (star 1)`,
  `Generic (starNeg 1)` in that order — cvtail PREREVIEW P1). Companion: `tri_triangle_value : C(T) = −τ` (lem:A-small-values (i)'s shape).

Row 128 (sm-6:313-319).
- **FR-CM-8 (domains and genericity witnesses).** "Every identity of cor:A-lawful on the domains stated there" = one field per field of
  the accepted `ALawfulData` with `cornerStateSum` for `amplitude`, same binders/sides/signs; every argument of an identity is generic
  BEFORE `C = A` is substituted, as the printed proof requires (sm-6:322-333): sides by `sideTuple.property`, the flat deletion by
  lem:children (i) (`generic_deleteVertex`), the halves by lem:children (ii) (`vertex_halves_children`), `P_ε` by lem:soft-generic (i)
  (`soft_family_generic`), `P̄` by `generic_reversal`, `K_{±1}` by lem:star-generic (iii), the cusp deletion by the printed domain check
  (the leaf). Witnesses are ASSERTED (`∧` / `∃`), never assumed — exactly `ALawfulData`'s convention.
- **FR-CM-9 (cusp law domain).** Hypothesis "when the deletion satisfies (G1)" = `G1 (deleteVertex w.center j)` exactly as cor:A-lawful
  / `ALawfulData.cusp_law`; the conclusion ASSERTS `∃ hQ : Generic (P(0)∖j)` (sm-6:335-359) so `C(P(0)∖j)` is defined, `κ = ±1` the
  rotation jump, loop/no-loop sides as in the accepted thm:A-S4; NO emptiness hypothesis (threaded cusps included; TARGETS "the full
  cusp jump on the source domain (the deletion satisfies G1), including threaded cusps"). The A-specific per-induced-root sub-clause
  is not repeated (§2.2). A `Generic` HYPOTHESIS instead would narrow the domain against TARGETS — not adopted (§7).
- **FR-CM-13 (the defining clause).** cor:A-lawful's "A(P) := A_g(P) (any g) is well defined on generic polygons" becomes TWO things:
  `root_values` (`C(P) = A_g(P)` for every root — the substitution of `C = A`, an extra true clause) and `shift_invariant` / `descends`
  ("well defined on generic polygons" for `C`, def:C's cyclic quotient). `chamber_constant` is included because printed ("chamber
  constancy") though it is prop:C-chamber's.
- **FR-CM-14 (side conventions).** `C(P_±)` at every pair of side parameters (the accepted C-row convention of prop:C-silent / hyp:R /
  thm:C-S5, equivalent to def:germ's chamber values by prop:C-chamber `cornerStateSum_side_eq`); flat sides named by the turn at `j`
  (thm:A-S3 / thm:uniqueness (b)); the printed "for a chamber-side identity … the constant side values of C and of A agree; no value at
  the wall centre and no limit is used" is literally the pointwise substitution at every side parameter.
- **FR-CM-15 (field types vs the C-row bundles).** `vertex_edge_law`, `triple_law`, `soft_theorem` are in `ALawfulData`'s shapes
  (`Generic λ₁ ∧ Generic λ₂ ∧ ∀ s t …`; `∀ … → ∀ s t …`; `∃ ε₁ > 0, ∀ ε < ε₁, ∃ hQ, …`), not the C-row bundles `CS7Data` (`∀ h₁ h₂`), `hyp_R`,
  `CSoftData` (`∀ hQ`) that DESIGN_A nested; the two are equivalent (lem:children (ii), lem:soft-generic (i), proof irrelevance) and the
  §6 `example`s PROVE the bundle-direction (`CInheritsData → hyp_R / CS7Data / CSoftData`). The CV/R tail reads none of these three
  fields.
- **FR-CM-16 (reversal, triangles).** `ReversalLawC` with the witness `(generic_reversal P).mpr hP` (def:shift's reversal preserves
  (G1), (G2): the printed "Reversal permutes the vertex triples and preserves the edge segments"); `TrianglesC` on `star 1`, `starNeg 1`.
- **FR-CM-17 (hyp:R in row 128).** `cor_C_inherits (hR : hyp_R)` consumes `hR` through `thm_comparison_of hR …` at every substituted
  argument and as `triple_law`; no other row of this lane takes `hR`.

## 6. The row-128 bundle shared with the CV/R tail's row 184 — FINAL shape and the exact edits

FINAL: `CInheritsData` as in Statements_FINAL.lean §4 (12 fields: `root_values`, `shift_invariant`, `descends`, `chamber_constant`,
`silent`, `flat_law`, `cusp_law : CuspLawC`, `vertex_edge_law` (ALawful-shaped), `triple_law` (ALawful-shaped), `soft_theorem`
(`∃ hQ`), `reversal_law : ReversalLawC`, `triangles : TrianglesC`). `CuspLawC`, `ReversalLawC`, `TrianglesC` are byte-identical to
work/drafts/cvtail/Statements_FINAL.lean:874-905 (checked by the §6 consumer example). This lane OWNS row 128's bundle.

Exact edits to work/drafts/cvtail/Statements_FINAL.lean (all in §5, lines 907-938; NOTHING else changes):
1. Replace the `structure CInheritsData … triangles : TrianglesC` block (:907-933) by this lane's §4 structure (adds `root_values` as
   the first field; retypes `vertex_edge_law : CS7Data` → the `Generic λ₁ ∧ Generic λ₂ ∧ ∀ s t …` field, `triple_law : hyp_R` → the
   `∀ n hn w e f k, TripleAt → ∀ s t, …` field, `soft_theorem : CSoftData` → the `∃ ε₁ > 0, ∀ ε < ε₁, ∃ hQ, …` field). Mark it "VERBATIM
   comparison/Statements_FINAL.lean §4 — TO BE UNIFIED".
2. Keep the placeholder `theorem cor_C_inherits (_hR : hyp_R) : CInheritsData := by sorry` (:937) until SM/CInherits.lean is ported,
   then delete it together with the three Props and the structure (import SM.CInherits instead).
3. `CornerLawsAndSoftData` (:943-968), `corner_laws_and_soft_of` (:973-985) and `corner_laws_and_soft` (:989-990): NO change —
   `corner_laws_and_soft_of` reads `hinh.cusp_law`, `hinh.reversal_law`, `hinh.triangles` only, at unchanged types (this lane's §6 first
   `example`). `CyclicLawC` (:893) stays the tail's own (discharged by `cornerStateSum_genericShift`; subsumed by `shift_invariant`).
Optional (not required): `triangles := trianglesC` in `corner_laws_and_soft_of` would make that field independent of row 128; the tail
should keep `hinh.triangles` (TARGETS: "inherited with cor:A-lawful").
Interface to the corner lane (rows 110/112): the FINAL reads `h7.vertex_edge_law` with `(h : VertexEdgeAt) (h₁ h₂ : Generic …) (tp tm)`
and `hs.soft_theorem` with `∀ hQ` and the ℚ multiplier — the corner FINAL's shapes verbatim (§0). A change there to `∃ hQ` or `∧ Generic λᵢ`
costs a ≤ 10-line bridge in `uniquenessHypotheses_C_of` / `cor_C_inherits_of` (the §6 examples show both directions typecheck). §0's
`corner_values_i` copy is the corner lane's PROVED clause (i), unchanged at port (§2.1).

## 7. Riskiest steps (ranked) and fallbacks

1. **U-CM-CUSPGEN** (the only open leaf; ≈ 300-450 lines, 6-10 h): plane geometry + `deleteVertex` index bookkeeping. Route §3.4 with
   every vocabulary item accepted; the sub-steps are independently testable (`cu_fused_interior_subset`, the lift's injectivity, the
   adjacency-transfer index lemma, the assembly). Fallback (recorded, NOT adopted): `CuspLawC` with `Generic (deletion)` as an extra
   HYPOTHESIS would prove now (`cu_cuspLawC_of` already has that form internally) but narrows the domain against TARGETS ("the deletion
   satisfies G1") and would force the same weakening on row 184's `cusp` field — so it is only the honest intermediate state
   ("one lemma leaf open"), never a statement change.
2. **Statement review of `CInheritsData`** (ALawful-shaped fields + `root_values`): the §6 examples and FR-CM-13/15 are the brief;
   either alternative (drop `root_values`; nest the bundles) is a field-type-only change with the proofs already in hand.
3. **Interface drift with the corner lane**: §0 copies `CS7Data`, `CSoftData`, `corner_values_i`; consumers read `h7.vertex_edge_law`,
   `hs.soft_theorem`, `corner_values_i … .2.2` by name; ≤ 10-line bridges each if the shapes move. Freeze before U-CM-ROWS.
4. **(L₀) reading** (FR-CM-3): both readings asserted; if a reviewer wants only one, weakening is a one-line change (the proof supplies both).
5. **Proof-irrelevance rewrites** in `cor_C_inherits_of` / `cu_cuspLawC_of` (`hcmp` against differently spelled witnesses) typecheck now;
   a port that changes witness spellings may need `cp_cornerStateSum_congr` / `show`. Cheap.
6. **Rows stay conditional** until 110/112 land (GAP-2 through thm:floor) — nothing in this lane depends on GAP-2 otherwise; all `_of`
   theorems and `trianglesC` are unconditional library material NOW, portable after the statement review, mapped only with the rows.
