# DESIGN A — rows 122 prop:anchor-values, 127 thm:comparison, 128 cor:C-inherits (fidelity-first), 2026-09-15

Architect A of the comparison lane (the last undesigned piece of the GAP-2 chain). Sketch:
work/drafts/comparison/Sketch_A.lean (`cd work/lean && lake env lean ../drafts/comparison/Sketch_A.lean`:
0 errors, 668 lines, 18 s; statements sorry-free; exactly 5 `sorry`: the 2 LEAVES `cmp_triangle_value`,
`cmp_cusp_deletion_generic` and the 3 ROW THEOREMS of §5, which are one-liners once rows 105/110/112 land).
PROVED outright: the whole of row 122 except its "C satisfies these hypotheses" soft half (which is
`hs : CSoftData` by construction); the descent `cmp_C`; the flat bridge CS3 → thm:uniqueness (b); the
assemblies `cmp_uniqueness_hypotheses_of`, `thm_comparison_of`, `cor_C_inherits_of`; all companions.

Sources (SM15): reference/SM/sm-5-transport.tex:461-476 / proof 477-501 (122); sm-6-comparison.tex:299-303
/ 304-311 (127); 313-319 / 320-368 (128). Dependencies (tools/claims.py, blueprint/DEPENDENCIES.json):
122 ← def:anchors, lem:soft-generic, prop:A-chamber, prop:C-chamber, thm:A-soft, thm:C-soft;
127 ← def:C, def:polygon, hyp:R, lem:corner-values, prop:C-chamber, prop:C-silent, thm:C-S3, thm:C-S7,
thm:C-soft, thm:uniqueness; 128 ← cor:A-lawful, def:C, def:germ, def:walls, lem:children, lem:soft-generic,
lem:star-generic, thm:comparison; 184 SM:corner_laws_and_soft ← cor:C-inherits, Bridge:theorem, thm:C-soft, thm:C-S5.
Pending inputs: rows 105 lem:corner-values (`CornerValuesData`), 110 thm:C-S7 (`SM.thm_C_S7 : CS7Data`),
112 thm:C-soft (`SM.thm_C_soft : CSoftData`) — corner lane, work/drafts/corner/Statements_FINAL.lean §3-§5,
copied VERBATIM into Sketch_A §0 ("to be unified"). Fixed names (work/lean/axiom-policy.json `targets`):
`SM.thm_comparison`, `SM.cor_C_inherits`; hyp:R mode `explicit_parameter` (`SM.hyp_R : Prop`, SM/HypR.lean:83;
consumers take `(hR : hyp_R)`; Bridge/SmR.lean:51 `sm_R_of_cv_R`; the CV/R tail's row 183 `Bridge.sm_R`
discharges it in row 184). Proposed name: `SM.prop_anchor_values : AnchorValuesData`.

## 0. Summary of the decisions

| | decision |
|---|---|
| domain of "a function on generic polygons" | `F : ∀ (n : ℕ) [NeZero n], GenericPolygon n → ℤ`, the accepted thm:uniqueness object (SM/Uniqueness.lean:35); `C` enters through its cyclic descent `cmp_C` (Quotient.lift on `genericCyclicSetoid` by the accepted `cornerStateSum_genericShift`, SM/CChamber.lean:1362) |
| 122 shape | `AnchorValuesData`, 9 fields = the printed clauses: `zero`, `loop`, `loop_triangle` (the two loop-anchor kinds of def:anchors), `loop_turn`, `loop_triangle_turn`, `C_hypotheses : AnchorValuesHypotheses cmp_C`, `A_zero`, `A_loop`, `A_loop_triangle`; hypotheses bundle `AnchorValuesHypotheses F` = `UniquenessHypotheses.chamber` + `.soft` verbatim |
| 127 shape | plain theorem (as `SM.uniqueness`): `thm_comparison (hR : hyp_R) : ∀ n [NeZero n] (hn) (P) (hP : Generic P), cornerStateSum hn hP = amplitude P hP.1 hn` |
| 128 shape | `CInheritsData` = the CV/R tail's proposal ADOPTED verbatim (cvtail/Statements_FINAL.lean §5: `CuspLawC`, `ReversalLawC`, `TrianglesC`, 11 fields) PLUS one field `root_values` (`C(P) = A_g(P)` ∀ g); `cor_C_inherits (hR : hyp_R) : CInheritsData` |
| where the pending rows enter | conditional library theorems `anchor_values_of (hs : CSoftData)`, `thm_comparison_of (hCV : CornerValuesData) (h7 : CS7Data) (hs : CSoftData) (hR)`, `cor_C_inherits_of hCV h7 hs hR` (D-F11/D-F14); row theorems declared/mapped only when the three corner rows are accepted |
| new mathematics | two leaves: `C` of a generic triangle (the printed (f) sentence) and the cusp deletion's genericity (sm-6:335-359) |

## 1. Fidelity risks FR-CM-* — recorded BEFORE stating (to be copied into AUTHOR_NOTES)

Row 122 (sm-5:461-476).
- FR-CM-1 "a function on generic polygons of all arities, constant on chambers": `F : ∀ n [NeZero n], GenericPolygon n → ℤ`
  (thm:uniqueness' reviewed reading: literally a function on the orbit space `𝓤_n/(ℤ/n)`, unconstrained below arity 3);
  "constant on chambers" = constancy on the chambers of the POLYGON space (`chamber`, def:chamber), `UniquenessHypotheses.chamber`
  verbatim — not labelled-chamber constancy, and NOT silence (the printed hypothesis names chambers only; the consumer
  thm:uniqueness cites "(a) and (e)", and its (a) also contains silence, which is unused here — `AnchorValuesHypotheses.of_uniqueness`).
- FR-CM-2 "satisfying the soft theorem in the form of thm:C-soft at every admissible soft insertion into a generic polygon":
  `UniquenessHypotheses.soft` verbatim = `CSoftData.soft_theorem` with `F` for `C`: `∃ δ > 0, ∀ ε ∈ (0, δ), ∀ hQ : Generic (P_ε),
  (F(P_ε) : ℚ) = softAmplitudeMultiplier P j q · F(P)`. The function-dependent threshold `δ_F` is the existential; the anchor's
  geometric bound `ε₀` is the DATA `A.bound` of def:anchors (SM/Anchors.lean:52-58) — the two-bound structure of the printed proof
  ("not a bound uniform over the functions") is kept, and the identities are asserted at the anchor's OWN parameter `A.param`.
- FR-CM-3 "F(Z) = 0 for every zero anchor, F(Y) = τ_j(P) F(P) for every loop anchor": anchors are the accepted def:anchors structures
  `ZeroAnchor m r`, `LoopAnchor m r`, `LoopAnchorZero m` (`Z = Y = A.polygon = softInsertion A.parent A.vertex A.vector A.param`,
  parent `A.parent`, insertion vertex `A.vertex`); the loop clause is ONE printed sentence over two Lean types, hence the two
  fields `loop` (case (L)) and `loop_triangle` (case (L₀)); `τ_j(P) = turn A.parent A.vertex : SignType`, cast to ℤ; identities in
  ℤ (the printed `F` is integer-valued: "assigning an integer", thm:uniqueness). The polygon is presented as
  `polygonProjection ⟨A.polygon, A.polygon_generic⟩` (def:polygon's representative convention).
- FR-CM-4 "In case (L), τ_j(P) = −sgn(r)": field `loop_turn`, literally `LoopAnchor.parent_turn` of def:anchors (a consequence of
  the definition, restated because printed; `SignType.sign r`).
- FR-CM-5 "in case (L₀), it is the orientation sign of the parent triangle": read as the common sign of the three turns of the
  generic parent triangle (lem:chi-basic (i) / lem:A-small-values (i): `A_small_values_i`, SM/SmallValues.lean:260), which equals
  its rotation number (lem:rot; `rotationNumber_triangle`, SM/RotationTriangle.lean:25). Field `loop_triangle_turn`: `τ_j ≠ 0 ∧
  (∀ i, τ_i = τ_j) ∧ rot(P) = τ_j`. "Orientation sign" is not a defined term of SM15; both readings are recorded.
- FR-CM-6 "The function C satisfies these hypotheses": field `C_hypotheses : AnchorValuesHypotheses cmp_C` — `C` read on the polygon
  space through its cyclic descent `cmp_C` (`cmp_C_projection : cmp_C n (polygonProjection ⟨P,hP⟩) = cornerStateSum hn hP`); the
  chamber half is prop:C-chamber (accepted, `prop_C_chamber.constant`), the soft half is thm:C-soft (`hs : CSoftData`, explicit).
  Companions `AnchorValuesData.C_zero / C_loop` state the resulting labelled identities `C(Z) = 0`, `C(Y) = τ_j C(P)`.
- FR-CM-7 "The same identities hold for A_g at every anchor root other than the soft edge, with the corresponding parent root used
  on the right-hand side": fields `A_zero`, `A_loop`, `A_loop_triangle` on `treeCoefficient` (def:treesum's `A_g`) at every root
  `a ≠ A.softEdge` (`= softOldIndex j j`, def:anchors' soft edge `E_j`), with the parent root `g` the UNIQUE one with
  `a = softParentEdge A.vertex g` (thm:A-soft's correspondence: unchanged edges to themselves, the return edge to `E_j`;
  `∃!` as in the accepted `soft_theorem_treeCoefficient`, SM/SoftTheoremTree.lean:28). G1 witnesses `A.polygon_generic.1`,
  `A.parent_generic.1`. The printed "without using root independence" is honoured: the proof uses prop:A-chamber's labelled
  chamber constancy at the fixed root (`A_chamber`, SM/TreeChamber.lean:92, clause 2), not thm:root-indep-proof.

Row 127 (sm-6:299-303).
- FR-CM-8 "Assume Hypothesis R": explicit parameter `(hR : hyp_R)` (policy `explicit_parameter`; `SM.hyp_R` is the all-side-points
  form, equivalent to the chamber-value form by `hyp_R_iff_base`, SM/HypR.lean); it enters ONLY as thm:uniqueness (d)
  (`UniquenessHypotheses.triple`, exactly the printed "(d) Hypothesis R"). Row 184 discharges it with `Bridge.sm_R`.
- FR-CM-9 "C(P) = A(P) for every generic polygon P": labelled form `cornerStateSum hn hP = amplitude P hP.1 hn` for every arity
  `n ≥ 3` and every generic labelled tuple, `A(P) = amplitude` = cor:A-lawful's `A(P) := A_g(P)` at root 0 (SM/ALawful.lean:37).
  Both sides are cyclically invariant (accepted), so the polygon-level statement is the companion `thm_comparison_polygon_of`
  (`cmp_polygonSum = alA_polygonAmplitude` on `GenericPolygon n`); `C(P) = A_g(P)` for every root is `thm_comparison_root_of`.
  A plain theorem (the shape of the sibling `SM.uniqueness`), not a one-field bundle.
- FR-CM-10 The proof is the printed one: thm:uniqueness at `cmp_C` with (a) prop:C-chamber + prop:C-silent, (b) thm:C-S3,
  (c) thm:C-S7, (d) hyp:R, (e) thm:C-soft, (f) lem:corner-values (i). The three pending rows are explicit hypotheses
  `hCV : CornerValuesData`, `h7 : CS7Data`, `hs : CSoftData` of `thm_comparison_of`; nothing else is assumed.
- FR-CM-11 (b): `CS3Data.flat_law` (SM/CS3.lean:2478) is stated for side parameters below its own radius `δ` with the sides named by
  `IsRightSide/IsLeftSide` (turn at `j`); thm:uniqueness (b) wants all nonzero parameters with the named turn. The bridge
  `cmp_flat_bridge` (PROVED) moves each side value to `δ/2` by prop:C-chamber's side constancy (`cornerStateSum_side_eq`,
  SM/HypR.lean:119) and `side_turn_constant` (SM/GermTurnSigns.lean:27); the deletion's genericity witness is quantified
  (proof-irrelevant; lem:children (i) supplies it). Same proposition, no strengthening.
- FR-CM-12 (f): the printed two sentences ("Its only decomposition is empty, so def:C gives −1 when ℓ = 3 and +1 when ℓ = 0")
  become the library lemma `cmp_triangle_value : C(T) = −τ` for every generic triangle with common turn `τ` (the shape of
  lem:A-small-values (i)); `TrianglesC` (`C(K₁) = −1 ∧ C(K₋₁) = +1`) follows from lem:star-generic's turns.

Row 128 (sm-6:313-319).
- FR-CM-13 "every identity of cor:A-lawful on the domains stated there": one field per field of the accepted `ALawfulData`
  (SM/ALawful.lean:44-131) with `cornerStateSum` for `amplitude`; cor:A-lawful's defining clause `A(P) := A_g(P)` becomes
  `root_values : C(P) = A_g(P)` for every root (its substitution — the ONE field added to the CV/R tail's proposal);
  `shift_invariant`/`descends`/`chamber_constant` are `C`'s own (def:C row, prop:C-chamber), included because printed
  ("well defined on generic polygons", "chamber constancy").
- FR-CM-14 the cusp law: `CuspLawC` (cvtail, adopted): domain `G1 (deleteVertex …)` exactly as cor:A-lawful ("when the deletion
  satisfies (G1)"); the conclusion ASSERTS `∃ hQ : Generic (P(0)∖j)` — the printed proof's domain check (sm-6:335-359) — so
  `C(P(0)∖j)` is defined; `κ = ±1` the rotation jump, loop/no-loop sides as in the accepted thm:A-S4/cor:A-lawful; NO emptiness
  hypothesis (threaded cusps included, TARGETS). The A-specific per-induced-root sub-clause of `ALawfulData.cusp_law` is not
  repeated (under the proved genericity it is equivalent to the generic clause by root independence).
- FR-CM-15 the vertex–edge, triple and soft fields are the C-row bundles `CS7Data`, `hyp_R`, `CSoftData` (the accepted C-row
  conventions: sides at all parameter pairs, genericity of `λᵢ`/`P_ε` quantified) rather than literal copies of the A shapes
  (`Generic λ₁ ∧ Generic λ₂ ∧ …`, `∃ hQ`); they are equivalent to those by lem:children (ii) / lem:soft-generic (i) and
  prop:C-chamber, and are what row 184 consumes. The triple law for `C` IS Hypothesis R (`triple_law : hyp_R`).
- FR-CM-16 reversal: `ReversalLawC` with the witness `(generic_reversal P).mpr hP` (def:shift's reversal preserves (G1),(G2):
  `generic_reversal`, SM/GenericReversal.lean:64 — the printed "Reversal permutes the vertex triples and preserves the edge
  segments"). Triangles: `TrianglesC` on `star 1`, `starNeg 1` (lem:star-generic (iii)).
- FR-CM-17 hyp:R enters `cor_C_inherits (hR : hyp_R)` once, through `thm_comparison hR` at every substituted argument and as the
  `triple_law` field; rem:conditional (sm-6) is respected: no other row of this lane takes `hR`.

## 2. Statements (clause map; Sketch_A.lean)

### Row 122 → `AnchorValuesData` (§2 of the sketch)
`AnchorValuesHypotheses F : Prop := { chamber : ∀ n [NeZero n] (hn : 3 ≤ n) (P Q : GenericPolygon n), Q ∈ chamber P → F n Q = F n P,
soft : ∀ n [NeZero n] (hn) (P) (hP) (j) (q), SoftAdmissible P j q → ∃ δ > 0, ∀ ε, 0 < ε → ε < δ → ∀ hQ : Generic (softInsertion P j q ε),
(F (n+1) ⟦P_ε⟧ : ℚ) = softAmplitudeMultiplier P j q * (F n ⟦P⟧ : ℚ) }` (both fields byte-identical to SM/Uniqueness.lean:37-38, 72-76).
Fields of `AnchorValuesData` (printed clause → field):
| printed | field | status |
|---|---|---|
| F(Z) = 0 for every zero anchor | `zero : ∀ F, AnchorValuesHypotheses F → ∀ m [NeZero m] r (A : ZeroAnchor m r), F (m+1) ⟦A.polygon⟧ = 0` | PROVED |
| F(Y) = τ_j(P) F(P) for every loop anchor (L) | `loop : … (A : LoopAnchor m r), F (m+1) ⟦A.polygon⟧ = (turn A.parent A.vertex : ℤ) * F m ⟦A.parent⟧` | PROVED |
| … (L₀) | `loop_triangle : … (A : LoopAnchorZero m), same` | PROVED |
| In case (L), τ_j(P) = −sgn(r) | `loop_turn : turn A.parent A.vertex = -SignType.sign r` | PROVED |
| in case (L₀), the orientation sign of the parent triangle | `loop_triangle_turn : turn ≠ 0 ∧ (∀ i, turn A.parent i = turn A.parent A.vertex) ∧ rotationNumber A.parent = τ_j` | PROVED |
| The function C satisfies these hypotheses | `C_hypotheses : AnchorValuesHypotheses cmp_C` | chamber PROVED; soft = `hs` |
| the same identities for A_g at every anchor root other than the soft edge, parent root on the right | `A_zero : ∀ … (a : ZMod (m+1)), a ≠ A.softEdge → treeCoefficient A.polygon _ a _ = 0`; `A_loop`, `A_loop_triangle : a ≠ A.softEdge → ∃! g, a = softParentEdge A.vertex g ∧ treeCoefficient A.polygon _ a _ = τ_j * treeCoefficient A.parent _ g _` | PROVED |
Row theorem: `prop_anchor_values : AnchorValuesData := anchor_values_of thm_C_soft` (declared when row 112 lands).

### Row 127 → `thm_comparison` (§3, §5)
`theorem thm_comparison (hR : hyp_R) : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
cornerStateSum hn hP = amplitude P hP.1 hn` — one printed clause, one conclusion. Library form `thm_comparison_of hCV h7 hs hR`
(PROVED modulo the leaves); companions `thm_comparison_root_of` (every root `g`), `thm_comparison_polygon_of` (polygon space).
Row theorem := `thm_comparison_of corner_values thm_C_S7 thm_C_soft hR`.

### Row 128 → `CInheritsData` (§4, §5)
`theorem cor_C_inherits (hR : hyp_R) : CInheritsData`, fields (all with `cornerStateSum` for `amplitude`): `root_values`,
`shift_invariant`, `descends`, `chamber_constant`, `silent`, `flat_law` (`∃ hQ : Generic (deleteVertex w.center j), ∀ sRight sLeft …`),
`cusp_law : CuspLawC`, `vertex_edge_law : CS7Data`, `triple_law : hyp_R`, `soft_theorem : CSoftData`, `reversal_law : ReversalLawC`,
`triangles : TrianglesC`. Library form `cor_C_inherits_of hCV h7 hs hR` (PROVED modulo the leaves); row theorem :=
`cor_C_inherits_of corner_values thm_C_S7 thm_C_soft hR`.

## 3. The row-128 shape shared with the CV/R tail's row 184 — ADOPT, with one added field

The CV/R tail (work/drafts/cvtail/Statements_FINAL.lean §5, PLAN_FINAL.md FR-F-184-4) proposed `CInheritsData` as "ALawfulData with
`cornerStateSum`, minus `root_independent` and minus the per-induced-root cusp sub-clause", with `CuspLawC`, `ReversalLawC`,
`TrianglesC` and the placeholder `cor_C_inherits (_hR : hyp_R) : CInheritsData := sorry`. This lane ADOPTS all of it byte-for-byte
(Sketch_A §0 and §4 copy the three Props and the eleven fields verbatim) and ADDS the first field
`root_values : ∀ n [NeZero n] (hn) (P) (hP : Generic P) (g : ZMod n), cornerStateSum hn hP = treeCoefficient P hP.1 g hn`
(FR-CM-13: cor:A-lawful's defining clause with `C = A` substituted; the printed "every identity" includes it, and it is the
literal content of thm:comparison carried into the corollary). Consequences for row 184: `corner_laws_and_soft_of (hR) (h7) (hs)
(hinh : CInheritsData)` reads `hinh.cusp_law`, `hinh.reversal_law`, `hinh.triangles` only (checked: Sketch_A §6 `example`), so it
needs NO change — not even a field-type change; the row `corner_laws_and_soft := corner_laws_and_soft_of Bridge.sm_R thm_C_S7
thm_C_soft (cor_C_inherits Bridge.sm_R)` typechecks against this bundle as written. If the CV/R tail prefers to keep its 11-field
structure, dropping `root_values` costs one line here (`thm_comparison_root_of` stays as a companion). Reading of TARGETS' "Use the
normalizations and reversal/cyclic identities inherited with cor:A-lawful as stated there": `triangles`, `reversal_law`, and
`shift_invariant`/`descends` (cyclic) are exactly those fields.

## 4. Proof routes (accepted lemmas by file:line; where the pending rows enter)

### Row 122 (sm-5:477-501) — PROVED in the sketch (prefix `av_`)
1. `av_softAnchor_value F hF A` (any `SoftAnchorData`): `(F(P_ε) : ℚ) = mult · F(P)` at `ε = A.param`. Printed proof verbatim:
   `hF.soft` at the parent gives `δ_F`; `ε' := min(ε, δ_F)/2`; both `P_ε` and `P_ε'` lie in the labelled/polygon chamber `B` of
   `A.bound_spec` (def:anchors' `ε₀`, SM/Anchors.lean:52-58 = lem:soft-generic (i)); `hF.chamber` equates the values; the soft
   theorem at `ε'`. (It is the `F`-half of the accepted `unA_softAnchor_delta`, SM/Uniqueness.lean:333.)
2. Zero anchors: `softAmplitudeMultiplier_mixed` (SM/SoftAmplitudeSectors.lean:110, needs `A.admissible`, `A.mixed`) → `0`.
   Loop anchors: `softAmplitudeMultiplier_loop` (:120, `A.loop`) → `τ_j`. Cast back to ℤ (`exact_mod_cast`).
3. `loop_turn := A.parent_turn` (SM/Anchors.lean:85); `loop_triangle_turn`: `subst A.triangle`, `A_small_values_i`
   (SM/SmallValues.lean:260), `rotationNumber_triangle (generic_regular le_rfl _)` (SM/RotationTriangle.lean:25).
4. `A_*`: `av_rooted A a ha` — `soft_theorem_treeCoefficient hm A.parent_generic j q A.admissible A.bound A.bound_pos`
   (SM/SoftTheoremTree.lean:28) gives `ε₁` and, at `ε' < min(A.param, ε₁)`, the unique `g` with `a = softParentEdge j g` and the
   ℚ-identity at root `a`; `(A_chamber hm1).2.1 B _ hch a` (SM/TreeChamber.lean:92, labelled-chamber constancy of the tree data at
   the fixed root, prop:A-chamber) twice through `B` transports `A_a` from `P_ε'` to `P_param`; uniqueness of `g` by
   `softParentEdge_injective` (SM/SoftParentEdges.lean:49). Then the sector lemmas as in 2 (`av_A_zero`, `av_A_loop_of_sector`).
5. `C_hypotheses`: `av_C_chamber` by `Quotient.inductionOn₂` and `prop_C_chamber.constant` (SM/CChamber.lean:1373); the soft half by
   `hs.soft_theorem` rewritten through `cmp_C_projection`. **thm:C-soft enters here and only here.**

### Row 127 (sm-6:304-311) — PROVED modulo two leaves (prefix `cmp_`)
0. Descent: `cmp_cornerStateSum_compat` (setoid witness `Q.val = shift k P.val` → `Q = genericShift k P` → `cornerStateSum_genericShift`,
   SM/CChamber.lean:1362); `cmp_polygonSum hn := Quotient.lift …`; `cmp_C n Q := if hn : 3 ≤ n then cmp_polygonSum hn Q else 0`;
   `cmp_C_projection`. (Same construction as `alA_polygonAmplitude`, SM/ALawful.lean:173.)
1. `cmp_uniqueness_hypotheses_of hCV h7 hs hR : UniquenessHypotheses cmp_C` (SM/Uniqueness.lean:35), field by field:
   (a) `chamber := av_C_chamber`; `silent` := `prop_C_silent.extension/.cut` (SM/CSilent.lean:1844; `tp := t`, `tm := s`);
   (b) `flat` := `cmp_flat_bridge` (PROVED): `thm_C_S3.flat_law n hn w j hf.2.1 hf.2.2.2.1 hf.2.2.1 hf.2.2.2.2` (SM/CS3.lean:2478;
   `FlatAt` = `4 ≤ n ∧ pointZeros ∧ concurrences ∧ StrictBetween ∧ SignChanges`, SM/NamedWallPredicates.lean:14) gives `δ ≤ radius`;
   `cmp_side_repr` writes `w.curve s` as `(w.sideTuple b t).val` (`ri_sideTuple_true_val/false_val`, SM/RootIndependence.lean:122/125);
   `side_turn_constant` (SM/GermTurnSigns.lean:27) gives `IsRightSide/IsLeftSide` at `t₀ = δ/2`; `cornerStateSum_side_eq`
   (SM/HypR.lean:119) moves the values; `cmp_congr` handles the tuple equality.
   (c) `vertex_edge` := `h7.vertex_edge_law n hn w M a hc h₁ h₂ t s` (shapes coincide literally; `cmp_C_projection'` at the halves'
   `contactHalfSizes_bounds hn hc.1`). **thm:C-S7 enters here.**
   (d) `triple` := `hR n hn w e f k hT t s` (SM/HypR.lean:83). **hyp:R enters here.**
   (e) `soft` := `(av_C_hypotheses_of hs).soft`. **thm:C-soft enters here.**
   (f) `triangles` := `cmp_triangles hCV` from the LEAF `cmp_triangle_value hCV T hT τ hτ : C(T) = −τ` at `star 1` (turns `1`:
   `star_generic_law le_rfl`.1.2.1.2.2.2.1) and `starNeg 1` (turns `−1`: .1.2.2.2.2.2.1), SM/StarGenericLaw.lean:21.
   **lem:corner-values enters here and only here.**
2. `thm_comparison_of` := `uniqueness cmp_C (…) n hn P hP` (SM/Uniqueness.lean:454) rewritten by `cmp_C_projection'`.
3. Leaf route for `cmp_triangle_value` (unit U-CM-TRI), the printed (f) sentences: in `ZMod 3` every pair is adjacent
   (`adjacent`, SM/Polygon.lean:63; `decide`), so `IsCrossing T s` (SM/Crossings.lean:12, needs `remote`) is false and
   `Crossing T`, `Visit T` are empty; hence every `S : Finset (Crossing T)` is `∅`, `∅ ∈ independentSupports` (`mem_independentSupports`,
   SM/InterlaceSupports.lean:27-40, `IsIndepSet ∅`), the single carrier `q` of `∅` (`component_card_independent`, SM/CarrierComponentCount.lean:104:
   `card = 0 + 1`) has `carrierCrossings = ∅` (SM/CarrierCrossings.lean:56) so `m_Q = 0`; every corner mark is a vertex mark
   (`Mark T = ZMod 3 ⊕ Visit T`, `Visit T` empty) with `IsTrueCorner ∅ (Sum.inl i)` (SM/CarrierTrueCorners.lean:44), so
   `ccpCornerPolygon_turn_vertex` (SM/CarrierCornerPolygon.lean:598) makes `q` uniform with sign `τ`; `hCV.embedded_value` gives
   `c(q) = 1`; `uniformDecompositions = {∅}` (SM/CornerStateSum.lean:136); `cornerStateSum = (−1)^{ℓ(T)} · 1` (:166) with
   `leftTurns T = #{i : τ_i = 1}` = `3` if `τ = 1`, `0` if `τ = −1` (`turn_eq_of_…`, def:C `left_turns`).

### Row 128 (sm-6:320-368) — PROVED modulo one leaf
`cor_C_inherits_of hCV h7 hs hR`: `hcmp := thm_comparison_of hCV h7 hs hR`; then, field by field, the accepted `A_lawful` field
(SM/ALawful.lean:201) with `C = A` rewritten at EVERY argument — the printed "substitute `C = A` at every one of them, including the
deletions and halves just checked": `root_values` (`A_lawful.root_independent`); `shift_invariant` (`cornerStateSum_genericShift`);
`descends` (`cmp_polygonSum`); `chamber_constant` (`cornerStateSum_eq_of_mem_labelledChamber` SM/CChamber.lean:1366,
`prop_C_chamber.constant`); `silent` (prop:C-silent); `flat_law` (`A_lawful.flat_law` gives `Generic (P(0)∖j)` by lem:children (i)
and the law; three rewrites by `hcmp`); `cusp_law` (LEAF `cmp_cusp_deletion_generic w j hf hG1 : Generic (P(0)∖j)`, then
`A_lawful.cusp_law n w j hf hG1` — case `b`, uniqueness, `κ`, the rotation jump, and its `Generic → −κ·A(Q)` clause — with three
rewrites by `hcmp`); `vertex_edge_law := h7`; `triple_law := hR`; `soft_theorem := hs`; `reversal_law` (`A_lawful.reversal_law`,
witnesses `(generic_reversal P).mpr hP` vs `g1_reversal_forward hP.1` are proof-irrelevant); `triangles := cmp_triangles hCV`.
Leaf route for `cmp_cusp_deletion_generic` (unit U-CM-CUSPGEN), sm-6:335-359: G1 is the hypothesis; G2 (`SM/Generic.lean:14`):
suppose `x ∈ edgeInterior Q a ∩ edgeInterior Q b ∩ edgeInterior Q c`, `a, b, c` distinct. (i) `g1_common_interiors_remote`
(SM/GenericTopology.lean:47) makes them pairwise remote in `Q`. (ii) Lift each edge of `Q` to an edge of the centre `P(0)` with `x` in
its relative interior: unchanged edges to themselves (`edgeInterior_deleteVertex`, SM/DeletionInteriors.lean; index map
`DeletionEdgeLift`, :39), the fused edge `−1 = [A,B]` to the LONGER of `E_{j−1}(0) = [A,M]`, `E_j(0) = [M,B]`: `CuspAt`
(SM/CuspDefinition.lean:41-45) says `M ∉ [A,B]` with `A, M, B` collinear (`pointZeros = {turnSupport j}` ⇒ `turn = 0` at `j`), so
`[A,B] ⊂ [A,M]` or `[A,B] ⊂ [M,B]` and `relint [A,B] ⊂ relint` of that edge (the cusp analogue of `fused_interior_lift`, :22, whose
`affine_interior_subdivision` is replaced by a containment of segments). (iii) Injectivity of the lift (`deletionEdgeLift_injective`,
:42, plus: the longer cusp edge is not the lift of an unchanged edge since neither `E_{j−1}(0)` nor `E_j(0)` survives). (iv) The three
lifted edges are pairwise remote in `P(0)`: unchanged-unchanged as in `Q` (adjacency ⇔ shared vertex, both vertices of `Q`); the
longer cusp edge's neighbours are the other cusp edge (not an edge of `Q`) and one edge of `Q` adjacent to the fused edge (excluded
by (i)). (v) Hence `ConcurrenceTriple P(0) {…}` (SM/ZeroTriples.lean:61) — contradiction with `concurrences = ∅` (`hf.2.2.1`,
SM/GermDefinition.lean:14). Template: `g2_deleteVertex` (SM/DeletionGeneric.lean:11) and `flat_center_g2` (SM/FlatAdjacent.lean:79).

## 5. Unit decomposition (byte-identical copies of Sketch_A.lean §-sections; statements frozen; leaves `sorry`; helpers prefixed)

Check per unit: `cd work/lean && lake env lean ../drafts/comparison/U_<unit>.lean` (18 s cold on the current cache). Assembly: the
sketch IS the skeleton — replace the two leaf `sorry`s by the units' proofs, clash scan, `#print axioms` (expected standard +
`SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness` through def:C — `SM.lit_homfly_descent`/`SM.src_contact` only once the corner rows
are plugged in); port after statement review as SM/Comparison.lean (library) — §0 deleted when SM/CornerValues, SM/CS7, SM/CSoft land;
§5 row theorems declared and mapped only then (D-F11/D-F14). Reassessment rule per UNIT (2 attempts / 60 min).

| unit | prefix | content | lines | hours | deps | status |
|---|---|---|---|---|---|---|
| U-CM-DESC | `cmp_` | descent `cmp_polygonSum`, `cmp_C`, projections; `av_C_chamber` | 50 | — | accepted | DONE (sketch §1) |
| U-CM-AV | `av_` | row 122: `av_softAnchor_value`, sectors, `av_rooted`, `av_loop_triangle_turn`, `anchor_values_of`, companions | 190 | — | accepted, `hs` | DONE (sketch §2) |
| U-CM-FLAT | `cmp_` | `cmp_side_repr`, `cmp_flat_bridge` (CS3 → thm:uniqueness (b)) | 50 | — | accepted | DONE (sketch §3) |
| U-CM-TRI | `tri_` | LEAF `cmp_triangle_value` (§4 route 3): no crossings in `ZMod 3`, `Ind = {∅}`, single carrier, uniform, `m_Q = 0`, `c = 1`, `ℓ` count | 250 | 4 | accepted, `hCV.embedded_value` | OPEN (wave 1) |
| U-CM-HYP | `cmp_` | `cmp_uniqueness_hypotheses_of`, `thm_comparison_of`, companions | 90 | — | TRI, FLAT | DONE modulo TRI |
| U-CM-CUSPGEN | `cg_` | LEAF `cmp_cusp_deletion_generic` (§4 route (i)-(v)): cusp fused-edge containment, edge lift, injectivity, remoteness transfer, `ConcurrenceTriple` | 500 | 8 | accepted | OPEN (wave 1, RISKIEST) |
| U-CM-INH | `cmp_` | `CInheritsData`, `cor_C_inherits_of` | 110 | — | CUSPGEN, HYP | DONE modulo CUSPGEN |
| U-CM-ROWS | — | `prop_anchor_values`, `thm_comparison`, `cor_C_inherits` one-liners; map; review | 10 | 1.5 | rows 105/110/112 accepted | BLOCKED on the corner lane |
| total | | 2 leaves open | **≈ 1,250 (sketch 668 + ≈ 600 leaf lines)** | ≈ 14 prover-h, 1 wave, ~1 day wall with 2 lanes | | |

Launch NOW (against the frozen statements): U-CM-CUSPGEN and U-CM-TRI in parallel; both are floor-free and corner-free (TRI only
consumes the `CornerValuesData` bundle as a hypothesis, i.e. the accepted-shaped statement of row 105, not its proof). The three row
theorems wait for `SM.corner_values`, `SM.thm_C_S7`, `SM.thm_C_soft`; until then the conditional theorems are library material and
FINAL_REVIEW should say "122/127/128 conditional-complete on rows 105/110/112" (the honest intermediate state), or, if the leaves
also stall, "…, two lemma leaves open (triangle value, cusp deletion genericity)".

## 6. Riskiest steps (ranked) and fallbacks

1. **U-CM-CUSPGEN** — new geometry (the only step of the lane not printed as a lemma anywhere in SM15 except inside the proof of
   cor:C-inherits). The flat-wall analogue (`g2_deleteVertex`) took ~40 lines on top of ~150 lines of interior/lift lemmas built for
   `StrictBetween`; the cusp needs the segment containment `[A,B] ⊂ [A,M]` or `⊂ [M,B]` from `¬ ∃ t ∈ [0,1], M = A + t(B−A)` plus
   collinearity (`turn = 0` at `j` from `pointZeros = {turnSupport j}` via `PointZeroTriple`, SM/ZeroTriples.lean:13) — an
   affine-parameter computation, not topology. Fallback (recorded, NOT adopted): a field with `hQ : Generic (P(0)∖j)` as HYPOTHESIS
   would weaken the domain against TARGETS ("the source domain (the deletion satisfies G1)"); so the leaf is mandatory for row 184
   and the fallback is only an intermediate honest state.
2. **U-CM-TRI** — the carrier API at `S = ∅` on a 3-gon: `Visit T` empty needs `IsCrossing` false for every pair (`remote` is
   `¬ adjacent`; in `ZMod 3` `j − i ∈ {−1, 0, 1}` always, `decide`); the uniformity needs "every corner mark of the sole carrier is a
   vertex mark" (`ccpCornerMark_isTrueCorner` + case on `Mark = Sum`); the leftTurns count is `Finset.card_filter` on `ZMod 3`.
   Fallback: prove `TrianglesC` directly at `star 1`/`starNeg 1` by the same route (no generality lost for the rows; the general
   `C(T) = −τ` is a companion).
3. **Interface drift** — §0 copies `CornerValuesData`, `CS7Data`, `CSoftData` (corner FINAL) and `CuspLawC`/`ReversalLawC`/`TrianglesC`
   (cvtail FINAL). The consumers here read: `hCV.embedded_value` (TRI), `h7.vertex_edge_law` with `∀ h₁ h₂ tp tm` (HYP (c)),
   `hs.soft_theorem` with `∀ hQ` and the ℚ multiplier (AV, HYP (e)). A change to `∃ hQ` or to `∧ Generic λᵢ` costs a 10-line bridge
   each; nothing else moves. Freeze before U-CM-ROWS.
4. **The (f) dependency** — `thm_comparison_of` takes `hCV : CornerValuesData` although only clause (i) is used, and clause (i) is
   UNCONDITIONAL in the corner lane (`corner_values_i`, corner/Statements_FINAL.lean:350, proved without the floor). Once
   SM/CornerValues.lean (or the (i)-only theorem) is ported, `thm_comparison_of` can drop `hCV` for a call to `corner_values_i`,
   making rows 127/128 conditional on rows 110/112 only. Not done in the sketch (the drafts directory cannot be imported).
5. **Proof-irrelevance rewrites** — the `hcmp` rewrites in `cor_C_inherits_of` match `cornerStateSum hn hP` against terms whose
   `hn`/`hP` proofs differ syntactically; they typecheck in the sketch (defeq by proof irrelevance), but a port that changes the
   witness terms (e.g. the corner lane's `contactHalfSizes_bounds` spelling) may need `cmp_congr`/`show`. Cheap.
6. **Size/time** — the whole lane is ≈ 1,250 lines; the two leaves are ≈ 750 of them. No multi-thousand-line step; the critical path
   is U-CM-CUSPGEN (8 h) → port → the corner rows.
