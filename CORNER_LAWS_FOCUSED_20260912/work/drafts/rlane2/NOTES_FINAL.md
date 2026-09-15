# NOTES_FINAL — R lane part 2, judge's merge of Statements_A / Statements_B (rows 168, 170, 172–178)

File: `work/drafts/rlane2/Statements_FINAL.lean` (1178 lines). Checked 2026-09-14 with
`cd work/lean && lake env lean ../drafts/rlane2/Statements_FINAL.lean`: exit 0, no errors, exactly nine
`sorry` warnings = the nine row theorems `RProof.exterior` (L336), `availability_zero_one` (L426),
`generic_selector` (L574), `generic_transport` (L661), `generic_selected` (L722), `extreme_pair_zero`
(L785), `extreme_transport` (L868), `extreme_selected` (L921), `cv_R : CV.hyp_R` (L1001). Every other
declaration is a definition or PROVED. `#print axioms` (scratch copy `/tmp/rl2/Statements_FINAL_axioms.lean`):
`three_le_of_h3` [propext, Quot.sound]; `extremeLocal_iff`, `mem_Ind_of_mem_outsideSupports`,
`supportEmb_apply`, `strandSign_eq_crossingSign`, `transportSupport_transportSupport_symm`,
`OppositeSides.symm`, `mem_outsideSupports_transport`, `outsideSupports_transport` [propext,
Classical.choice, Quot.sound]; everything mentioning `CV.X1`/`X1Summand` (`rowTerm_of_mem_Ind`,
`rowTerm_of_not_mem_Ind`, `X1_eq_sum_rowTerm`, `X1_eq_sum_fibreTerm`, `rowTerm_eq_exterior_mul_touching`,
`near_of_fibre_identities`, `CvTheoremData.of_fibre_identities`, `hyp_R_of_near_of_chamberinv`,
`smR_shape_of_hyp_R`) additionally `SM.lit_homfly` (the accepted literature interface reached through
`homfly`; not a new axiom); `cv_R` [.. sorryAx ..] as expected.

Inputs judged: `Statements_A.lean` (1065 lines, 9 sorry) + `NOTES_A.md`; `Statements_B.lean` (839 lines,
9 sorry) + `NOTES_B.md`. Both compile (re-checked by the judge: A 12.7 s, B 8.2 s, both exit 0, nine
`sorry` warnings each, all at row theorems). Compared clause by clause against R_ASSEMBLY_SPEC.md,
OPEN_WORK.md items 2–4, R_ATTACHMENT_WARRANTS.md (R-EXTERIOR-1 Statement + proof §1–§4),
R_GENERIC_NONSELECTED_SELECTOR_PROOF.md, R_GENERIC_COMMON_TRANSPORT_PROOF.md,
R_GENERIC_SELECTED_COUPLE_PROOF.md, R_EXTREME_PAIR_ZERO_PROOF.md, R_EXTREME_SINGLETON_TRANSPORT_PROOF.md,
R_EXTREME_SELECTED_COUPLE_PROOF.md, R_GENERIC_ORBIT_ACTUAL_TABLE.md, d1_setup.tex def:X1 / prop:chamberinv,
d10_axioms.tex ax:R, DECISION_FINAL.md R5–R7, the scout report (work/reports/cv-lane-plan-20260913.md
§5 rows 168–178), the accepted cores (work/lean/RProof/Cores.lean, = work/drafts/rlane/Statements_FINAL.lean
+ NOTES_FINAL.md), CV/X1.lean, CV/ChamberInvII.lean, CV/Carriers.lean (def:wind, `turn_visit_of_traced`),
SM/FlatCarriersDefs.lean (`geoSmoothingSuccessor`, `geoCornerTurn`), Bridge/B1.lean.

## 0. Verdict and scores

| criterion | A | B | notes |
|---|---|---|---|
| FIDELITY (clause by clause) | 8.5 | 5.5 | B's row-172 `mixed_carrier` is **false** (§4 below): it demands the two co-owned smoothing corners to be the two visits on the *shared* strand; the accepted skeleton (`LocalTable.succ`) puts them on different carriers. B's row 170 `SummandTransport` is the better rendering of "carrier/record, selector, rotation and coefficient transport" (A omits the record data). A's row 168 `factorization` is the printed "single value `C_Q` serves both sides"; B's is one-sided. B's 175 adds a proof-step field. |
| FEASIBILITY (typechecked; provable-now; instantiation cost) | 8.5 | 6.0 | Both compile with nine sorries. A PROVES `outsideSupports_transport` from the accepted row 171 (B leaves it as a bundle field/hypothesis). Both name `R:generic_selector` as the only whole row provable now — true for A's statement, false for B's (its bundle is unsatisfiable on any generic-orbit event with `Q = ∅`). |
| CONSISTENCY (accepted cores, bridge) | 8.0 | 8.0 | Both reuse the cores' vocabulary and the R6 `CV.hyp_R` verbatim. B adds the bridge-consumption check `smR_shape_of_hyp_R` (B1/B3 + `isSimpleRIII_eventOfTriple` + B4's pointwise shape) — adopted. B's `wallMap` duplicates the accepted `transportSupport`; B's file-wide `Classical.propDecidable` instance is a friction risk with the accepted `instDecidableEqCrossing`. |
| **total** | **25.0** | **19.5** | **Winner: A.** The merge takes A as the base (rows 168, 172, 173, 174, 176, the assembly lemmas) and grafts B's row 170 (`SummandTransport`, `fibre_zero/one/correspond`), B's clause splits in 175/177, and B's row-178 architecture (`CvTheoremData` without the chamber clause, global `CvRNear`, `ChamberInvII`, `hyp_R_of_near_of_chamberinv`, `smR_shape_of_hyp_R`) with A's proved `outsideSupports_transport` filling B's field. |

## 1. Shared decisions (all nine rows)

* **Domain — F2(A), no narrowing.** `E : CV.Event n`, `E.IsSimpleRIII e f g h3 h4e h4f h4g`; bundles
  `structure <Row>Data (hn : 3 ≤ n) (E) (e f g) (δ : ℝ) : Prop`, one field per specified clause with the
  clause quoted; theorems `RProof.<fixed name> (hn) (E) (e f g) h3 h4e h4f h4g (hE) : ∃ δ, 0 < δ ∧ δ ≤
  E.radius ∧ <Row>Data hn E e f g δ` (the accepted cores' shape plus `hn`).
* **`hn : 3 ≤ n` explicit** (B): needed by `CV.X1` (CV fixes `n ≥ 3`, d1:932), quantified by R6 in
  `CV.hyp_R`; `three_le_of_h3` (PROVED) shows it is derivable from `h3`, so a consumer holding only the
  cores' data can supply it. A's alternative (bundle at `three_le_of_h3 h3`) is definitionally the same
  by proof irrelevance; the explicit form reads better and matches `CV.X1 hn …`.
* **X₁ consumed literally.** `T_ν(J)` / `F_±(S)` = `rowTerm hn (genericAt E t ht.1) S := CV.X1Summand hn hG S`
  (`wind(S) ∏_L Ω₁(S,L)` if `S ∈ Ind`, else `0` — "absent rows being zero"); `Φ_±(Q)` = `fibreTerm hn E e f g
  t ht Q := fibreSum … (rowTerm …) Q` (the accepted row-171 sum); `X_1(P_±)` = `CV.X1 hn (E.curve t)
  (genericAt E t ht.1)`. Display (3) at `F_±` is `X1_eq_sum_fibreTerm` (PROVED) — the "X₁ flag" of
  work/drafts/rlane/NOTES_FINAL.md §3 is closed.
* **Across the wall.** The accepted `SM.transportSupport hs Q` (= `Q.map (crossingTransport hs).toEmbedding`,
  the form of `FibrePartitionData.avail_same`), `hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s`
  quantified in every cross-wall field (proof-irrelevant; supplied by `LocalizationData.crossing_set_constant`);
  `supportEmb hs` is the same map as an embedding for `Finset.map` reindexing (`supportEmb_apply`, PROVED).
  B's `wallMap`/`wallMapEmb` aliases dropped.
* **Full availability** `FullAvail hP e f g Q : avail hP e f g Q = triangleCrossings P e f g`
  (R_ATTACHMENT_WARRANTS.md preamble). **Orbits/sides by graphs:** generic = `¬ ExtremeLocal`; `K3` side
  `CompleteLocal`, empty side `EmptyLocal` (`extremeLocal_iff` is `Iff.rfl`); two-edge side `EdgeAB ∧ EdgeBC`
  etc. Sides are never named by coorientation (R_EXTREME_SELECTED_COUPLE_PROOF.md:39–42 "named by their
  graphs … independent of coorientation"); identities symmetric in the sides are stated for `t, t'` opposite.
* **Fixed labels** `a = x_ef`, `b = x_eg`, `c = x_fg` (the accepted `generic_table`); a text printed in
  relabelled canonical words is rendered by its canonical-branch clause (selected pair `ac`, `s_a = s_b = s_c`)
  plus the two relabelled instances (selected `ab`, `bc`), covering all six generic branches (F2(A)). B's
  label-free `selectedPair` (an `if`-chain evaluated AC, AB, BC) was not adopted: it is a new sign-defined
  object whose graph meaning needs `selected_is_graph_selected` at every use, and its evaluation order is a
  hidden convention; the fixed-label form is what the accepted table states.
* **Per-carrier objects:** CV's own on the accepted geo layer — `q : GeoComponent hP S`, `CV.weight`, `CV.wind`,
  `CV.CarrierMixed`, `CV.Omega1`, `CV.carrierR`, `CV.groupedWrithe`, `CV.groupedPoly`, `CV.U`, `CV.pieceOf`,
  `CV.pieceLabels`; "a carrier contains a visit" = `geoOwner hP S (Sum.inr v) = q` (conv:selected-visits at
  selected visits).
* **`CV.hyp_R`** defined once here in R6's verbatim form (both drafts identical); it is the CV:ax:R row's fixed
  name and the type of `RProof.cv_R`; the assembler places it once (CV row module or the R module).

## 2. Row 168 — R:exterior (`ExteriorData`, `RProof.exterior`)

| sentence (R_ATTACHMENT_WARRANTS.md:154–185) | field / definition |
|---|---|
| "A carrier of `S` is *triangle-disjoint* when it contains none of the six traversal visits belonging to `T`, including a selected triangle crossing's smoothing-site visits" | `TriangleDisjoint hP S e f g q` (no visit of a triangle crossing is owned by `q`; identical in A and B) |
| `C_{Q,σ}(A) = ∏_{triangle-disjoint L} wt_σ(L) Ω_{1,σ}(S,L)`; `ρ_σ(A)` | `exteriorFactor hn hG hS e f g`, `touchingFactor …` (identical in A and B; `Ω₁` at `S = Q ∪ A`, so the factor carries `hS`) |
| proof §3 "`τ_σ(A) = C_{Q,σ} · ρ_σ(A)` as an identity, including when either factor is zero" | `rowTerm_eq_exterior_mul_touching` PROVED (both drafts) |
| "Then `C_{Q,σ}(A)` is independent of `A`" | `independent_of_A` (any `A, A' ⊆ T`, one side; NOT restricted to full availability, as printed — row 170 reads it at `|𝓐(Q)| ≤ 1`) |
| "and its common value is the same for `σ=−` and `σ=+`. Write that single value as `C_Q`; it may be zero." | `wall_invariant` (any `A` at `t`, any `A'` at `t'`, `Q` transported) |
| "Consequently every full-availability row factors exactly as `τ_σ(A) = C_Q · ρ_σ(A)`" | `factorization`: under `FullAvail Q`, for every `A` on side `t` AND every `A'` on side `t'`, `rowTerm = C_Q * touchingFactor` with the SAME `C_Q` |

Merge decision on `factorization`. A: `∃ C : ℤ`, both sides (literal "single value", but the value is
anonymous — recovering `C = exteriorFactor` needs `independent_of_A`, since `touchingFactor` may be `0` and
cannot be cancelled). B: one side only, `C_Q` = the base row's exterior factor (`A = ∅`, needing `Q ∈ Ind`).
FINAL: B's explicit representative (`exteriorFactor … (mem_Ind_of_mem_outsideSupports hQ)`, the base row on
side `t`) in A's two-sided shape. The clause is then a plain instantiation of the two constancy clauses and
the proved split (no extra proof burden), and the consumer gets the value. The full-availability binder is
kept as printed (the general form for any `A` follows from (a)+(b)+the split; not asserted, to stay literal).
OPEN_WORK item 4 ("without division; absent supports, empty products, dead selectors, both directions,
arbitrary exterior geometry"): independence hypotheses exclude absent supports, `wt = 0` allowed, no division,
both directions quantified, `Q` arbitrary.

## 3. Row 170 — R:availability_0_1 (`AvailabilityZeroOneData`, `RProof.availability_zero_one`)

| sentence (R_ASSEMBLY_SPEC.md:55–64; OPEN_WORK item 2) | field |
|---|---|
| "At availability zero … the local supports themselves correspond" | `fibre_zero`: `Ind(G[𝓐(Q)]) = {∅}` (B) |
| "… or one …" | `fibre_one`: `𝓐(Q) = {z}`, fibre `= {∅, {z}}` (B) |
| (the correspondence across the wall) | `fibre_correspond`: the far fibre is the `supportEmb` image (B) |
| "but that does **not** prove their summands agree. Prove the required carrier/record, selector, rotation and coefficient transport" | `summand_transport`: `SummandTransport` = `wind` equal (selector) ∧ ∃ carrier bijection `τ` with `weight`, `carrierR` (rotation), `groupedWrithe` + `groupedPoly` (record), `Omega1` (coefficient) matched (B; A lacked the record data) |
| "… their summands agree" | `summands_agree`: `F_+(Q ∪ J) = F_-(Q ∪ J)` for every `J` of the fibre (A; consumer-facing intermediate) |
| (4) `Φ_+(Q) = Φ_-(Q)`; OPEN_WORK item 2 "the fibre identities for availability 0 and 1" | `fibre_identity` (both) |
| "These cases cannot be omitted because the four core proofs assume full availability" | the hypothesis `card = 0 ∨ card = 1` (`FibrePartitionData.avail_card` excludes `2`) |

Reading checked: at availability 0 the three triangle crossings are dominated by `Q` (in no piece, not
corners), so the carriers' corner lists and piece records coincide across the wall (the three adjacent
transpositions only move unselected, non-piece marks); at availability 1 the selected `x` has wall-invariant
corner signs (`crossingSign`, `chamber_change`) and the other two are dominated. So the carrier-by-carrier
transport is the true shape (the scout report's G7 analysis and B's reading agree). Downgrade path if a
reviewer prefers the bare identity: keep `fibre_zero/one/correspond` + `fibre_identity`, move
`summand_transport`/`summands_agree` to the proof lane.

## 4. Row 172 — R:generic_selector (`GenericSelectorData`, `RProof.generic_selector`) — A adopted

| sentence (R_GENERIC_NONSELECTED_SELECTOR_PROOF.md) | field |
|---|---|
| :10–12 "Among the three one-sided local pair supports, one is the graph-selected pair complementary to the degree-two singleton of `P3`" | `selected_pair_unique` (exactly one of (4) holds on the event; the graph identification is the accepted `GenericTableData.selected_is_graph_selected`, cited in the docstring) |
| (5)–(6) "`sgn det(u,v) = sgn det(u,w)` … `det(v,u) = −det(u,v)`, and `det(u,w)`. By (5), the signs in (6) are opposite" | `corner_signs_opposite` (per nonselected pair, both traversal orders; `strandSign = crossingSign` is `rfl`) |
| :129–139 "one carrier contains the entire arc and both of its endpoint smoothing corners … The carrier is mixed regardless of all its other corners" | `mixed_carrier` via `MixedSharedStrandCarrier`: one carrier owns the marks `(x, v)` and `(y, u)` — or `(y, w)` and `(x, u)` — and is `CV.CarrierMixed` |
| :12–13 "Each of the other two pair rows has winding selector zero on the side where it is present" | `selector_zero` (`Q ∪ J ∈ Ind → wind (Q ∪ J) = 0`) |
| :150–151 "Consequently its entire X1 row is zero before any coefficient is read" | `row_zero` (no presence hypothesis; absent rows are `0`) |
| :13–15 "arbitrary exterior gaps and outside independent support `Q`; no coefficient, exterior-factor division, or nonvanishing hypothesis" | quantification `∀ Q ∈ outsideSupports, FullAvail Q →`, generic orbit `¬ ExtremeLocal`, nothing else |

**Why B's `mixed_carrier` was rejected (kernel-checkable).** B requires two visits `v, w` of the two crossings
of `J` with `v.2.val = w.2.val` (the SAME edge, i.e. both on the shared strand `u`), the same `geoOwner`, and
opposite nonzero `geoCornerTurn`s. Under def:smoothing (`geoSmoothingSuccessor = ρ ∘ selectedMarkPerm`,
conv:selected-visits) the mark of a selected visit is the corner at which its carrier ARRIVES along that
visit's edge and leaves along the twin's edge (`CV.turn_visit_of_traced`, CV/Carriers.lean:533). The carrier
through the intact `u`-arc therefore owns one corner on `u` and one on `v` or `w`, never both `u`-visits: for
`E = b a A c a B c b C` with `S = {a, b}` (pair `ab`, nonselected in the canonical branch; present on `E`,
`Q = ∅` is an outside support with `𝓐 = T`), the accepted `LocalTable.succ wordE {a, b}` evaluates to
`[8, 5, 3, 4, 2, 6, 7, 1, 0]` on positions `0..8 = b(e) a(e) A c(f) a(f) B c(g) b(g) C`: cycles `{0, 8}` =
`(b(e), C)`, `{1, 5, 6, 7}` = `(a(e), B, c(g), b(g))`, `{2, 3, 4}` = `(A, c(f), a(f))` — the table's
`(1)[C](256)[B](34)[A]`. The two `e`-visits `b(e)` (0) and `a(e)` (1) lie on different carriers, so B's field
fails, while A's second disjunct (`(y, w) = b(g)` = 7 and `(x, u) = a(e)` = 1 co-owned) holds, with corner
turns `det(g, e)` and `det(e, f)`, opposite by (5). B's `GenericSelectorData` is thus unsatisfiable on every
generic-orbit event, and B's `generic_selector` — reported by B as "provable now" — is false as stated.
(The skeleton→carrier identification is the flagged obligation of §9 risk 8, but the ownership convention is
the accepted one and the counterexample is at the level of the accepted table.)

## 5. Row 173 — R:generic_transport (`GenericTransportData`, `RProof.generic_transport`)

| sentence (R_GENERIC_COMMON_TRANSPORT_PROOF.md:16–59) | field |
|---|---|
| (1) "In the displayed graph the selected pair is `ac` … equality of the `a` and `c` determinant signs. If the `b` sign were opposite, the triple would be … alternating … Hence … `= sigma`" | `canonical_branch`: generic → (`SelectedAC ↔ s_a = s_b ∧ s_b = s_c`) — checked: `s_a = s_c` ∧ nonalternating ⇒ `s_b = s_a` |
| (2) "`T_P(empty) = T_E(empty)`" | `empty_row` (all generic branches) |
| (2) "`T_P(a) = T_E(a)`, `T_P(c) = T_E(c)`" | `endpoint_rows_canonical` (under `s_a = s_b ∧ s_b = s_c`; A's `endpoint_a`/`endpoint_c` merged into one field) |
| "Every generic branch can be put in this form by relabelling … The same relabelling carries the crossings" | `endpoint_rows_relabelled`: `SelectedAB → rows a, b`; `SelectedBC → rows b, c` (endpoints = the members of the selected pair, by the table of R_GENERIC_NONSELECTED_SELECTOR_PROOF.md:110–116 and `selected_is_graph_selected`) |

Not rendered (proof devices): the "arbitrary-`Q` successor lift" (2a), the residual-graph isomorphisms
`c ↦ b`, `a ↦ b` (§2–§3). B's `selected_pair_invariant` is unnecessary in fixed labels (strand signs are
wall-invariant, accepted `chamber_change`, so a `Selected*` hypothesis at `t` is the same at `t'`).

## 6. Row 174 — R:generic_selected (`GenericSelectedData`, `RProof.generic_selected`) — A adopted

| sentence (R_GENERIC_SELECTED_COUPLE_PROOF.md:17–37) | field |
|---|---|
| "`b` is the degree-two vertex of the path, and `ac` its complementary independent pair on `P` … `T_E(b) = T_P(b) + T_P(ac)` (GSC)" | `couple_canonical`: `s_a = s_b = s_c`, `t` the two-edge side (`EdgeAB ∧ EdgeBC`), `t'` opposite: `T_t'(b) = T_t(b) + T_t(ac)` |
| "Relabel the three local crossings so …" | `couple_relabelled`: `SelectedAB` (centre `c`, two-edge side `EdgeAC ∧ EdgeBC`): `T_t'(c) = T_t(c) + T_t(ab)`; `SelectedBC` (centre `a`, two-edge side `EdgeAB ∧ EdgeAC`): `T_t'(a) = T_t(a) + T_t(bc)` — branch/centre/side table checked against `selected_is_graph_selected` |
| "with the opposite coorientation obtained by multiplying the equation by `−1`" | remark, not rendered |

B identified `P` by "`Q ∪ selectedPair ∈ Ind`" (equivalent: `ac` is present exactly on the two-edge side);
A's graph naming is kept for uniformity with 175–177. B's `centre_is_degree_two` is the accepted
`selected_is_graph_selected`; not repeated.

## 7. Row 175 — R:extreme_pair_zero (`ExtremePairZeroData`, `RProof.extreme_pair_zero`)

| sentence (R_EXTREME_PAIR_ZERO_PROOF.md:7–51) | field |
|---|---|
| "Each local pair support is absent on the `K3` side" | `pair_absent_on_complete` (B's split) |
| "and present on the empty-graph side" / "The support `S` is independent" | `pair_present_on_empty` |
| "The remaining crossing `z` is undominated by `S` … a singleton component … Hence `{z}` is a singleton residual piece" | `third_singleton_piece` (both drafts; the hypothesis under which thm:s7universal (D)(i) = CV:singleton_D_i is read) |
| "Its complete X1 term on the latter generic polygon is zero, for arbitrary outside support and exterior geometry" | `pair_row_zero` |

B's `singleton_factor_zero` ("Otherwise every carrier of `S` is uniform … `Ω₁(S,A) = 0`") is the instance of
CV:singleton_D_i inside the proof, not a statement clause (the same rule as the rlane NOTES_FINAL applied to
row 167's clumps); it is the proof-lane lemma of unit PZ.

## 8. Rows 176 / 177 — R:extreme_transport, R:extreme_selected

Row 176 (`ExtremeTransportData`, A adopted): `singleton_rows_present` (":23–25 Full availability is part of
the statement … every `Q ∪ {j}` is independent on both sides"), `graphs_complementary` (":25–26 R-LOC-2 clause
4 … `H[T]=K3` iff `L[T]` empty"), `sign_branch` ((3) `s_x = σ, s_y = −σ, s_z = σ` as `s_a = s_c ∧ s_b = −s_a`),
`transport_x/y/z` ((2), "separately and without a symmetry assumption"; symmetric in the sides, so no side is
named). B's `∀ x ∈ T` form is equivalent; the three fields render "separately". The words (1) and the
rowwise table (5) are proof data.

Row 177 (`ExtremeSelectedData`, B's split + the common `couple`): `full_present_on_empty` (":27 makes `Q ∪ T`
an independent support on `L`"), `full_absent_on_complete` (":27–28 On `H`, `T` is not independent"; for every
`Q`), `couple` ((2) `T_H(∅) − T_L(∅) = T_L(xyz)` with `t` = `CompleteLocal` side). A's `extreme_signs`
(`ExtremeLocal ↔` alternating) is the accepted `extreme_iff_alternating` verbatim — dropped as redundant.

## 9. Row 178 — R:cv_theorem (`CvTheoremData`, `CvRNear`, `ChamberInvII`, `RProof.cv_R : CV.hyp_R`)

| sentence | field / lemma |
|---|---|
| (3) at `F_±` "`X_1(P_±) = Σ_{Q ∈ Ind(G[W])} Φ_±(Q)`" | `state_sum` = `X1_eq_sum_fibreTerm` PROVED (row 171 + `CV.X1_eq_sum_X1Summand`) |
| "the same finite outside-support set" | `outside_supports_transport` = `outsideSupports_transport` PROVED (A; from `FibrePartitionData.graph_on_W_same`; B had it as a hypothesis field) |
| "the proved identities (4)" | `fibre_identities` (the one clause supplied by rows 168–177 through `FibrePartitionData.avail_card`) |
| "Equality is preserved by finite summation, giving exactly CV ax:R" | `near` = `near_of_fibre_identities` PROVED; `CvTheoremData.of_fibre_identities` PROVED (needs `LocalizationData` for `hs`, `FibrePartitionData`, and the identities) |
| R6 "`cv_R = cv_R_near + chamberinv(ii)`" | `CvRNear` (global punctured form), `ChamberInvII` (prop:chamberinv (ii) in the form `CV.X1_eq_of_mem_chamber_of_pieceHomfly` proves modulo `PieceHomflyTransported`), `hyp_R_of_near_of_chamberinv` PROVED (B; A's `sides_of_near` is the same with the constancy as an explicit hypothesis) |
| "Apply the independently proved bridge afterwards" | `smR_shape_of_hyp_R` PROVED (B): `CV.hyp_R` + B4's pointwise shape ⇒ `C(P₊) = C(P₋)` at every side parameter of every SM simple triple germ, via `Bridge.eventOfTriple`, `exists_sorted_tripleAt`, `isSimpleRIII_eventOfTriple` — the consumption `Bridge.sm_R` will make (BRIDGE.md (19)–(21)) |

A's `sides` field (the all-sides form inside the R bundle) was not kept: it would make the R bundle depend on
prop:chamberinv (ii); B's separation keeps `CvTheoremData` provable from the R rows alone and isolates the
chamber step in one proved lemma. `cv_R`'s intended proof: `hyp_R_of_near_of_chamberinv cv_R_near chamberinv_ii`
with `cv_R_near := fun n _ hn E e f g h3 h4e h4f h4g hE => ⟨δ, …, CvTheoremData.of_fibre_identities hn hL hF hfib⟩`
(`hL`, `hF` from the accepted rows at a common radius; `hfib` from unit A2 below) and `chamberinv_ii` from
CV row 147 (ii).

## 10. Dependencies (checked against the RA texts and DEPENDENCIES.json)

| row | consumes (printed proof) | DEPENDENCIES.json | status of inputs |
|---|---|---|---|
| 168 exterior | R-LOC-2, R-PAR, def:wind, def:X1, def:piecediagram, lem:piececurve, ax:gausscode, ax:homfly, lem:turnlift(ii), lem:guardconst; needs record-invariance of `pieceHomfly` across supports/sides (CV:lem:pieceintrinsic, row 156) | lists cor:groupedknot (not used by the printed proof), lem:carrierword, R:parity | 156 pending (unit running); rest accepted |
| 170 availability_0_1 | R:fibre_partition, R:exterior-type transport of all carriers; 156 | R:fibre_partition, R:exterior | 156 pending |
| 172 generic_selector | R-LOC-2 (2b), def:wind, selector_A, `turn_visit_of_traced`, `weight_of_mixed`, `generic_table` | R:generic_table, def:wind, selector_A | ALL ACCEPTED |
| 173 generic_transport | R:generic_table, R:exterior, cor:groupedknot (empty row), lem:turnlift(ii), ax:homfly RIII invariance + an actual RIII move on the grouped diagram (G11), 156 | R:generic_table, R:exterior, cor:groupedknot | cor:groupedknot pending, 156 pending, G11 open |
| 174 generic_selected | 172, 173's lift, R:exterior, thm:carrierfloor (C),(D), lem:fulltwist, lem:homflyrows(ii), knot parity, uniformrot, turnlift(ii), cor:groupedknot, an RII move (G10) | R:generic_table, R:generic_selector, R:exterior, thm:carrierfloor, fulltwist, homflyrows | thm:carrierfloor BLOCKED (ax:slbound ← fd:contact, GAP-2) |
| 175 extreme_pair_zero | R-PAR (P1) over every outside crossing, def:pieces, CV:singleton_D_i (thm:s7universal (D)(i)) | R:parity, CV:singleton_D_i | singleton_D_i pending (partial-clause row; ← cor:groupedknot, carrierfloor, cb:singleton) |
| 176 extreme_transport | R:exterior, lem:fulltwist, selector_A, thm:carrierfloor, homflyrows(ii), knot parity, uniformrot, turnlift(ii), cor:groupedknot, an RII move (G10), 156 | R:exterior, fulltwist, selector_A, thm:carrierfloor | thm:carrierfloor BLOCKED (GAP-2) |
| 177 extreme_selected | R:exterior, homflyrows (ii)/(iii), selector_A, thm:carrierfloor, knot parity, uniformrot, turnlift(ii), cor:groupedknot, RIII + RII moves and an ambient isotopy through the wall (G10/G11) | R:exterior, homflyrows, selector_A, thm:carrierfloor | thm:carrierfloor BLOCKED (GAP-2) |
| 178 cv_R | rows 164, 171, 168–177, prop:chamberinv (ii) (← 156) | CV:ax:R and the R rows | 156 / 147 (ii) pending |

## 11. Provable now (with today's library) and unit split

Whole row provable now: **R:generic_selector only** (all five fields are X₁-free or reduce to
`rowTerm_of_mem_Ind`/`_not_mem_Ind` + `wind = 0`). Every other row is statement-only today; the X₁-free
clauses below are provable now as intermediate lemmas.

| unit | rows / clauses | inputs | when | est. |
|---|---|---|---|---|
| **U-SEL** | 172 whole: `selected_pair_unique`, `corner_signs_opposite` (sign case analysis on `generic_table.selected_unique`, `nonzero`, `crossingSign_swap`); `mixed_carrier` (R-LOC-2 (2b) `LocalizationData.adjacent` ⇒ the two same-edge visits are consecutive marks with no vertex mark between them ⇒ `geoSmoothingSuccessor` carries the arc, both selected endpoints in one cycle; corner turns by `turn_visit_of_traced`; mixed by opposite signs); `selector_zero` (`weight_of_mixed`, `Finset.prod_eq_zero`); `row_zero` | accepted | NOW | ~500 lines |
| **U-PRE** | the X₁-free presupposition clauses: 170 `fibre_zero/fibre_one/fibre_correspond` (`avail_same`, `F1.mem_localFibre`, singletons independent); 173 `canonical_branch`; 175 `pair_absent_on_complete/pair_present_on_empty/third_singleton_piece` (`CV.mem_Ind_iff`, `CV.mem_U`, `ParityData.interlaced_pair`); 176 `singleton_rows_present/graphs_complementary/sign_branch` (`complement_on_triangle`, `extreme_iff_alternating`); 177 `full_present_on_empty/full_absent_on_complete` | accepted | NOW | ~450 |
| **U-A2** | the assembly lemma `fibre_identities` from the eight bundles: `Φ(Q) = Σ_{J ⊆ T} rowTerm (Q ∪ J)` at full availability (absent `J` contribute `0`), the eight-subset case split per orbit (generic: `∅` (173), the selected pair's singletons (173), the centre and the selected pair (174), the two nonselected pairs (172 / absent), `T` absent; extreme: `∅`/`T` (177), singletons (176), pairs (175 / absent)), availability `0/1` by 170; then `CvRNear` from `CvTheoremData.of_fibre_identities` | the bundles' types only (no sorry consumed until the rows are proved) | NOW (statement-level) | ~350 |
| U-EXT | 168: carrier fibre-stability (`geoSmoothingSuccessor_union_of_disjoint`), piece stability (`CV.mem_U`, `pieceLabels`), wall transport of `wt`/`R` (`GeoMarkTransport`, `geoCarrierRotation_eq_of_family`); `Ω₁` via the piece records | 156 (record iso of `pieceHomfly`) | after 156 | ~1000 |
| U-AV | 170 `summand_transport/summands_agree/fibre_identity` | U-EXT's transport toolkit, 156 | after 156 | ~500 |
| U-GT | 173 rows (empty: grouped polynomial via RIII move + record iso; endpoints: `c ↦ b`, `a ↦ b` isomorphisms) | cor:groupedknot, 156, G11 | after 158 | ~800 |
| U-PZ | 175 `pair_row_zero` | CV:singleton_D_i | after 179 | ~150 |
| U-GS / U-ET / U-ES | 174 / 176 / 177 (the RA ledgers on `Omega1`/`carrierR`/`groupedPoly` with `fulltwist`, `homflyrows`, `uniformrot`, `turnlift`, `carrierfloor`) | thm:carrierfloor (GAP-2), cor:groupedknot, G10/G11 | blocked | ~1000 each |
| U-CV | `cv_R := hyp_R_of_near_of_chamberinv (…U-A2…) chamberinv_ii` | 147 (ii) ← 156 | after 147 | ~30 |

## 12. Fidelity risks to record in AUTHOR_NOTES before the rows are stated

1. **Row 172 ownership convention.** `MixedSharedStrandCarrier` names the two co-owned corners as the marks
   `(x, v)`,`(y, u)` or `(y, w)`,`(x, u)` — the visit on the INCOMING edge of each corner (`turn_visit_of_traced`,
   conv:selected-visits). A reviewer must not "correct" this to the two `u`-visits: that reading is false
   (§4, kernel-checkable on `LocalTable.succ wordE {a, b}`). Record the `#eval` in the review note.
2. **`CV.hyp_R` is declared in an R draft** (fixed name of CV:ax:R, R6 form); the assembler must ensure one
   declaration is seen by the CV row, `RProof.cv_R` and `Bridge.sm_R`. Its all-sides form makes `cv_R` depend on
   prop:chamberinv (ii) (`PieceHomflyTransported`, ← lem:pieceintrinsic 156); `hyp_R_of_near_of_chamberinv`
   isolates this. Fallback if (ii) slips: `Bridge.sm_R` needs only `CvRNear` + B4 `pointwise` + `SM.prop_C_chamber`
   (a second reduction lemma; an executor decision to be recorded, not made here).
3. **`ExteriorData.factorization`** represents `C_Q` by the base row `Q` on side `t`; equal to every other
   representative on either side by `independent_of_A` + `wall_invariant`. The full-availability binder is the
   printed one and must not be read as a narrowing (the general form is two lines away).
4. **Row 170 `summand_transport`** renders "carrier/record, selector, rotation and coefficient transport" as a
   carrier bijection with matched `weight`/`carrierR`/`groupedWrithe`/`groupedPoly`/`Omega1` — stronger than the
   bare fibre identity; it is the true shape of the availability-≤1 argument. Downgrade path in §3.
5. **Fixed labels + relabelled branches** (173, 174): the endpoint/centre/two-edge-side assignment per branch
   (`ac`: endpoints `a, c`, centre `b`, side `EdgeAB ∧ EdgeBC`; `ab`: `a, b`, `c`, `EdgeAC ∧ EdgeBC`; `bc`: `b, c`,
   `a`, `EdgeAB ∧ EdgeAC`) follows the six-case table and `selected_is_graph_selected`; in the canonical branch
   the two-edge side is `δ = +1` (`canonical_words`). Reviewers should re-check the table.
6. **Sides named by graphs** (`CompleteLocal`, `EmptyLocal`, `EdgeAB ∧ EdgeBC`), never by coorientation — the
   texts' own convention; identities symmetric in the sides carry no side name.
7. **Presupposition fields** beyond the bare printed claims: 170 `fibre_zero/one/correspond`; 172
   `selected_pair_unique`, `corner_signs_opposite`; 173 `canonical_branch`; 175 `pair_absent/present`,
   `third_singleton_piece`; 176 `singleton_rows_present`, `graphs_complementary`, `sign_branch`; 177
   `full_present/absent`; 178 `state_sum`, `outside_supports_transport`, `near`. Each is a sentence of the
   Statement/scene-setting paragraphs and is derivable from the accepted cores (none is stronger than the RA
   proofs establish); list them in the review note.
8. **Skeleton ↔ carrier identification** (rlane NOTES_FINAL §6 risk 6) is now an implicit proof obligation of
   rows 172–177 (the words `P/E`, `H/L`, the "arbitrary-`Q` successor lift" are proof steps; the bundles assert
   only row-term identities). The proof lane builds the lift on `geoSmoothingSuccessor`.
9. **Shared obstacle:** every `Ω₁` transport across the wall (168, 170, 173, 176, 177) needs the record-invariance
   of `pieceHomfly` (`Classical.choose` in `pieceSupport`; `CV.gausscode_polynomial` / `RecordIso`) — the same open
   point as CV row 147's `PieceHomflyTransported` (lem:pieceintrinsic, row 156). DEPENDENCIES.json lists 156 for
   no R row and lists cor:groupedknot for 168 although the printed R-EXTERIOR proof does not use it; record both.
10. **Blocked rows:** 174, 176, 177 need CV:thm:carrierfloor (GAP-2 via CV:ax:slbound ← fd:contact) — statable,
    to be reported as unprovable under the frozen interfaces unless GAP-2 closes; 175's `pair_row_zero` needs
    CV:singleton_D_i; 173's rows need CV:cor:groupedknot (+ the G11 RIII move); 176/177 also G10 (RII moves,
    ambient isotopy through the wall).
11. **`hn : 3 ≤ n` explicit** in every X₁-dependent row (R6; `three_le_of_h3` derives it from `h3`); the row
    signatures therefore differ from the four accepted cores by this one leading argument.
12. **`SM.lit_homfly`** appears in `#print axioms` of every statement touching `CV.X1` (through `homfly`): the
    accepted literature interface, to be listed in the review note, not a new axiom.
13. **Instances:** `exteriorFactor`/`touchingFactor` filter with `open scoped Classical in`; the accepted
    `instDecidableEqCrossing` vs classical instances inside `CV.Ind`/`CV.U`/`avail` may need `convert` /
    instance-generic lemmas in proofs (rlane NOTES_FINAL §6 risk 8).

## 13. Validation performed by the judge

* `lake env lean` on Statements_A (exit 0, 9 sorry), Statements_B (exit 0, 9 sorry), Statements_FINAL
  (exit 0, exactly 9 sorry = the nine row theorems, 8.1 s; no other warnings).
* `#print axioms` on all 18 proved auxiliaries of the FINAL (header of this file): standard axioms, plus
  `SM.lit_homfly` exactly where `CV.X1` is mentioned; `cv_R` shows `sorryAx` as expected.
* `#eval (List.finRange 9).map (LocalTable.succ wordE {a, b})` = `[8, 5, 3, 4, 2, 6, 7, 1, 0]` (cycles
  `{0,8}`, `{1,5,6,7}`, `{2,3,4}` = the table's `(1)[C](256)[B](34)[A]`); `succ wordP {a, c}` =
  `[4, 2, 3, 1, 8, 6, 7, 5, 0]` (cycles `{0,4,8}`, `{1,2,3}`, `{5,6,7}` = `(14)[C](23)[A](56)[B]`) — the basis
  of §4 and a re-check of the accepted table.
* Hand check of `corner_signs_opposite` (all three pairs, both orders) against (5)–(6) with `crossingSign_swap`;
  of `canonical_branch` (`s_a = s_c` ∧ nonalternating ⇒ all equal); of the branch/endpoint/centre/side table of
  173–174 against R_GENERIC_NONSELECTED_SELECTOR_PROOF.md:110–116 and `selected_is_graph_selected`; of B's
  `fibre_zero/one` (subsets of `{z}` are independent); of the availability-≤1 transport reading (§3).
