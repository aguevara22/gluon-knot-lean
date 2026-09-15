# Final fidelity review — completed 2026-09-14 18:15 UTC / 2:15pm ET (pod executor)

**Status: final; the focused stage is INCOMPLETE.** Drafted by the pod executor's documentation agent at
14:57Z while the certificate-rows lane (rows 76-80, 83) and the row-93 lane were still running
(AUTHOR_NOTES.md "End-of-work preparation started — 2026-09-14 ~14:50Z"); finalized at 18:15Z after the
last acceptances (18:05Z) and the stage check (18:06Z). It follows the checklist of FINAL_REVIEW.md item
by item. The four machine-derived tables (§1, §2, §3, §4.4) were regenerated at 18:06Z by
`python3 work/delivery/tools/gen_final_review_tables.py --write` from `tools/claims.py --json`, the map,
the audit summary and the review files (accepted 168, pending 24); every count in the prose was checked
at 18:10Z against `python3 tools/claims.py --pending-only`, `work/lean/lean-declarations.json` and the
receipts named in §0. This is a fidelity review of implemented Lean declarations against the frozen SM15
source; it is not an author approval and it does not claim the mathematics finished (§5). Final state:
**claims verified 109/132 (82.6%); checklist 168/192 accepted, 0 implemented-awaiting-review, 24 pending;
final targets 4/8; `python3 tools/check_lean.py work/lean --all` FAILED with "stage is incomplete" (§4.8).**

## 0. Sources of truth used

- Row status, declaration, module, review file: `work/lean/lean-declarations.json` (192 rows; edited only
  through `work/port/map_row.py`). Claim numbering "#": `python3 tools/claims.py --json` (184 units in
  document order; the 8 map rows outside it — 5 literature interfaces, `hyp:R`, `CV:ax:R`, `lem:weak-open` —
  are tagged `m<map index>`). The notes and STATUS.md use the claims.py numbers (row 91 = `cp:finite-contact-path`).
- Kernel evidence: `work/checks/stage-development.json` (current development receipt, byte-identical to
  `work/checks/dev-check-frontrowsw3b-accepted.json`, 18:06Z: passed=true, 168 mapped, 36 079 audited) and
  `work/checks/declaration-audit.json` (per-declaration axioms, `statement_hashes`); per-run receipts
  `work/checks/dev-check-*.json` (79, all passed); logs `work/checks/checker-run-*.log`. Stage check:
  `work/checks/stage-all-attempt-1806.log` (FAIL — the 24 unaccepted rows listed) and `work/checks/stage-1.json`
  (`passed: false`).
- Reviews: `work/reviews/<row>.json` (one per accepted row; the reviewer's inputs sit next to it as
  `<row>-reviewer-input-statement.lean.txt` and `<row>-source-excerpt-*.txt` / `<row>-registry-excerpt.md.txt`).
- Policy: `work/lean/axiom-policy.json` (standard axioms, five literature names, fixed target names);
  `blueprint/AXIOM_REGISTRY.md`; `blueprint/DEPENDENCIES.json`; the execution rule
  `/workspace/repos/lean/reassessment_rule.md` (adopted 17:00Z, §6).
- Decisions and disclosed readings: `work/AUTHOR_NOTES.md` (labels D-*, D-F1..D-F16, D-FR1, D-ER1, D-CP-1,
  FR-*, FR-C*, FR-R*, FR-CP-*, FR-ER-*, CE-R*, K-*, R-*, GAP-1/GAP-2), `work/drafts/gap2/GAP2_STATEMENTS_MEMO.md`,
  `work/drafts/gap2/CPRow91_PLAN.md`, `work/drafts/pldiscs/PLDISCS_FEASIBILITY.md`, `work/STATUS.md`.
- Source frame SM15: `reference/`, `provenance/SM15`, `blueprint/` (frozen; never edited).

## 1. Summary of the 132 claims / 192 checklist rows by status  (table regenerated 18:06Z)

<!-- BEGIN:SUMMARY -->
| unit class | total | accepted | implemented (awaiting review) | pending |
|---|---|---|---|---|
| source claims (tools/claims.py: "claims verified") | 132 | 109 | 0 | 23 |
| definitions / conventions (units of work, not claims) | 52 | 52 | 0 | 0 |
| literature interfaces + hypotheses + extra lemma (map rows outside claims.py) | 8 | 7 | 0 | 1 |
| checklist rows total (work/lean/lean-declarations.json) | 192 | 168 | 0 | 24 |
| final targets (EXECUTION.json) | 8 | 4 | 0 | 4 |

Generated 2026-09-14 18:06 UTC from `python3 tools/claims.py --json` (claims verified 109/132), the map and `work/delivery/receipts/declaration-audit.summary.json`. Current checker receipt work/checks/stage-development.json: passed=True, stage=None, stage_accepted=False, mapped_declarations=168, audited_declarations=36079.
<!-- END:SUMMARY -->

Final state (`python3 tools/progress.py --once` at 18:08Z: "claims verified 109/132 (82.6%); kernel-checked
awaiting review 0; 87.5% checklist (168/192 accepted); targets 4/8"; `work/PROGRESS.md`): claims verified
109/132, checklist 168/192, targets 4/8 (`prop:C-chamber`, `prop:C-silent`, `thm:C-S3`, `thm:C-S5`), 0 rows
implemented-awaiting-review, 24 pending (`python3 tools/claims.py --pending-only` lists the 23 pending claims;
the 24th pending map row is the interface `src:contact`, outside claims.py). 109/132 is the reachable ceiling
without GAP-2 recorded at 12:20Z (STATUS.md checkpoint 14:46Z): every row that is neither GAP-2-blocked nor deferred
(row 57) is accepted. At draft time (14:57Z) the figures were 102/132, 160/192, 32 pending; the eight rows accepted
since are `hyp:R` (15:45Z), `ng:commutation` (16:25Z), `ng:front-I`, `ng:front-III`, `ng:deletions` (17:40Z),
`ng:front-II`, `ng:local-front-bound`, `fd:ng-bound` (18:05Z). All 168 accepted rows have `statement_sha256` equal
to `statement_hashes` of the current audit (`work/delivery/receipts/declaration-audit.summary.json`, keyed by row) and
a review file with `verdict: "faithful"` (re-checked 18:10Z over the whole map; the checker enforces the same).

## 2. Accepted rows — one line each  (table regenerated 18:06Z; 168 rows)

Columns: `#` claim number (claims.py) or `m<map index>`; axioms from `declaration-audit.json` with
`std` = propext, Classical.choice, Quot.sound; `H` = `SM.lit_homfly`; `LM` = `SM.lp_lm`;
`LMU` = `SM.lp_lm_uniqueness`; `NG` = `SM.ng_finite_word` (the four declared literature interfaces —
nothing else appears, §4.3). "Disclosed readings" is one clause taken from the review's
`discrepancies` / `stronger_than_source` / `weaker_than_source` arrays and the AUTHOR_NOTES fidelity-risk
entries; "labels" names the recorded risk/decision items the reviewers cited. All 168 verdicts are `faithful`;
39 handover rows additionally carry `countersignature_20260913` (re-review by separate sessions, AUTHOR_NOTES
2026-09-13 ~16:15Z), and `lem:chi-basic`, `lem:g1`, `prop:A-chamber` carry the SM15 `source_realignment.re_review`.

<!-- BEGIN:ACCEPTED -->
| # | row | Lean declaration | module | review file | verdict | axioms | disclosed readings (one clause) |
|---|---|---|---|---|---|---|---|
| 1 | `def:polygon` | `SM.polygonData` | SM.Polygon | reviews/def-polygon.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); The printed meta-clause 'every notion below is invariant under σ' is not part of the definition's content and is only p… [3 notes] |
| 2 | `def:chirotope` | `SM.chirotopeData` | SM.Chirotope | reviews/def-chirotope.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Definitions are given on a wider domain than the printed one: chi and turn are defined for every n (including n = 0, 1,… [1 note] |
| 3 | `lem:chi-basic` | `SM.chi_basic` | SM.Chirotope | reviews/lem-chi-basic.json | faithful | std | handover review + countersignature 2026-09-13; SM15 wording-only change (left/right naming convention) re-read and countersigned (source_realignment.re_review) |
| 4 | `def:generic` | `SM.Generic` | SM.Generic | reviews/def-generic.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); G2 reads 'three distinct edge segments' as three pairwise distinct indices (Generic.lean:14-17); if two differently ind… [2 notes] |
| 5 | `lem:g1` | `SM.g1` | SM.G1Consequences | reviews/lem-g1.json | faithful | std | handover review + countersignature 2026-09-13; SM15 clause (iv) "two distinct adjacent edges" — SM.g1 already states i ≠ j (re_review countersigned) |
| 6 | `def:crossings` | `SM.crossingData` | SM.CrossingEquiv | reviews/def-crossings.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); The Lean crossing set, point, parameter and sign are total definitions on every LabelledTuple n (only [NeZero n] for cr… [3 notes] |
| 7 | `lem:crossing-test` | `SM.crossing_test` | SM.Crossings | reviews/lem-crossing-test.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Finiteness of X(P) (third conjunct, Crossings.lean:161) is asserted under G1 alone, whereas the source sentence (sm-1-p… [2 notes] |
| 8 | `lem:wall-segment-stability` | `SM.wall_segment_stability` | SM.WallSegmentStability | reviews/lem-wall-segment-stability.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Nonzero directions are assumed only at the centre (hnz, Lean line 121) while the source's 'nonzero oriented segments' (… [6 notes] |
| 9 | `def:chamber` | `SM.chamber_definition` | SM.CyclicChambers | reviews/def-chamber.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); CyclicChambers.lean:156-157 gives the preimage explicitly as the union of the components of the n cyclic translates gen… [2 notes] |
| 10 | `prop:chambers` | `SM.chambers` | SM.ChamberPaths | reviews/prop-chambers.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Representation remark only (not a weakening of content): the order clause is phrased with the explicit Cramer formula e… [3 notes] |
| 11 | `def:gauss` | `SM.gauss_definition` | SM.GaussDefinition | reviews/def-gauss.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); The theorem additionally proves facts the printed definition only presupposes or that follow from lem:crossing-test: in… [3 notes] |
| 12 | `def:interlace` | `SM.interlacement_definition` | SM.InterlaceDefinition | reviews/def-interlace.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Aggregate clause 2 (InterlaceDefinition.lean:19-21) asserts the 'exactly one visit of y between the two visits of x' fo… [3 notes] |
| 13 | `def:visible` | `SM.visible_signature_definition` | SM.VisibleDefinition | reviews/def-visible.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Clause 4 (VisibleDefinition.lean:16): injectivity of the alphabet embedding Cycle (Crossing P) -> Cycle (Finset (ZMod n… [5 notes] |
| 14 | `def:weak` | `SM.weak_definition` | SM.WeakGeneric | reviews/def-weak.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Domain generality (benign): WeakGeneric, weakLocus, silentLocus, WeakTuple and WeakPolygon (WeakGeneric.lean:11-25, 92-… [7 notes] |
| 15 | `def:regular` | `SM.regular_definition` | SM.RegularDefinition | reviews/def-regular.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Clauses 5-6 (RegularDefinition.lean:22-23): Regular (shift a P) <-> Regular P and principalTurn (shift a P) i = princip… [2 notes] |
| 16 | `def:shift` | `SM.reversal_definition` | SM.Reversal | reviews/def-shift.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Reversal.lean:20-24 / 75-88: involutivity of reversal and of polygonReversal is proved and included in reversal_definit… [3 notes] |
| 17 | `lem:rot` | `SM.rotation_number` | SM.RotationTheorem | reviews/lem-rot.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Extra conjunct: cyclic-shift invariance ∀ a : ZMod n, rotationNumber (shift a P) = rotationNumber P (RotationTheorem.le… [4 notes] |
| 18 | `lem:uniformrot` | `SM.uniform_rotation` | SM.UniformRotation | reviews/lem-uniformrot.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); no notes |
| 19 | `lem:shift` | `SM.shift_reversal` | SM.ShiftTheorem | reviews/lem-shift.json | faithful | std | proved as printed on SM15 (clause (iii) with −z(P), clause (iv) on the regular locus); SM12 counterexample work/repairs/ShiftZeroTurn.lean documents the erratum (scope_issue/sm15_note in the map); cold-start review 2026-09-12 + countersignature |
| 20 | `def:admissible` | `SM.admissible_definition` | SM.Admissible | reviews/def-admissible.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); The vertex count n of GenericPolygon n is a natural number while the printed pair (n,r) lives in ℤ²; since admissibilit… [3 notes] |
| 21 | `lem:fibres` | `SM.nonempty_fibres` | SM.Fibres | reviews/lem-fibres.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); no notes |
| 22 | `def:germ` | `SM.wall_germ_definition` | SM.GermDefinition | reviews/def-germ.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); The theorem additionally asserts the labelled-side clause polygonProjection '' labelledSide b = side b (GermDefinition.… [2 notes] |
| 23 | `lem:triple-sides` | `SM.triple_sides` | SM.TripleSides | reviews/lem-triple-sides.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); The Lean witness additionally asserts δ ≤ g.radius (TripleSides.lean:89); this is a trivial bookkeeping conjunct, not a… [1 note] |
| 24 | `def:walls` | `SM.named_walls_definition` | SM.NamedWallsDefinition | reviews/def-walls.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); NamedWallsData proves the printed prose claims 'the types are mutually exclusive' (exclusivity, unique_kind) and 'the t… [4 notes] |
| 25 | `lem:flat-sides` | `SM.flat_sides` | SM.FlatSides | reviews/lem-flat-sides.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); FlatSidesData asserts Function.Injective g.center (all central vertices distinct); the source only proves this inside t… [6 notes] |
| 26 | `lem:wall-sides` | `SM.wall_sides` | SM.WallSides | reviews/lem-wall-sides.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Each branch supplies one common local radius delta (0<delta<=radius) for all its local clauses at once, and includes t=… [8 notes] |
| 27 | `lem:cusp-sides` | `SM.cusp_sides_of_continuous_curve` | SM.CuspCurve | reviews/lem-cusp-sides.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); side_laws, other_crossings, needle_turns, rotation_jump, loop_arc and empty_middle_edge are asserted for every side par… [5 notes] |
| 28 | `def:deletion-halves` | `SM.deletion_halves_definition` | SM.DeletionHalvesDefinition | reviews/def-deletion-halves.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); DeletionData records several immediate consequences the printed definition leaves implicit (fused closing edge P(j+1)-P… [3 notes] |
| 29 | `lem:children` | `SM.children` | SM.Children | reviews/lem-children.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); None. The extra hypotheses 3 ≤ k (both clauses) and the instance argument NeZero k are harmless: def:polygon already re… [4 notes] |
| 30 | `lem:transport-polynomials` | `SM.transport_polynomials` | SM.TransportPolynomials | reviews/lem-transport-polynomials.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); family_exact and one_per_name (TransportPolynomials.lean:17-20): the family is exactly the image of the name type and t… [6 notes] |
| 31 | `thm:relgp` | `SM.relative_general_position` | SM.RelativeGeneralPosition | reviews/thm-relgp.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); generic_endpoint_collar (RelativeGeneralPosition.lean:49-50): a positive generic collar at both endpoints is asserted;… [6 notes] |
| 32 | `def:root` | `SM.rootData` | SM.RootBoundary | reviews/def-root.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Cosmetic only, not a fidelity loss: `rootData` bundles the edge-vector function `edge` (ℓ_g = μ_{g+1} − μ_g, Polygon.le… [3 notes] |
| 33 | `def:gates` | `SM.gatesData` | SM.Gates | reviews/def-gates.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Lean gatesData (Gates.lean:99) is defined for every n with [NeZero n], not only n >= 3 as the source's polygons require… [2 notes] |
| 34 | `lem:gates-nonzero` | `SM.gates_nonzero` | SM.Gates | reviews/lem-gates-nonzero.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); no notes |
| 35 | `def:treesum` | `SM.treesumData` | SM.TreeCoefficient | reviews/def-treesum.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Harmless generality only: openTreeRec/rootedTreeRec (TreeCoefficient.lean:15-27) are defined over any CommRing with arb… [1 note] |
| 36 | `lem:treesum-trees` | `SM.treesum_trees` | SM.PlaneTreeFormal | reviews/lem-treesum-trees.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Conjunct 3 gives the specialization of the left-hand side (the recursion) only; the statement does not literally say th… [5 notes] |
| 37 | `prop:A-chamber` | `SM.A_chamber` | SM.TreeChamber | reviews/prop-A-chamber.json | faithful | std | handover review + countersignature 2026-09-13; SM15 "constant on every labelled chamber (the root fixed)" = the labelled-chamber conjunct of SM.A_chamber (re_review countersigned) |
| 38 | `def:nearfar` | `SM.nearfarData` | SM.NearFar | reviews/def-nearfar.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); geometricBoundaryArray is defined for every LabelledTuple n and root g : ZMod n, not only for polygons satisfying (G1)… [2 notes] |
| 39 | `lem:farout` | `SM.farout` | SM.Farout | reviews/lem-farout.json | faithful | std | handover review + countersignature 2026-09-13 (faithful); Farout.lean:15-20 — the inverse polynomials Psi have coefficients in R (depending on the fixed D, H); if 'polynomial in… [6 notes] |
| 40 | `thm:single-triple` | `SM.WallGerm.single_triple_wall_response` | SM.SingleTripleWallResponse | reviews/thm-single-triple.json | faithful | std | Formal only: d and the closeness radius δ (Lean 99) are quantified inside ∀ p ω x y z (Lean 93), so they may nominally depend on the chosen… [8 notes] |
| 41 | `def:induced-roots` | `SM.induced_roots_definition` | SM.InducedRootsDefinition | reviews/def-induced-roots.json | faithful | std | Uniqueness in the nonincident case (stmt 52) is asserted only for child edges whose ordered labels are (g, g+1); an edge of P∖j with labels… [6 notes] |
| 42 | `thm:A-S3` | `SM.WallGerm.flat_law_treeCoefficient` | SM.FlatLawTree | reviews/thm-A-S3.json | faithful | std | Conjunct 1 (statement line 29) asserts as a conclusion that exactly one punctured side is the right side (τ_j = -1 at every point) and the… [4 notes] |
| 43 | `thm:A-S4` | `SM.WallGerm.cusp_law_treeCoefficient` | SM.CuspLawTree | reviews/thm-A-S4.json | faithful | std | Lean conclusion (line 34) adds existence and uniqueness of the cusp case b (exactly one of the two printed betweenness placements holds); t… [4 notes] |
| 44 | `thm:A-S7` | `SM.WallGerm.vertex_edge_law_treeCoefficient` | SM.VertexEdgeLawTree | reviews/thm-A-S7.json | faithful | std | Statement line 30: `w.BigonAt M a ∨ w.SlidingAt M a` is asserted as a conclusion (the source only assumes 'of bigon or sliding type'; the d… [4 notes] |
| 45 | `thm:A-R3E` | `SM.WallGerm.triple_and_silent_laws_treeCoefficient` | SM.TripleSilentLawsTree | reviews/thm-A-R3E.json | faithful | std | Formal nuance only (equivalent, not a discrepancy): conclusions are asserted at every pair of labelled points (t on P_+, s on P_-) rather t… [1 note] |
| 46 | `def:soft` | `SM.softInsertion_definition` | SM.SoftInsertionDefinition | reviews/def-soft.json | faithful | std | labelling of P_ε pinned only through bijectivity and cyclic successor relations |
| 47 | `lem:soft-generic` | `SM.soft_family_generic` | SM.SoftGenericLemma | reviews/lem-soft-generic.json | faithful | std | All convergence statements (D_ε → v, inherited point and both parameters, newborn point) are two-sided Tendsto along 𝓝 0 on globally define… [9 notes] |
| 48 | `thm:A-soft` | `SM.SoftDuplication.soft_theorem_treeCoefficient` | SM.SoftTheoremTree | reviews/thm-A-soft.json | faithful | std | ε₀ is an arbitrary positive real (S31 `ε0 : ℝ`, `hε0 : 0 < ε0`), not only the constant of lem:soft-generic (source 1158-1159); the source s… [5 notes] |
| 49 | `prop:A-reversal` | `SM.treeCoefficient_reversal_shift_law` | SM.ReversalShiftLaw | reviews/prop-A-reversal.json | faithful | std | Statement line 14 requires the typeclass instance `[NeZero n]` in addition to `hn : 3 ≤ n` (line 19). Every n ≥ 3 is nonzero, so no case of… [2 notes] |
| 50 | `def:decomposition` | `SM.decomposition_definition` | SM.DecompositionDefinition | reviews/def-decomposition.json | faithful | std | Statement lines 36-38: descent of IsDecomposition along the cyclic relabelling (crossingSupportShift a S under generic_shift a P) is not st… [3 notes] |
| 51 | `def:smoothing` | `SM.smoothing_definition` | SM.SmoothingDefinition | reviews/def-smoothing.json | faithful | std | continuum traversal circle replaced by the finite marked circle (Mark P); cycles as successor orbits |
| 52 | `conv:selected-visits` | `SM.selected_visits_convention` | SM.SelectedVisitsConvention | reviews/conv-selected-visits.json | faithful | std | finite successor model of the source proof over the ported Carrier lane |
| 53 | `lem:carriers` | `SM.carriers_lemma` | SM.CarriersLemma | reviews/lem-carriers.json | faithful | std | (i) "independent of the order of reconnections" has no propositional counterpart (carriers defined directly as cycles) |
| 54 | `def:uniform` | `SM.uniform_definition` | SM.UniformDefinition | reviews/def-uniform.json | faithful | std | Domain: CarrierUniform, CarrierMixed, UniformDecomposition, carrierRotation, carrierLeftTurns are defined for every S : Finset (Crossing P)… [3 notes] |
| 55 | `def:positive-lift` | `SM.positive_lift_definition` | SM.PositiveLiftDefinition | reviews/def-positive-lift.json | faithful | std | Diagram is a labelled presentation (base vertex, component order) of the printed diagram; polygonal class (sm-3:337-343) |
| 56 | `def:gauss-record` | `SM.gauss_record_definition` | SM.GaussRecordDefinition | reviews/def-gauss-record.json | faithful | std | domain = polygonal generic diagrams (regular smooth immersions of the bridge paragraph not in the class) |
| 58 | `def:flat-carriers` | `SM.flat_carriers_definition` | SM.FlatCarriers | reviews/def-flat-carriers.json | faithful | std | non-blocking (STRONGER): common_gauss_word.1 (stmt 819-820) asserts equality of the linear Gauss LISTS cut at label 0 for the sides, beyond… [20 notes] |
| 59 | `cor:flat-carriers` | `SM.flat_carriers` | SM.FlatCarriers | reviews/cor-flat-carriers.json | faithful | std | non-blocking (STRONGER): centre_turn_signs (stmt 1220-1223) adds a conclusion absent from printed clause (ii) (which speaks only of 'both s… [16 notes] |
| m60 | `lit:homfly` | `SM.lit_homfly` | SM.LinkInterfaces | reviews/lit-homfly.json | faithful | std+H | polygonal Diagram domain (def:positive-lift reading); planar isotopy = EqvGen(Reparam ∨ Deform); descent over LinkEquiv (D2); skein triples = switch-and-smooth (D3) |
| m61 | `lp:lm` | `SM.lp_lm` | SM.LinkInterfaces | reviews/lp-lm.json | faithful | std+LM | ∃-form for "the function constructed in LM §1"; witness lmF pinned by lp:lm-uniqueness; polygonal domain |
| m62 | `lp:lm-uniqueness` | `SM.lp_lm_uniqueness` | SM.LinkInterfaces | reviews/lp-lm-uniqueness.json | faithful | std+LM+LMU | competitor hypothesis Q = 1 on every crossing-free one-component polygon (formally stronger hypothesis, no effect) |
| 60 | `lp:coefficient-transport` | `SM.coefficient_transport` | SM.CoefficientTransport | reviews/lp-coefficient-transport.json | faithful | std+LM+LMU | non-blocking: S5 'the crossing-free circle' (singular) is rendered as 'every one-component crossing-free diagram' (`Diagram.IsCrossingFreeC… [2 notes] |
| 61 | `lp:core` | `SM.lp_core` | SM.PolynomialBlock | reviews/lp-core.json | faithful | std+H+LM+LMU | non-blocking: `gaussian` (stmt 1161) states the evaluation via the proof's eq. lp:gaussian (φ(l) = ia, φ(m) = −iz, sm-3:1067-1069); the the… [6 notes] |
| 62 | `lp:split-circle` | `SM.split_circle` | SM.PolynomialBlock | reviews/lp-split-circle.json | faithful | std+LM | non-blocking: the hypothesis `IsSplitCircleAddition D D'` requires only that the restriction of D' to the components other than the added c… [2 notes] |
| 63 | `rp:record-polynomial` | `SM.record_polynomial` | SM.PolynomialBlock | reviews/rp-record-polynomial.json | faithful | std+LM | `coeff_eq` (stmt 1151-1152): the coefficient clause is stated only for the Gaussian evaluation P (coefficients a^d z^k of reMap(φ(F_D)) ∈ R… [8 notes] |
| 64 | `lc:presentations` | `SM.presentations` | SM.PolynomialBlock | reviews/lc-presentations.json | faithful | std+LM | non-blocking: the illustrative instance list (page-chart changes, crossing-free replacements, compatible height choices; excerpt lines 6-9)… [6 notes] |
| 65 | `lc:single-crossing` | `SM.single_crossing` | SM.SingleCrossing | reviews/lc-single-crossing.json | faithful | std+LM | non-blocking: the conclusion `P D = 1` = `reMap (phi (T.toTG (lmF D))) = 1` does not by itself assert `imMap (phi (T.toTG (lmF D))) = 0`; t… [2 notes] |
| 66 | `mp:join` | `SM.join` | SM.MarkedProducts | reviews/mp-join.json | faithful | std+LM | labels D9; non-blocking: `MarkedDiagram.μ` (statement l.149) is data with no printed counterpart; it is fully determined by (D, I) through `comp_eq` +… [8 notes] |
| 67 | `mp:stack` | `SM.stack` | SM.Stack | reviews/mp-stack.json | faithful | std+LM | non-blocking: block tags are 0..q-1 (`Fin q`) where the print writes 1..q; the relabelling is order-preserving so "smaller-index block" is… [4 notes] |
| 68 | `mp:zero-link` | `SM.zero_link` | SM.ZeroLink | reviews/mp-zero-link.json | faithful | std | Applies only to polygonal diagrams (`Diagram` = generic `Shadow` of closed polygons with k ≥ 3 vertices, `Regular` components, `tail_off`),… [7 notes] |
| 69 | `mp:lowest` | `SM.lowest` | SM.MarkedProducts | reviews/mp-lowest.json | faithful | std+LM | non-blocking: `two_component_row` (stmt 379-382) renders the printed remark "For c = 2 this is the two-component mixed row …" (excerpt l.12… [3 notes] |
| 70 | `mp:blocks` | `SM.blocks` | SM.MarkedProducts | reviews/mp-blocks.json | faithful | std+LM | D9: clean marked join = RecordIso to joinRecord; sign_preserved as an abstract bijection; realizes clause kept and proved |
| 71 | `def:C` | `SM.corner_state_sum_definition` | SM.CornerStateSum | reviews/def-C.json | faithful | std+H | non-blocking: cornerSlot and carrierRotationInt (S:61-63, 82-84) are total in S — they have values (round of a possibly non-integer carrier… [9 notes] |
| 72 | `lem:C-X1` | `SM.C_X1` | SM.CX1 | reviews/lem-C-X1.json | faithful | std+H | non-blocking: `carrierWeight`, `wind` and the fields weight_right / weight_left / weight_mixed / wind_eq (St:22-31, 36-51) are stated for e… [7 notes] |
| 73 | `ng:front-domain` | `SM.front_domain_definition` | SM.FrontSmooth | reviews/ng-front-domain.json | faithful | std | FR-1 polygonal reading of S(F) (S is a Diagram carrying the Marking of the rounded curve G); FR-2 cusp criterion in derivative form; FR-3/FR-4 smooth = C^∞, 1-periodic parameter circles |
| 74 | `ng:smoothing-record` | `SM.ng_smoothing_record` | SM.FrontRecordBridge | reviews/ng-smoothing-record.json | faithful | std+LM | FR-1/D-F6: IsRounding S does not tie S to the rounded curves G; printed content kernel-checked as library thm SM/FrontGeomModel.lean isRounding_of_geomModel (cited, not a row) |
| 75 | `def:adeg` | `SM.adeg_definition` | SM.AdegDefinition | reviews/def-adeg.json | faithful | std | Field `domain` (statement line 26) asserts IsDomain R for the whole ring R = ℤ[a^{±1},z^{±1}]; the source (line 1889) only calls the coeffi… [3 notes] |
| 76 | `ng:commutation` | `SM.ng_commutation` | SM.FrontRowsW2S | reviews/ng-commutation.json | faithful | std+LM | labels FR-10, FR-16, FR-5, FR-8, FR-9; deform_*: only jointly C^∞ families (fixed circle indexing, fixed 1-periodic parametrizations) on [0,1] × ℝ count as 'deformations through… [13 notes] |
| 77 | `ng:front-I` | `SM.ng_front_I` | SM.FrontRowsW3 | reviews/ng-front-I.json | faithful | std+LM | labels FR-1, FR-16, FR-6, FR-8; Class: the Lean row holds for PL realizations of closed oriented Rutherford words (SM.realize : OWord → PLFront), not for arbitrary fronts… [5 notes] |
| 78 | `ng:front-II` | `SM.ng_front_II` | SM.FrontRowsW3b | reviews/ng-front-II.json | faithful | std+LM | labels FR-1, FR-16, FR-5, FR-8; Class narrowing (disclosed FR-8/FR-5): the printed 'front type-II moves' act on fronts of ng:front-domain; the Lean fields quantify only ov… [3 notes] |
| 79 | `ng:front-III` | `SM.ng_front_III` | SM.FrontRowsW3 | reviews/ng-front-III.json | faithful | std+LM | labels FR-1, FR-16, FR-8; Class narrowing (FR-8, disclosed): only realizations of closed oriented words, not arbitrary fronts of ng:front-domain; closed by the accep… [7 notes] |
| 80 | `ng:deletions` | `SM.ng_deletions` | SM.FrontRowsW3 | reviews/ng-deletions.json | faithful | std+LM | labels FR-1, FR-13, FR-16, FR-6, FR-8; Class reading FR-8 (disclosed, judged non-blocking): stated on standard realizations of closed oriented words whose letters contain the del… [8 notes] |
| 81 | `ng:circle` | `SM.ng_circle` | SM.FrontRowsW2 | reviews/ng-circle.json | faithful | std+LM | FR-8 class narrowing: sentence 1 on realizations of closed oriented Rutherford words (SM.realize), sentence 2 on PLFront (FR-11); FR-5 word layer is the printed certificate device |
| 82 | `ng:cusp-skein` | `SM.ng_cusp_skein` | SM.FrontRowsW2 | reviews/ng-cusp-skein.json | faithful | std+LM | FR-8 stated on SM.realize of closed oriented words; FR-12 unique compatible smoothing as a theorem, right-cusp templates outside the row |
| m86 | `ng:finite-word` | `SM.ng_finite_word` | SM.FrontInterfaces | reviews/ng-finite-word.json | faithful | std+NG | literature axiom stated on closed oriented words (FR-6): PrincipalChain stop rule as a consequence of Laws; empty word included (trivial) |
| 83 | `ng:local-front-bound` | `SM.ng_local_front_bound` | SM.FrontRowsW3b | reviews/ng-local-front-bound.json | faithful | std+LM+NG | labels FR-1, FR-16, FR-NB-4; The theorem is conditional on `F.IsRounding S` and asserts nothing about the existence of a rounding: for a front F with no Lean-rounding t… [3 notes] |
| 84 | `fd:transverse-neighborhood` | `SM.fd_transverse_neighborhood` | SM.TransverseNeighborhood | reviews/fd-transverse-neighborhood.json | faithful | std | FR-TN-3 no smoothness field for h (forced); FR-TN-5 TransverselyIsotopic endpoints; one false internal leaf repaired without statement change |
| 85 | `fd:parameter-avoidance` | `SM.fd_parameter_avoidance` | SM.ParameterAvoidance | reviews/fd-parameter-avoidance.json | faithful | std | FR-PA-1 K compact in EuclideanSpace ℝ (Fin d), not an abstract manifold |
| 86 | `fd:contact-motions` | `SM.fd_contact_motions` | SM.ContactMotions | reviews/fd-contact-motions.json | faithful | std | SmoothDependence proved inside the module (D-F13 superseded); unconditional |
| 87 | `fd:generic-front` | `SM.fd_generic_front` | SM.GenericFront | reviews/fd-generic-front.json | faithful | std | D-F15 compact support inside IsContactIsotopy = disclosed strengthening; FR-GF-1..8 |
| 88 | `fd:linking-calculus` | `SM.fd_linking_calculus` | SM.LinkingCalculusRow | reviews/fd-linking-calculus.json | faithful | std | D-F16 restated unconditionally (RegularPoleCount proved); framing pushoff embeddedness not asserted (printed sentence claims disjointness only) |
| 89 | `ce:rounding` | `SM.ce_rounding` | SM.CeRounding | reviews/ce-rounding.json | faithful | std | CE-R1 diagram = RegularGenericProjection (no polygonal Diagram delivered); CE-R2 ℝ-indexed SpatialFamily via the smoothTransition time clamp; CE-R4 construction constants differ (statement unaffected) |
| 90 | `ce:smoothing-record` | `SM.ce_smoothing_record` | SM.CeSmoothingRecord | reviews/ce-smoothing-record.json | faithful | std+LM | D-1 collar field on CleanCuspSmoothing; K-3 D_ε fields quantify over CuspRoundingFamily; K-5 clean neighbourhood convex (IsDisc); FR-1 polygonal reading |
| 92 | `def:transverse-front` | `SM.transverse_front_definition` | SM.TransverseFront | reviews/def-transverse-front.json | faithful | std | contact space, C^∞ 1-periodic embedded loops, z′ − y x′ > 0; RegularGenericProjection is "the diagram" (GAP-1: no polygonal record built here) |
| 93 | `fd:ng-bound` | `SM.fd_ng_bound` | SM.NgBound | reviews/fd-ng-bound.json | faithful | std+LM+NG | labels FR-1, FR-NB-1, FR-NB-2, FR-NB-3, FR-NB-4; [presuppositional, non-blocking] The Lean row does not assert that a front admits a rounding (no existence clause); if some SmoothFront had… [8 notes] |
| 95 | `cf:def-turning` | `SM.turning_definition` | SM.TurningNumber | reviews/cf-def-turning.json | faithful | std | non-blocking: `IsSeamLift` (stmt 124-125) fixes the seam at parameter 0, whereas the printed lift is 'at a seam' (any cut point of ℝ/ℤ). Co… [19 notes] |
| 96 | `cf:lem-turnlift` | `SM.turnlift` | SM.TurnLift | reviews/cf-lem-turnlift.json | faithful | std | `3 ≤ n` hypothesis on the (ii) fields and `rounding` (571, 574, 579, 584, 588, 596) — not printed, but implied by `Regular P`, so vacuous (… [19 notes] |
| 97 | `cf:lem-rounding` | `SM.cf_lem_rounding` | SM.Rounding | reviews/cf-lem-rounding.json | faithful | std | FR-R1 D_ε = polygonal D carried by the smooth curve (Carried record); FR-R3 no_triple via PolygonDiagram.generic; FR-R4 period-1 parameter; witness exports more than printed |
| 98 | `cf:lem-curl` | `SM.cf_lem_curl` | SM.Curl | reviews/cf-lem-curl.json | faithful | std+LM | FR-C1 record-level carrying (RecordCarried, no τ_eval at the kink); FR-C2 disc inside any preassigned neighbourhood (stronger); FR-C4 P_{F'} = P_F via polygonal RI |
| 101 | `cb:blocks` | `SM.cb_blocks_definition` | SM.CBBlocks | reviews/cb-blocks.json | faithful | std+H+LM+LMU | R-1..R-12: SM block = accepted CV.Piece; owner defined via a fixed visit and pinned; hn : 3 ≤ n bundle parameter |
| 102 | `cb:products` | `SM.cb_products` | SM.CBProducts | reviews/cb-products.json | faithful | std+LM | R-4/R-5: D_H = positiveLift of a carrier of an independent refinement; P_H = recordPolynomial of the restricted record |
| 104 | `cb:embedded-rotation` | `SM.cb_embedded_rotation` | SM.EmbeddedRotation | reviews/cb-embedded-rotation.json | faithful | std | D-ER1 proved independently of deferred row 57; FR-ER-2 sign read at supporting vertices (bounded region not defined); Embedded P wider than generic m = 0 |
| 106 | `prop:C-chamber` | `SM.prop_C_chamber` | SM.CChamber | reviews/prop-C-chamber.json | faithful | std+H | quantified over labelled representatives with polygonProjection Q ∈ chamber (polygonProjection P); entails cyclic-relabelling invariance (printed content made explicit) |
| 107 | `prop:C-silent` | `SM.prop_C_silent` | SM.CSilent | reviews/prop-C-silent.json | faithful | std+H | design B/R2 hybrid (work/drafts/csilent/PLAN_FINAL.md); exterior-extension (E) and pure-cut (C) walls as printed |
| 108 | `thm:C-S3` | `SM.thm_C_S3` | SM.CS3 | reviews/thm-C-S3.json | faithful | std+H | side values below an existential δ with τ_j = ∓1 over both Booleans (equivalent to chamber values by def:germ + prop:C-chamber); n ≥ 4 via N = n+1 |
| 109 | `lem:homflyrows` | `SM.homflyrows` | SM.MarkedProducts | reviews/lem-homflyrows.json | faithful | std+H+LM+LMU | labels D2, D9; The well-definedness of K#J and K⊔J as LinkEquiv classes (that all realizations are link-equivalent) is not stated (docstring 439); the pri… [12 notes] |
| 111 | `thm:C-S5` | `SM.thm_C_S5` | SM.CS5 | reviews/thm-C-S5.json | faithful | std+H | conclusion on the germ's own no-loop side points P(t), t in the side interval (chamber values via prop:C-chamber) |
| m118 | `hyp:R` | `SM.hyp_R` | SM.HypR | reviews/hyp-R.json | faithful | std+H | labels FR-HR-1, FR-HR-3, FR-HR-4, GAP-2; Non-blocking (FR-HR-3): the binder hn : 3 ≤ n (statement file :84) restricts to n ≥ 3, which the printed sentence does not state; it is the… [3 notes] |
| 113 | `def:star` | `SM.star_definition` | SM.StarDefinition | reviews/def-star.json | faithful | std | none disclosed (arrays empty) |
| 114 | `lem:star-generic` | `SM.star_generic_law` | SM.StarGenericLaw | reviews/lem-star-generic.json | faithful | std | Clause (ii) tangency (statement lines 29–32) is rendered by two independently sufficient characterizations at once — orthogonality of the e… [2 notes] |
| 115 | `lem:transport-lengths` | `SM.transport_lengths_law` | SM.TransportLengthsLaw | reviews/lem-transport-lengths.json | faithful | std | Nominal only: hab : a ≤ b (L19) excludes a > b, i.e. the empty Icc a b; the source's "compact interval" (S4) is a nonempty [a,b] (its proof… [3 notes] |
| 116 | `lem:transport-angle-interval` | `SM.transport_angle_interval_law` | SM.TransportAngleIntervalLaw | reviews/lem-transport-angle-interval.json | faithful | std | Statement line 20: the conjunct ∀ i, unitDir (θ i) = (Real.cos (θ i), Real.sin (θ i)) is an extra, definitionally true clause pinning the n… [4 notes] |
| 117 | `thm:mycyclic` | `SM.mycyclic` | SM.MycyclicTheorem | reviews/thm-mycyclic.json | faithful | std | orbit_fibre_pathConnected (statement L48-51): Mathlib IsPathConnected includes nonemptiness (∃ x ∈ F), so the Lean also asserts the orbit f… [4 notes] |
| 118 | `lem:transport` | `SM.transport_lemma` | SM.TransportLemma | reviews/lem-transport.json | faithful | std | Piecewise-affine is rendered as affine on the closed cells of a uniform mesh of [0,1] (statement lines 34-35), a special case of a general… [3 notes] |
| 119 | `lem:soft-rotation` | `SM.soft_rotation_law` | SM.SoftRotationLaw | reviews/lem-soft-rotation.json | faithful | std | Nuance, not a discrepancy: the Lean's threshold ε₀ (stmt l.20) is its own existential and is not identified with the ε₀ of lem:soft-generic… [3 notes] |
| 120 | `def:anchors` | `SM.anchors_definition` | SM.AnchorsDefinition | reviews/def-anchors.json | faithful | std | bound_spec (statement lines 57-61, data clause lines 166-172) requires all P_ε, 0 < ε < ε₀, to lie in one LABELLED chamber (connectedCompon… [2 notes] |
| 121 | `prop:anchors-exist` | `SM.anchors_exist` | SM.Anchors | reviews/prop-anchors-exist.json | faithful | std | Conjunct 5 (statement 152-154) omits the case-(Z) hypothesis `Admissible (m : ℤ) r` (source 404-405 says 'in case (Z)'; def:anchors 376): i… [5 notes] |
| 123 | `lem:A-small-values` | `SM.A_small_values_lemma` | SM.SmallValuesLemma | reviews/lem-A-small-values.json | faithful | std | Statement line 20: the conjunct `τ ≠ 0` is not in the printed sentence (source line 3-4 says only 'all turns have a common sign τ'). It is… [1 note] |
| 124 | `thm:root-indep-proof` | `SM.root_independence` | SM.RootIndependence | reviews/thm-root-indep-proof.json | faithful | std | none disclosed (arrays empty) |
| 125 | `cor:A-lawful` | `SM.A_lawful` | SM.ALawful | reviews/cor-A-lawful.json | faithful | std | flat_law (stmt 65-73) asserts Generic (deleteVertex w.center j), whereas thm:A-S3 (sm-2 401-409) states only (G1) of the deletion and the c… [7 notes] |
| 126 | `thm:uniqueness` | `SM.uniqueness` | SM.Uniqueness | reviews/thm-uniqueness.json | faithful | std | formally weaker-or-equal hypotheses (theorem at least as strong) |
| 129 | `CV:def:polygon` | `CV.polygon_definition` | CV.Setup | reviews/cv-def-polygon.json | faithful | std | Domain extension only (non-blocking): CV.IsPolygon (stmt 47) is defined for every n : ℕ, including n = 0, 1, 2 where the print (d1_setup.te… [1 note] |
| 130 | `CV:def:regular` | `CV.regular_definition` | CV.Setup | reviews/cv-def-regular.json | faithful | std | The explanatory sub-clause 'where the two candidate values ±π are both excluded from the open interval' (source 32-33) is rendered only by… [6 notes] |
| 131 | `CV:def:guarded` | `CV.guarded_definition` | CV.Setup | reviews/cv-def-guarded.json | faithful | std | "real polynomial functions" (tex 43): the bundle records only `continuous` (S 988) and `finite` (S 987); polynomiality is not stated as a f… [9 notes] |
| 132 | `CV:def:generic` | `CV.generic_definition` | CV.Setup | reviews/cv-def-generic.json | faithful | std | The alternative wording of prop:fidelity (i), 'equivalently every remote pair whose relative interiors meet has nonzero direction determina… [7 notes] |
| 133 | `CV:def:diagrammatic` | `CV.diagrammatic_definition` | CV.Setup | reviews/cv-def-diagrammatic.json | faithful | std | The hexagon non-example of 320-325 and the printed remark that 'the clause about preimages and shared images is not implied by the others'… [7 notes] |
| 134 | `CV:def:interlace` | `CV.interlace_definition` | CV.Events | reviews/cv-def-interlace.json | faithful | std | non-blocking: the bundle is stated for `hP : CrossingGeometry P` (statement file 274, 318) while the printed row fixes a diagrammatic polyg… [8 notes] |
| 135 | `CV:def:smoothing` | `CV.smoothing_definition` | CV.Carriers | reviews/cv-def-smoothing.json | faithful | std | "do not cross" (d1:358): `noncrossing_arcs` is a determinant-sign identity plus a repeat of transversality; no field asserts non-crossing o… [15 notes] |
| 136 | `CV:lem:carriers` | `CV.carriers` | CV.CarriersLemma | reviews/cv-lem-carriers.json | faithful | std | (ii) ranges over marked points of Γ only (finite carrier model); double points via accepted def:interlace |
| 137 | `CV:lem:carrierword` | `CV.carrierword` | CV.CarrierWord | reviews/cv-lem-carrierword.json | faithful | std | binder NARROWED to diagrammatic polygons and iterated carriers (round-2 unanimous; content-preserving on every instance the source uses) |
| 138 | `CV:def:wind` | `CV.wind_definition` | CV.Carriers | reviews/cv-def-wind.json | faithful | std | The count '\|S\|+1 carriers' (exc. 22-23) is not asserted anywhere in the bundle (deferred to lem:carriers (i), row 136) — non-blocking, a ci… [13 notes] |
| 139 | `CV:def:pieces` | `CV.pieces_definition` | CV.Carriers | reviews/cv-def-pieces.json | faithful | std | non-blocking: fields `pieces_nonempty` (l.762-764), `pieces_disjoint` (l.766-767), `pieces_cover` (l.769-771) have no literal printed sente… [9 notes] |
| 140 | `CV:def:record` | `CV.record_definition` | CV.RecordHomfly | reviews/cv-def-record.json | faithful | std | non-blocking: the oriented circle Γ itself is not part of the Lean record; only the cyclic successor on V (S130, S352). [15 notes] |
| 141 | `CV:def:homfly` | `CV.homfly_definition` | CV.RecordHomfly | reviews/cv-def-homfly.json | faithful | std+H+LM+LMU | non-blocking: the derivation sentence 'obtained by applying the skein relation at a crossing between L and a split unknot' (d1_setup 554-55… [11 notes] |
| 142 | `CV:def:piecediagram` | `CV.piecediagram_definition` | CV.PieceCurve | reviews/cv-def-piecediagram.json | faithful | std+H | `erased` (stmt 626-630): the double-point clause is `Nonempty (Crossing ≃ H)` = equal cardinality only; the printed 'every double point out… [12 notes] |
| 143 | `CV:lem:piececurve` | `CV.piececurve` | CV.PieceCurve | reviews/cv-lem-piececurve.json | faithful | std | Formally only: the bundle requires hn : 3 ≤ n (statement 637), absent from d1:594; CV polygons have n ≥ 3 by def:polygon, so no printed cas… [19 notes] |
| 144 | `CV:def:rot` | `CV.rot_definition_full` | CV.RotationSmooth | reviews/cv-def-rot.json | faithful | std | non-blocking: the intermediate claims of the printed 'Why regularity is part of the definition' argument (d1_setup 748-762: deletion of a f… [17 notes] |
| 145 | `CV:lem:turnlift` | `CV.turnlift_full` | CV.TurnLift | reviews/cv-lem-turnlift.json | faithful | std | non-blocking: polygon_ray_independent (statement 118-120) is not a sentence of the lemma; it is def:rot 744-745 ('the sum is independent of… [18 notes] |
| 146 | `CV:def:X1` | `CV.X1_definition` | CV.X1 | reviews/cv-def-X1.json | faithful | std+H+LM+LMU | The normalising identities of def:homfly (P(○) = 1, skein) are not restated in this bundle (they live in row 142's piece_polynomial and in… [11 notes] |
| 147 | `CV:prop:chamberinv` | `CV.chamberinv` | CV.ChamberInvRow | reviews/cv-prop-chamberinv.json | faithful | std+H+LM+LMU | Non-blocking: clause-(i) fields (stmt 66, 68, 71) are stated for every n with [NeZero n] rather than under the printed "Fix n >= 3" (src 93… [6 notes] |
| 148 | `CV:def:event` | `CV.event_definition` | CV.Events | reviews/cv-def-event.json | faithful | std | The cusp position clause p_1(0) ∉ [p_0, p_2] implicit in the word 'cusp' is not a field of `EventExampleData` (only the docstring, stmt 633… [13 notes] |
| 149 | `CV:lem:guardconst` | `CV.guardconst` | CV.Events | reviews/cv-lem-guardconst.json | faithful | std | Domain in n: `Event (n) [NeZero n]` (reviewer 332) admits n = 1, 2, whereas the printed def:polygon (d1_setup.tex 8-9) fixes n ≥ 3; the Lea… [2 notes] |
| 150 | `CV:def:silent` | `CV.silent_definition` | CV.Events | reviews/cv-def-silent.json | faithful | std | non-blocking (documentation only): the module header (input lines 8, 19-21) and the Row 150 section comment (1061-1071, 'Also the forced Re… [5 notes] |
| 151 | `CV:lem:silence` | `CV.silence` | CV.Silence | reviews/cv-lem-silence.json | faithful | std+H+LM+LMU | Formally only: the Lean lemma is stated for n ≥ 3 (`hn : 3 ≤ n`, statement 493/505, plus `[NeZero n]`), because the accepted `CV.X1` is def… [8 notes] |
| 152 | `CV:lem:rounding` | `CV.rounding` | CV.Rounding | reviews/cv-lem-rounding.json | faithful | std | labels FR-CV1, FR-CV2, FR-CV3, FR-CV4, FR-CV5, FR-CV7, FR-R1, FR-R3, FR-R4; [W1] `Diagrammatic L` adds the no-triple / 'exactly two preimages' clause to the printed hypothesis list d3:35-38 (narrower domain; disclos… [14 notes] |
| 153 | `CV:lem:uniformrot` | `CV.uniformrot` | CV.UniformRot | reviews/cv-uniformrot.json | faithful | std | non-blocking: neg_three (stmt 284-285) concludes `rot L hL = -1` where the source (excerpt 7-8, d3:269-270) says "equality in absolute valu… [7 notes] |
| 154 | `CV:lem:curl` | `CV.curl` | CV.Curl | reviews/cv-lem-curl.json | faithful | std+LM | labels FR-C1, FR-C2, FR-C3, FR-C5, FR-C6; NON-BLOCKING: "disc" = IsDisc (any convex compact body with nonempty interior) rather than a round disc; the existential Δ is therefore dra… [18 notes] |
| 156 | `CV:lem:pieceintrinsic` | `CV.pieceintrinsic` | CV.PieceIntrinsic | reviews/cv-lem-pieceintrinsic.json | faithful | std+H+LM+LMU | labels F4; `same_link` (S:1007-1009): HOMFLY-PT equality instead of "present the same oriented link" — the recorded F4 replacement of CV:ax:gausscode… [15 notes] |
| 157 | `CV:lem:homflyrows` | `CV.homflyrows` | CV.HomflyRows | reviews/cv-lem-homflyrows.json | faithful | std+H+LM+LMU | labels D2, D9; Non-blocking: connected_sum reads the printed 'K # J' as EVERY clean marked join of EVERY pair of marked representatives (IsCleanMarkedJoin… [7 notes] |
| 158 | `CV:cor:groupedknot` | `CV.groupedknot` | CV.GroupedKnot | reviews/cv-cor-groupedknot.json | faithful | std+H+LM+LMU | labels D9, F4; 'retaining exactly the labels of W' / 'exactly the crossings of H₁ ∪ ⋯ ∪ H_k' is certified by a bare cardinality bijection Nonempty (Γ.Cros… [18 notes] |
| 159 | `CV:lem:fulltwist` | `CV.fulltwist` | CV.FullTwist | reviews/cv-fulltwist.json | faithful | std+H+LM+LMU | non-blocking: `Relation.ReflTransGen RII (D_H.switch q) D_L` admits the empty chain, i.e. the case D_H.switch q = D_L literally; the printe… [5 notes] |
| m166 | `CV:ax:R` | `CV.hyp_R` | RProof.X1Rows | reviews/cv-ax-R.json | faithful | std+H | CV.hyp_R is a Prop definition (the hypothesis) in the R6 all-sides chamber-value form; hn : 3 ≤ n presupposition |
| 160 | `CV:ax:homfly` | `CV.ax_homfly` | CV.Axioms | reviews/cv-ax-homfly.json | faithful | std+H+LM+LMU | DERIVED (theorem, not axiom) from SM.lit_homfly/lp_lm/lp_lm_uniqueness; D2: links = LinkEquiv classes of polygonal diagrams |
| 163 | `CV:ax:gausscode` | `CV.gausscode_polynomial` | CV.Axioms | reviews/cv-ax-gausscode.json | faithful | std+H+LM+LMU | F4 replacement (scope change recorded AUTHOR_NOTES ~01:24Z): conclusion homfly D = homfly D′ instead of "present the same oriented link"; strictly weaker; all consumers pass through polynomial equality |
| 164 | `CV:selector_A` | `CV.selector_A` | CV.SelectorA | reviews/cv-selector-A.json | faithful | std | non-blocking: the ownership of the two visit marks of a selected crossing (which of v, twin v lies on which carrier) follows SM conv:select… [5 notes] |
| 166 | `R:localization` | `RProof.localization` | RProof.Cores | reviews/r-localization.json | faithful | std | corollary sentence 2 ("both orbits occur") omitted by executor decision (consumed by nothing) |
| 167 | `R:parity` | `RProof.parity` | RProof.Cores | reviews/r-parity.json | faithful | std | avail_wall_invariant conditional on the cross-wall support identification hs (R-LOC-2 (1)) |
| 168 | `R:exterior` | `RProof.exterior` | RProof.X1Rows2 | reviews/r-exterior.json | faithful | std+H+LM+LMU | exterior factor represented by the base row; printed full-availability binder kept |
| 169 | `R:fibre_partition` | `RProof.fibre_partition` | RProof.Cores | reviews/r-fibre-partition.json | faithful | std | X₁-free form of the partition identity for every support (the complete def:X1 summand identity lives in the X₁ rows) |
| 170 | `R:availability_0_1` | `RProof.availability_zero_one` | RProof.X1Rows2 | reviews/r-availability.json | faithful | std+H+LM+LMU | summand_transport stronger than the bare fibre identity; cross-wall fields presuppose hs |
| 171 | `R:generic_table` | `RProof.generic_table` | RProof.Cores | reviews/r-generic-table.json | faithful | std | words/tables asserted on the canonical branch s_a = s_b = s_c (relabelled instances by F2(A)) |
| 172 | `R:generic_selector` | `RProof.generic_selector` | RProof.X1Rows | reviews/r-generic-selector.json | faithful | std+H | fixed labels a = x_ef, b = x_eg, c = x_fg with the canonical branch + relabelled instances; sides named by local graphs; ownership convention kernel-checked (mixed_carrier was FALSE in design B) |
| 173 | `R:generic_transport` | `RProof.generic_transport` | RProof.GenericTransport | reviews/r-generic-transport.json | faithful | std+H+LM+LMU | G11 RIII-wall invariance proved by an explicit polygonal RIII move; hs crossing-set identification a universally quantified hypothesis of cross-wall fields |
| 179 | `Bridge:B1` | `Bridge.B1` | Bridge.B1 | reviews/bridge-b1.json | faithful | std | non-blocking: `[NeZero n]` (statement line 47) is carried as an instance argument in addition to `hn : 3 ≤ n`; it is implied by hn and only… [5 notes] |
| 180 | `Bridge:B2` | `Bridge.B2` | Bridge.B1 | reviews/bridge-b2.json | faithful | std | stated under sorted naming rep e < rep f < rep k; unsorted case via exists_sorted_tripleAt |
| 181 | `Bridge:B3` | `Bridge.B3` | Bridge.B3 | reviews/bridge-b3.json | faithful | std | non-blocking: `SignChanges` (both SM and CV renderings) carries an extra `δ ≤ radius` clause absent from the printed 'there is δ>0 with φ(P… [6 notes] |
| 182 | `Bridge:B4` | `Bridge.B4` | Bridge.B4 | reviews/bridge-b4.json | faithful | std+H+LM+LMU | the C = X₁ dictionary through the accepted geo*_eq_generic lemmas (CV-DOM option (C)) |
| m192 | `lem:weak-open` | `SM.weak_open` | SM.WeakOpen | reviews/lem-weak-open.json | faithful | std | extra supporting lemma outside the 132 (scope_note in the map) |
<!-- END:ACCEPTED -->

## 3. Pending rows — one line each with the reason  (table regenerated 18:06Z; 24 rows)

<!-- BEGIN:PENDING -->
| # | row | policy / fixed name | status | reason at draft time |
|---|---|---|---|---|
| 57 | `lem:gauss-two-discs` | — | pending | DEFERRED — PL Jordan–Schoenflies on S²; judged INFEASIBLE now (12-20k lines, no Mathlib Jordan/Euler/triangulations): work/drafts/pldiscs/PLDISCS_FEASIBILITY.md §2.4; only non-GAP-2 consumer (row 104) proved without it (D-ER1). AUTHOR_NOTES 2026-09-13 ~20:55Z, 2026-09-14 ~04:38Z, ~12:45Z |
| 91 | `cp:finite-contact-path` | — | pending | GAP-2 — proved modulo one named clause (see §3.1 paragraph); library module SM/ContactPathOfDescent.lean, never mapped (D-F11) |
| m97 | `src:contact` | `SM.src_contact` | pending | NEVER DECLARED — literature interface consumed only by fd:contact (94) and CV:ax:etnyre (161), both GAP-2-blocked (blueprint/DEPENDENCIES.json edges); no consumer can cite it, so it was not stated (5th of the five admitted interfaces; policy name SM.src_contact) |
| 94 | `fd:contact` | — | pending | GAP-2 via row 91 (and the undeclared src:contact interface) |
| 99 | `cf:thm-carrierfloor` | — | pending | GAP-2 — clauses (R)(A)(B) statable/provable, clause (C) blocked via fd:contact (94) (GAP-2 memo §3(c); D-F12: partial clauses not pursued) |
| 100 | `thm:floor` | — | pending | GAP-2 — z_parity provable, a_floor blocked via cf:thm-carrierfloor (C) |
| 103 | `cb:singleton` | — | pending | GAP-2 via thm:floor |
| 105 | `lem:corner-values` | — | pending | GAP-2 via cb:singleton (clause (ii)); clause (i) also cites deferred row 57 |
| 110 | `thm:C-S7` | `SM.thm_C_S7` | pending | GAP-2 via cb:singleton / thm:floor — target row, fixed name SM.thm_C_S7 not declared (D-F11) |
| 112 | `thm:C-soft` | `SM.thm_C_soft` | pending | GAP-2 via lem:corner-values — target row, fixed name SM.thm_C_soft not declared (D-F11) |
| 122 | `prop:anchor-values` | — | pending | GAP-2 via thm:C-soft |
| 127 | `thm:comparison` | `SM.thm_comparison` | pending | GAP-2 via lem:corner-values / thm:C-S7 / thm:C-soft — fixed name SM.thm_comparison not declared; also consumes hyp:R (explicit parameter) |
| 128 | `cor:C-inherits` | `SM.cor_C_inherits` | pending | GAP-2 via thm:comparison — fixed name SM.cor_C_inherits not declared |
| 155 | `CV:thm:carrierfloor` | — | pending | GAP-2 — (R)(A)(B)(C) through the polygon bridge, (D) provable now; blocked via CV:ax:slbound → fd:contact (memo §3(c)) |
| 161 | `CV:ax:etnyre` | — | pending | GAP-2 — D-F10 option (iii): no independent sl object; kept as the parametrised bundle CV.SlBoundData with 162; a sixth axiom rejected by policy |
| 162 | `CV:ax:slbound` | — | pending | GAP-2 — statable on TransverseKnot, blocked via fd:contact (memo §3(b)) |
| 165 | `CV:singleton_D_i` | — | pending | GAP-2 via CV:thm:carrierfloor and cb:singleton |
| 174 | `R:generic_selected` | `RProof.generic_selected` | pending | GAP-2 — needs CV:thm:carrierfloor (R lane statement panel, AUTHOR_NOTES ~06:35Z); statable |
| 175 | `R:extreme_pair_zero` | `RProof.extreme_pair_zero` | pending | BLOCKED via CV:singleton_D_i (GAP-2); statable |
| 176 | `R:extreme_transport` | `RProof.extreme_transport` | pending | GAP-2 — needs CV:thm:carrierfloor; statable |
| 177 | `R:extreme_selected` | `RProof.extreme_selected` | pending | GAP-2 — needs CV:thm:carrierfloor; statable |
| 178 | `R:cv_theorem` | `RProof.cv_R` | pending | BLOCKED — RProof.cv_R : CV.hyp_R needs rows 174-177; not declared (statement fixed in work/drafts/rlane2/Statements_FINAL.lean) |
| 183 | `Bridge:theorem` | `Bridge.sm_R` | pending | BLOCKED — Bridge.sm_R waits only for RProof.cv_R (AUTHOR_NOTES 07:33Z); not declared |
| 184 | `SM:corner_laws_and_soft` | `SM.corner_laws_and_soft` | pending | BLOCKED — final theorem needs Bridge:theorem, cor:C-inherits, thm:C-soft; not declared (D-F11); reported INCOMPLETE |
<!-- END:PENDING -->

**The 24 pending rows, by reason** (checked against `python3 tools/claims.py --pending-only` = 23 pending claims, and
the map = 24 non-accepted rows; the stage log names the same 24):
- **22 claim rows blocked by GAP-2** — row 91 `cp:finite-contact-path`, proved modulo `SM.AmbientIsotopyDescent`
  (library module `work/lean/SM/ContactPathOfDescent.lean`; statement independently reviewed clean,
  `work/reviews/cp-finite-contact-path-conditional.json`, 3/3 lenses faithful, 2 refuters clean; label: **proved modulo
  Reidemeister's theorem for smooth isotopies (literature premise + isotopy extension)**; not mapped, §3.1) and its
  downstream rows 94, 99, 100, 103, 105, 110, 112, 122, 127, 128, 155, 161, 162, 165, 174, 175 (via `CV:singleton_D_i`),
  176, 177, 178, 183, 184.
- **1 deferred claim row** — 57 `lem:gauss-two-discs`, judged INFEASIBLE now (`work/drafts/pldiscs/PLDISCS_FEASIBILITY.md`);
  its only non-GAP-2 consumer 104 `cb:embedded-rotation` was proved without it and is accepted (§3.2).
- **1 interface row** — `src:contact` (`SM.src_contact`), never declared: no reachable consumer (§3.5).

### 3.1 GAP-2 (rows 91 → 94 → 99 → 100 → 103 → 105 → 110/112 → 122/127/128 → 184; 155/161/162/165; 174-178 → 183 → 184)

Decision record: AUTHOR_NOTES.md "Front block: representation adopted … scope gaps — 2026-09-14 ~02:38Z"
(FR-7, D-F3), "GAP-2 statement memo received; reclassification of rows 89/90 and decisions — ~07:51Z"
(D-F10, D-F11, D-F12), "Row 91 … PROVED MODULO the descent clause … — ~10:26Z" (D-CP-1, FR-CP-1..10),
"Row 91 conditional theorem reviewed and PORTED as library … — ~10:52Z"; memo
`work/drafts/gap2/GAP2_STATEMENTS_MEMO.md` (§1 the gap precisely, §3 decisions, §4 row sheets);
plan `work/drafts/gap2/CPRow91_PLAN.md` (§6 paragraph, §7 closing routes). The paragraph of §6, with its
label adjusted to the sharpened reading of the later entry (~10:52Z) and the port location updated:

> Row 91 cp:finite-contact-path: statement fixed as `SM.ContactPathData` (work/lean/SM/ContactPathOfDescent.lean,
> ported from work/drafts/gap2/CPRow91_Statements.lean; one field per printed clause of sm-3:3210-3233, on the
> accepted vocabulary of rows 89/90). The row is **proved modulo Reidemeister's theorem for smooth isotopies
> (literature premise + isotopy extension)**: `SM.cp_finite_contact_path_of_descent : SM.AmbientIsotopyDescent →
> SM.ContactPathData` (0 sorry; axioms = the standard three + the registered `lit_homfly`, `lp_lm`,
> `lp_lm_uniqueness`), from the accepted rows 89 (`ce_rounding`), 90 (`ce_smoothing_record`), rp:record-polynomial
> and lp:core. `AmbientIsotopyDescent` is a `def … : Prop`, not an axiom: for a jointly smooth family of oriented
> spatial embeddings whose two ends have ordinary regular generic xz projections, the HOMFLY–PT values of any
> polygonal readings of the two end diagrams agree. It is lit:homfly's fifth clause ("Its value depends only on the
> oriented link presented by D") read on spatial isotopies — the single sentence of the printed proof
> (sm-3:3313-3316) that the frozen interface cannot discharge: `SM.lit_homfly` states that clause as
> `HomflyClauses.descent` over `LinkEquiv` (planar isotopy and the three Reidemeister moves between polygonal
> diagrams; design D2), and passing from a smooth spatial isotopy to such a move sequence is Reidemeister's theorem,
> declared outside the formal scope with no sixth axiom admitted. Because the clause is stated on the smooth family
> of embeddings, it also absorbs the isotopy-extension step the printed proof performs by hand (sm-3:3264-3313;
> FR-CP-7 as sharpened by the statement review, work/reviews/cp-finite-contact-path-conditional.json: 3/3 lenses
> faithful, 2 refuters clean). The clause is a true theorem of mathematics (Reidemeister + isotopy extension), so the
> conditional row asserts nothing false; the gap is a scope exclusion, not a conjecture. Three
> equivalent-by-implication forms are recorded: `AmbientIsotopyDescent` (what the proof consumes),
> `AmbientIsotopyLinkEquiv` (Reidemeister's theorem proper; implies the first through the frozen descent), and
> `AmbientIsotopyDescentLit ∧ IsotopyExtension` (the printed proof's own split into the literature premise on an
> actual ambient isotopy and the isotopy-extension analysis of sm-3:3264-3313, the latter provable in principle,
> ~3-5k lines). The declaration is library material (D-F11/D-F14) and is not mapped as implemented; consequently
> rows 94, 99(C), 100(a_floor), 103, 105, thm:C-S7, thm:C-soft, thm:comparison, cor:C-inherits and
> SM:corner_laws_and_soft remain open with this single reason.

Per the memo (D-F12 reporting rule) the following are NOT to be lumped with the unprovable rows: 89 and 90 are
accepted; 99 clauses (R)(A)(B), 100 `z_parity` and 155 clause (D) are provable now but were not pursued because no
claim closes without (C)/`a_floor` (partial clauses of a row are not the row). CV:ax:etnyre (161): D-F10 option
(iii) — no independent `sl` object; the printed shape is kept as the parametrised bundle `CV.SlBoundData`; a
definitional `sl := writhe` was rejected as a substitution and a sixth axiom by the policy. Statement-only bundles
of the blocked rows (`work/drafts/gap2/Gap2Statements.lean`, 31 structures, compiles) are never mapped (D-F11).

### 3.2 Row 57 `lem:gauss-two-discs` — deferred

`work/drafts/pldiscs/PLDISCS_FEASIBILITY.md` §2.4 verdict: **INFEASIBLE now** (12 000-20 000 lines: the two-region
clause 4-6k, the PL-disc clause = PL Schoenflies 5-8k with new PL vocabulary, extension clauses cheap only on
convex model discs; Mathlib has no Jordan curve theorem, planar Euler count or triangulations); recommendation keep
DEFERRED, no lane. Its only non-GAP-2 consumer, row 104 `cb:embedded-rotation`, was proved independently by a
polygonal secant-lift argument (decision D-ER1, AUTHOR_NOTES ~12:45Z; accepted ~13:40Z); its other consumer
`lem:corner-values` (i) is GAP-2-blocked anyway. The blueprint edge 57 → 104 (`blueprint/DEPENDENCIES.json`) is
therefore not realised by the proof route; `tools/claims.py` uses that column only for `--next`.

### 3.3 Rows 76-80, 83, 93 — all ACCEPTED (in progress at draft time)

Certificate rows lane (design `work/drafts/frontrows/PLAN_FINAL.md`, statements frozen in `Statements_FINAL.lean`,
FR-8..FR-17, D-F7..D-F9): all eight certificate rows 76-83 and their consumer 93 are accepted; the front block (rows
73-94 minus the GAP-2 rows 91 and 94) is complete. The lane was ported incrementally as sorry-free modules (D-FR1),
each importing the previous one: `SM/FrontRowsW2.lean` (rows 81 `ng:circle`, 82 `ng:cusp-skein`; accepted 13:10Z),
`SM/FrontRowsW2S.lean` (the sweep block + `represent` + row 76 `SM.ng_commutation`), `SM/FrontRowsW3.lean` (leaves
`typeIII_site`, `typeI_move`, `crossedCusp_move`; rows 77 `SM.ng_front_I`, 79 `SM.ng_front_III`, 80 `SM.ng_deletions`),
`SM/FrontRowsW3b.lean` (leaf `typeII_move`, `certificate_laws`, `word_bound`; rows 78 `SM.ng_front_II`, 83
`SM.ng_local_front_bound`) and `SM/NgBound.lean` (row 93 `SM.fd_ng_bound := fd_ng_bound_of ng_local_front_bound`, recipe B of
`NGBOUND_PLAN.md`). Size: 14 666 + 8 601 + 13 267 + 3 367 = 39 901 lines for the four FrontRows modules (`wc -l`, 18:10Z),
plus 108 for `SM/NgBound.lean` (D-F9 predicted 17-23k for the lane; see §7 on the notes' "≈ 26.8k" figure). Axioms:
rows 76-80 std + `SM.lp_lm`; rows 83 and 93 std + `SM.lp_lm` + `SM.ng_finite_word` (the one declared use of the fourth
interface, as the `\status` lines predicted); the leaves `represent`, `typeI/II/III`, `crossedCusp_move` standard only.
Readings disclosed before the rows were stated and cited by the reviewers: FR-8 (the rows hold for PL realizations
`SM.realize` of closed oriented Rutherford words, not arbitrary fronts of ng:front-domain — the printed certificate
device, FR-5), FR-9/FR-10 (row 76: only jointly C^∞ families with fixed circle indexing count as deformations), FR-13,
FR-16, FR-NB-1..4 (rows 83/93: conditional on `F.IsRounding S`, no existence clause). The FR-8 fallback of D-F7 (a class
change on 76/83/93 if `represent` stalled) was NOT needed: `represent` was proved on the smooth class (15:30Z).
Record (AUTHOR_NOTES.md 2026-09-14): "Certificate rows wave 2 done … wave 3 launched — ~12:30Z"; "Sweep lane launched
(leaf `represent` → rows 76, 83) — ~13:30Z"; "Sweep lane done: `represent` PROVED, row 76 closed — ~15:30Z" (52 of 54
sweep leaves proved; the two unproved leaves were FALSE as stated, consumed by nothing, removed at port time — D-FR2);
"ng:commutation (row 76) ACCEPTED — ~16:25Z"; "Certificate rows wave 3a: U5 done, U6 wrapped with 2 of 3 leaves —
~16:55Z" (D-FR4: port the rows whose leaves are proved first); "Reassessment rule adopted; stagnation audit for row 78
(`typeII_move`) — ~17:00Z" (the bounded test: `typeII_move` proved by ~18:30Z, else rows 78/83/93 reported incomplete
with the exact remaining obligation); "Rows 77, 79, 80 ported — ~17:15Z"; "Row 78 audit outcome: `typeII_move` PROVED
within the bound — ~17:30Z" (D-FR5: the U6 version is ported, the independent U6b proof kept as cross-check);
"Rows 77, 79, 80 ACCEPTED — ~17:40Z"; "Rows 78, 83, 93 ported and mapped — ~17:50Z"; "Rows 78, 83, 93 ACCEPTED — the
certificate rows lane is complete — ~18:05Z". Reviews: 3/3 faithful and 2 refuters clean for each of the seven rows
(`work/reviews/ng-commutation.json`, `ng-front-I.json`, `ng-front-III.json`, `ng-deletions.json`, `ng-front-II.json`,
`ng-local-front-bound.json`, `fd-ng-bound.json`; reviewer inputs = the modules with every proof stripped).

### 3.4 The blocked R obligations (174-178), Bridge:theorem (183) and the final theorem (184)

See the R table in §4.4. Rows 174 `R:generic_selected`, 176 `R:extreme_transport`, 177 `R:extreme_selected` need
`CV:thm:carrierfloor` (155, GAP-2); 175 `R:extreme_pair_zero` needs `CV:singleton_D_i` (165, GAP-2 via 155 and
`cb:singleton`); 178 `RProof.cv_R : CV.hyp_R` needs 174-177; 183 `Bridge.sm_R` waits only for `RProof.cv_R`
(AUTHOR_NOTES 07:33Z checkpoint); 184 `SM.corner_laws_and_soft` needs 183, `cor:C-inherits`, `thm:C-soft`. All nine
statements are fixed and compile with exactly one `sorry` each in `work/drafts/rlane2/Statements_FINAL.lean`
(statement panel ~06:35Z, readings recorded there); the four accepted ones were ported without change. None of the
five pending names (`RProof.generic_selected`, `RProof.extreme_pair_zero`, `RProof.extreme_transport`,
`RProof.extreme_selected`, `RProof.cv_R`), nor `Bridge.sm_R`, `SM.corner_laws_and_soft`, `SM.thm_C_S7`,
`SM.thm_C_soft`, `SM.thm_comparison`, `SM.cor_C_inherits`, `SM.src_contact` is declared in `work/lean`
(audit 18:06Z; D-F11: a row theorem with an unprovable hypothesis is not the row and is never mapped). `SM.hyp_R` IS
declared and accepted (§3.5), and `Bridge/SmR.lean` proves `SM.sm_R_of_cv_R : CV.hyp_R → SM.hyp_R` from the accepted
rows as library material, so 183 reduces to `Bridge.sm_R := SM.sm_R_of_cv_R RProof.cv_R` the moment 178 exists.

### 3.5 `src:contact` and `hyp:R`

`src:contact` (policy name `SM.src_contact`, the fifth literature interface, `blueprint/AXIOM_REGISTRY.md` "src:contact —
AXIOM", sm-3:3341-3365) was never declared: `blueprint/DEPENDENCIES.json` lists it as a dependency of exactly
`fd:contact` (94) and `CV:ax:etnyre` (161), both GAP-2-blocked, and the package rule "no consumer may cite an axiom
before acceptance" gave no reason to state an interface nobody can consume. It is registry text that needs no further
source (CLAUDE.md rule 8) and could be stated and interface-reviewed at any time; §5 lists it as open. `hyp:R`
(`SM.hyp_R`, mode `explicit_parameter`) is stated and **accepted** (definition row; stated 15:15Z, accepted 15:45Z,
`work/reviews/hyp-R.json` 3/3 faithful, 2 refuters clean): a `def … : Prop` in `work/lean/SM/HypR.lean` in the all-sides
form of the accepted prop:C-silent for the identical printed phrase (reading FR-HR-1; the one-parameter form
`HypRDiagonal` and the base-point form `HypRBase` are proved equivalent to it via prop:C-chamber inside the module;
FR-HR-2 only simple triple walls `TripleAt`; FR-HR-3 `hn : 3 ≤ n` presupposition; FR-HR-8 no `axiom SM.hyp_R`). Its
consumer check `SM.sm_R_of_cv_R : CV.hyp_R → SM.hyp_R` is proved in `work/lean/Bridge/SmR.lean` (library, not mapped);
its row consumers `thm:comparison` and `Bridge:theorem` remain open (GAP-2). Its CV counterpart `CV:ax:R` is stated and
accepted as the Prop definition `CV.hyp_R` (RProof/X1Rows.lean:124). Both hypotheses of the package are therefore stated.

## 4. The checklist of FINAL_REVIEW.md, item by item

### 4.1 The definitions denote the source objects

52 definition/convention rows are accepted with a review each (§2). Evidence per object: **actual polygons** —
`def:polygon` `SM.polygonData` (LabelledTuple n = ZMod n → ℝ × ℝ; reviews/def-polygon.json + countersignature),
`def:generic`, `def:crossings`, `def:regular`, `def:admissible`. **Connected-component chambers** — `def:chamber`
`SM.chamber_definition`: `chamber X = connectedComponent X` in `GenericPolygon n = Quotient (genericCyclicSetoid n)` =
𝓤_n/(ℤ/n) with the coinduced (quotient) topology, expanded to Mathlib primitives in reviews/prop-C-chamber.json and
its refuter; used unchanged by `prop:chambers`, `prop:A-chamber`, `prop:C-chamber`. **Continuous wall germs** —
`def:germ` `SM.wall_germ_definition` (SM.GermDefinition), `def:walls`, and the germ-based hypotheses of `thm:C-S3`
(`WallGerm.FlatAt`), `thm:C-S5`, `prop:C-silent`. **Independent supports, carriers** — `def:decomposition`,
`conv:selected-visits`, `lem:carriers`, `def:flat-carriers`/`cor:flat-carriers` (SM/FlatCarriers.lean), `CV:def:smoothing`,
`CV:def:wind`, `CV:def:pieces`, `CV:lem:carriers` on the accepted geometric carrier layer (CV-DOM decision option (C),
AUTHOR_NOTES ~02:20Z, `work/drafts/cvdom/DECISION_FINAL.md`; disclosed: carriers are finite marked cycles, CV:lem:carrierword's
binder narrowing). **Local polynomials and records** — design decision `work/reports/design-decision-diagram-record-20260913.md`
(polygonal oriented link diagrams `Shadow`/`Diagram`, combinatorial `Record`, `Laurent₂ ℤ`), rows `def:positive-lift`,
`def:gauss-record`, `lp:core`, `rp:record-polynomial`, `lc:presentations`, `lp:split-circle`, `mp:*`, `def:adeg`,
`cf:def-turning`. **The full state sum** — `def:C` `SM.corner_state_sum_definition` / `cornerStateSum hn hP : ℤ`
(SM/CornerStateSum.lean, bundle field `state_sum` reproduces sm-3:1697-1698; reviews/def-C.json). No empty domain is
substituted: the reviewers checked non-vacuity where a bundle quantifies over a constructed class (CE-R11 witness in
`SM/CeRoundingNonVacuity.lean`; K-3/K-4 for row 90 argued, not kernel-checked — §5). No definition asserts a desired
theorem: every C law is a theorem about `cornerStateSum`, not a field of a definition (TARGETS.md).

### 4.2 Quantifiers, hypotheses and conclusions preserved; helper definitions expanded

Process (ACCEPT_CYCLE.md steps 4-6 as run here): the reviewers received only the SM15 source excerpt, the row's Lean
text with every proof replaced by `sorry` (`work/reviews/<row>-reviewer-input-statement.lean.txt`, produced by
`work/port/strip_proofs.py` for large modules) and the definition modules; each review compares domain, quantifiers,
hypotheses and conclusion clause by clause with helper definitions expanded to primitives and records
`stronger_than_source` / `weaker_than_source` / `discrepancies`; two adversarial refuters attack the statement. The
statement hash binds the type and every local definition it uses (DELIVERY_AUDIT.md defect 2), so a later helper change
invalidates the review — all 168 hashes match the current audit. Disclosed deviations, all judged non-blocking and
all recorded before the rows were stated: polygonal readings of smooth diagrams (FR-1, FR-CP-1, CE-R1; rows 73, 74, 89-92,
97, 98); the word/PL layer as the printed certificate device (FR-5, FR-8; rows 76-83, and 93 through 83);
ℝ-indexed jointly smooth families with the smoothTransition clamp instead of [0,1] (CE-R2, FR-CP-4/5; rows 89, 86-88);
record-level carrying at the curl (FR-C1; row 98); the collar field (D-1; rows 89-91); the rounding record theorem
`isRounding_of_geomModel` supplying row 74's printed content (D-F6, `SM/FrontGeomModel.lean`); CV binders `hn : 3 ≤ n` /
`[NeZero n]` as presuppositions; CV:lem:carrierword's binder narrowing (round-2 unanimous). 106 of 168 reviews list
strengthenings — printed content made explicit or exports beyond print (constant speed, windows, correspondences) — none
narrowing a conclusion. Weakenings of substance: none accepted; the F4 replacement of `CV:ax:gausscode` (polynomial equality
for link equivalence) is a recorded scope change, judged explicitly by its reviewers (§4.3).

### 4.3 Literature declarations exactly printed; no extra axiom, sorryAx or native_decide

Four of the five permitted interfaces are declared, each as a single `axiom` in ∃-form over a field-named Prop structure
of the printed clauses: `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness` (`work/lean/SM/LinkInterfaces.lean`) and
`SM.ng_finite_word` (`SM/FrontInterfaces.lean`). Interface reviews against the registry text (`blueprint/AXIOM_REGISTRY.md`
= the sm-3 lines; excerpts `work/reviews/*-registry-excerpt.md.txt`; input `work/reviews/interfaces-reviewer-input-statement.lean.txt`):
`reviews/lit-homfly.json`, `lp-lm.json`, `lp-lm-uniqueness.json` (3+2+2 lenses faithful, 2+1+1 refuters clean; AUTHOR_NOTES
2026-09-13 ~20:55Z), `reviews/ng-finite-word.json` (3/3, 2 clean; ~04:56Z). "Allowed name but stronger type": each clause
was matched to a printed sentence; the one formally stronger hypothesis (`lp:lm-uniqueness` competitor `unknot` on every
crossing-free polygon) makes the axiom weaker, not stronger; the descent clause of `lit_homfly` is over `LinkEquiv`
(design D2) — weaker than the printed "depends only on the oriented link", which is precisely why GAP-2 exists (§3.1).
`SM.src_contact` is not declared (§3.5). **Kernel evidence:** `work/checks/stage-development.json` (= `dev-check-frontrowsw3b-accepted.json`, 18:06Z)
passed=True with 168 mapped and 36 079 audited declarations; the audit's axiom sets over the 168 mapped declarations
are exactly {propext, Classical.choice, Quot.sound} (114 rows) plus subsets of {`SM.lit_homfly` (28 rows), `SM.lp_lm`
(42), `SM.lp_lm_uniqueness` (19), `SM.ng_finite_word` (3: the interface itself, rows 83 and 93)}; no `sorryAx`, no
`Lean.ofReduceBool` (native_decide), no other constant (recounted 18:10Z from
`work/delivery/receipts/declaration-audit.summary.json`). `work/lean` contains no `sorry` (rule 3; drafts live in `work/drafts/`). The CV "axioms" are theorems:
`CV.ax_homfly` derived from the three SM interfaces, `CV.gausscode_polynomial` = F4 replacement (scope change recorded
AUTHOR_NOTES ~01:24Z items (a)-(d); reviewers judged the replacement strictly weaker and sufficient for every in-scope
consumer, `reviews/cv-ax-gausscode.json`), as OPEN_WORK.md requires; `CV:ax:R` is a Prop definition, not an axiom.

### 4.4 The R parameter  (table regenerated 18:06Z)

<!-- BEGIN:RTABLE -->
| obligation | policy name | status | declared? | module | axioms | note |
|---|---|---|---|---|---|---|
| `R:localization` | `RProof.localization` | accepted | yes | RProof.Cores | std | accepted |
| `R:parity` | `RProof.parity` | accepted | yes | RProof.Cores | std | accepted |
| `R:exterior` | `RProof.exterior` | accepted | yes | RProof.X1Rows2 | std+H+LM+LMU | accepted |
| `R:fibre_partition` | `RProof.fibre_partition` | accepted | yes | RProof.Cores | std | accepted |
| `R:availability_0_1` | `RProof.availability_zero_one` | accepted | yes | RProof.X1Rows2 | std+H+LM+LMU | accepted |
| `R:generic_table` | `RProof.generic_table` | accepted | yes | RProof.Cores | std | accepted |
| `R:generic_selector` | `RProof.generic_selector` | accepted | yes | RProof.X1Rows | std+H | accepted |
| `R:generic_transport` | `RProof.generic_transport` | accepted | yes | RProof.GenericTransport | std+H+LM+LMU | accepted |
| `R:generic_selected` | `RProof.generic_selected` | pending | no | — | — | GAP-2 — needs CV:thm:carrierfloor (R lane statement panel, AUTHOR_NOTES ~06:35Z); statable |
| `R:extreme_pair_zero` | `RProof.extreme_pair_zero` | pending | no | — | — | BLOCKED via CV:singleton_D_i (GAP-2); statable |
| `R:extreme_transport` | `RProof.extreme_transport` | pending | no | — | — | GAP-2 — needs CV:thm:carrierfloor; statable |
| `R:extreme_selected` | `RProof.extreme_selected` | pending | no | — | — | GAP-2 — needs CV:thm:carrierfloor; statable |
| `R:cv_theorem` | `RProof.cv_R` | pending | no | — | — | BLOCKED — RProof.cv_R : CV.hyp_R needs rows 174-177; not declared (statement fixed in work/drafts/rlane2/Stat… |
| `Bridge:B1` | `Bridge.B1` | accepted | yes | Bridge.B1 | std | accepted |
| `Bridge:B2` | `Bridge.B2` | accepted | yes | Bridge.B1 | std | accepted |
| `Bridge:B3` | `Bridge.B3` | accepted | yes | Bridge.B3 | std | accepted |
| `Bridge:B4` | `Bridge.B4` | accepted | yes | Bridge.B4 | std+H+LM+LMU | accepted |
| `Bridge:theorem` | `Bridge.sm_R` | pending | no | — | — | BLOCKED — Bridge.sm_R waits only for RProof.cv_R (AUTHOR_NOTES 07:33Z); not declared |
| `SM:corner_laws_and_soft` | `SM.corner_laws_and_soft` | pending | no | — | — | BLOCKED — final theorem needs Bridge:theorem, cor:C-inherits, thm:C-soft; not declared (D-F11); reported INCO… |
| `CV:ax:R` | `CV.hyp_R` | accepted | yes | RProof.X1Rows | std+H | accepted |
| `hyp:R` | `SM.hyp_R` | accepted | yes | SM.HypR | std+H | accepted |
<!-- END:RTABLE -->

Exposure: the conditional comparison theorem (`thm:comparison`, would take `SM.hyp_R` as an explicit parameter,
axiom-policy mode `explicit_parameter`) is not declared. `SM.hyp_R` itself IS declared and accepted (row `hyp:R`,
`work/lean/SM/HypR.lean`; audit kind `definition`, axioms std+H through `cornerStateSum`; reviews/hyp-R.json): a
`def … : Prop` — for every n ≥ 3, every wall germ `g` with `g.TripleAt e f k` (a simple triple wall, def:walls (T),
FR-HR-2) and all side parameters `tp tm`, `cornerStateSum` takes the same value on the two labelled side representatives
`g.sideTuple true tp`, `g.sideTuple false tm` — reading FR-HR-1 (all-sides form, the one the accepted prop:C-silent uses
for the identical printed phrase; `HypRDiagonal` and `HypRBase` proved equivalent via prop:C-chamber); it is a
hypothesis, never an axiom (FR-HR-8). The consumer check `SM.sm_R_of_cv_R : CV.hyp_R → SM.hyp_R` is proved from the
accepted rows (B1-B4 pointwise) in `work/lean/Bridge/SmR.lean` (library, not mapped; `Bridge.sm_R` NOT declared), so
`Bridge:theorem` is `Bridge.sm_R := SM.sm_R_of_cv_R RProof.cv_R` once `R:cv_theorem` exists. In the CV lane the
hypothesis is the Prop `CV.hyp_R` (RProof/X1Rows.lean:124; accepted row `CV:ax:R`, form R6: for every simple RIII event,
`X1 (E.curve t₊) = X1 (E.curve t₋)` for all `t₊ > 0 > t₋`), consumed only as the *type* of the unproved
`RProof.cv_R`, as the conclusion of the proved auxiliary `hyp_R_of_near_of_chamberinv`, and as the hypothesis of
`SM.sm_R_of_cv_R`. Every accepted R row
exposes its parameters explicitly (`hn : 3 ≤ n`; the cross-wall crossing-set identification `hs` of R-LOC-2 (1) as a
universally quantified hypothesis of the cross-wall fields, never asserted); none takes an R, lawful-quantity or
corner-law assumption — their axiom sets are `std` (four cores) or `std+H(+LM+LMU)` through `CV.X1`/`homfly`
(table). No R-dependent result is imported: the R modules import CV events, `CV.X1`, `CV:lem:pieceintrinsic`,
`CV:prop:chamberinv`, `CV:lem:silence`, `Bridge.B4` and the SM geometry — nothing downstream of `thm:comparison`
or `cor:C-inherits`. **Incomplete:** `RProof.cv_R`, `Bridge.sm_R` and `SM.corner_laws_and_soft` are not declared,
so no "proved CV R theorem", "resulting SM R theorem" or unconditional final theorem exists to inspect (§3.4).

### 4.5 R coverage of the printed domain; both orbits; B1-B4

Partition by outside support and availability: `R:fibre_partition` (exhaustion, disjointness, sizes 0/1/3) accepted.
Availability 0 and 1: `R:availability_0_1` accepted (summand transport stronger than the bare fibre identity).
Availability 3, generic orbit: `R:generic_table`, `R:generic_selector` (172), `R:generic_transport` (173, the RIII-wall
invariance G11 proved by an explicit polygonal RIII move) accepted; `R:generic_selected` (174) pending (GAP-2).
Extreme orbit: 175-177 pending (GAP-2). Exterior factor without division: `R:exterior` accepted (base-row
representative, printed full-availability binder kept). Localization and parity warrants: `R:localization`,
`R:parity` accepted (std axioms only). So the printed simple, transversal, forced-bundle domain is **not** fully
covered: the extreme orbit and the generic selected couple are open. B1-B4 (`Bridge/B1.lean` = B1+B2, `B3.lean`,
`B4.lean`; reviews/bridge-b1.json … bridge-b4.json) compare the SM15 and CV conventions clause by clause (B2 under
sorted naming with the unsorted case recovered; B4 = the pointwise dictionary `X₁ = C` on SM-generic polygons through
the accepted `geo*_eq_generic` agreement lemmas, `SM/GeoCarrierAgreement.lean`), with no assumed equality of generic
loci: the agreement is proved on the accepted definitions (CV-DOM (C)).

### 4.6 Clause table for `SM.corner_laws_and_soft`  (the final declaration is NOT declared)

| Clause | Source rows | Status at completion (18:06Z) |
|---|---|---|
| Chamber constancy and silence | `prop:C-chamber`, `prop:C-silent` | **accepted**: `SM.prop_C_chamber` (SM/CChamber.lean; reviews/prop-C-chamber.json), `SM.prop_C_silent` (SM/CSilent.lean; reviews/prop-C-silent.json; both wall types (E) and (C) as printed) |
| Flat deletion jump | `thm:C-S3` (actual deletion `deleteVertex`, side sign) | **accepted**: `SM.thm_C_S3` (SM/CS3.lean; reviews/thm-C-S3.json; side values via def:germ + chamber constancy) |
| Vertex-edge jump | `thm:C-S7` (both bigon branches, sliding, actual children `λ₁, λ₂`, sign `s`) | **open (GAP-2)** via `cb:singleton` ← `thm:floor` ← `cf:thm-carrierfloor`(C) ← `fd:contact` ← row 91; `SM.thm_C_S7` not declared |
| Triple invariance | `hyp:R` discharged by the proved R/bridge theorem | **open**: `SM.hyp_R` stated and **accepted** (SM/HypR.lean; reviews/hyp-R.json) and `SM.sm_R_of_cv_R : CV.hyp_R → SM.hyp_R` proved (Bridge/SmR.lean, library); but `RProof.cv_R` and `Bridge.sm_R` are not declared (rows 174-178 GAP-2/blocked), so the hypothesis is not discharged |
| Full cusp jump | `cor:C-inherits`, `cor:A-lawful` (deletion satisfies G1; threaded cusps) | **open (GAP-2)** via `thm:comparison`; `cor:A-lawful` itself **accepted** as `SM.A_lawful` (SM/ALawful.lean; reviews/cor-A-lawful.json); `SM.cor_C_inherits` not declared |
| Empty-cusp zero | `thm:C-S5` | **accepted**: `SM.thm_C_S5` (SM/CS5.lean; reviews/thm-C-S5.json) |
| Soft theorem | `thm:C-soft` (every direction/attachment-sign sector incl. zero sectors, sufficiently small ε) | **open (GAP-2)** via `lem:corner-values` ← `cb:singleton`; prerequisites `def:soft`, `lem:soft-generic`, `lem:soft-rotation`, `thm:A-soft` accepted; `SM.thm_C_soft` not declared |
| Descent and normalization | cyclic, reversal, triangle statements inherited with `cor:A-lawful` | **accepted** as A-level rows: `prop:A-reversal`, `thm:mycyclic`, `thm:root-indep-proof`, `thm:uniqueness`, `cor:A-lawful`; their transfer to C is part of the open `cor:C-inherits` |

### 4.7 The conclusion concerns the source C

Every accepted C row is stated on `cornerStateSum hn hP` of the accepted `def:C` for `P : LabelledTuple n`,
`hP : Generic P`, `hn : 3 ≤ n` (reviews/prop-C-chamber.json clause 1; thm-C-S3, thm-C-S5, prop-C-silent likewise),
with wall data from `def:germ`/`def:walls` and deletions from `def:deletion-halves`/`def:induced-roots`; no row
abstracts C into "a function with the laws". Arguments at which C is evaluated are generic by construction (side
points of germs, `deleteVertex` under the printed n ≥ 4 / G1 conditions). A full-target statement over all cusps and
all soft sectors does not exist yet (§4.6).

### 4.8 Certificates; 4.9 the stage check

`EXECUTION.json` commissions no computation certificates in this focused package (`"certificates": []`); the
"certificate rows" 76-83 are source lemmas of sm-3 (Rutherford/Ng front words), now all accepted (§3.3), not external
certificates, and no `native_decide` or external data enters the library.

**Stage check.** `python3 tools/check_lean.py work/lean --all` was run at 18:06Z (log
`work/checks/stage-all-attempt-1806.log`) and **FAILED as expected**, with exactly:

> FAIL: stage is incomplete; unaccepted rows: Bridge:theorem, CV:ax:etnyre, CV:ax:slbound, CV:singleton_D_i,
> CV:thm:carrierfloor, R:cv_theorem, R:extreme_pair_zero, R:extreme_selected, R:extreme_transport, R:generic_selected,
> SM:corner_laws_and_soft, cb:singleton, cf:thm-carrierfloor, cor:C-inherits, cp:finite-contact-path, fd:contact,
> lem:corner-values, lem:gauss-two-discs, prop:anchor-values, src:contact, thm:C-S7, thm:C-soft, thm:comparison, thm:floor

`work/checks/stage-1.json` records `{"passed": false, "stage": 1, "state": "checking"}`. The 24 rows named are exactly the
24 pending rows of §3 (22 GAP-2, row 57, `src:contact`). **The single focused stage is INCOMPLETE and is reported as
such** (CLAUDE.md rule 9). What binds the accepted state is the development receipt
`work/checks/dev-check-frontrowsw3b-accepted.json` (18:06Z run: passed=true, `stage: null`, `stage_accepted: false`,
168 mapped, 36 079 audited; byte-identical to the current `work/checks/stage-development.json` and to
`work/delivery/receipts/stage-development.json`); `work/progress-watch.log` and `tools/progress.py` accordingly print
"Stage 1: not established by a current checker receipt". The root FINAL_REVIEW.md is itself in the checker's bundle
(`bundle_sha256`), so the executor re-runs the development checker after this review is appended to it and refreshes
`work/delivery/` so that the delivered receipt binds the delivered bytes; a receipt older than that edit is evidence
about its own time only.

## 5. Remaining gaps (honest list)

1. **GAP-2** — the one missing clause is `SM.AmbientIsotopyDescent` (§3.1): lit:homfly's descent clause read on smooth
   spatial isotopies, i.e. Reidemeister's theorem for smooth isotopies of polygonal readings plus isotopy extension.
   Closing it (`CPRow91_PLAN.md` §7): (α) a spatial descent field on the frozen `HomflyClauses` = type change of
   `SM.lit_homfly` — small in code, a policy change on a frozen interface, re-acceptance of every consumer; (β) prove
   `AmbientIsotopyLinkEquiv` (Reidemeister for smooth isotopies + PL bridge) — multi-thousand lines, no policy issue,
   out of horizon; (γ) `AmbientIsotopyDescentLit ∧ IsotopyExtension` — (α)'s status for the first plus ~3-5k lines of
   analysis for the second. 22 claim rows (91 and its 21 downstream rows, §3) and the unused interface row `src:contact` stay open with this
   single reason; the four target theorems, `Bridge.sm_R`, `RProof.cv_R` and `SM.corner_laws_and_soft` are among them.
2. **Row 57** `lem:gauss-two-discs` deferred as infeasible now (§3.2).
3. **`SM.src_contact` never declared** (§3.5) — statable from registry text at any time; consumers blocked.
4. ~~`SM.hyp_R` never stated~~ — **resolved 15:45Z**: stated as a Prop definition and accepted (§3.5, §4.4); its
   row consumers `thm:comparison` and `Bridge:theorem` remain blocked by GAP-2.
5. ~~Rows 76-80, 83, 93 in progress~~ — **done**: all seven accepted between 16:25Z and 18:05Z (§3.3); the certificate
   rows lane 76-83 and its consumer 93 are complete, no FR-8 fallback was used.
6. **Reviews are AI reviews only** (STATE_OF_WORK §4): 168 rows reviewed by Claude Code subagents of the same model
   family as the implementer (disclosure §6); the 39 handover rows were re-reviewed once by separate sessions
   (countersignatures 2026-09-13); the 129 rows accepted since had one 3-lens + 1-or-2-refuter workflow each and no
   second session. No human has read any review.
7. **Non-vacuity / geometric-reading items argued but not kernel-checked:** K-4 (row 90, non-vacuity of
   `CleanCuspSmoothing`), FR-2 (row 73, equivalence of the derivative-form cusp criterion with the (u², u³) normal form
   and the geometric upper/lower reading), FR-ER-2 (row 104, the bounded complementary region is not defined; the sign
   clause is read at supporting vertices), K-3 (row 90, D_ε fields quantify over `CuspRoundingFamily`).
8. **Conditional library theorems are NOT mapped** (no content effect on the accepted rows): `SM/ContactPathOfDescent.lean`
   (`SM.cp_finite_contact_path_of_descent`, row 91 modulo `AmbientIsotopyDescent`), `Bridge/SmR.lean`
   (`SM.sm_R_of_cv_R : CV.hyp_R → SM.hyp_R`, the shape of row 183 without its premise), `RProof/X1Rows3.lean`
   (`GT_generic_transport_of_G11`, row 173 modulo G11 — superseded by the accepted `RProof/GenericTransport.lean`; header
   updated 18:00Z to say so), `SM/LinkingCalculus.lean` (row 88 conditional; the accepted unconditional row is
   `SM/LinkingCalculusRow.lean`; pointer sentence fixed 18:00Z). None of these carries a row status; D-F11 forbids mapping
   a row theorem with an undischarged premise. Remaining docstring defects listed in STATUS.md item 6 (LinkLaurentRing.lean:80-81,
   LinkInterfaces.lean 55-60/180-181, FlatCarriersDefs.lean header).
9. **Blueprint edge 57 → 104** not realised by the proof route (D-ER1); blueprint stays frozen, the deviation is recorded.

## 6. Process

**Accept cycle used for every row** (ACCEPT_CYCLE.md, with the tooling of `work/port/`): pick the unit
(`tools/claims.py --next` / lane plan) → statement fixed BEFORE proving, fidelity risks recorded in AUTHOR_NOTES before
the row is stated → proof produced in `work/drafts/` (checked with `lake env lean`, never `lake build` there) → ported
verbatim into `work/lean/{SM,CV,RProof,Bridge}` with only a header added (`make_lane_modules.py`, D-FR1 for sorry-free
increments) → `lake build` → `map_row.py implement` → `python3 tools/check_lean.py work/lean` (kernel check: builds
mapped modules, rejects sorryAx and unregistered axioms, writes the statement hash) → independent AI review: three
reviewer subagents with distinct lenses + two adversarial refuters, proof withheld (briefs `work/port/review_prompt_<slug>.md`,
inputs `work/reviews/<slug>-reviewer-input-statement.lean.txt`, raw output `<slug>-review-workflow-raw.json`) →
`summarize_review.py` + `write_review_and_accept.py` (unanimity required; a split verdict sends the row to round 2 with a
neutral disclosure, e.g. CV:lem:carrierword, ng:front-domain, CV:lem:carriers, CV:lem:piececurve) → row `accepted` →
checker again (receipt `work/checks/dev-check-<slug>-accepted.json`) → `tools/progress.py --once` → AUTHOR_NOTES,
STATUS.md, TASKS.json. 79 development receipts record the growth from 41 mapped / 4 579 audited (2026-09-13 13:44Z,
`dev-check-single-triple-implemented.json`) to 168 / 36 079 (2026-09-14 18:06Z, `dev-check-frontrowsw3b-accepted.json`);
all 79 passed.

**AI-review disclosure** (text of `ai_review_disclosure` in every review written by this executor, e.g.
`work/reviews/prop-C-chamber.json`): "AI review. Four separate Claude Code subagents (model claude-fable-5-1) were
spawned by the executor on 2026-09-13 in one workflow: three reviewers with distinct lenses and one adversarial refuters
instructed to find any discrepancy. Each received only the printed SM15 source files, the row's Lean text with every
proof replaced by sorry (reviews/prop-C-chamber-reviewer-input-statement.lean.txt), and the Lean definition modules; none
saw the proof module work/lean/SM/CChamber.lean or the executor's reasoning. The executor (author) is
executor-pod-claude-fable-5-1-20260913, a different session of the same model. No human has read these reviews."
(later rows: "Five … three reviewers … two adversarial refuters … on 2026-09-14"). Identities in the map (168 accepted rows): authors
`executor-pod-claude-fable-5-1-20260913` (128 rows), `root-implementation-20260910` (39), `executor-coldstart-claude-fable-5-1-20260912`
(1); reviewers `reviewer-pod-claude-fable-5-1-20260913 (independent Claude Code workflow subagents …)` (128),
`review_chirotope-independent-20260910` (30), `review_relgp_full-independent-20260911` (9), `reviewer-coldstart-claude-fable-5-1-20260912` (1).

**Lane pattern** for the large rows: design panel (two architects + judge, or three proposers + three judges) →
`PLAN_FINAL.md` with fidelity risks → `Statements_FINAL.lean` (compiles; exactly the row theorems as `sorry`) →
`Skeleton_FINAL.lean` (leaf sorries, assembly proved) → prover units on byte-identical copies (statements never change) →
false leaves repaired without statement change and recorded (FR-C8, FR-R6, CE-R10) → assembler → statement pre-review /
numeric probes → port. **Library hygiene:** no `sorry` in `work/lean`; clash scans before every port (renamed duplicate
helpers recorded); never delete, rename or rewrite an accepted declaration (D-F6 extends the library instead); fixed
target names from `axiom-policy.json`; incremental porting of sorry-free modules only (D-FR1); a checkpoint receipt after
every accept. **Scope decisions** are in AUTHOR_NOTES with labels (§0) and were taken without any author contact
(AUTONOMOUS_EXECUTION.md); counterexamples/false leaves went to `work/repairs/` or were repaired inside the lane.

**Reassessment rule** (adopted 2026-09-14 ~17:00Z, AUTHOR_NOTES.md "Reassessment rule adopted; stagnation audit for row
78"): Mark's execution rule `/workspace/repos/lean/reassessment_rule.md` — reassess automatically after two substantive
attempts or 60 minutes of active work without a newly accepted source claim; helpers, compiles, packets and renamed
strategies do not reset stagnation; a complete kernel-proved claim whose acceptance is merely delayed is an acceptance
bottleneck, not a mathematical stall; the response is a bounded method audit with one decisive test, an effort bound and
a stated consequence on failure, never a weakened claim or a changed denominator. One bounded audit was recorded: for
row 78 `ng:front-II` (leaf `typeII_move`, variants (b) geometry, (d) and the dispatch open after unit U6's ~4 h), the
diagnosis was decomposition/effort, not mathematics (the same machinery had proved variants (a), (c) and the two sibling
leaves); the decisive test — `typeII_move` proved and compiled in the follow-up unit W3_U6b with standard axioms by
~18:30Z, else rows 78/83/93 reported INCOMPLETE with the exact remaining obligation and the proved partial kept as
library — **succeeded at 17:30Z**, before its bound (D-FR5: the U6 version was ported, U6b kept as the independent
cross-check). The same audit classified rows 77/79/80 (leaves already kernel-proved in unit copies) as an acceptance
bottleneck and answered it with the incremental delta module of 17:15Z. The accepted count was reported unchanged
(103/132) by the audit itself, as the rule requires.

## 7. Inconsistencies noticed between the tools' output and the notes (for the executor)

Resolved since the draft:
- `work/STATUS.md` header: rewritten at 18:00Z to a current-state header (17:55Z figures; the 2026-09-13 header kept
  below as history). Its sentence "The remaining 21 checklist rows are GAP-2-blocked, or row 57, or src:contact"
  undercounts: 24 rows were non-accepted at that time (22 GAP-2 + row 57 + `src:contact`) — correct it in the final
  checkpoint.
- GAP-2 row count: AUTHOR_NOTES ~12:20Z and STATUS 13:06Z said "21 rows"; the 18:05Z entry says "22 claim rows
  GAP-2-blocked (+ src:contact, unused), row 57 deferred", which matches the pending list and the stage log
  (24 = 22 + 1 + 1). Reconciled.
- `hyp:R`: stated (15:15Z) and accepted (15:45Z) as a Prop definition; the draft's open question is closed.
- `RProof/X1Rows3.lean`: header now records that it is superseded as the row module by `RProof/GenericTransport.lean`
  (comment-only edit 18:00Z; statement hashes unchanged).

Still to note:
- **Lane size:** AUTHOR_NOTES ~17:50Z gives the per-module figures FrontRowsW2 14 665, W2S 8 600, W3 13 266, W3b 3 366 and
  sums them to "≈ 26.8k lines"; the figures sum to 39 897 (`wc -l` at 18:10Z: 14 666 + 8 601 + 13 267 + 3 367 = 39 901,
  plus `SM/NgBound.lean` 108). This review uses ≈ 39.9k (§3.3); D-F9's prediction of 17-23k was exceeded by more than
  the note states. The closing brief given to the documentation agent repeated the 26.8k figure.
- **`work/delivery/refresh.sh` line 92** copies `work/FINAL_REVIEW.md` — a file that does not exist — into the package;
  the delivered `work/delivery/FINAL_REVIEW.md` is a copy of the ROOT `FINAL_REVIEW.md` made by hand at 18:15Z. After
  any later edit of the root file, re-copy it by hand (`cp FINAL_REVIEW.md work/delivery/FINAL_REVIEW.md`) before the
  last `refresh.sh` (which rewrites `MANIFEST.sha256` over whatever is in the directory).
- `work/delivery/tools/gen_final_review_tables.py` still carries `PENDING_REASONS` entries for the now-accepted rows
  76-80, 83, 93 and `hyp:R` ("IN PROGRESS at draft time", "NOT STATED"); they are unused (reasons are emitted for pending
  rows only) but stale.
- Rows 104 `cb:embedded-rotation` (accepted 13:40Z) and 173 `R:generic_transport` (14:45Z) were accepted before the
  draft was written and are part of its 160; the closing brief listed them among the post-draft acceptances. The counts
  here (160 → 168 by the eight rows named in §1) are the ones checked against the map.
- Numbering: claims.py "#" (184 units) ≠ map index (192 rows); e.g. `cp:finite-contact-path` is 91 in claims.py and 95 in
  the map. The notes use claims.py numbers throughout; §2-§3 do too (`m<index>` for the 8 rows outside claims.py).
- STATE_OF_WORK.md/CLAUDE.md speak of 39/40 handover rows and 328 modules; the library now has 665 modules (628 SM, 28 CV,
  5 RProof, 4 Bridge; ~248k lines, `wc -l` 18:10Z). Historical, but the delivery README carries current figures.
- FINAL_REVIEW.md's sentence about "both independent computation certificates" applies to the full handoff; the focused
  `EXECUTION.json` has `"certificates": []`.
- `ng:finite-word`'s audited axiom set is `propext, SM.ng_finite_word` (no Classical.choice/Quot.sound) — consistent with a
  plain structure statement, noted so nobody reads it as an anomaly.
