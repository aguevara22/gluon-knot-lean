# U7c — REPORT (CV:def:piecediagram 142, CV:lem:piececurve 143, CV:def:X1 146, on the accepted geo layer)

Written 2026-09-14 (≈04:30 UTC / 12:30am ET) by the U7c prover subagent (claude-fable-5-1) of the pod executor,
for the CV-DOM decision work/drafts/cvdom/DECISION_FINAL.md (§0 option (C), §2 fidelity + readings (ii)/(iii),
§3 rulings R1–R6, §4 review-note template, §5 unit U7c, §6 order of rows step 4). Paths relative to the package
root /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912. Nothing under
work/lean was written; both drafts were checked with `cd work/lean && lake env lean` only (details in §0).

## 0. Deliverables and status

| item | rows 142 + 143 | row 146 |
|---|---|---|
| file | `work/drafts/cvdom/U7c/CVPieceCurve.lean` — **683 lines** (≈85 module docstring); intended home `work/lean/CV/PieceCurve.lean` | `work/drafts/cvdom/U7c/CVX1.lean` — **261 lines** (≈58 module docstring); intended home `work/lean/CV/X1.lean` |
| imports | `CV.CarrierWord` (row 137: `carrierword_inherits_order`, `carrierword_traced`, `carrierGaussList_eq_filter`; through it `CV.CarriersLemma` (row 136: `pieceOwner`, `exists_unique_piece_carrier`, `owner_eq_of_mem_U`, `owner_eq_of_interlaces_mem_U`, `mem_piecesOn_iff`, `pieceOwner_pieceOf`), `CV.Carriers` (rows 135/138/139: `Piece`, `pieceOf`, `pieceLabels`, `pieceWrithe`, `piecesOn`, `wind`), `CV.CarrierBridges` (U0), `SM.GeoCarrierCrossings`/`Noncrossing`/`Order`/`Count`); `CV.RecordHomfly` (accepted def:record/def:homfly: `SingleCircle`, `singleCircle_record`; through it `CV.Axioms` (`AxHomflyData`, `ax_homfly`) and `SM.LinkInterfaces` (`homfly`, `homfly_circle`, `homfly_skein`)); `SM.GeoPositiveLift` (U4: `geoCarrierShadow(_generic)`, `geoPositiveLift(_isPositive/_sign/_writhe)`, `eq_geoPositiveLift_of_isPositive`, `geoCarrierCrossingEquiv`; through it U2b `geoCornerPolygon_regular`, U2c `geo_self_intersections`) | `CV.PieceCurve` (this unit), `CV.Rotation` (accepted CV:def:rot: `rot`, `rotAbs`, `rotAbs_cast`; `regular_iff_sm` from `CV.Setup`) |
| check | `cd work/lean && lake env lean ../drafts/cvdom/U7c/CVPieceCurve.lean` → **exit 0, no output** (≈6 s) | `CV.PieceCurve` is not yet a module under work/lean, so the draft was checked against an `.olean` of the first file built OUTSIDE work/lean: `cp CVPieceCurve.lean /tmp/u7c_root/CV/PieceCurve.lean; cd work/lean; lake env bash -c 'lean --root=/tmp/u7c_root /tmp/u7c_root/CV/PieceCurve.lean -o /tmp/u7c_olean/CV/PieceCurve.olean -i /tmp/u7c_olean/CV/PieceCurve.ilean'`, with the existing `work/lean/.lake/build/lib/lean/CV/*.olean` symlinked into `/tmp/u7c_olean/CV/` (Lean resolves a whole package prefix from one search-path root), then `lake env bash -c 'LEAN_PATH="/tmp/u7c_olean:$LEAN_PATH" lean ../drafts/cvdom/U7c/CVX1.lean'` → **exit 0, no output** (≈6 s). Once `CV/PieceCurve.lean` is ported, the plain `lake env lean ../drafts/cvdom/U7c/CVX1.lean` is the check. |
| sorries | **none** (`grep -c sorry` = 0) | **none** (`grep -c sorry` = 0) |
| bundles | `structure CV.PieceCurveData (hn) (hD : Diagrammatic P) (S) (hS : S ∈ Ind hD.crossingGeometry) (H : Piece _ S) : Prop` — 10 fields; `structure CV.PieceDiagramData (hn) (hD) (S) (hS) (H) : Prop` — 7 fields | `structure CV.X1DefinitionData (hn) (hG : Generic P) : Prop` — 10 fields |
| row theorems PROVED | `CV.piececurve hn hD S hS H : PieceCurveData hn hD S hS H` (PROVE row); `CV.piecediagram_definition hn hD S hS H : PieceDiagramData hn hD S hS H` (DEFINE row) | `CV.X1_definition hn hG : X1DefinitionData hn hG` (DEFINE row) |
| axioms | `CV.piececurve`, `CV.exists_pieceSupport`, `CV.pieceDiagram`, `CV.pieceCarrier_gaussWord`, `CV.exists_unique_piece_owner_of_subset`: `[propext, Classical.choice, Quot.sound]`; `CV.piecediagram_definition`, `CV.pieceHomfly`: `+ SM.lit_homfly` (through `homfly`) | `CV.X1`, `CV.Omega1`: standard `+ SM.lit_homfly`; `CV.carrierR`, `CV.groupedWrithe_eq_card_geoCarrierCrossings`, `CV.biUnion_pieceLabels_piecesOn`: standard; `CV.X1_definition`: standard `+ SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (through the field `homfly_exists := ax_homfly`, the accepted CV:ax:homfly) |
| binders | `hD : CV.Diagrammatic P`, `hS : S ∈ CV.Ind hD.crossingGeometry`, `H : CV.Piece hD.crossingGeometry S` (d1:565 "For a diagrammatic parent `P`", d1:592–593 "Let `P` be diagrammatic, `S ∈ Ind(G_P)`, and let `H` be a residual piece of `S`"); `hn : 3 ≤ n` as in §5's shapes `CV.piececurve (hn) …`, `CV.piecediagram_definition (hn) …` (reading (iii); §4 item 2) | `hG : CV.Generic P` (d1:909 "Let `P` be generic"); `S ∈ Ind(G_P)` and the carrier `L` quantified inside the per-carrier fields as the text binds them; `hn : 3 ≤ n` as in §5 ("`CV.X1` as in the prototype", `X1 (hn) (P) (hG)`) and R6 (`X1 hn (E.curve tp) …`) |
| tier | support `K_H`, carrier `q_H`, Gauss word: tier 0 (`hD.crossingGeometry`); the geometric clauses (regular corner polygon, generic shadow, self-intersections, positive lift): tier 1 (`CarrierGeometry.ofDiagrammatic hD`, ruling R4). **No tier-2 (`WeakGeneric`) fact anywhere**: rows 142/143 stay on the printed `Diagrammatic` binder (risk 3 of §7 did not materialise) | tier 1 through `CarrierGeometry.ofCV hG` for `geoCornerPolygon_regular` (the (G1) guard is not used) |
| accepted declarations modified / `geo*` names re-declared | none (ruling R3; the one helper whose name began with `geo` was renamed `pieceCarrier_geoCarrierCrossings`). All **66** new declaration names grepped against every declaration head under work/lean (excluding `.lake`): **0 collisions** | same scan, same result |
| `hn` hygiene | absent from every *definition* of row 143 (`pieceSupport`, `pieceCarrier`, `pieceCurve`) and from the combinatorial lemmas (§1–§5 of the file); on the geometric lemmas (§6, via `include hn in` where the statement does not mention it) and on `pieceDiagram`/`pieceHomfly` (the positive lift needs `3 ≤ geoCornerCount`, U2b's `three_le_geoCornerCount hn`) | on `groupedPoly`, `carrierR`, `slot`, `Omega1`, `X1` (through `pieceHomfly hn` and `geoCornerPolygon_regular hn`); absent from `groupedWrithe` and the `w_{S,L}` lemmas |

R6 shape confirmed: `noncomputable example (hn : 3 ≤ n) (E : Event n) (tp : E.Parameter) (hp : 0 < tp.val) : ℤ :=
X1 hn (E.curve tp) (E.generic_punctured tp hp.ne')` typechecks (`#check @CV.X1 : {n : ℕ} → [NeZero n] → 3 ≤ n →
(P : LabelledTuple n) → CV.Generic P → ℤ`). lean-declarations.json: `CV:def:piecediagram`, `CV:lem:piececurve`,
`CV:def:X1` are `pending` with empty `declaration`; the names used are the ones the unit brief fixes.

## 1. Row 143 — CV:lem:piececurve (d1_setup.tex:592–611; proof 612–690)

### 1.1 The construction on the geo layer (Gap G4)

The statement binds `C_H` to "the closed plane curve that the proof's own route constructs, and nothing else":
(1) smooth `S` only → the `|S|+1` carriers of `S`; (2) take the carrier of `H` (lem:carriers (iv)); (3) Step 5's
iteration: while the current carrier of `H` has a double point `d ∉ H`, smooth `d` and keep the daughter carrying `H`.

* **Invariant** `CV.StepInvariant hP S H K : Prop` (structure, three fields): `subset_U : K ⊆ U hP S`,
  `disjoint : Disjoint K (pieceLabels hP S H)`, `indep : S ∪ K ∈ Ind hP` — the set `K` of double points smoothed
  so far beyond `S`. `StepInvariant.empty hS` is the start.
* **Step 4** (`mem_pieceLabels_of_interlaces`, d1:633–636 "an undominated crossing interlacing a member of `H` lies
  in `H`"): adjacency in `residualGraph hP S` puts both ends in one connected component
  (`SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj`). Hence `pieceLabels_subset_U_union`: under the
  invariant every label of `H` is undominated at `S ∪ K` (neither in `S` nor in `K`; interlaces nothing in `S`;
  interlaces nothing in `K`, which would pull that element of `K` into `H`).
* **Step 5, "well defined"** (`exists_unique_piece_owner_of_subset`, d1:640–650 and 606–608): for any `T ∈ Ind(G_P)`
  with `pieceLabels H ⊆ U(T)` there is exactly one carrier of `T` owning all visits of all labels of `H`. Proof: the
  connectivity induction of lem:carriers (iv) (CV/CarriersLemma.lean §3, gap G3) run at `T` along walks of `G_P[U(S)]`
  (`owner_eq_of_walk_of_subset`): every vertex of a walk starting in `H` is in `H` (hence in `U(T)`), each edge is an
  interlacing of two crossings of `U(T)`, and lem:carriers (ii)+(iii) at `T` (`owner_eq_of_interlaces_mem_U hP hT`)
  identify the owners along it. With `T = S ∪ K`: `StepInvariant.exists_unique_owner`.
* **One step** (`StepInvariant.insert`, d1:640–650 "If `C` has a double point `d` outside `K`, smooth it … The
  hypotheses persist"): a crossing `d` of the carrier `q` of `S ∪ K` with `d ∉ H` is unselected and interlaces no
  selected crossing (U2a `geoCarrierCrossings_subset_U`), so `S ∪ insert d K` is independent
  (U2a `geoIndependent_insert_unselected`), `d ∈ U(S)` (`U_subset_of_subset`) and `d ∉ H`.
* **Measure and termination** (`card_compl_insert_lt`, `exists_pieceSupport_aux`, d1:652–655): strong induction
  (`Nat.strong_induction_on`) on the number of unselected crossings `|[m] ∖ (S ∪ K)|`, which drops by one at every
  step. This is a coarser measure than the printed "double points outside `K`", but it bounds it and needs no choice
  of carrier in its definition. The recursion stops when `geoCarrierCrossings (S ∪ K) q ⊆ pieceLabels H`; equality
  then holds because every label of `H` is an unselected crossing both of whose visits lie on `q`.
* **Existence** (`exists_pieceSupport hP hS H`, tier 0), exactly §5 U7c's existential for row 143:
  `∃ (K) (_ : S ∪ K ∈ Ind hP) (q : GeoComponent hP (S ∪ K)), Disjoint K (pieceLabels hP S H) ∧ K ⊆ U hP S ∧
  geoCarrierCrossings hP (S ∪ K) q = pieceLabels hP S H ∧ (∀ c ∈ pieceLabels hP S H, ∀ v, v.1 = c →
  geoOwner hP (S ∪ K) (Sum.inr v) = q) ∧ GeoInheritsMarkOrder hP (S ∪ K)`.

Relation to §5's three invariants: (a) `S ∪ K` independent = `StepInvariant.indep`; (b) "`H` owned by one carrier"
is *derived* at every stage from `subset_U` + `disjoint` (Step 4 + the connectivity induction); (c) "retained
crossings ⊆ labels on the carrier" holds automatically and is not needed for termination.

### 1.2 Definitions (§5: "`CV.pieceSupport`, `CV.pieceCarrier` (Classical.choose), `CV.pieceCurve := geoCornerPolygon _ (S ∪ K_H) q_H`")

All on `(hD : Diagrammatic P) {S} (hS : S ∈ Ind hD.crossingGeometry) (H : Piece hD.crossingGeometry S)`; write
`hP := hD.crossingGeometry`, `K := pieceSupport hD hS H`, `q := pieceCarrier hD hS H`.

| name | type | what |
|---|---|---|
| `pieceSupport hD hS H` | `Finset (Crossing P)` | `K_H`, `Classical.choose (exists_pieceSupport hP hS H)` |
| `pieceSupport_spec`, `pieceSupport_mem_Ind : S ∪ K ∈ Ind hP`, `pieceSupport_geoIndependent : GeoIndependent hP (S ∪ K)` | | (`Exists.fst` of the spec; ruling R2 form) |
| `pieceCarrier hD hS H` | `GeoComponent hP (S ∪ K)` | `q_H`, `Classical.choose` of the second existential |
| `pieceCarrier_spec`, `pieceSupport_disjoint : Disjoint K (pieceLabels hP S H)`, `pieceSupport_subset_U : K ⊆ U hP S`, `pieceSupport_stepInvariant : StepInvariant hP S H K` | | |
| `pieceCarrier_geoCarrierCrossings : geoCarrierCrossings hP (S ∪ K) q = pieceLabels hP S H` | | "double points exactly `H`", combinatorial form |
| `pieceCarrier_owns : ∀ c ∈ pieceLabels hP S H, ∀ v, v.1 = c → geoOwner hP (S ∪ K) (Sum.inr v) = q` | | `q_H` carries `H` |
| `pieceCarrier_unique q' (hq') : q' = q` | | `q_H` is THE carrier of `H` at `S ∪ K_H` |
| `pieceSupport_inheritsMarkOrder : GeoInheritsMarkOrder hP (S ∪ K)`, `pieceCarrier_traced : TracedSuccessor hP (S ∪ K) q` | | lem:carrierword at `S ∪ K_H` |
| `pieceCarrier_gaussWord : (carrierGaussList hP (S ∪ K) q).filter (·.1 ∈ pieceLabels hP S H) = (geometricGaussList hP).filter (·.1 ∈ pieceLabels hP S H)` | | **the Gauss word of `C_H` is the parent word restricted to `H`** (row 137's `carrierGaussList_eq_filter`, `List.filter_filter`, `List.filter_congr`, `pieceCarrier_owns`) |
| `pieceCurve hD hS H` | `LabelledTuple (geoCornerCount hP (S ∪ K) q)` | **`C_H`** `:= geoCornerPolygon hP (S ∪ K) q` |
| `pieceCurve_regular hn : SM.Regular (pieceCurve …)`, `pieceCurve_cvRegular hn : CV.Regular (pieceCurve …)` | | U2b `geoCornerPolygon_regular` (tier 1), `regular_iff_sm` |
| `pieceShadow hn hD hS H` (abbrev) | `Shadow` | `geoCarrierShadow hn (ofDiagrammatic hD) (pieceSupport_geoIndependent …) q` |
| `pieceShadow_generic hn : (pieceShadow …).Generic` | | U4 `geoCarrierShadow_generic` (tier 1) |
| `pieceCurve_selfIntersections hn x : GeoIsSelfIntersection hP (S ∪ K) q x ↔ ∃ c ∈ pieceLabels hP S H, x = crossingPoint c` | | **"double points exactly the crossings of `H`", geometric form** — U2c `geo_self_intersections` clause 1 |
| `pieceShadowCrossingEquiv hn : (pieceShadow …).Crossing ≃ {c // c ∈ pieceLabels hP S H}` | | U4 `geoCarrierCrossingEquiv` ∘ `Equiv.subtypeEquivRight` |

On the choice: the printed proof's step "If `C` has a double point `d` outside `K`, smooth it" is itself a free
choice, so the text's `C_H` is determined only up to it; `Classical.choose` from `exists_pieceSupport` fixes one
admissible terminal `K_H` (§5's prescription). `pieceSupport_stepInvariant` + `pieceCarrier_geoCarrierCrossings`
show it is a fixed point of the iteration (the invariant holds and no step applies). Every admissible terminal `K`
gives a curve with double points exactly `H` and word the restriction — the datum of def:piecediagram.

### 1.3 Clause → field map (`PieceCurveData hn hD S hS H`, CVPieceCurve.lean:490–543) and proof sources

| printed sentence (d1_setup.tex) | field | rendering | proved from |
|---|---|---|---|
| 594–596 "smooth every crossing of `S` — of `S` *only* — so that the curve falls into the `|S|+1` carriers of `S`" | `carriers_of_S` | `Fintype.card (GeoComponent hP S) = S.card + 1` | row 136 `(carriers hD S hS).count` |
| 596–597 "take the one carrier that carries `H`, which is unique by Lemma lem:carriers (iv)"; 606–607 "so `H` lies on one carrier before the iteration begins" | `initial_carrier` | `∃! q₀ : GeoComponent hP S, ∀ c ∈ pieceLabels H, ∀ v, v.1 = c → geoOwner hP S (inr v) = q₀` | row 136 (iv) `exists_unique_piece_carrier` |
| 597–598 "and apply to it Step 5's iteration, smoothing at each step one double point outside `H`" | `step` | `∀ K, StepInvariant K → ∀ q, ∀ d ∈ geoCarrierCrossings hP (S ∪ K) q, d ∉ pieceLabels H → StepInvariant (insert d K)` | `StepInvariant.insert` (U2a `geoCarrierCrossings_subset_U`, `geoIndependent_insert_unselected`; `U_subset_of_subset`) |
| 598–599 "and keeping the daughter curve that carries `H`, which Step 5 shows is well defined"; 607–608 "and each subsequent step preserves that" | `step_well_defined` | `∀ K, StepInvariant K → ∃! q : GeoComponent hP (S ∪ K), ∀ c ∈ pieceLabels H, ∀ v, v.1 = c → geoOwner hP (S ∪ K) (inr v) = q` | `StepInvariant.exists_unique_owner` ← `exists_unique_piece_owner_of_subset` |
| 599–600 "Then `C_H` …" (the binding of `C_H` to the iteration's result; proof 654–656 "after finitely many steps the curve `C_H` has double points exactly `K`") | `terminal` | `StepInvariant K_H ∧ (q_H carries H)` | `pieceSupport_stepInvariant`, `pieceCarrier_owns` |
| 599–600 "Then `C_H` is a closed plane curve" | `closed_plane_curve` | `SM.Regular (pieceCurve) ∧ (pieceShadow hn).Generic` | `pieceCurve_regular hn` (U2b), `pieceShadow_generic hn` (U4) |
| 600 "whose double points are exactly the crossings of `H`" | `double_points` | `geoCarrierCrossings hP (S ∪ K_H) q_H = pieceLabels H ∧ ∀ x, GeoIsSelfIntersection hP (S ∪ K_H) q_H x ↔ ∃ c ∈ pieceLabels H, x = crossingPoint c` | `pieceCarrier_geoCarrierCrossings`, `pieceCurve_selfIntersections hn` (U2c) |
| 600–602 "and whose Gauss word is the parent word restricted to `H` in the parent's cyclic order" | `gauss_word` | `GeoInheritsMarkOrder hP (S ∪ K_H) ∧ TracedSuccessor hP (S ∪ K_H) q_H ∧ (carrierGaussList … q_H).filter (∈ H) = (geometricGaussList hP).filter (∈ H)` | row 137 (`pieceSupport_inheritsMarkOrder`, `pieceCarrier_traced`), `pieceCarrier_gaussWord` |
| 609–611 "In particular that restricted word is realizable, and the datum of Definition def:piecediagram is the datum of `C_H`" | `realizable` | `Nonempty ((pieceShadow hn).Crossing ≃ {c // c ∈ pieceLabels H})` — the restricted word is read off an actual closed curve whose double points are `H` | `pieceShadowCrossingEquiv hn` (U4) |

Sentences 603–606 ("This binding is the construction and not a description of its result. The route above smooths
nothing but `S`") are realised by the definitions (`pieceCurve` is defined from the iteration's terminal state;
`K_H ⊆ U(S)` disjoint from `H` in `terminal`), not rendered as further fields. Steps 1–3 of the proof (d1:613–632)
are the lane's `geo_neighbor_visit_owners_ne`, `mem_geoCarrierCrossings_iff_U`/`geoCarrierCrossings_subset_U`,
`carrierGaussList_eq_filter`, used inside the proofs; the counter-example `d a a d b b` (d1:668) is kept as a comment
in the module docstring.

## 2. Row 142 — CV:def:piecediagram (d1_setup.tex:565–591)

### 2.1 Definitions (reading (ii))

| name | type | what |
|---|---|---|
| `pieceDiagram hn hD hS H` | `Diagram` | `geoPositiveLift hn (CarrierGeometry.ofDiagrammatic hD) (pieceSupport_geoIndependent hD hS H) (pieceCarrier hD hS H)` — the positive lift of `C_H` |
| `pieceHomfly hn hD hS H` | `R` | **`P_H(a,z)`** `:= homfly (pieceDiagram hn hD hS H)` |
| `pieceDiagram_Γ` (simp, `rfl`), `pieceDiagram_componentCount` (`= 1`, `rfl`), `pieceDiagram_comp i` (`(Γ.comp i).P = pieceCurve`, `rfl`) | | |
| `pieceDiagram_isPositive x`, `pieceDiagram_sign x : … = 1` | | U4 |
| `pieceDiagram_writhe : writhe = ((pieceLabels hP S H).card : ℤ)`, `pieceDiagram_writhe_eq_pieceWrithe` | | U4 `geoPositiveLift_writhe` + `pieceCarrier_geoCarrierCrossings` |
| `pieceDiagramCrossingEquiv : (pieceDiagram …).Γ.Crossing ≃ {c // c ∈ pieceLabels hP S H}` | | |
| `eq_pieceDiagram_of_isPositive D (hΓ : D.Γ = pieceShadow …) (hpos : ∀ x, D.IsPositive x) : D = pieceDiagram …` | | U4 `eq_geoPositiveLift_of_isPositive` |
| `pieceDiagram_singleCircle_record : SingleCircle (pieceDiagram …).record` | | accepted `singleCircle_record` |

`hG := CarrierGeometry.ofDiagrammatic hD` (U0) and `hD.crossingGeometry` are identified by proof irrelevance, so
`pieceCarrier hD hS H : GeoComponent hD.crossingGeometry (S ∪ K)` is accepted by `geoPositiveLift hn hG …` directly.

### 2.2 Clause → field map (`PieceDiagramData hn hD S hS H`, CVPieceCurve.lean:628–670) and proof sources

| printed sentence (d1_setup.tex) | field | rendering | proved from |
|---|---|---|---|
| 565–568 "the diagram of a residual piece `H` is the parent curve `P` with every double point outside `H` erased — the two strands drawn as passing without interaction —" (reading (ii)) | `erased` | `(pieceDiagram).Γ = pieceShadow ∧ componentCount = 1 ∧ (∀ i, (Γ.comp i).P = pieceCurve) ∧ Nonempty (Γ.Crossing ≃ {c // c ∈ pieceLabels H})` — the diagram's curve is `C_H`, one closed curve whose double points are exactly `H` | `rfl`, `rfl`, `rfl`, `pieceDiagramCrossingEquiv` |
| 568–570 "and every double point of `H` resolved by the divide convention: the branch whose direction `u_over` satisfies `det(u_over, u_under) > 0` passes over" | `divide_convention` | `∀ x, (pieceDiagram).IsPositive x` (`IsPositive x := 0 < det (dir (overStrand x)) (dir (underStrand x))`, LinkDiagram.lean:547 — the same formula) | U4 `geoPositiveLift_isPositive` |
| 570–571 "Under this convention every crossing of the diagram is positive," | `positive` | `∀ x, (pieceDiagram).sign x = 1` | U4 `geoPositiveLift_sign` |
| 571–572 "so its writhe is `w(H) = |H|`, the number of double points of `H`." | `writhe` | `(pieceDiagram).writhe = pieceWrithe hP S H ∧ pieceWrithe hP S H = |pieceLabels H|` | `pieceDiagram_writhe_eq_pieceWrithe`, `rfl` |
| 572–574 "We write `P_H(a,z)` for the HOMFLY–PT polynomial of the link so presented, normalized as in Definition def:homfly." | `piece_polynomial` | `pieceHomfly = homfly (pieceDiagram) ∧ (∀ D, D.IsCrossingFreeCircle → homfly D = 1) ∧ (∀ Dp Dm D0, IsSkeinTriple Dp Dm D0 → R.a * homfly Dp - R.aInv * homfly Dm = R.z * homfly D0)` — the two normalising identities of def:homfly ("`P_H` is normalized by the first two identities", d1:553) | `rfl`, `homfly_circle`, `homfly_skein` (SM/LinkInterfaces, from `lit_homfly`) |
| 576–586 "*What 'erased' means* … the datum is a word *together with a rotation system*, not a bare word, and the definition above is to be read as naming that pair. To erase a double point is to omit it from that datum." (reading (ii)) | `datum` | the datum is that of the actual closed curve `C_H`: its word is the parent word restricted to `H` in the parent's cyclic order (row 143's Gauss-word clause), and its rotation system is the plane geometry of `C_H` itself — the diagram is the unique diagram on the shadow of `C_H` all of whose crossings are positive | `pieceCarrier_gaussWord`, `eq_pieceDiagram_of_isPositive` |
| 587–589 "The combinatorial shadow of the datum — the word with its over/under and signs and nothing else — is Definition def:record." | `record_shadow` | `SingleCircle (pieceDiagram).record` — the record (`Diagram.record`, CV:def:record) of the piece diagram, a single circle | `pieceDiagram_singleCircle_record` |

The shipped-code citation (d1:580–583, `sub_word_and_rot`) is not a mathematical clause and is not rendered.

## 3. Row 146 — CV:def:X1 (d1_setup.tex:908–930)

### 3.1 Definitions (`hn : 3 ≤ n`, `hG : Generic P`, `{S}`, `hS : S ∈ Ind hG.crossingGeometry`; `hP := hG.crossingGeometry`)

| name | type | what |
|---|---|---|
| `groupedPoly hn hG hS q` | `R` | `P_{S,L} := ∏ H ∈ piecesOn hP S q, pieceHomfly hn (hG.diagrammatic hn) hS H` (row 142 read at `hD := hG.diagrammatic hn`, the accepted `CV.Generic.diagrammatic`; `hS`, `H`, `q` transport by proof irrelevance) |
| `groupedWrithe hG q` | `ℤ` | `w_{S,L} := ∑ H ∈ piecesOn hP S q, pieceWrithe hP S H` |
| `carrierPolygon_cvRegular hn hG hS q : CV.Regular (geoCornerPolygon hP S q)` | | U2b `geoCornerPolygon_regular hn (CarrierGeometry.ofCV hG) …` + `regular_iff_sm` |
| `carrierR hn hG hS q` | `ℕ` | `R(L) := rotAbs (geoCornerPolygon hP S q) (carrierPolygon_cvRegular …)` — CV:def:rot's `R(L) = |rot(L)|` (accepted `CV.rotAbs`) of the carrier's corner polygon; `carrierR_cast : (carrierR : ℤ) = |rot …|` |
| `slot hn hG hS q` | `ℤ` | `1 - groupedWrithe hG q - (carrierR hn hG hS q : ℤ)` |
| `Omega1 hn hG hS q` | `ℤ` | `Ω₁(S,L) := coeffAt (slot …) 0 (groupedPoly …)` (accepted `coeffAt d k f := f.coeff (d, k)`, "zero if that monomial is absent") |
| `X1 hn P hG` | `ℤ` | `∑ S ∈ (Ind hP).attach, wind hP S.1 * ∏ q : GeoComponent hP S.1, Omega1 hn hG S.2 q` |

The sum runs over the **attached** index set `(Ind hP).attach` so that each summand receives the membership proof
`S ∈ Ind(G_P)` under which `P_{S,L}` and `R(L)` are defined — the shape of the accepted SM def:C (`SM.cornerStateSum`,
SM/CornerStateSum.lean:166–170, "The sum runs over the attached index set so that each summand receives the
membership proof") and of `cornerStateSum_eq_sum_independentSupports` (:174), which U6/B4 will compare it with.
No junk values anywhere (the prototype's `hS`-free definitions were only possible because `pieceSupport` was sorried).

Companions: `groupedPoly_of_piecesOn_eq_empty`, `groupedWrithe_of_piecesOn_eq_empty`;
`biUnion_pieceLabels_piecesOn hP hS q : (piecesOn hP S q).biUnion (pieceLabels hP S) = geoCarrierCrossings hP S q`
(lem:carriers (iv) + lem:piececurve Step 2: the labels of the pieces on `q` are exactly the crossings of `q`);
`piecesOn_pairwiseDisjoint`; **`groupedWrithe_eq_card_geoCarrierCrossings hG hS q : groupedWrithe hG q =
((geoCarrierCrossings hP S q).card : ℤ)`** (§5 U7c's "also `CV.groupedWrithe_eq_card_geoCarrierCrossings`") and
`groupedWrithe_eq_geoCarrierCrossingCount` (U2a's count).

### 3.2 Clause → field map (`X1DefinitionData hn hG`, CVX1.lean:197–244) and proof sources

| printed clause (d1_setup.tex:908–930) | field | rendering | proved from |
|---|---|---|---|
| "For a carrier `L` of `S` set `P_{S,L} = ∏_{H carried by L} P_H`" | `grouped_poly` | `∀ S hS q, groupedPoly hn hG hS q = ∏ H ∈ piecesOn hP S q, pieceHomfly hn (hG.diagrammatic hn) hS H` | `rfl` |
| "`w_{S,L} = Σ_{H carried by L} w(H)`" | `grouped_writhe` | `∀ S q, groupedWrithe hG q = ∑ H ∈ piecesOn hP S q, pieceWrithe hP S H` | `rfl` |
| "the products and sums taken over the residual pieces assigned to `L` by Lemma lem:carriers (iv)" | `assigned_by_carriers_iv` | `∀ S hS q H, H ∈ piecesOn hP S q ↔ pieceOwner hP hS H = q` | row 136 `mem_piecesOn_iff` |
| "with the empty product `P_{S,L} = 1` and the empty sum `w_{S,L} = 0` when no piece is carried by `L`" | `empty_conventions` | `∀ S hS q, piecesOn hP S q = ∅ → groupedPoly … = 1 ∧ groupedWrithe … = 0` | `simp` |
| "Here `P_H` is the HOMFLY–PT polynomial of the link that the piece `H` presents, in the normalization of Definition def:homfly" | `piece_polynomial` | `∀ S hS H, pieceHomfly hn (hG.diagrammatic hn) hS H = homfly (pieceDiagram hn (hG.diagrammatic hn) hS H)` (row 142; `homfly` is def:homfly's polynomial, accepted row 141) | `rfl` |
| "that such a polynomial exists at all is Axiom ax:homfly, and this definition is where it is first read" | `homfly_exists` | `AxHomflyData` (the accepted CV:ax:homfly bundle) | `ax_homfly` (this is where `lp_lm`, `lp_lm_uniqueness` enter `X1_definition`'s axioms) |
| "The *slot* of `L` is the integer `1 − w_{S,L} − R(L)`" | `slot_def` | `∀ S hS q, slot … = 1 - groupedWrithe hG q - (carrierR … : ℤ) ∧ (carrierR … : ℤ) = |rot (geoCornerPolygon hP S q) _|` (`R(L) = |rot(L)|`, CV:def:rot) | `rfl`, `carrierR_cast` (`rotAbs_cast`) |
| "the *factor* is `Ω₁(S,L) = [a^{1−w_{S,L}−R(L)} z^{0}] P_{S,L}(a,z)` — the coefficient itself, taken as a value, with no sign gate and no zero-gate applied" | `factor` | `∀ S hS q, Omega1 … = coeffAt (1 - groupedWrithe hG q - (carrierR … : ℤ)) 0 (groupedPoly …)` | `rfl` |
| "and `X₁(P) = Σ_{S ∈ Ind(G_P)} wind(S) ∏_L Ω₁(S,L)`" | `state_sum` | `X1 hn P hG = ∑ S ∈ (Ind hP).attach, wind hP S.1 * ∏ q : GeoComponent hP S.1, Omega1 hn hG S.2 q` (`Ind` of CV:def:interlace, `wind` of CV:def:wind) | `rfl` |
| "the inner product running over the `|S|+1` carriers of `S`" | `carriers_count` | `∀ S ∈ Ind hP, Fintype.card (GeoComponent hP S) = S.card + 1` | row 136 `(carriers (hG.diagrammatic hn) S hS).count` |

def:wind's last sentence ("`wind(S) ≠ 0` forces every carrier to be uniform"), which the prototype carried as a
field `wind_ne_zero`, belongs to row 138 (`WindDefinitionData`, U7a) and is not repeated.

## 4. Readings the reviewer should confirm (none is a scope change)

1. **Reading (ii)** (DECISION_FINAL §2, verbatim): "(ii) def:piecediagram's 'parent curve with every double point
   outside `H` erased' is the datum (restricted word + rotation system, d1:580–590) realised by the piece curve
   `C_H` of lem:piececurve, so `CV.pieceDiagram H` is the positive lift (divide convention = `Diagram.IsPositive`)
   of the carrier of `S ∪ K_H` that carries `H`". Rendered as `pieceDiagram := geoPositiveLift … (pieceCarrier …)`;
   the `erased`/`datum` fields say what "erased" means on this layer.
2. **Reading (iii)** (verbatim): "(iii) `hn : 3 ≤ n` is carried where the geo lemmas need it (CV fixes `n ≥ 3`
   globally, d1:932)". `hn` is a parameter of the three bundles as §5's shapes prescribe; it is NOT on any
   definition of row 143 (`pieceSupport`, `pieceCarrier`, `pieceCurve`), only on the geometric lemmas
   (`include hn in`) and on `pieceDiagram`/`pieceHomfly`/`carrierR`/`X1`. `CV.Diagrammatic` does not itself yield
   `3 ≤ n` as a library lemma (`CV.Regular.three_le` exists, `Diagrammatic.three_le` does not), so `hn` cannot be
   dropped from `pieceDiagram` without new work.
3. **"closed plane curve"** = the corner polygon `pieceCurve` (regular, U2b) with generic one-component shadow (U4);
   **"double points"** = `GeoIsSelfIntersection` points of the carrier (U2c) = crossing points of its
   `geoCarrierCrossings` = the shadow's `Crossing` type (U4). All three forms are in the bundle.
4. **"Gauss word … in the parent's cyclic order"** = the double-point subword of `carrierGaussList` (row 137's
   reading: the visits of the carrier in the order it traverses them, `TracedSuccessor`) equals `geometricGaussList`
   restricted to the visits of `H`. Selected visits on `q_H` (smoothing sites: corners, not double points) are
   filtered out on both sides, as the sentence is about double points.
5. **"the one carrier that carries `H`"** and the daughter "that carries `H`" are rendered as owning ALL visits of
   ALL labels of `H` (row 136 (iv)'s reading), uniquely.
6. **The measure** of the recursion is the number of unselected crossings, not the number of double points outside
   `H`; the printed measure is bounded by it and the termination statement is the same.
7. **`R(L)`** is CV:def:rot's `rotAbs` on the corner polygon (accepted row 144); its identification with
   `geoCarrierRotationInt`/SM's `carrierRotationInt` is U6's agreement, not this row's business.
8. **`Σ_{S ∈ Ind(G_P)}` over `attach`** — the accepted SM def:C shape, a rendering artefact of the dependent
   summand, not a change of the index set.
9. The **ownership convention** at a selected crossing (SM conv:selected-visits) enters only through which visits lie
   on `q_H`; the rows' clauses read owners of unselected visits (labels of `H`) except through `carrierGaussList`,
   where the selected visits are filtered out.

## 5. The three bundles

Pasted verbatim from the compiled files: `PieceCurveData`/`piececurve` = CVPieceCurve.lean:490–566,
`PieceDiagramData`/`piecediagram_definition` = CVPieceCurve.lean:628–681, `X1`/`X1DefinitionData`/`X1_definition`
= CVX1.lean:184–259 (see the files; the executor's final message carries the same text).

## 6. `#print axioms` (copies of the files with the lines appended; /tmp/u7c_pc_axioms.lean, /tmp/u7c_x1_axioms.lean)

```
'CV.piececurve' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.piecediagram_definition' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly]
'CV.exists_pieceSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.pieceDiagram' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.pieceHomfly' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly]
'CV.pieceCarrier_gaussWord' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.exists_unique_piece_owner_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.X1_definition' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]
'CV.X1' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly]
'CV.Omega1' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly]
'CV.carrierR' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.groupedWrithe_eq_card_geoCarrierCrossings' depends on axioms: [propext, Classical.choice, Quot.sound]
'CV.biUnion_pieceLabels_piecesOn' depends on axioms: [propext, Classical.choice, Quot.sound]
```
`lit_homfly` enters through `homfly` (P_H); `lp_lm`/`lp_lm_uniqueness` enter `X1_definition` only through the field
`homfly_exists := ax_homfly`. If the reviewer prefers row 146 free of the lp axioms, that one field can be weakened to
the two normalising identities as in row 142's `piece_polynomial` (then `lit_homfly` only).

## 7. Remaining sorries

**None** in either file. Nothing is left unproved; no obstacle arose; no tier-2 need arose for rows 142/143
(risk 3 of DECISION_FINAL §7 is discharged for the whole positive-lift chain: U4 + this unit).

## 8. Method and time

1. Read DECISION_FINAL §0/§2/§3/§4/§5/§6/§7 in full, d1_setup.tex 480–720 and 895–945, the cv-lane plan §142/§143/§146
   and G4, the prototype, the U4/U7b/U7b2 reports, and the interfaces of every module consumed (§0 imports).
2. Designed G4 as the invariant + strong induction (§1.1); wrote CVPieceCurve.lean in one pass. Compile round 1: three
   `include hn in` placements; round 2: one `include` had to precede the docstring; round 3: exit 0. CVX1.lean:
   round 1: one `include hS in`; round 2: exit 0.
3. Checks: `#print axioms` (13 declarations), sorry grep (0/0), name-collision grep of all 66 new heads (0), R6-shape
   `#check`, lean-declarations.json row status.
4. ≈ 2 h including reading, design, writing, compile loops, checks and this report.

## 9. Notes for the assembler and downstream units

* **Porting order.** `CV/PieceCurve.lean` (imports `CV.CarrierWord`, `CV.RecordHomfly`, `SM.GeoPositiveLift`)
  before `CV/X1.lean` (imports `CV.PieceCurve`, `CV.Rotation`). Both are picked up by the lakefile glob `CV.+`.
  The probe files under /tmp are not deliverables.
* **For U6 / Bridge:B4 `pointwise`.** `pieceDiagram hn hD hS H = geoPositiveLift hn (ofDiagrammatic hD) hK q_H`
  definitionally, so on SM-generic `P` U4's `geoPositiveLift_eq_generic` turns `pieceHomfly` into
  `homfly (positiveLift hn hP (S ∪ K_H) (e q_H) hdec)` by `congrArg`; `pieceCarrier_geoCarrierCrossings` +
  `geoCarrierCrossings_eq_generic` give the label sets; `groupedWrithe_eq_card_geoCarrierCrossings` is the
  `w_{S,L} = carrierCrossingCount` half of §5 U6's `CV.groupedWrithe_eq_carrierCrossingCount`; `carrierR` is `rotAbs`
  of `geoCornerPolygon`, to be compared with `carrierRotationInt` through `geoCornerPolygon_apply_eq_generic`/`polyOfList`
  (U4 §6) or `recastTuple` (CChamber) and CV:lem:rot-ident. `X1` is a sum over `(Ind hP).attach`,
  `cornerStateSum_eq_sum_independentSupports` over `(independentSupports hn hP).attach`; `Ind_eq_generic`
  (CV/Events.lean:204) connects the index sets. `Ω₁ = cornerCoefficient` still waits for cb:products (row 102).
* **For U5a (chamberinv (ii)).** `X1` depends on `P` only through `Ind hP`, `wind`, `piecesOn`, `pieceOwner`,
  `pieceSupport`/`pieceCarrier` (chosen from an existential whose statement is record-level), `geoCornerPolygon`
  (for `rotAbs`) and `homfly` of the positive lift. Under a `GeoMarkTransport` the existential transports, so
  `pieceSupport` can be transported by re-choosing on the other side and `pieceCarrier_unique`; the lifts are then
  related through `eq_pieceDiagram_of_isPositive`.
* **Companions available now:** `exists_pieceSupport` (tier 0), the `StepInvariant` API,
  `exists_unique_piece_owner_of_subset` ("`H` stays on one carrier under any admissible refinement", useful for
  R:exterior / R:fibre_partition), `pieceCarrier_gaussWord`, `pieceCurve_selfIntersections`,
  `pieceShadowCrossingEquiv`, `eq_pieceDiagram_of_isPositive`, `biUnion_pieceLabels_piecesOn`,
  `groupedWrithe_eq_card_geoCarrierCrossings`.
