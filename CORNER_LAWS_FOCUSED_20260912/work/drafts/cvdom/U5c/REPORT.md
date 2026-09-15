# CV-DOM unit U5c — REPORT (2026-09-14, ~06:45 UTC / 2:45am ET)

Prover: Claude Code subagent (claude-fable-5-1) of the pod executor. Task: close the one open lemma of
CV/ChamberInvII.lean (`PieceHomflyTransported`, U5a report §6) and state/prove row 147 CV:prop:chamberinv
(reference/R/CV/d1_setup.tex:932–939), both clauses. Nothing under work/lean was written. Paths relative to
the package root /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912.

## 1. Deliverables

| file | intended home | lines | decls | check | axioms |
|---|---|---:|---:|---|---|
| `work/drafts/cvdom/U5c/PieceHomflyTransport.lean` (**primary**) | `work/lean/CV/PieceHomflyTransport.lean`; imports `CV.ChamberInvII`, `CV.PieceIntrinsic` | 100 | 2 | `cd work/lean && lake env lean ../drafts/cvdom/U5c/PieceHomflyTransport.lean`: **exit 0, no output, no `sorry`** | standard + `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness` (both theorems) |
| `work/drafts/cvdom/U5c/CVChamberInv.lean` (**the row**) | `work/lean/CV/ChamberInvRow.lean` (name chosen not to clash with the accepted `CV/ChamberInv.lean`); imports `CV.PieceHomflyTransport` | 88 | 3 | overlay compile (§3): **exit 0, no output, no `sorry`** | `CV.chamberinv`, `CV.chamberinv_ii`: standard + `SM.lit_homfly`, `SM.lp_lm`, `SM.lp_lm_uniqueness`; `CV.ChamberInvData` (the statement): standard + `SM.lit_homfly` |
| `work/drafts/cvdom/U5c/PieceHomflyTransport_selfcontained.lean` (cross-check, optional) | not for porting unless CV/PieceIntrinsic is withdrawn; imports only `CV.ChamberInvII` | 955 | 82 | `lake env lean`: **exit 0, no output, no `sorry`** | the two final theorems as above; the whole record-isomorphism layer (`CV.PieceHomfly.*`, 80 decls) is standard-axiom only |

`grep -c sorry` = 0 on all three files (the word does not occur, docstrings included). No fully-qualified name
clash: `grep -rn` over work/lean for `CV.ChamberInvData`, `CV.chamberinv_ii`, `CV.chamberinv`,
`CV.pieceHomflyTransported`, `CV.homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq` and every
`CV.PieceHomfly.*` name returns nothing (the existing `CV.liftVisit` of CV/PieceIntrinsic.lean is a different
declaration in a different namespace from `CV.PieceHomfly.liftVisit`; the primary file does not define the latter).

## 2. Route — which one worked

The **recommended record route** (U5a report §6 item 2) worked, in two steps.

1. **Choice independence at one polygon.** `pieceSupport` is a `Classical.choose` (CV/PieceCurve.lean:327), so
   the support `K'` chosen at `Q` need not be the transport `tK` of the support `K` chosen at `P`. On a fixed
   polygon `Q` (tier 1, `hG : CarrierGeometry Q`), two carriers `q₁`, `q₂` of independent supports `T₁`, `T₂`
   with `geoCarrierCrossings T₁ q₁ = geoCarrierCrossings T₂ q₂` have positive lifts with **isomorphic records**
   (CV:def:record's clauses (a)–(d) for "the identity map on the visits of `H`"), hence the same HOMFLY
   polynomial by the accepted CV:ax:gausscode replacement `CV.gausscode_polynomial` (CV/Axioms.lean:260):
   `CV.homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`.
   * Primary file: the record isomorphism is the accepted row CV:lem:pieceintrinsic's
     `CV.exists_recordIso_of_geoCarrierCrossings_eq` (CV/PieceIntrinsic.lean:823, ported 05:57Z while this unit
     ran) — 3 lines of proof.
   * Self-contained file (written before PieceIntrinsic landed; kept as an independent cross-check): the
     isomorphism is built from scratch — occurrences of the lift ≃ visits of the retained crossings
     (`liftVisit`/`liftVisitEquiv`/`liftOcc`: crossing = U4 `geoCarrierCrossingEquiv`, strand = the block
     `visitBlock` of the corner polygon through the visit, from `geo_mark_block` and the shadow's `no_triple`);
     pairing = `visitTwin` (`twin_liftVisit`); over bit = sign of `det` of the two parent edges
     (`isOver_liftVisit_iff`, the corner-polygon edges being positive multiples of the parent edges,
     `geoCornerPolygon_edge_smul`); signs all `+1`; **cyclic order**: the traversal coordinate of an
     occurrence on the corner polygon is the *block coordinate* `markCoord m = k + (p_m − blockStart k)/blockScale k`
     of its mark, strictly increasing along the `ρ_T`-orbit from the corner `c₀` (`markCoord_lt_succ`, from
     U2b's `geoCornerPolygon_block`: parameters increase inside a block, the block ends below `blockStart + blockScale`);
     by lem:carrierword (`TracedSuccessor`) that orbit is the carrier's mark list in the parent's traversal
     order, so the block coordinate and the parent key induce one cyclic order (`cycBetween_markCoord_iff`,
     via `cycBetween_map_of_strictMonoOn` and the rotation lemma `cycBetween_add_mod`); then
     `CV.recordIsoOfData`.
2. **Transport along the chamber** (`CV.pieceHomflyTransported`, identical in both files): at `Q`, the carrier
   `pieceCarrier_Q` of `S' ∪ K'` and the transported carrier `τ.component (S ∪ K) pieceCarrier_P` of `S' ∪ tK`
   have the same retained crossings — the labels of the piece (`pieceCarrier_geoCarrierCrossings` at `Q`,
   `pieceLabels_eq`, `geoCarrierCrossings_eq_of_mem_chamber`, `pieceCarrier_geoCarrierCrossings` at `P`) — so
   step 1 gives `homfly (lift_Q of (S' ∪ K', pieceCarrier_Q)) = homfly (lift_Q of (S' ∪ tK, τ.component …))`;
   U5a's `homfly_geoPositiveLift_eq_of_mem_chamber` (lit:homfly's planar clause along the chamber path) gives
   `= homfly (lift_P of (S ∪ K, pieceCarrier_P)) = pieceHomfly_P H`. The `CarrierGeometry`/`CrossingGeometry`
   proofs (`ofCV hQ` vs `ofDiagrammatic (hQ.diagrammatic hn)`) are identified by proof irrelevance.

No alternative route was needed. The definitional alternative (canonical `pieceSupport`) was not used.

## 3. How the files were checked

```
cd work/lean; LP="$(lake env printenv LEAN_PATH)"; LEANBIN="$(lake env which lean)"
lake env lean ../drafts/cvdom/U5c/PieceHomflyTransport.lean                 # exit 0, no output
lake env lean ../drafts/cvdom/U5c/PieceHomflyTransport_selfcontained.lean   # exit 0, no output
mkdir -p /tmp/u5c_root/CV /tmp/u5c_olean/CV
for f in "$PWD"/.lake/build/lib/lean/CV/*.olean; do ln -s "$f" /tmp/u5c_olean/CV/; done      # overlay (U5a REPORT §1)
cp ../drafts/cvdom/U5c/PieceHomflyTransport.lean /tmp/u5c_root/CV/
LEAN_PATH="/tmp/u5c_olean:$LP" "$LEANBIN" --root=/tmp/u5c_root -o /tmp/u5c_olean/CV/PieceHomflyTransport.olean /tmp/u5c_root/CV/PieceHomflyTransport.lean
LEAN_PATH="/tmp/u5c_olean:$LP" "$LEANBIN" ../drafts/cvdom/U5c/CVChamberInv.lean               # exit 0, no output
```
Axioms: `#print axioms` on /tmp copies (/tmp/u5c_row_ax.lean, /tmp/u5c_sc_ax.lean):
`CV.chamberinv`, `CV.chamberinv_ii`, `CV.pieceHomflyTransported`, `CV.homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`
→ `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]`;
`CV.ChamberInvData` → `[propext, Classical.choice, Quot.sound, SM.lit_homfly]`. `SM.lp_lm` and
`SM.lp_lm_uniqueness` enter through `CV.gausscode_polynomial` (= `SM.record_polynomial.P_eq` + `SM.lp_core.eq_homfly`),
exactly as the task anticipated; the statement `ChamberInvData` only mentions `homfly` (through `X1`).
Once the two primary files are ported into work/lean/CV, plain `lake env lean` works for both.

## 4. Declarations

**PieceHomflyTransport.lean** (namespace `CV`):
* `theorem homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq (hn) (hG : CarrierGeometry Q) {T₁ T₂} (hT₁ hT₂) (q₁ q₂) (hH : geoCarrierCrossings hG.cg T₁ q₁ = geoCarrierCrossings hG.cg T₂ q₂) : homfly (geoPositiveLift hn hG hT₁ q₁) = homfly (geoPositiveLift hn hG hT₂ q₂)`
* `theorem pieceHomflyTransported (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q) (h : Q ∈ chamber P) : PieceHomflyTransported hn hP hQ h`

**CVChamberInv.lean** (namespace `CV`): `structure ChamberInvData : Prop` (four fields, §5),
`theorem chamberinv_ii (hn) (hP) (hQ) (h : Q ∈ chamber P) : X1 hn Q hQ = X1 hn P hP`, `theorem chamberinv : ChamberInvData`.

**PieceHomflyTransport_selfcontained.lean** (namespace `CV`, helpers in `CV.PieceHomfly`): §0 `cycBetween_map_of_strictMonoOn`,
`cycBetween_add_mod`, `strictMonoOn_Iio_of_lt_succ`; §1 blocks `blockEdge`, `blockStart`, `blockScale`(+`_pos`),
`edge_geoCornerPolygon_eq`, `geoCornerPolygon_eq_edgePoint`, `edgePoint_geoCornerPolygon`, `block_data`, `blockLen`(+`_spec`),
`lt_blockLen_of_blockInterior`, `outSlot_edge_of_blockInterior`, `markBlock`, `markStep`, `markBlock_spec`, `markBlock_eq`,
`markCoord`, `markCoord_of_block`, `markCoord_geoCornerMark`, `blockInterior_succ`, `geoCornerPolygon_add_one_eq`,
**`markCoord_lt_succ`**; §2 orbit `mk`, `mk_of_lt`, `owner_mk`, `mk_inj_iff`, `exists_mk`, `succ_mk`, `pow_mk`, `cornerIndex`(+`_lt`, `mk_cornerIndex`),
`markCoord_mk_lt_succ`, `strictMonoOn_markCoord_mk`, `orbitPos`(+`_lt`), `mk_add_orbitPos`, `markList_pairwise`, `key_mk_lt`,
`strictMonoOn_key_mk`, **`cycBetween_markCoord_iff`**; §3 visits `owner_of_mem_geoCarrierCrossings`, `not_mem_of_mem_geoCarrierCrossings`,
`mem_twin`, `visitBlock`, `one_le_markStep_visit`, `visit_edge_eq_blockEdge`, `crossingPoint_mem_edgeSegment_visitBlock`,
`crossingPoint_mem_edgeInterior_visitBlock`, `shadowCrossing`(+`_crossingPoint`), `blockStrand_mem`, `liftVisit`, `liftVisit_injective`,
`liftVisit_surjective`, `liftVisitEquiv`(+`_apply`), `twin_liftVisit`, `det_smul_smul_both`, `isOver_liftVisit_iff`, `visitCoord_liftVisit`,
`visitBetween_liftVisit_iff`, `liftOcc`, `twin_liftOcc`, `isOver_liftOcc_iff`, `visitBetween_liftOcc_iff`; §4 `crossEquiv`(+`_val`), `liftIso`(+`_liftOcc`),
`liftIso_cyclicOrder`, `liftIso_doublePoints`, `liftIso_overUnder`, `liftIso_signs`, `liftRecordIso`; then the two theorems of §5.

## 5. Row 147 — clause → field map (d1_setup.tex:932–939)

| tex line | printed text | field of `CV.ChamberInvData` | proof |
|---|---|---|---|
| 932–933 | "Proposition (chambers and chamber invariance). Fix `n ≥ 3`." | binder placement, see §6 (1) | — |
| 935 | "(i) The generic locus `𝓤_n` is open in `(ℝ²)^n`," | `open_locus : ∀ (n) [NeZero n], IsOpen (genericLocus n)` | accepted `chamberinv_i.open_locus` |
| 936 | "and every chamber — every connected component of it — is open" | `chamber_open : ∀ (n) [NeZero n] (P), IsOpen (chamber P)` | accepted `chamberinv_i.chamber_open` |
| 936 | "and path connected." | `chamber_pathConnected : ∀ (n) [NeZero n] (P), Generic P → IsPathConnected (chamber P)` | accepted `chamberinv_i.chamber_pathConnected` |
| 937 | "(ii) `X_1` is constant on each chamber." | `x1_constant : ∀ (n) [NeZero n] (hn : 3 ≤ n) (P Q) (hP : Generic P) (hQ : Generic Q), Q ∈ chamber P → X1 hn Q hQ = X1 hn P hP` | `chamberinv_ii` = `X1_eq_of_mem_chamber_of_pieceHomfly hn hP hQ h (pieceHomflyTransported hn hP hQ h)` |

`theorem chamberinv : ChamberInvData` (fixed name `CV.chamberinv`). The (i) fields are the accepted
`CV.ChamberInvIData` fields with `n` quantified inside (the accepted shape; `chamberinv_i_of_three_le`
shows the `3 ≤ n` form is interchangeable). The (ii) field is the task's prescribed statement verbatim.

## 6. Readings for the reviewer (also in the module docstring of CVChamberInv.lean)

1. **`hn : 3 ≤ n`.** Clause (i) does not use it (as in the accepted `chamberinv_i`); clause (ii) needs it because
   `CV.X1` does (CV:def:X1 reads the positive lifts and corner polygons through U2b/U4, DECISION_FINAL §2 reading
   (iii)); it is quantified inside the field, together with `[NeZero n]` as in `X1`'s own signature (ruling R5).
2. **Chambers are `CV.chamber`** = connected components of the CV generic locus (CV:def:generic (B)), which contain
   the SM pure-cut walls — no SM-chamber fallback (DECISION_FINAL §4 note for prop:chamberinv(ii)).
3. **`X_1` is `CV.X1`** (row 146): `Ind(G_P) = CV.Ind`, CV:def:wind's `wind`, `Ω₁(S,L) = [a^{1−w_{S,L}−R(L)} z⁰] P_{S,L}`,
   `P_H = homfly (pieceDiagram H)`, `R(L) = |rot|` of the carrier's corner polygon.
4. **Direction of (ii).** The field reads `X1 hn Q hQ = X1 hn P hP` for `Q ∈ chamber P` (the task's form; ruling R6 quotes the
   symmetric form `X1 hn P hP = X1 hn Q hQ` — use `.symm`).
5. **Proof irrelevance used silently**: `CarrierGeometry.ofCV hQ` vs `CarrierGeometry.ofDiagrammatic (hQ.diagrammatic hn)`,
   `hQ.crossingGeometry` vs `(hQ.diagrammatic hn).crossingGeometry` (all `Prop`s), so `geoPositiveLift`/`geoCarrierCrossings`
   at the two proofs are the same terms.
6. **Duplication note.** CV/PieceIntrinsic.lean (row 156) landed during this unit and contains the same choice-independence
   record isomorphism; the primary file reuses it. The self-contained file is an independent proof of the same statement
   (different construction: block coordinates + `TracedSuccessor` orbit) and can serve as a cross-check or be discarded.

## 7. Lean notes for the assembler (things that cost time)

* A `hw : w.1 ∈ H` may not be reused at the type `(visitTwin w).1 ∈ H`: only defeq at default transparency, and `rw` then
  fails with "not type-correct under implicit transparency". Use an explicit `mem_twin`.
* Bijections between `D.Γ.Visit` types must be *typed* as `(geoPositiveLift …).Γ.Visit ≃ …` (a `def`), not as the abbrev
  `(geoCarrierShadow …).Visit ≃ …`, or `rw`/`simp` lemmas about `Equiv.trans` do not fire; hence the wrapper `liftOcc`.
* **Kernel deterministic timeout**: the four record clauses proved inside one theorem exceeded the kernel's budget although
  each alone passed (the kernel's defeq check of `(Equiv.subtypeEquivRight _ a).1 ≡ a.1` inside `cycBetween`/real terms is
  expensive); the fix was to prove each clause as its own declaration and to rewrite `(e a).1` to `a.1` with
  `Equiv.subtypeEquivRight_apply` instead of relying on `rfl`/`exact`.
* Temp artefacts: /tmp/u5c_root, /tmp/u5c_olean (overlay), /tmp/u5c_row_ax.lean, /tmp/u5c_sc_ax.lean, /tmp/u5c_*.lean (bisection copies with `sorry`, /tmp only).

## 8. Open

Nothing is left open for row 147. Both clauses are proved; `PieceHomflyTransported` is closed. Downstream consumers
(`CV.hyp_R`/`RProof.cv_R`, Bridge:B4 `sides`, U5b) can use `CV.chamberinv_ii` (or `.symm`).
