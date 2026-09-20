# Site_174_REPORT — unit I-174 (Wave 2): the `m`-corner bigon site of row 174 on the `E`-side carrier diagram

Prover (subagent), 2026-09-15 ≈ 20:30 UTC / 4:30pm ET.  File: `work/drafts/moves/Site_174.lean`
(= `Skeleton_W1.lean` + `import RProof.RALedgers` + 1072 appended lines, prefix `s174_`).  Inputs read:
PLAN_FINAL.md §4.2/§4.3/§3, W1_SKELETON_REPORT.md §1/§3/§4, Statements_FINAL.lean
(`exists_bigonData_of_triangle`, `gsc_fulltwist_of_bigon`), RProof/RALedgers.lean (`gsc_fulltwist_triple`,
`gsc_Ledger.qx/fulltwist`, `gsc_moves`), U_R174_REPORT.md §4, RProof/X1Rows3.lean (`GT_Endpoint`, its
namespace lemmas `xval/wval/mval`, `GT_owner_transport`, `GT_homfly_wall_gen`), RProof/GenericTransport.lean
Unit A (8780–10263: `G11_carrierEdge*`, `gu1_markSuccessor_eq_of_adjacent`, `G11_no_visit_between`,
`gu2_clear_closed`, `gu2_line_*_mem_segment`, `gu2_edgeSegment_sub`, `gu2_parallel_meet_vertex`, the affine
toolkit), SM/GeoPositiveLift.lean, SM/GeoCornerPolygon.lean, SM/FlatCarriersDefs.lean, SM/GeoCarrierCount.lean,
SM/LinkDiagram.lean (`switch`, `Shadow.single`), SM/LinkPositiveLift.lean (`positiveDiagram`).

## 0. Deliverables and checks

| item | result |
|---|---|
| `Site_174.lean` | 2947 lines = `Skeleton_W1.lean` (1866, byte-identical after the import block) + the import `RProof.RALedgers` + the appended section "Site 174" (lines 1868–2947, 1072 lines) |
| compile `cd work/lean && lake env lean ../drafts/moves/Site_174.lean` | exit 0, **0 errors**, ≈ 16 s; warnings: exactly the skeleton's **33** `declaration uses sorry` + its one cosmetic `<;>` linter note (line 566).  No new `sorry` (`grep -c sorry` = 34 on both files) |
| `python3 check_W1_identity.py Statements_FINAL.lean Site_174.lean` | check 2 (all **37** declarations of Statements_FINAL byte-identical): **PASS, 0 changed/missing**.  Checks 1 and 3 report `False` for the two reasons the task prescribes: the added import line shifts the 136-line prefix by one, and the appended material means the file no longer *ends* with Statements_FINAL's suffix.  With the import line removed and the file cut at the skeleton's `end SM.Link` (scratch copy) all three checks PASS |
| `#print axioms` | `s174_core`, `s174_site`: `propext, Classical.choice, Quot.sound, sorryAx` — `sorryAx` enters ONLY through the frozen leaf `exists_bigonData_of_triangle` (black box, as instructed); every `s174_` helper (`s174_order`, `s174_clear`, `s174_lift_val`, …) is standard-axiom; `s174_fulltwist_of_hrec` adds `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (through `gsc_fulltwist_of_bigon` → `CV.gausscode_polynomial`), the accepted footprint |
| reassessment rule | never triggered: no lemma took two failed attempts; the one hang was `decide` on `∀ i j : ZMod 3, adjacent i j` (replaced by `interval_cases` on `(j - i).val`) |

Nothing under `work/lean` was written.  Scratch probes live in the session scratchpad only.

## 1. What is PROVED (all `s174_`, namespace `SM.Link`, `open SM SM.GeoCarrier SM.Carrier RProof`)

### 1a. The generic core — `s174_core` (section `S174Core`)

Setting: `hG : CarrierGeometry P`, `hs' : ∀ s, IsCrossing P s ↔ IsCrossing P' s`, three labels `h_in h_s h_out`
with `hcef : IsCrossing P {h_in, h_s}` (the crossing `y`), `hceg : IsCrossing P {h_in, h_out}` (the corner
`c`), `hcfg : IsCrossing P {h_s, h_out}` (the crossing `z`), `hS : GeoIndependent hG.cg S`, `q : GeoComponent
hG.cg S`.

```
theorem s174_core (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hcS : xPair hceg ∈ S) (hy : xPair hcef ∈ geoCarrierCrossings hG.cg S q)
    (hz : xPair hcfg ∈ geoCarrierCrossings hG.cg S q)
    (hK_sel : ∀ c' ∈ S, c' ≠ xPair hceg → ∃ h ∈ c'.val, h ≠ h_in ∧ h ≠ h_s ∧ h ≠ h_out)
    (hord_in : visitParameter (G11_vef hcef) < visitParameter (G11_veg hceg))
    (hord_out : visitParameter (G11_vge hceg) < visitParameter (G11_vgf hcfg))
    (hsgn : crossingSign P h_in h_s = crossingSign P h_s h_out)
    (xs : (geoCarrierShadow hn hG hS q).Crossing)
    (hxs : xs = s174_lift hn hG hS q _ hy ∨ xs = s174_lift hn hG hS q _ hz) :
    ∃ B : BigonData ((geoPositiveLift hn hG hS q).switch xs),
      B.i = ⟨0, Nat.one_pos⟩ ∧ B.y = s174_lift hn hG hS q _ hy ∧ B.z = s174_lift hn hG hS q _ hz
```
`s174_lift hn hG hS q c hc := (geoCarrierCrossingEquiv hn hG hS q).symm ⟨c, hc⟩` is the crossing of the
carrier shadow at the retained crossing `c` (`s174_lift_crossingPoint`: its double point is `crossingPoint c`).
The proof supplies the five inputs of the frozen leaf `exists_bigonData_of_triangle` (with `i = 0`,
`a = jy`, `s = ⟨0, js⟩`, `y = lift y`, `z = lift z`):

| leaf input | how it is discharged (the `s174_` lemma) |
|---|---|
| `hk : 4 ≤ k` | `s174_four_le_cornerCount`: the two carrier edges of a retained crossing are non-adjacent (`gu1_carrierEdge_remote`), and in `ZMod 3` every pair is adjacent (`s174_adjacent_zmod3`) |
| `hy : y.val = {⟨0, a⟩, s}` | `s174_lift_val`: the strands of `lift v.1` are `⟨0, carrierEdge v⟩, ⟨0, carrierEdge (twin v)⟩` (a crossing of the shadow at the same double point, `Generic.crossingPoint_injective`); `a := jy := G11_carrierEdge (y_in)`, `js := G11_carrierEdge (y_s)` |
| `hz : z.val = {⟨0, a + 1⟩, s}` | `s174_carrierEdge_zout : G11_carrierEdge z_out = k₀` and `s174_carrierEdge_yin : G11_carrierEdge y_in + 1 = k₀`, where `k₀ := s174_k₀` is the corner index with `geoCornerMark k₀ = Sum.inr c_in` (`s174_owner_cin`: `ρ_S c_in = z_out` so `c_in` is owned by `q`; `s174_succ_yin : ρ_S y_in = c_in`; blocks via `geo_block_mark_eq`, `geoCornerPolygon_block`, `GeoBlockInterior.not_trueCorner`); `G11_carrierEdge z_s = js` by `G11_carrierEdge_eq_of_adjacent` |
| `same_over` | `s174_pos_over_lift_iff` (the positive lift's over strand at a lifted crossing is `⟨0, carrierEdge (twin v)⟩` iff `det (edge P (twin v).edge) (edge P v.edge) > 0`), `s174_switch_over_self_iff`, `s174_over_other_iff`, `Diagram.switch_overStrand_of_ne`, and the sign condition `hsgn` through `s174_pos_iff_of_sign_eq` / `s174_neg_pos_iff_of_sign_eq`; both switch positions (`xs = lift y` or `xs = lift z`) handled |
| `clear` (CLOSED triangle) | `s174_clear`: an edge `h ∉ {jy, k₀, js}` of the corner polygon lies inside the original edge `e_h` (`gu2_edgeSegment_sub`); `e_h ∉ {h_in,h_s,h_out}` → `gu2_clear_closed` (A8 on `P`); `e_h ∈ {h_in,h_s,h_out}` → a point of `K` on that line is on the corresponding side (`gu2_line_e/f/g_mem_segment`), which lies inside the local carrier edge, so `gu2_parallel_meet_vertex` makes it a corner point of `K`; `s174_corner_mem_K` shows the only corner point in `K` is `c` itself (vertices by `gu2_clear.2`, other selected crossings by `hK_sel` + `gu2_clear_closed`); and `geoCornerPolygon_tail_off` forbids the corner `k₀` on a non-incident edge |

Inputs derived inside the core from `hX` (A7, `G11_no_visit_between`, relabelled with `gu2_exact_of_eq`):
`s174_adj_in / s174_adj_out / s174_adj_s` (parameter-form adjacency of the three local pairs);
`s174_markSucc_yin / s174_markSucc_cout` (`gu1_markSuccessor_eq_of_adjacent`).

### 1b. The `GT_Endpoint` wrapper — `s174_site` (section `S174SiteMain`)

```
theorem s174_site (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (hw' : crossingTransport hs w ∈ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q') :
    ∃ B : BigonData ((CV.carrierDiagram hn hG' hSm' q').switch (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx')),
      B.i = ⟨0, Nat.one_pos⟩ ∧
      ((B.y = lift w' ∧ B.z = lift x') ∨ (B.y = lift x' ∧ B.z = lift w'))
```
(`lift c := s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' c _`;
`s174_cg hn hG' := CarrierGeometry.ofDiagrammatic (hG'.diagrammatic hn)`, and
`s174_carrierDiagram_eq : CV.carrierDiagram hn hG' hS' q' = geoPositiveLift hn (s174_cg hn hG') … q'` is `rfl`.)
`D_H := carrierDiagram hn hG' hSm' (W.τ qAB)` is the case `q' := W.τ qAB`; the switched crossing is the lifted
`x' = a`, exactly the ledger's `qx`.

The wrapper (i) reads the three `P'`-crossings `x' = x_{ℓ₁ℓ₂}, m' = x_{ℓ₁ℓ₃}, w' = x_{ℓ₂ℓ₃}` from `D.xval/mval/wval`
and `hs`; (ii) gets `ExactTriangleVisitOrders P' P ℓ₁ ℓ₂ ℓ₃` from `D.gauss` by `s174_exact_symm` (the
predicate is symmetric under `visitTransport`, proved here) and `s174_labels_eq D : {ℓ₁, ℓ₂, ℓ₃} = {e, f, g}`;
(iii) transfers the signs with `D.sign_eq` and `D.sgn`; (iv) **derives the traversal direction at the
corner** with `s174_order` (see 1c): `m'` before `x'` on `ℓ₁` ⟺ `w'` before `m'` on `ℓ₃`; then
* case `x'` before `m'` on `ℓ₁`: the corner polygon enters `m'` along `ℓ₁` and leaves along `ℓ₃`;
  `(h_in, h_s, h_out) = (ℓ₁, ℓ₂, ℓ₃)`, `(y, z) = (x', w')`, switch at `y`;
* case `m'` before `x'`: enters along `ℓ₃`, leaves along `ℓ₁` (the canonical picture of PLAN §4.2);
  `(h_in, h_s, h_out) = (ℓ₃, ℓ₂, ℓ₁)` (labels via `gu2_isCrossing_comm`/`gu2_xPair_comm`), `(y, z) = (w', x')`,
  switch at `z`.
In both cases the sign condition of the core, `crossingSign P' h_in h_s = crossingSign P' h_s h_out`, is
`crossingSign ℓ₁ ℓ₂ = crossingSign ℓ₂ ℓ₃` (+ `crossingSign_swap`), i.e. exactly (1) of GSC;
`hK_sel` is `s174_foreign_edge D` (every selected crossing of the transported centre row other than `m'`
comes from `Q`, hence has an edge outside `{ℓ₁,ℓ₂,ℓ₃}` by `D.Q_out`).

### 1c. The order lemma — `s174_order` (section `S174Site`, tier 0, standard axioms)

```
theorem s174_order (hP : CrossingGeometry P) {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
    (hc12 : IsCrossing P {ℓ₁, ℓ₂}) (hc13 : IsCrossing P {ℓ₁, ℓ₃}) (hc23 : IsCrossing P {ℓ₂, ℓ₃})
    (hs12 : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) (hs23 : crossingSign P ℓ₂ ℓ₃ = crossingSign P ℓ₁ ℓ₃) :
    (crossingParameter (xPair hc13) ℓ₁ _ < crossingParameter (xPair hc12) ℓ₁ _ ↔
      crossingParameter (xPair hc23) ℓ₃ _ < crossingParameter (xPair hc13) ℓ₃ _)
```
Proof: `x' - m' = (t_x - t_m) u₁`, `w' - m' = (s_w - s_m) u₃`, `x' - w' = (r_x - r_w) u₂`
(`gu2_xpt`, `gu2_edgePoint_sub`, `abel`), so `(x'-m') - (w'-m') = x'-w'`; taking `det(·, u₃)` and `det(u₁, ·)`
componentwise (`det` is the explicit `u.1 v.2 - u.2 v.1`, `linear_combination`) gives
`(t_x - t_m) det(u₁,u₃) = (r_x - r_w) det(u₂,u₃)` and `(r_x - r_w) det(u₁,u₂) = -(s_w - s_m) det(u₁,u₃)`;
the real lemma `s174_order_alg` (`B ≠ 0`, `0 < A·C`) then gives `0 < t_x - t_m ↔ s_w - s_m < 0`.
This is the fact PLAN §4.2 tacitly uses ("entering/exiting edges along `ℓ₃`/`ℓ₁`"): the sign condition
forces exactly one of the two orientations, and both occur — hence the disjunction in `s174_site`.

### 1d. Helpers (all PROVED, standard axioms)
`s174_pos_over_iff` (positive over strand ↔ `det > 0`), `s174_switch_over_self_iff`, `s174_over_other_iff`,
`s174_exact_symm`, `s174_ne_of_isCrossing`, `s174_triple_perm_gef'/feg'`, `s174_adj_in/out/s`,
`s174_markSucc_yin/cout`, `s174_succ_yin/cin`, `s174_owner_cin`, `s174_k₀`, `s174_k₀_spec`,
`s174_cornerPolygon_k₀`, `s174_carrierEdge_zout/yin`, `s174_lift`, `s174_lift_congr`,
`s174_lift_crossingPoint`, `s174_lift_injective_pt`, `s174_lift_val`, `s174_adjacent_zmod3`, `s174_four_le`,
`s174_four_le_cornerCount`, `s174_pos_iff_of_sign_eq`, `s174_det_ne_zero_of_isCrossing`,
`s174_det_smul_pos_iff`, `s174_pos_over_lift_iff`, `s174_not_pos_iff`, `s174_neg_pos_iff_of_sign_eq`,
`s174_K` (abbrev), `s174_corner_mem_K`, `s174_clear`, `s174_strand_ne_of_not_adjacent`, `s174_order_alg`,
`s174_mul_pos_of_sign_eq`, `s174_param_congr`, `s174_param_ne`, `s174_xPair_ne_of_mem`, `s174_labels_eq`,
`s174_foreign_edge`, `s174_cg`, `s174_carrierDiagram_eq`, `s174_reducedRecordOf`, `s174_reducedRecord_eq`,
`s174_reducedRecord_eq_swap`.

## 2. The pre-review claim ("no `BigonData` field must change") — VERIFIED for site 174

Every field is delivered through `exists_bigonData_of_triangle` as frozen.  Two points worth recording:
* **`clear` with the CLOSED `K`** is provable only because a carrier of an independent support has a
  *single* corner at the point `m'` (the other smoothing arc through `m'` belongs to another carrier,
  `geo_selected_visits_separated`).  In the proof this enters through `geoCornerPolygon_tail_off` (whose
  proof uses `geoCornerPolygon_injective`): a second corner at `m'` would put `m' ∈ K` on a fourth carrier
  edge and `clear` would be FALSE.  So the closed form is right for independent supports and would fail for
  a non-independent one — consistent with PLAN §3 (last bullet).
* **`hK_sel`**: the natural consumer-side input is "every other selected crossing has an edge outside the
  bundle" (a label fact, `D.Q_out`), not a point-set statement; the core converts it with `gu2_clear_closed`.
  `hk : 4 ≤ k` is automatic (a carrier with a retained crossing has ≥ 4 corners).

## 3. (b) The record identification `hrec` — STATED, not proved

```
def s174_hrec_prop hn hG hG' hSm hSm' qAB q' hx' hw' : Prop :=
  Nonempty (RecordIso
    (s174_reducedRecordOf ((carrierDiagram hn hG' hSm' q').switch (lift x')) (lift w') (lift x'))
    (carrierDiagram hn hG hSm qAB).record)
-- s174_reducedRecordOf D y₀ z₀ := D.record.restrictCrossings {c | c ≠ crossingOf (overVisit y₀) ∧ c ≠ crossingOf (overVisit z₀)}
```
`s174_reducedRecord_eq / _eq_swap` show `B.reducedRecord = s174_reducedRecordOf D (lift w') (lift x')` for the
`B` of `s174_site` in BOTH orientation cases (the keep-set is symmetric in `y, z`), so this single Prop is
exactly `hrec` of `gsc_fulltwist_of_bigon`.  Route and cost (G11 Unit-F pattern, `GT_owner_transport`;
estimate **1.5–2.5k lines**, above PLAN's 1.2k because of step (v)):
1. `(ρ.switch v).restrictCrossings S ≅ ρ.restrictCrossings S` when `v`'s crossing is NOT kept (the switched
   bits sit on deleted occurrences; `restrictCrossings` reads `isOver v.1` only at retained `v`): a
   `RecordIso` with `Equiv.refl` on the subtype, ≈ 80–150 lines (record level; note the frozen leaf
   `Record.restrictCrossings_switch` is the RETAINED case and is not what 174 needs).
2. The crossing correspondence: `c ∈ geoCarrierCrossings AB' ∧ c ≠ x', w' ↔ (crossingTransport hs)⁻¹ c ∈
   geoCarrierCrossings AB` — ownership transport on good marks (`GT_owner_transport`, `GT_carrierEquiv`,
   `GT_Endpoint.good_of_edge/good_of_outside`); shared with the ledger's `writhe_wall`/`omega_wall`
   (U_R174 §4 item 2), ≈ 400–600 lines.
3. Cyclic order: the visit order of a positive lift is the inherited order of the marked traversal circle
   on the carrier (`geoIndependent_inheritsMarkOrder`); after deleting the four occurrences of `x', w'` no
   triangle visit remains among the record visits (`m'` is selected, hence a corner, not a record visit), and
   `ExactTriangleVisitOrders` carries the order of every non-triangle pair on a common edge (edge labels
   order the rest), ≈ 300–500 lines.
4. Over bits and signs: both lifts are positive; the over strand at `c` is decided by
   `sign det(edge ℓ, edge ℓ')` of the two visited edges, carried by `D.sign_eq`, ≈ 100 lines.
5. Assembly against `restrictCrossings` (its successor is `firstReturn`; the U-M6 pattern
   `RecordIso.ofOcc`, `restrictCrossings_succ_val`, `firstReturn_no_between` or `CV.recordIsoOfData` on a
   one-circle record), ≈ 500–800 lines — the risk item (PLAN §6 R5).

## 4. (c) The `fulltwist` field from (a) + (b) — PROVED

```
theorem s174_fulltwist_of_hrec (D : GT_Endpoint …) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm) (hSm') (qAB) (q') (hx') (hw') (hrec : s174_hrec_prop hn hG hG' hSm hSm' qAB q' hx' hw') :
    ∃ D₀ : Diagram, gsc_fulltwist_triple (carrierDiagram hn hG hSm qAB) (carrierDiagram hn hG' hSm' q') D₀ (lift x')
```
via `gsc_fulltwist_of_bigon` (`hq := geoPositiveLift_isPositive`, both component counts `rfl`,
`B := s174_site`, `hrec := s174_reducedRecord_eq(_swap) ▸ hrec`); `gsc_fulltwist_triple` is
`moves_fulltwist_triple` verbatim (the `exact` closes by unfolding).  A realiser of `gsc_moves` takes
`q' := W.τ qAB`, `qx := lift x'` and `D₀` from the existential, and this discharges `gsc_Ledger.qx`,
`gsc_Ledger.fulltwist` (F-174: no interface edit, as PLAN §3 says).

## 5. What row 174 still needs beyond this site (estimates)

| obligation | content | lines |
|---|---|---|
| `hx'`, `hw'` (site inputs) | `x', w' ∈ geoCarrierCrossings hG'.cg S' (W.τ qAB)`: the four `ℓ₁/ℓ₂/ℓ₃`-visits of `x', w'` are owned by `AB'` — the arc `[m'(ℓ₁) → … → m'(ℓ₃)]` of the `E`-side polygon (`GT_owner_arc`, `AV_nextCorner`), given the ledger's choice of `qAB` as the carrier owning `x(ℓ₂), w(ℓ₂)` on `P` (U_R174 §4 items 1–2) | 0.4–0.8k |
| `hrec` (`s174_hrec_prop`) | §3 | 1.5–2.5k |
| the rest of `gsc_Ledger` | items 1 (carrier structure, `ρ`), 2 (`omega_wall`, `writhe_wall`), 3 (selector/rotation ledger), 5 (`smoothing`), 6 (`writhe_count`) of U_R174_REPORT §4 | ≈ 5–8k (PLAN §7) |
| the leaf `exists_bigonData_of_triangle` (U-M7) and Wave 1 | black boxes here | Wave 1 |

## 6. Pitfalls met (for the 176 prover — the `j`-corner site is `s174_core` with `(P', S, q, c, y, z) := (E-side polygon, Q ∪ {j}, …)`)
1. Never `set` a *type-level* term (`set Γ := geoCarrierShadow …`): `rw`/`simp` then fail with "motive is not
   type-correct at implicit transparency".  Terms (`set k₀`, `set ys`) are fine.
2. Strand literals `⟨0, j⟩` must carry the ascription `(⟨0, j⟩ : (geoCarrierShadow hn hG hS q).Strand)`; with
   the expected type `(geoPositiveLift …).Γ.Strand` or `Fin D.Γ.c` the numeral `0` fails to elaborate
   (`OfNat (Fin D.Γ.c) 0`).  Pass `i := ⟨0, Nat.one_pos⟩` to `exists_bigonData_of_triangle`.
3. `rw` with lemmas stated on `D.Γ.Crossing` against goals on `(geoCarrierShadow …).Crossing` (or `Sigma`
   literals at defeq-but-different types) fails: use `refine (lemma …).trans ?_` / `exact` (defeq) instead,
   and `Disjoint.mono_right (le_of_eq h)` with an `h` proved by `rw [← hK]; rfl` for the `clear` target.
4. `jy + 1` at the leaf's type `ZMod (D.Γ.comp i).k` versus `ZMod (geoCornerCount …)`: write
   `((jy + 1 : ZMod (geoCornerCount hG.cg S q)))` and let the application check defeq.
5. `decide` on `∀ i j : ZMod 3, adjacent i j` hangs; use `ZMod.natCast_zmod_val` + `interval_cases`.
6. Section variables used only in proofs need `include … in` (Lean 4 inclusion rules); `q` becomes an
   explicit argument wherever it appears in a statement.
7. `crossingParameter c i hi` is dependent in `c`: rewrite crossings with `s174_param_congr` (subst), never
   `rw [hc]`; `generalize` the six parameters before the vector identity.
8. `visitTwin`, `isTrueCorner_visit` live in `SM.Carrier`; `IsTrueCorner S (Sum.inr v)` is `v.1 ∈ S` by `Iff.rfl`.
9. `rcases hmark : geoCornerMark … with j | v` substitutes in the goal but not in earlier hypotheses.
10. The ownership hypotheses are stated with `hG'.crossingGeometry`; `CarrierGeometry.ofDiagrammatic …`.cg is
    accepted for it by proof irrelevance (`CrossingGeometry` is a Prop) — no transport needed.
