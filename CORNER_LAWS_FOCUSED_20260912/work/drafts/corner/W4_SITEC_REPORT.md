# W4_SITEC_REPORT — unit SITEC (I-110; prefix `s7sc_`; corner wave 4, under D-AUTH-20260919), 2026-09-19 06:15 UTC / 2:15am ET

File: `work/drafts/corner/W4_SITEC.lean` = `W3_Assembled.lean` (8,958 lines) + TWO inserted `s7sc_` blocks + the two SITE
sorry bodies replaced — **9,564 lines**, sha256 `5ad034553b30225038530a5341039246a2ad0ebb0468a40dcbfaa6970595709d`.
`diff W3_Assembled.lean W4_SITEC.lean` has exactly four hunks: `6959a6960,7174` (block s7sc.1, 215 lines, inserted immediately
BEFORE the docstring of `s7s_clear_local`, inside `section S7SiteWall`), `6981c7196,7246` (the `sorry` body of `s7s_clear_local`
→ 51-line proof), `7010a7276,7603` (block s7sc.2, 328 lines, inserted immediately BEFORE the docstring of
`s7s_wallTriangleData_of_bigon`, inside `section S7Site` after `end S7SiteWall`), `7023c7616,7629` (the `sorry` body of
`s7s_wallTriangleData_of_bigon` → 14-line proof).  **No other line changed**: every existing statement, name and docstring is
byte-identical (including the two "BLACK BOX … NOT proved" docstrings, which are frozen text and now describe closed theorems).
Frozen declarations: `python3 tools/stmt_check.py W4_SITEC.lean --base W3_Skeleton.lean` → **5/5 PASS**; `tail -n 43` of both
files identical; the docstring+statement+`sorry` blocks of `s7_sliding_law_at`, `s7_bigon_law_at` identical (Python line compare).
(The tool's default base `Statements_FINAL.lean` is the wave-1/2 frozen file and does not apply to the W3 lineage: 4/49, as for
`W3_Assembled.lean` itself.)
Compile: `cd work/lean && lake env lean ../drafts/corner/W4_SITEC.lean` — **0 errors, 0 non-sorry warnings, exactly 10
`declaration uses sorry`** (was 12): `s7q_box_ret` 4437, `s7q_box_carriers` 4519, `s7_sliding_law_at` 4844, `s7f_exists_bigonSplit`
5371, `s7f_exists_twoNewbornTerm` 5388, `s7f_exists_ineligible_transport` 5725, `s7z_F_exists` 9206, `s7z_returned_of_FSector`
9226, `s7z_oneNewborn_exists` 9245, `s7_bigon_law_at` 9512.  21 s warm.
`grep -c sorry`: **20 → 18** (the two SITE bodies; the 8 prose mentions and the 10 remaining bodies unchanged).
Nothing written under `work/lean`; scratch files only in the session scratchpad (`sitec/C1b.lean`, `sitec/C2.lean`, `sitec/AX.lean`).
No import added.
Axioms (`#print axioms` on the scratch copy `AX.lean` = the file + 16 `#print axioms` lines after `end SM`):
**`s7s_clear_local`, `s7s_wallTriangleData_of_bigon`, `s7s_carrier_data_of_wall`, `s7s_siteData_of_wall`** and every `s7sc_`
theorem = `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`** (SITE's two former black boxes and the two theorems that
consumed them are now fully proved with standard axioms); `s7s_switch_value` `+ SM.lp_lm`, `s7s_cornerHomfly_skein`
`+ SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (unchanged policy set, no `sorryAx`); `w3_s7_bigon_law_at_of` standard `+ lit_homfly`,
no `sorryAx` (unchanged); `s7_bigon_law_at` and `thm_C_S7` still carry `sorryAx` (the leaves; unchanged axiom lists otherwise).
Reassessment rule: **not triggered** — no lemma took two failed attempts.  Scratch C1 (clearance) needed 3 compile rounds
(round 1: `ne_of_isCrossing_pair` lives in namespace `P1`; a stray `conv_lhs`; the adjacency lemma needs `(v := …) (w := …)`
since `v.1 ∈ …` does not determine `v`; round 2: the six-component `gu1_carrierEdge_block` destructured with five patterns, and
`gu2_edgePoint_sub` at `edgePoint P M 0` leaves `(ty - 0)` before `div_mul_cancel₀`); scratch C2 (wall data) needed 3 rounds
(round 1: `rw` into `w.2.property : ↑w.2 ∈ ↑w.1` fails — dependent motive — use `h ▸ w.2.property`; `linear_combination` cannot see
through unreduced `contactWindowEdge M a (some true)` / `(G11_vef hx).2.val` — state the defeq form with `have … := hedge` first;
`rw [crossingParameter_eq_of_support_pair_of_geometry … _ rfl]` with a `_` membership proof finds no occurrence — use `congrArg`;
round 2: two sign/direction slips).  Both scratch files then compiled clean; the insertion compiled first time.

## 0. What the unit delivers, in one paragraph

**SITE's two black boxes are closed; `s7s_siteData_of_wall` is sorry-free.**  (i) `s7s_clear_local` — clearance of the carrier
edges lying on the three LOCAL original edges `M−1`, `M`, `a` other than the local pieces `j_in`, `j_in+1`, `j_s` — is proved by
a route SHORTER than the estimated 300-450 lines (215 + 51): instead of the per-edge block-parameter bookkeeping of
W3_SITE_REPORT §2.1, the general fact **two distinct carrier edges of one corner polygon lying on the same original edge are
disjoint** (`s7sc_disjoint_of_same_outSlot`: adjacent ones would make the true corner between them come in and go out on one
original edge, `s7sc_inEdge_ne_outSlot`; non-adjacent ones meet only at a retained double point whose two visits lie on the two
out-slot edges, `geo_nonadjacent_meet`, i.e. on one original edge, against `visitTwin_edge_ne`), combined with **the closed contact
triangle meets each local original edge only in the corresponding side** (`s7sc_K_side_pred/succ/base`, from the ported
`gu2_mem_segment_ab_of_line` and the non-degeneracy `det(P M − x, y − x) = (1 − t_x)(r_y − r_x) det(E_{M−1}, E_a) ≠ 0`,
`s7sc_tri_det_ne_zero`) and the sides' containment in the local carrier edges (`x, P M ∈ edgeSegment Q j_in`, `P M, y ∈
edgeSegment Q (j_in+1)`, `x, y ∈ edgeSegment Q j_s` from `gu1_carrierEdge_block`, `s7s_cornerPolygon_of_wall`,
`G11_carrierEdge_eq_of_adjacent` + convexity `s7sc_segment_subset_edgeSegment`).  (ii) `s7s_wallTriangleData_of_bigon` — the
`P`-level wall data on both sides of a bigon wall below a radius — is proved on the accepted `vertex_sides` (through the ported
`s7a_exists_sideLocal`): window clauses (2)-(4) are `VertexLocalData.visit_windows` read at the contact visits and at the other visits
(`s7sc_window_clauses`: the contact visits are within `η` of the window centres `1`, `0`, `r`; every other visit on `M−1`, `M`, `a` is
unaffected, hence outside its window, hence at least `η` away), and the printed emptiness (1) is `s7sc_eventually_clear`: at the
centre the contact vertex lies on no edge other than `M−1`, `M`, `a` (`contact_vertex_incidence`), so it is at positive distance
`ε_e` from each such compact edge segment; near the centre the three triangle vertices are within `ε_e/4` of it (the two contact
crossing points are `edgePoint Q (M−1) (edgeParameter Q (M−1) a)`, `edgePoint Q M (edgeParameter Q M a)`, continuous at the centre
by `continuousAt_contact_pair_parameters` with the central values `1`, `0` of `contact_parameters_center`) and every point of the
edge `e` of `Q` is within `ε_e/4` of the same-parameter point of the edge `e` of the centre; the eventual statement is transported
to a radius by `eventually_center_iff_radius` and read on both sides with `sideTime_val_abs`.  Both closures use only standard
axioms.  Consequence: the SITE chain `s7s_siteData_of_wall → s7s_site → s7s_rii_witnesses → s7s_switch_value →
s7s_cornerHomfly_skein` now has NO sorry on it; what the bigon leaf still needs from SITE's side is exactly the record
identification `hrec` (`s7s_hrec_prop`, reduced to the unswitched form by `s7s_hrec_prop_of_unswitched`; U110-A content,
W3_SITE_REPORT §3, 1,000-1,650 lines) and the per-support instantiation of B2 (W3_ASSEMBLY_REPORT §3.2).

## 1. PROVED (all `s7sc_`; standard axioms)

### 1.1 Block s7sc.1 — clearance (lines 6960-7174, `section S7SCClear` inside `section S7SiteWall`)
| declaration | line | content |
|---|---|---|
| `s7sc_edgeSegment_eq_segment P i` | 6968 | `edgeSegment P i = segment ℝ (P i) (P (i+1))` (`segment_eq_image'`) |
| `s7sc_segment_subset_edgeSegment` | 6980 | `u, v ∈ edgeSegment P i → segment ℝ u v ⊆ edgeSegment P i` (convexity) |
| `s7sc_left_mem_edgeSegment`, `s7sc_right_mem_edgeSegment` | 6987, 6991 | the two endpoints lie on the closed edge |
| `s7sc_one_ne_zero (hn : 3 ≤ n)` | 6996 | `(1 : ZMod n) ≠ 0` |
| **`s7sc_inEdge_ne_outSlot hn hP S m (hm : IsTrueCorner S m)`** | 7004 | `geoInEdge hP m ≠ (geoOutSlot hP S m).1` — vertex: `i − 1 ≠ i` (`geoInEdge_vertex`, `geoOutSlot_vertex`); selected visit: own edge vs twin's edge (`geoInEdge_visit`, `geoOutSlot_selected`, `visitTwin_edge_ne`) |
| **`s7sc_disjoint_of_same_outSlot hn hG hS q (hne : h ≠ j) (he : outSlot h = outSlot j)`** | 7020 | `Disjoint (edgeSegment Q h) (edgeSegment Q j)` — adjacent: `geoCornerPolygon_outEdge_eq_inEdge_of_independent` + the lemma above at the corner between; non-adjacent: `geo_nonadjacent_meet` + `visitTwin_edge_ne` |
| `s7sc_xPair_ne hx hy hn` | 7049 | `xPair hx ≠ xPair hy` (`M − 1 ∈ {a, M}` impossible) |
| **`s7sc_tri_det_ne_zero hx hy hn hP`** | 7060 | `det (P M − x) (y − x) ≠ 0` (`= (1 − t_x)(r_y − r_x) det(E_{M−1}, E_a)`; `r_x = r_y` would give `x = y`, against `crossingPoint_injective_of_geometry`) |
| **`s7sc_K_side_pred / _succ / _base hx hy hn hP (hz : z ∈ s7s_K hx hy) (hze : z ∈ edgeSegment P e)`** | 7088, 7105, 7138 | `z ∈ segment ℝ x (P M)` / `segment ℝ (P M) y` / `segment ℝ x y` for `e = M−1` / `M` / `a` (`gu2_mem_segment_ab_of_line` with `t = (s − t_x)/(1 − t_x)`, `s/t_y`, `(s − r_x)/(r_y − r_x)`; hull re-ordered by `Set.insert` commutation; the other two determinants are `±` the first by `simp only [det, …]; ring`) |

**`s7s_clear_local` — CLOSED** (line 7187; body 7196-7246): `hjout := s7s_jout_of_wall`, `hjy : carrierEdge (G11_vfg hy) = carrierEdge
(G11_vfe hx)` (`G11_carrierEdge_eq_of_adjacent (v := G11_vfe hx) (w := G11_vfg hy)` from clause (4)), `hPM := s7s_cornerPolygon_of_wall`;
the out-slot edges and edge-segment memberships of the three local carrier edges from `gu1_carrierEdge_block`; then for `z ∈ edgeSegment Q
h ∩ K` with `h` on `e` (`gu2_edgeSegment_sub`), the side lemma puts `z` on the local side, the containment puts it in the local carrier edge
`j_loc ∈ {j_in, j_in+1, j_s}`, and `s7sc_disjoint_of_same_outSlot` with `h ≠ j_loc` (`h1`/`h2`/`h3`) and equal out-slot edges (`he`,
`gu1_carrierEdge_block`) contradicts.  The route does not need the block-parameter monotonicity of W3_SITE_REPORT §2.1.

### 1.2 Block s7sc.2 — the `P`-level wall data (lines 7276-7603, `section S7SCWall` inside `section S7Site`; `open Filter Topology`)
| declaration | line | content |
|---|---|---|
| `s7sc_contactWindowEdge_none/_false/_true`, `s7sc_contactWindowCenter_none/_false/_true`, `s7sc_contactLeg_false/_true` | 7289-7303 | the slot bookkeeping, all `rfl` (`none ↦ a, r`; `some false ↦ M − 1, 1`; `some true ↦ M, 0`) |
| `s7sc_crossing_ext` | 7309 | a crossing is determined by its support |
| `s7sc_not_affected_pred hn hx w (hw : w on M−1) (hwx : w.1 ≠ xPair hx)`, `_succ`, `_base` | 7313, 7325, 7337 | `¬ ContactAffected M a w.1.val` (the other affected support would put `M−1 ∈ {a, M}` / `M ∈ {a, M−1}`) |
| **`s7sc_window_clauses hn (hL : VertexLocalData hn P Q M a r η) (hQ : G1 Q) (hcg : CrossingGeometry Q) hx hy`** | 7350 | clauses (2) ∧ (3) ∧ (4) of `s7s_WallTriangleData Q M a hx hy` — `hL.visit_windows hQ` at `G11_vef hx` (slot `some false`, so `|t_x − 1| < η`), `G11_vgf hy` (slot `some true`, `|t_y| < η`), `G11_vfe hx`, `G11_vfg hy` (slot `none`, `|· − r| < η`); at an unaffected visit the window is excluded, and `0 < visitParameter < 1` (`crossingParameter_interior_of_geometry`) closes the inequalities; for clause (4) the visits of `x`, `y` themselves are handled by `s7s_visit_ext` and `lt_irrefl` |
| `s7sc_isCompact_edgeSegment P e` | 7442 | image of `Icc 0 1` under the continuous `edgePoint P e` |
| `s7sc_exists_gap P p e (hp : p ∉ edgeSegment P e)` | 7456 | `∃ ε > 0, ∀ w ∈ edgeSegment P e, ε ≤ dist p w` (`IsCompact.exists_isMinOn`) |
| **`s7sc_center_not_mem hn hsep hz e he1 he2 he3`** | 7465 | `P M ∉ edgeSegment P e` for `e ∉ {M−1, M, a}` at the centre (`contact_vertex_incidence` with `¬ incident M e`) |
| `s7sc_edgePoint_dist_le e (h0 : dist (Q e) (P e) < ρ) (h1 : dist (Q (e+1)) (P (e+1)) < ρ) hs0 hs1` | 7476 | `dist (edgePoint Q e s) (edgePoint P e s) ≤ ρ` (`(1 − s) • (Q e − P e) + s • (Q (e+1) − P (e+1))`, `norm_smul`) |
| `s7sc_xpt_eq hcg hx`, `s7sc_ypt_eq hcg hy` | 7496, 7503 | `crossingPoint (xPair hx) = edgePoint Q (M−1) (edgeParameter Q (M−1) a)`, `crossingPoint (xPair hy) = edgePoint Q M (edgeParameter Q M a)` (`gu2_xpt`, `crossingParameter_eq_of_support_pair_of_geometry`) |
| **`s7sc_eventually_contact_near hn hsep hz hm r hr (hρ : 0 < ρ)`** | 7514 | `∀ᶠ Q in 𝓝 P`, the two Cramer contact points and `Q M` are within `ρ` of `P M` (`continuousAt_contact_pair_parameters`, `contact_parameters_center`, `contact_edgePoint_endpoint`, `continuous_vertex`, `continuous_edge`) |
| **`s7sc_eventually_clear hn hsep hz hm r hr`** | 7555 | `∀ᶠ Q in 𝓝 P, CrossingGeometry Q → ∀ e ∉ {M−1, M, a}, ∀ hx hy, Disjoint (edgeSegment Q e) (s7s_K hx hy)` (`eventually_all` over `e`; `ε_e` from the gap; `convexHull_min … (convex_ball _ _)`; the triangle inequality `ε ≤ dist (P M) w₀ ≤ dist (P M) w + dist w w₀ < ε/4 + ε/4`) |

**`s7s_wallTriangleData_of_bigon` — CLOSED** (line 7611; body 7616-7629): `hV := h.1 : g.VertexEdgeAt M a`; `s7a_exists_sideLocal hn g
M a hV` gives `r η δ₁` with `VertexLocalData hn g.center (g.curve (g.sideTime b t)) M a r η` for `t.val < δ₁`, both sides;
`(g.eventually_center_iff_radius _).mp (g.continuous_curve.continuousAt.eventually (s7sc_eventually_clear hn hV.1 hV.2.1 hV.2.2.2.1 r hr))`
gives `δ₂`; `δ := min δ₁ δ₂`; on side `b` at `t`, `hcg := generic_crossingGeometry hn (g.sideTuple b t).2`, clauses (2)-(4) from
`s7sc_window_clauses` and clause (1) from the eventual statement at `g.sideTime b t` (`sideTime_val_abs`).  The statement's `hx hy`
are consumed as given (the side that carries both contact crossings); on the other side the statement is vacuous, as intended.

## 2. NOT proved — none in this unit.  New black boxes from other units — none.

Nothing believed false.  The frozen statements of both closed declarations were provable exactly as stated; no restatement.

## 3. Consequences for the bigon leaf (W3_ASSEMBLY_REPORT §3.2, Prop B2)

`s7s_siteData_of_wall (hW : s7s_WallTriangleData P M a hx hy) hxq hyq : s7s_SiteData …` is now **sorry-free**, and the `P`-level wall data
`hW` is supplied on both sides below a radius by `s7s_wallTriangleData_of_bigon`.  So the K-side recipe of W3_SITE_REPORT §5 has steps 1-2
and 4 fully proved: `hW := s7s_wallTriangleData_of_bigon hn g M a h |>.choose_spec.2 b t ht hx hy`, `W := s7s_siteData_of_wall …`, then
`s7s_cornerHomfly_skein … W D_L hrec v hv : cornerHomfly = a⁻² P(D_L) + a⁻¹ z P(D₀)` — the ONLY remaining input on the SITE side is
`hrec : s7s_hrec_prop … D_L` (via `s7s_hrec_prop_of_unswitched`, the unswitched record identification, U110-A content, 1,000-1,650 lines,
W3_SITE_REPORT §3).  Updated remaining estimate for B2: W3_BLOCK_REPORT §2's 3,500-5,400 minus SITE's 600-950 for the two boxes
(done in 608 lines).  Nothing else in the file changed; the `w3_` glue and the five Props are untouched.

## 4. How to consume the new material (for U110-A / K)

* `s7s_wallTriangleData_of_bigon hn g M a h : ∃ δ > 0, ∀ b t, t.val < δ → ∀ hx hy, s7s_WallTriangleData (g.sideTuple b t).1 M a hx hy`.
* `s7sc_disjoint_of_same_outSlot` is general (any carrier of an independent support): two carrier edges on one original edge are
  disjoint — useful for any further clearance/ordering argument on carrier edges (e.g. the S3 corner correspondence of ROT §6).
* `s7sc_eventually_clear` is stated on `𝓝 P` for any vertex–edge centre data `(hsep, hz, hm, r, hr)`, independent of the germ;
  `s7sc_eventually_contact_near` likewise gives the convergence of the two contact points to the contact vertex at any rate `ρ`.
* `s7sc_window_clauses` is stated for any `VertexLocalData hn P Q M a r η` with `G1 Q`, `CrossingGeometry Q` — usable on either side.

## 5. Pitfalls met (v4.34.0-rc2; in addition to W3_SITE_REPORT §6)
1. `G11_carrierEdge_eq_of_adjacent hn hG hT q hv hw he hadj` cannot infer `v w` from `hv : v.1 ∈ …`: pass `(v := …) (w := …)`.
2. `gu1_carrierEdge_block` has SIX components (`r, 1 ≤ r, ρ^r = inr v, GeoBlockInterior, outSlot = v.2.val, crossingPoint ∈ edgeSegment`);
   five patterns silently bind the last two as a pair.
3. `rw [h] at hmem` with `hmem := w.2.property : ↑w.2 ∈ ↑w.1` fails (the element's type depends on `w.1`): use `h ▸ w.2.property` typed at
   the target set, then `rw [hw] at hmem` on the element.
4. `linear_combination` does not unfold `contactWindowEdge M a (some true)` or `(G11_vef hx).2.val`; state `have h' : M - 1 = M := hedge` first.
5. `rw [lemma … _ rfl]` with a `_` for a membership-proof argument may find no occurrence; `exact congrArg (edgePoint Q e) (lemma … (mem_pair_left _ _) rfl)` works.
6. `gu2_edgePoint_sub` at parameter `0` leaves `(t - 0)`; `rw [sub_zero]` before `div_mul_cancel₀`.
7. `Set.mem_setOf_eq` is deprecated in this Mathlib (`Set.mem_ofPred_eq`); membership in `edgeSegment` unfolds by `rintro ⟨t, h0, h1, rfl⟩` directly.
8. `module` closes the affine identities `edgePoint Q e s − edgePoint P e s = (1 − s) • (Q e − P e) + s • (Q (e+1) − P (e+1))` after `simp only [edgePoint, edge]`.

Timeline: 05:40 UTC start (read author_response.md, D-AUTH-20260919 already recorded at AN L6520, the SITE/ASSEMBLY reports, the library);
05:52 scratch C1 clean (clearance); 05:55 first insertion, full compile 0 errors, 11 sorries; 06:05 scratch C2 clean (wall data);
06:08 second insertion, full compile 0 errors, 10 sorries; 06:10 `#print axioms`; 06:15 report.
