# W1_SKELETON_REPORT — unit U-M0 of the moves toolkit (Wave 1 skeleton)

U-M0 (subagent), 2026-09-15 19:15 UTC / 3:15pm ET.  Inputs: PLAN_FINAL.md (§1a, §4, §5, §6 R1),
Statements_FINAL.lean (frozen), DESIGN_B.md + Sketch_B.lean, SM/Smoothing.lean (§0', §4 `StrandKind`/`SpliceModel`,
§7-pre `ZMod.val` toolbox, §7a `mergedTuple`, §8 record bridge), SM/LinkMoves.lean (`IsDisc`, `Arc`, `IsArc`,
`ArcCover`, `OutsideMatch`, `Clean`, `MoveMatch`, `RIIData` :599), SM/LinkDiagram.lean (`Shadow`, `Generic`,
`Diagram`, `StrandMap`, `crossingParam`), SM/LinkRecord.lean (`Record`, `RecordIso`, `crossingOf`, `firstReturn`),
SM/LinkDiagramRecord.lean (`record`, `twin`, `overBit`, `nextVisit`, `cycNext_unique_on`), SM/MarkedProducts.lean
(`CrossKeep`, `restrictCrossings`, `RecordIso.ofOcc`), the four consumer sites (U_S7G.lean :565, U_R174.lean :926/:1086,
U_R176.lean :878/:915, U_R177.lean :1118/:1365).

## 0. Deliverables and checks

| item | result |
|---|---|
| `work/drafts/moves/Skeleton_W1.lean` | 1866 lines = `Statements_FINAL.lean` lines 1–136 (byte-identical) + the new section `## 1c` (lines 137–1578) + `Statements_FINAL.lean` lines 137–424 unchanged except the BODY of `exists_rii_deletion` (now PROVED) |
| compile (`cd work/lean && lake env lean ../drafts/moves/Skeleton_W1.lean`) | exit 0, **0 errors**, 1 cosmetic linter warning (`<;>` style at line 565), ≈ 12 s |
| `declaration uses sorry` | **33** = 4 frozen leaves that stay leaves (`BigonData.reducedRecord_counts`, `Record.restrictCrossings_switch`, `exists_bigonData_of_triangle`, `G11_core_sw`) + **29 sub-leaves** `m1_…m6_…` (list in §2) |
| `grep -c sorry Skeleton_W1.lean` | 34 = 33 bodies + the frozen header comment (line 17 "Every `sorry` is a LEAF …"); no other occurrence |
| statement byte-identity | `python3 check_W1_identity.py Statements_FINAL.lean Skeleton_W1.lean` → prefix (1–136) identical; all **37** declarations of Statements_FINAL have byte-identical statements in the skeleton; suffix identical except the body of `exists_rii_deletion` |
| `exists_rii_deletion` | **PROVED** (from `m1_exists_cut`, `m7_rii`, `reducedDiagram_componentCount`, `m6_recordIso`); the four frozen leaves above are untouched |
| `m7_riiData : RIIData C.U (B.reducedDiagram C) D` | **PROVED** as a structure instance from the U-M4/U-M5 sub-leaves and the proved end-point equalities |
| `m6_recordIso`, `m2_generic`, `crossingEquiv`, `visitEquiv`, `recordIso` | **PROVED / defined** from their sub-leaves (assembly done, nothing left for M7 there) |

Nothing under `work/lean` was written.

## 1. The API (section `## 1c` of Skeleton_W1.lean; namespace `SM.Link.BigonData`, `B : BigonData D`)

Conventions (fixed here, consumed by every unit): `M_m := P (a + m)` (`B.M m`), `B.strand m := ⟨i, a + m⟩`
(`m = 0` = `e_in`, `1 ≤ m < j` the run, `m = j` = `e_out`), `B.eIn = ⟨i, a⟩`, `B.eOut = ⟨i, a + j⟩` (syntactically the
frozen fields' strands), `B.Foreign u := u ≠ s ∧ ∀ m ≤ j, u ≠ strand m`; `B.k := (D.Γ.comp i).k`,
`B.k' := k − j + 2`.  Reduced labels with the rotation `M₀ = 0`: `Q 0 = M₀`, `Q 1 = M'`, `Q 2 = q`, `Q n = M_{j+n−2}`
(`3 ≤ n < k'`); kinds `cutIn` (label 0, `[M₀, M']`), `mid` (label 1, `[M', q]`), `cutOut` (label 2, `[q, M_{j+1}]`),
`old e` (labels ≥ 3 on component `i`; every strand of the other components).  **Every strand of component `i` is
addressed as `⟨B.i, (m : ZMod _)⟩` with `m : ℕ`, `m < k'`** (`strand_cases`) — this is what keeps the dependent
`ZMod ((reducedShadow).comp i).k` out of every proof (see Pitfalls).

### 1c.0 Site vocabulary (all PROVED)
`k, k', M, strand, eIn, eOut, Foreign`; `three_le_k, j_add_three_le_k, hk' (= hk on B.k, for omega), five_le_k',
three_le_k', k'_add_j`; `strand_zero, strand_j, M_zero (M 0 = tail e_in), M_succ_j (M (j+1) = head e_out),
tail_strand, head_strand, strand_inj (labels < k)`; `foreign_iff` (Foreign ↔ the four hypotheses of `clear`),
`clear_of_foreign`; `eIn_ne_eOut, s_ne_eIn, s_ne_eOut, y_ne_z, eIn_mem_y, s_mem_y, eOut_mem_z, s_mem_z`;
`param_of_edgePt_eq` (an `edgePt` parameter hitting a crossing point of its own strand is in `(0,1)`),
`ty_pos, ty_lt_one, tz_pos, tz_lt_one, tsy_pos, tsy_lt_one, tsz_pos, tsz_lt_one`; `M_zero_not_mem_K,
M_succ_j_not_mem_K`; `no_io_of_succ` (the `no_io` field of a `j = 1` site is automatic — for U-M7's triangle builder).

### 1c.1 `structure Cut` — U-M1's deliverable (the frozen interface between M1 and M2–M6)
Fields: `U, disc : IsDisc U, K_sub : K ⊆ interior U`; parameters `tp tM tq tin tout` with
`0 < tp < tM < ty`, `tz < tq < 1`, `0 < tin < min tsy tsz`, `max tsy tsz < tout < 1`; the six membership laws
`in_iff / in_int_iff` (`e_in ∩ U = [p, M₁]`, `∩ interior U = (p, M₁]`), `out_iff / out_int_iff`
(`[M_j, q]` / `[M_j, q)`), `s_iff / s_int_iff` (`[b_in, b_out]` / open); `clear : ∀ u, Foreign u → Disjoint (seg u) U`;
`q_off_in : det (dir e_in) (q − M') ≠ 0` (q ∉ line(e_in)); `mid_off_out : det (q − M') (dir e_out) ≠ 0`
(M' ∉ line(e_out)); `mid_side : ∀ θ ∈ [0,1], det (dir s) (M' + θ•(q − M') − tail s) ≠ 0` (`[M', q]` misses `line(s)`).
Points `C.p, C.M', C.q, C.sIn, C.sOut`.  PROVED consequences: `tM_pos, tM_lt_one, tp_lt_one, tq_pos, tin_lt_tout,
tin_lt_tsy/tsz, tsy/tsz_lt_tout, isClosed_U, mem_frontier_iff, p_mem, p_not_mem_interior, p_frontier` (same for
`q, sIn, sOut`), `M'_mem_interior, M_zero_not_mem, M_succ_j_not_mem, tail_s_not_mem, head_s_not_mem,
run_mem_interior`.  Sub-leaf: **`m1_exists_cut : Nonempty B.Cut`**.

### 1c.2 `inductive Kind (B)` = `old e | cutIn | mid | cutOut` (all PROVED)
`orig` (`old e ↦ e`, `cutIn, mid ↦ e_in`, `cutOut ↦ e_out`), `tail tM tq`, `dir tM tq`, `head`, `seg`, `interior`,
`pred`, `succ` (the reconnection tables), `Occurs κ := ∀ m ≤ j, κ ≠ old (strand m)`, `origParam`/`liftParam`
(`cutIn: θ·tM / θ/tM`, `cutOut: tq + θ(1−tq) / (θ−tq)/(1−tq)`, identity otherwise).  Laws: `occurs_*`,
`not_occurs_old_eIn/eOut`, `liftParam_origParam`, `origParam_liftParam`, `dir_eq_smul_orig` (κ ≠ mid, positive factor),
`tail_add_smul_dir` (κ ≠ mid: the point at parameter θ is `edgePt orig (origParam θ)`), `seg_old`, `interior_old`,
`head_eq_tail_succ`, `succ_pred`, `pred_succ` (occurring kinds).

### 1c.3 The reduced tuple / component / shadow (all PROVED)
`reducedTuple tM tq : LabelledTuple k'` (by `ZMod.val` case analysis), `reducedComp`, `reducedShadow tM tq :=
⟨D.Γ.c, D.Γ.hc, Function.update D.Γ.comp B.i reducedComp⟩` (SAME `c`, same indexing of components);
`reducedShadow_c (rfl), reducedShadow_comp_self, reducedShadow_comp_of_ne, reducedShadow_k_self, reducedShadow_k_of_ne`,
`PolyComp.P_natCast_eq_of_eq` (transport of nat-labelled vertices along `C = C'`), `natCast_k'_eq_zero`,
**`strand_cases` (`@[elab_as_elim]`)**, `reducedTuple_val/zero/one/two/of_ge/k'`, `tail_mk_i, dir_mk_i,
tail_mk_of_ne, dir_mk_of_ne`.

### 1c.4 The kind map and the index laws (all PROVED)
`kindIdx n`, `kind u` (classical `if`), `oldIdx b := ((b : ZMod k) − a − j).val + 2`, `strandOf : Kind → Strand`,
`orig u := (kind u).orig`; `kindIdx_zero/one/two/of_ge`, `kind_mk_i`, `kind_mk_of_ne`, **`tail_eq`** (`Γ'.tail u =
(kind u).tail`), **`dir_eq`**, `seg_eq`, `interior_eq`, `head_eq`, **`eval_eq`** (evaluation of a traversal point through
its kind), **`kind_occurs`**, `kindIdx_inj`, `kindIdx_old_fst`, **`kind_injective`**, `oldIdx_spec`,
**`kind_strandOf`** (occurring kinds are realised), `kind_surj`, `strandOf_kind`, `natCast_sub_one_eq`,
**`kind_pred`** (`kind ⟨u.1, u.2 − 1⟩ = (kind u).pred`), **`kind_succ`**, **`adjacent_iff_kind`**,
**`incidentTail_iff_kind`**, `strandOf_old_fst`.  These are the analogue of Smoothing's `SpliceModel` laws, proved
for the one concrete shadow (no abstract model layer: there is one construction, not two).

### 1c.5–1c.9 (section `Construction`, `C : B.Cut`, `C.shadow := reducedShadow C.tM C.tq`)
`m2_generic : C.shadow.Generic` (PROVED from `m2_regular, m2_tail_off, m2_transverse, m2_no_triple`);
`origCrossing C y'` (needs `m3_isCrossing_orig`), `orig_mem_origCrossing` (PROVED), `crossingEquiv : C.shadow.Crossing
≃ {x // x ≠ y ∧ x ≠ z}` (PROVED from `m3_*`), `overStrand'`, `overStrand'_mem`, `orig_overStrand'` (PROVED),
**`reducedDiagram C : Diagram`**, `reducedDiagram_Γ`, `reducedDiagram_componentCount (rfl)`,
`reducedDiagram_underStrand_orig`, **`m3_sign`** (PROVED from `m3_kind_ne_mid`: signs are inherited);
arcs `arcIn C : D.Γ.Arc` (`⟨i, (a, tp), (a+j, tq)⟩`), `arcS C` (`⟨s.1, (s.2, tin), (s.2, tout)⟩`), `arcIn' C`
(`⟨i, (0, tp/tM), (2, 0)⟩`), `sStrand C := strandOf (old s)`, `arcS' C`, `kind_sStrand` (PROVED), the eight end
evaluations `eval_arcIn_start/stop, eval_arcS_start/stop, eval_arcIn'_start/stop, eval_arcS'_start/stop` (PROVED:
`p, q, b_in, b_out` on both sides); `origPt` (U-M5's `φ` on traversal points), `orig_fst` (PROVED: `orig` keeps the
component); `origVisit C v`, `origVisit_fst`, `origVisit_injective` (PROVED), **`crossKeep_keep_iff`** (PROVED: the
retained occurrences of `reducedRecord` are exactly those at crossings `≠ y, z`), `origVisit_keep`, `visitEquiv :
C.shadow.Visit ≃ {w // CrossKeep keep w}` (PROVED from `m6_exists_origVisit`), `compOf_origVisit`, `twin_origVisit`,
`overBit_origVisit`, `sign_origVisit` (PROVED), `key v := if compOf v = i then rexB_rot k a.val (visitCoord v) else
visitCoord v` (the U-M6 key), **`recordIso C : RecordIso (reducedDiagram C).record B.reducedRecord`** (PROVED as a
structure from `m6_succ`, `twin_origVisit`, `overBit_origVisit`, `sign_origVisit`, `compOf_origVisit`),
`m6_recordIso`, **`m7_riiData`**, **`m7_rii : RII (reducedDiagram C) D`**.

## 2. Sub-leaves per unit (exact names; all `theorem … := by sorry`)

| unit | sub-leaves (Skeleton_W1.lean line) | consumes / notes |
|---|---|---|
| **U-M1** | `m1_exists_cut : Nonempty B.Cut` (463) | the gap construction; MUST also prove `q_off_in`, `mid_off_out`, `mid_side` — these need the SIDE LEMMA (the run vertices lie strictly on one side of `line(s)`, `M₀, M_{j+1}` strictly on the other; recommended internal lemmas `m1_side_run`, `m1_side_in`, `m1_side_out`, see §5) |
| **U-M2** | `m2_regular` (1093), `m2_tail_off` (1100), `m2_transverse` (1108), `m2_no_triple` (1115) | `m2_generic` is assembled; use `strand_cases`, `tail_eq/dir_eq/seg_eq/interior_eq`, `adjacent_iff_kind`, `incidentTail_iff_kind`, `kind_injective`, the `Cut` fields |
| **U-M3** | `m3_isCrossing_orig` (1129), `m3_kind_ne_mid` (1145), `m3_orig_injOn_crossing` (1151), `m3_origCrossing_ne_y` (1157), `m3_origCrossing_ne_z` (1160), `m3_crossingPoint_origCrossing` (1164), `m3_origCrossing_injective` (1169), `m3_exists_lift` (1175), `m3_crossingParam` (1250) | `crossingEquiv`, `m3_sign`, `reducedDiagram` are assembled |
| **U-M4** | `m4_arcIn_ne_arcS` (1336), `m4_arcIn'_ne_arcS'` (1340), `m4_arcCover` (1348), `m4_arcCover'` (1353), `m4_clean` (1359), `m4_clean'` (1363), `m4_inner_iff'` (1368), `m4_no_inner` (1373), `m4_sep_y` (1378), `m4_sep_z` (1381), `m4_same_over` (1385) | the end evaluations are PROVED; `ArcCover` includes `IsArc` and disjointness |
| **U-M5** | `m5_moveMatch : Nonempty (MoveMatch C.U (B.reducedDiagram C) D)` (1415) | `φ := origPt` on `Outside`, `ψ := crossingEquiv` (all crossings of `D'` are outer; the outer crossings of `D` are those `≠ y, z`), `e := Equiv.refl` with `orig_fst` |
| **U-M6** | `m6_exists_origVisit` (1457), `m6_key_lt_iff` (1516), `m6_succ` (1524) + the frozen record leaves `BigonData.reducedRecord_counts` (118), `Record.restrictCrossings_switch` (132) | `visitEquiv`, `recordIso`, `m6_recordIso` are assembled |
| **U-M7** | `exists_bigonData_of_triangle` (frozen leaf, 1613) | `m7_riiData`, `m7_rii`, `exists_rii_deletion` are PROVED; M7 = the triangle builder only (+ `no_io_of_succ` is ready) |
| Wave 3 | `G11_core_sw` (frozen leaf) | untouched |

Dependency order (unchanged from PLAN §5): M1 ∥ M2 ∥ M3 → M4 ∥ M5 ∥ M6 → M7.  Note M2 depends only on `Cut`
(not on M1's proof), so M1/M2/M3 run in parallel; M4 needs M3's `m3_crossingPoint_origCrossing` for `m4_no_inner`;
M5 needs M3; M6 needs M3 (`origVisit`) and its own key.

## 3. Pre-review of the frozen `BigonData` fields against the four sites — VERDICT: **no field must change**

| field | 110 (`j = 1`, `D = lift.switch x`, corner wall) | 174 (`m`-corner of `carrierDiagram.switch qx`) | 176 (`j`-corner of `carrierDiagram q'.switch y`) | 177 (6) (`j = 2` on `(smoothDiagram …).switch y`) |
|---|---|---|---|---|
| `i, a, j, hj` | `i = 0` (one component), `a` = edge into the wall vertex, `j = 1` | idem at `m` | idem at the `j`-corner | `i` = the component carrying `cutStartS → arcST → cutEndT`, `a` = label of `cutStartS` (`kI−1` mixed / `kI−dd−1` self), `j = 2` |
| `hk : j + 3 ≤ k` | `k ≥ 5` automatic: `s` is on the same component and non-adjacent to `e_in, e_out` | idem (one-component `geoPositiveLift`) | idem | **needs `k_B ≥ 5`** for the run component; `k_B = kI − dd + 2` (self) is `≥ 5` iff `dd ≤ kI − 3`, i.e. the piece of the corner polygon strictly between the two visits of `x` has ≥ 2 edges (true for a K3 site: the outer letters between the `x`-visits; a `dd = kI − 2` polygon would be a curl at `x`).  The consumer must discharge it; see §4 for the fallback |
| `s, y, z, hy, hz` | `s` = the remote edge, `y = x`, `z` = the crossing on `(M, M+1)` — `hy/hz` from the wall data | `s` = the `ℓ₂` strand through `w(ℓ₂), x(ℓ₂)`; the two crossings of R-LOC (2) | `s` = the third triangle edge, `u', v'` | `s` = the `g`-strand; `y` on `cutStartS`, `z` on `cutEndT` (`Smoothing.liftCrossing` of the original `y, z`; the `StrandKind` API gives their strands) |
| `run_free` | vacuous (`1 ≤ m < 1`) | vacuous | vacuous | the run edge is `arcST`: `Smoothing.kind_ne_arc_of_mem` (no crossing uses an arc) |
| `no_io` | **automatic**: `no_io_of_succ` (PROVED here) | idem | idem | `cutStartS` and `cutEndT` are pieces of `e, f`, which meet only at `x`, removed by the cut (`u3_disj_cutStartS_cutEndT`) |
| `same_over` | after switching the positive `x` the remote strand is over at both (`switch_overStrand_self`, `positiveLift_isPositive`, sign table sm-4:614-618) | after switching `qx` | after switching `y` | after switching `y` on the smoothing output (the printed RII pair) |
| `ty tz tsy tsz + specs` | `D.crossingParam y (mem)` + `crossingParam_spec` (rewrite `edgePoint … = edgePt`) | idem | idem | idem |
| `K, K_convex, K_compact` | `convexHull ℝ {pt y, M, pt z}` (`Set.Finite.isCompact_convexHull`, `convex_convexHull`) | idem | idem | `convexHull ℝ {pt y, s⁻, t⁺, pt z}` |
| `run_mem` | `M₁ ∈ K` (a vertex of the hull) | idem | idem | `s⁻, t⁺` are vertices of the hull |
| `in_iff, out_iff, s_iff` | barycentric side lemmas of a triangle whose sides are the three local segments — U-M7's `exists_bigonData_of_triangle` (G11 affine-basis toolkit 9093–9259) | via the same builder | via the same builder | the quadrilateral `K = Δ` with the corner at `x` cut: `K ∩ line(e) = [y, s⁻]`, `K ∩ line(f) = [t⁺, z]`, `K ∩ g = [y, z]` — consumer's own barycentric work (≈ the triangle lemmas + one cut) |
| `clear` (closed form) | U110-A's wall data "no other edge or vertex meets the contact triangle" in the `G11_Config.clear_edge` shape (frontier clause + vertex clause → closed set) | R-LOC (2)–(4) via `GT_Endpoint.adj1..3` and G11 Unit A's toolkit | idem | old kinds: the configuration's triangle clearance; the other new kinds `cutEndS, cutStartT, arcTS` lie in the OPPOSITE cone at `x` (`x + λ e_s − μ e_t`, `λ, μ ≥ 0`, not both 0) while `K ⊂ conv{x, y, z}` lies in the cone `x − λ e_s + μ e_t`: disjoint — the cone-geometry lemma is the consumer's |

Redundancy: `run_mem` is derivable for `m = 1` and `m = j` from `in_iff`/`out_iff` but not for `1 < m < j`; keep.
`K_compact` is needed (`ρ₀ > 0`, `IsCompact.cthickening`).  No field is impossible.  Two observations for the
executor (no change proposed): (i) `hk : j + 3 ≤ k` is stronger than the construction needs (`j + 2 ≤ k` gives
`k' ≥ 4` and the same kind tables; `j + 1 = k` would change `pred cutIn`); it buys uniform tables (`pred cutIn = old
(a − 1)` and `succ cutOut = old (a + j + 1)` distinct old strands) and is satisfied at all four sites — only 177 (6)
has to prove it (row above).  (ii) `clear` quantifies over CLOSED `K`; for the triangle sites this is
`G11_Config.clear_edge`'s form (PLAN §3 last bullet), derived from the frontier + vertex clauses.

## 4. Pitfalls found while building the skeleton (read before starting any unit)

1. **Dependent `ZMod` moduli.**  `(reducedShadow).comp i` is `Function.update … B.i reducedComp` — equal to
   `reducedComp` only propositionally (`reducedShadow_comp_self`), so `n : ZMod ((reducedShadow).comp B.i).k` cannot be
   rewritten to `ZMod k'` (`rw` motive errors on `n.val`, `↑m`).  The skeleton's discipline: address every strand of
   component `i` as `⟨B.i, (m : ZMod _)⟩` with `m : ℕ`, `m < k'` (`strand_cases`, `tail_mk_i`, `dir_mk_i`,
   `kind_mk_i`), transport vertices with `PolyComp.P_natCast_eq_of_eq`, compare labels with
   `Smoothing.nat_eq_of_zcast_eq`, and use `lt_of_lt_of_eq (ZMod.val_lt n) (reducedShadow_k_self …)` instead of
   `rw … at hn`.  `natCast_sub_one_eq (hN : N = N')` keeps the modulus `N` of the strand type and its value `N'` apart.
2. **`if` on `u.1 = B.i`.**  `u.1 : Fin (reducedShadow).c` versus `B.i : Fin D.Γ.c` are defeq but not syntactically
   equal at instance transparency: `rw [ite_eq_left/right]` fails on `kind`'s `if`; use `split_ifs` (done in
   `kind_mk_i`, `kind_mk_of_ne`).  `kind` is defined with `open scoped Classical in`.
3. **`omega` and the abbrev `B.k`.**  `B.hk : j + 3 ≤ (D.Γ.comp i).k` and `B.k` are different atoms for `omega`; use
   `B.hk'` / `B.three_le_k` / `B.k'_add_j` (stated on `B.k`).
4. **Toolchain renames** (Lean 4.34.0-rc2 / current Mathlib): `if_pos/if_neg` → `ite_eq_left/ite_eq_right`
   (deprecated, still work), `Finset.pair_eq_singleton`, `ZMod.natCast_eq_zero_iff (a b) : (a : ZMod b) = 0 ↔ b ∣ a`,
   `Nat.cast_pred`, `push_neg` deprecated (use `not_lt.mp`/`push Not`), `Set.mem_setOf_eq` deprecated (use `show`).
5. **`strand_cases` needs `@[elab_as_elim]`**; call it as `refine B.strand_cases tM tq ?_ ?_ u` (for two strands
   nest the refines, as in `kind_injective`).
6. **`nomatch h` inside `first | …`** is not recoverable; use `cases h` on constructor-mismatched equalities.
7. **Direction of `RIIData`.**  `RIIData U D' D`: the FIRST diagram is crossing-free (`a, b`, `no_inner`), the SECOND
   carries `x₁ x₂` — so `RIIData C.U (reducedDiagram C) D`, `a := arcIn'`, `a' := arcIn`, and `RII (reducedDiagram) D`
   is `⟨U, Or.inl ⟨…⟩⟩`.  `a_start : D.Γ.eval a'.startPt = D'.Γ.eval a.startPt` reads `original = reduced`.
8. **`mid ∩ s = ∅` is not free.**  It needs the side lemma (run strictly on one side of `line(s)`), which also gives
   `q ∉ line(e_in)`; M1 owns it (`Cut.mid_side`, `Cut.q_off_in`).  `M' ∉ line(e_out)` is a CHOICE of `t_M` (a line
   meets `(p, y)` in at most one point unless it contains `e_in`, which forces `y = z`).
9. **`Kind.orig mid = e_in` is junk**; every use of `orig` on a crossing strand goes through `m3_kind_ne_mid`.
10. **Load**: ≈ 12 s per compile at load 10 on 8 cores; iterate on scratch files importing `RProof.GenericTransport`.

## 5. Recommended unit prompts (Wave 1)

Common preamble for every unit: "File `work/drafts/moves/Skeleton_W1.lean` (compile:
`cd work/lean && lake env lean ../drafts/moves/Skeleton_W1.lean`, 0 errors, 33 `sorry` declarations).  Never change a
statement (`python3 ../drafts/moves/check_W1_identity.py Statements_FINAL.lean Skeleton_W1.lean` must still pass;
also `grep -c sorry` must only decrease).  Write your proofs in a copy `Skeleton_W1_<unit>.lean` (or in scratch files
importing the same modules and copying the needed declarations), replacing exactly your unit's `sorry`s; report the
`#print axioms` of each closed sub-leaf (standard only).  Read §1c's header comment and §4 of W1_SKELETON_REPORT.md
(pitfalls) first.  Reassessment rule: two failed attempts / 60 min on one sub-leaf → stop and report."

* **U-M1 (`m1_exists_cut`, ≈ 900–1200 lines).**  (a) Side lemma: `side P := det (dir s) (P − tail s)`; prove
  `line(s) ∩ K = [y, z]` (from `s_iff`, `tsy, tsz ∈ (0,1)`), that no run edge meets `line(s)` (run edges ⊆ `K` by
  convexity, meet `s` only at a crossing, `run_free`), hence all `M_m` (`1 ≤ m ≤ j`) have one strict sign, and `M₀`,
  `M_{j+1}`, `edgePt e_in t` (`t < ty`), `edgePt e_out t` (`t > tz`) the opposite one (`side` is affine along an edge
  and vanishes at `ty`/`tz`).  (b) `F := ⋃_{foreign} seg u ∪ {M₀, M_{j+1}, tail s, head s}` compact, disjoint from
  `K` (`clear_of_foreign`, `M_zero_not_mem_K`, `M_succ_j_not_mem_K`, `s_iff` at 0, 1); `ρ₀ := infDist`-gap `> 0`
  (`IsCompact.exists_infDist_eq_dist` or `Metric.infDist_pos_iff`); `U := Metric.cthickening (ρ₀/2) K`
  (`Convex.cthickening`, `IsCompact.cthickening`, `Metric.self_subset_cthickening`, `K ⊆ interior U` by
  `Metric.ball_subset_interior`-type arguments on the sup metric); `Cut.clear`.  (c) `tp := sInf {t ∈ [0,1] | edgePt e_in t ∈ U}`
  etc.; the closed iff's from convexity of `U` along a segment; the interior iff's from
  `Convex.openSegment_closure_interior_subset_interior` (M₁ ∈ interior) and the frontier argument at `tp`.  (d) choose
  `tM ∈ (tp, ty)` off `line(e_out)`; `q_off_in` and `mid_side` from (a).  Deliver `⟨C⟩`.
* **U-M2 (`m2_regular`, `m2_tail_off`, `m2_transverse`, `m2_no_triple`, ≈ 1200 lines).**  Work by `strand_cases`
  and the kind laws; the case tables are in the docstrings of the four sub-leaves.  Key inputs: `Cut.clear` (foreign
  edges miss `U`; `cutIn, mid, cutOut ⊆ U` by `Kind.tail_add_smul_dir`/convexity), `Cut.q_off_in`, `Cut.mid_off_out`,
  `Cut.mid_side`, `Generic.seg_inter_seg_eq` (`e_in ∩ s = {y}`), `D.generic.*` pulled back through `orig` for old
  pairs (`adjacent_iff_kind`, `Kind.dir_eq_smul_orig`, `Smoothing.det_smul_smul`, `regularPair_smul_pos`,
  `regularPair_of_det_ne_zero`).
* **U-M3 (nine sub-leaves, ≈ 800 lines).**  Follow Smoothing §6b (`isCrossing_orig` :3171, `origCrossing_injective`
  :3262, `liftCrossing` :3424, `crossingParam_toDiagram` :3664) with kinds `old/cutIn/cutOut` in place of the seven.
  `m3_kind_ne_mid`: a strand of a crossing has a common point with a NON-adjacent strand; `mid`'s only common points
  are its ends `M'`, `q` with `cutIn`, `cutOut` (adjacent) — needs `Cut.mid_side`, `Cut.clear`, the two `det` fields.
  `m3_exists_lift`: for `x ≠ y, z` both strands are foreign / `s` / `e_in` at `t < tp` / `e_out` at `t > tq`; lift by
  `strandOf (old e)`, `⟨i, 0⟩`, `⟨i, 2⟩` and `Kind.tail_add_smul_dir`.
* **U-M4 (eleven sub-leaves, ≈ 1500–2200 lines; the R1 risk).**  Template: Smoothing §5 `arcS/arcT` (:2080–2230,
  `arc_mem_iff_of_same_edge`, `arc_inner_iff_of_same_edge` :1966/1984, `traversalBetween_span_two` :1887) and §6d
  (:3685–4310).  `m4_arcCover.mem_iff` is the big classification: a traversal point on component `i` with label
  `a + m`; on other components only `s` matters (`Cut.clear`).  For `D'` use `eval_eq` + `kind_mk_i` per label
  `0, 1, 2, ≥ 3`.  `Clean.frontier_injOn`: the frontier points of the trace are exactly `p, q, b_in, b_out`
  (`Cut.*_frontier`, the interior iff's), none a vertex or double point.  If the general-`j` `mem_iff` stalls (two
  attempts / 60 min), apply PLAN §6 R1: freeze `j ∈ {1, 2}` as two instances.
* **U-M5 (`m5_moveMatch`, ≈ 800 lines).**  Template: Smoothing §6e (:4313–4600: `origPt`, `origPt_bijective`,
  `outsideEquiv`, `outsideEquiv_dir_pos`, `dir_strandBefore_origPt`, `outerEquiv`, `outsideEquiv_outerOverPt`).  Here
  `φ` goes `D'.Outside → D.Outside` directly (`origPt`); `dir_pos_before` at `M₀` and `M_{j+1}` uses `kind_pred`
  (`strandBefore`); `ψ := crossingEquiv` composed with "outer ↔ `≠ y, z`" (`m4_inner_iff'`, `m4_no_inner`); `over_eq`
  via `orig_overStrand'` + `m3_crossingParam` + `Kind.liftParam_origParam`.
* **U-M6 (`m6_exists_origVisit`, `m6_key_lt_iff`, `m6_succ` + the two frozen record leaves, ≈ 1500–2000 lines).**
  Template: Smoothing §8 (`key` :6072, `key_nextVisit_no_between` :6174, `succ_of_coord` :6835, `lt_iff_of_blocks`
  :7078, `cyclicOffset_val_add` :7048, `rexB_rot_of_lt/le`).  Blocks on component `i` in the rotated coordinate
  `r = rexB_rot k a.val (visitCoord)`: `[0, tp)` ↦ `r / tM` (cutIn), `[j + tq, j + 1)` ↦ `2 + (r − j − tq)/(1 − tq)`
  (cutOut), `[j + 1, k)` ↦ `r − (j − 2)` (old); retained occurrences of `e_in` have `t < tp` and of `e_out` `t > tq`
  (`Cut.clear` + the iff's).  `m6_succ`: `cycNext_unique_on` on `D'.visitCoord` (per component) against
  `firstReturn_no_between D.visitSucc (CrossKeep keep) key` and `nextVisit_no_between`; `rexB_rot` preserves
  `cycBetween`.  Then `reducedRecord_counts` (`Record.crossingCount`/`writhe` of `restrictCrossings`: the retained
  occurrence set is `M ∖ {4 occurrences}`, `Fintype.card_subtype_compl`) and `Record.restrictCrossings_switch`
  (`RecordIso.mk` with `Equiv.refl` on `{v // CrossKeep S v}`; `firstReturn` is literally the same permutation since
  `switch` keeps `succ`; bits/signs by `if v ∈ {x, pair x}` on both sides).
* **U-M7 (`exists_bigonData_of_triangle`, ≈ 600 lines).**  Build the `BigonData` with `j = 1`, `K := convexHull ℝ
  {pt y, M₁, pt z}`, `no_io := no_io_of_succ`, `run_free` vacuous, `run_mem` (vertex of the hull), `ty tz tsy tsz :=
  crossingParam`, and the three side lemmas `in_iff/out_iff/s_iff` by barycentric coordinates (G11's affine-basis
  toolkit GenericTransport 9093–9259: `y, M₁, z` affinely independent since `z ∉ line(e_in)` — `e_in ∩ s = {y}` and
  `z ≠ y`); `clear` is the hypothesis.  Nothing else remains for M7.

## 6. What the executor must decide

1. Accept the `Cut` interface as frozen (it is the only new interface between units; every M2–M6 statement is
   phrased on `C : B.Cut`).  Adding a field later costs M1 only; removing one costs its consumers.
2. Wave 2 may start now on `exists_bigonData_of_triangle`'s STATEMENT (unchanged) — the sites do not touch `Cut`.
3. 177 (6): the consumer must prove `k_B ≥ 5` (§3, `hk`); if any real site had `k_B = 4` the frozen `hk` would
   have to become `j + 2 ≤ k` (kind tables unchanged; `five_le_k'` → `four_le_k'` in ≈ 6 proofs).  Not expected.
4. The 29 sub-leaves are the whole remaining Wave-1 content; their docstrings carry the proof sketches.
