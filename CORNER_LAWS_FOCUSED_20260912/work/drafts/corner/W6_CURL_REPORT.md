# W6_CURL_REPORT.md — unit W6-CURL (wave 6, prefix `w6k_`), 2026-09-19

File: `work/drafts/corner/W6_CURL.lean` = `W5_Assembled.lean` (25,237 lines) with ONE insertion of 357 lines
(`diff W5_Assembled.lean W6_CURL.lean | grep "^[0-9]"` = `24298a24299,24655`), immediately before the
`include hloc ht in` + docstring of `w5b_box_curlData` (W5 line 24299 → W6 line 24656; the theorem line W5 24304 → W6 24661), inside `section W5BRData` of
`section W4Bigon`.  No statement, name or docstring of `W5_Assembled.lean` is changed; NO sorry body is replaced
(`grep -c sorry`: 22 before, 22 after).  Full compile: 0 errors (see §5).

## 0. In one paragraph

**The curl component is PROVED in the corrected form `w6k_box_curlData`** — the statement of `w5b_box_curlData`
(same conclusion `w5b_CurlData hn g h h₁ t T₀ hS₁ DA i`, same record hypothesis `hrec`) with the six radius facts of
the wall added: `hr0 : 0 < r`, `hr1 : r < 1`, `hr : g.center M = edgePoint g.center a r`, `hη : 0 < η`,
`hηr : 4 * η < r`, `hηr1 : 4 * η < 1 - r`.  `#print axioms w6k_box_curlData` =
`[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]` — no `sorryAx`.
`w5b_box_curlData` AS STATED (hypotheses `hloc : s7a2_IntervalLocal hn g M a r η δ`, `ht : t.val < δ` only) keeps its
`sorry` (rule 1: I may not change its statement; rule 3: it is not FALSE, but its hypotheses do not reach any proved
lemma about `P₂(t)` — §2).  The consumer `w5b_noninterlacingData` (W6 line 24695) has all six facts in scope; the swap
is the one-token edit of §3.

## 1. What is proved (all sorry-free; `w6k_` block, W6 lines 24299-24655)

Part A — a curl at the RECORD level (`section W6CurlRecord`, no geometry, no interlacement graph, no `BlockSupply`):
- `w6k_gap_curl ρ h1 S₂ v hv hS₂ hadj`: on a one-circle record with `succ v = τ v` and `S₂` the chord of `v`
  (`∀ k, CrossKeep S₂ k → k = v ∨ k = τ v`), every other occurrence lies in the gap after `τ v`
  (`ArcBetween (τ v) w ((restrictCrossings S₂).succ ⟨τ v, _⟩).1`; positions `steps (τ v) · < |M| − 1 = steps (τ v) v`).
- `w6k_gap_rest ρ h1 S₁ S₂ hS hdisj v hv hS₂ hadj h3` (`2 < |M|`): from `u₁ = succ⁻¹ v ∈ S₁` the two curl occurrences
  (positions `1`, `2`) precede every other `S₁`-occurrence (positions `≥ 3`) — the gap of the complementary block.
- `w6k_P_eq_one_of_two_occ ρ h1 hM D hD`: a diagram whose record is one-circle with `|M| = 2` has `P D = 1`
  (`card_visit_eq_two_mul`, `Fintype.card_eq_one_iff`, `single_crossing.one_crossing`).
- `w6k_card_restrict_pair`: `|(restrictCrossings S₂).M| = 2`.
- **`w6k_P_eq_of_curl ρ h1 hreal S₁ S₂ hS hdisj v hv hS₂ hadj h3 D hD D' hD' : P D = P D'`** for `D` with record `ρ`
  and `D'` with record `ρ.restrictCrossings S₁`: `exists_iso_joinRecord_of_gaps` at the two gaps gives
  `restrictCrossings univ ≅ joinRecord μ₁ μ₂`; both restrictions are realizable
  (`isRealizable_restrictCrossings_of_gapContiguous`); the marks are printed as marked intervals
  (`exists_markedInterval_of_mark`), `D` is the clean marked join (`IsCleanMarkedJoin` is record-level),
  `SM.join.join_value` gives `P D = P D' · P J₂`, and `P J₂ = 1`.  Axioms: `[propext, Classical.choice, Quot.sound, lp_lm]`.
- `w6k_card_visits T : |{u : Visit P // u.1 ∈ T}| = 2 |T|`; `w6k_gaussRecord_writhe hc T : (gaussRecord hc T).writhe = |T|`.

Part B — the curl component (`section W6Curl`, in the `W5BRData` context, with the six radius variables):
- `w6k_X hn g h t X₁ := insert y (img ι₁ X₁)` (abbrev), `w6k_y_not_mem_img`: `y ∉ img ι₁ X₁`
  (`s7b_firstCrossingQ_not_affected`; `y = {a, M}` is contact-affected).
- **`w6k_curl_adjacent`** (needs `w5b_hd`): in `gaussRecord (cg P₂) (w6k_X X₁)` there is an occurrence `v` with
  `v.1 = y_a` and `succ v = pair v`.  Proof: in the `κ`-coordinate from `μ_M` (BR Part 2b, `w5b_Lκ` = the `κ`-sorted
  Gauss list, `w5b_Lκ_sorted`, `w5b_Lκ_rot`, `w5b_mem_Lκ`): `κ(y_ℓ) < η` (`s7o_kappa_yl_bounds`),
  `3η < κ(ι₁ c) < D + r − 3η` (`s7p_kappa_first_bounds`), `D + r − η < κ(y_a)` (`s7p_kappa_va_bounds`), with `D ≥ 2`
  (`s7o_bounds`); so `w5b_sorted_split` at `u = y_ℓ`, `z = y_a` has `B = []`, i.e. `gaussList ~r (y_ℓ :: A ++ [y_a])`,
  a `w5b_GaussSplit` at `y_ℓ` with `visitTwin y_ℓ = y_a` (`s7e_twin_vl`); `GaussSplit.succ_val` + `w5b_next_split_y` +
  `List.next_singleton` give `succ(y_a) = y_ℓ = pair(y_a)`.  Axioms: standard only.
- **`w6k_box_curlData hn g h h₁ t T₀ hloc ht hS₁ hr0 hr1 hr hη hηr hηr1 DA i hrec : w5b_CurlData hn g h h₁ t T₀ hS₁ DA i`**:
  `value`: `S₂ := {p | label p = y}`, `S₁ := {p | label p ∈ img ι₁ X₁}` (`CB.label_mem`, `CB.label_crossingOf`; `hS₂` from
  `w5b_y_visits`); if `X₁ = ∅` both sides are `1` (`w6k_P_eq_one_of_two_occ`, `P_circle` +
  `positiveLift_isCrossingFreeCircle`); else `w6k_P_eq_of_curl` with `D' = positiveLift L₁ hS₁`, whose record is
  `ρ.restrictCrossings S₁` through KL1 `CB.positiveLiftRecordIso`, BR's `w5b_gaussIso₁` and KL3
  `CB.gaussRecord_restrict_iso`; then `cornerHomfly = homfly (positiveLift …)` by `P_eq_homfly`.
  `writhe`: `record_writhe`, `RecordIso.writhe_eq`, `w6k_gaussRecord_writhe`, `|insert y S| = |X₁| + 1`
  (`card_insert_of_notMem`, `card_map`), `carrierCrossingCount = |X₁|` (rfl).

Route change against the W5_ASSEMBLY_REPORT §6 plan (BLOCK's `s7k_curl_component_value` / `_writhe` with a
`BlockSupply` for the curl record and a block correspondence `e` to `L₁`'s blocks; cb:products): NOT used.  A
`BlockSupply` needs an actual diagram per interlacement block of `gaussRecord (insert y S)` and a block bijection
transported through two record isomorphisms; the two-block join at the curl's gaps (Part A) needs none of it and is
what `SM.blocks.product` itself is built from.  `s7k_curl_component_*`, `cb_products`, `interlacementGraph` are not
referenced.

## 2. The remaining sorry and why the box is left AS STATED (rule 3 disclosure)

`w5b_box_curlData` (W6 line 24661; W5 24304) keeps `sorry`.  Its only geometric hypotheses are
`hloc : s7a2_IntervalLocal hn g M a r η δ` (`∀ u, |u| < δ → VertexLocalData hn g.center (g.curve u) M a r η`) and
`ht : t.val < δ`, for ARBITRARY `r η δ`.  Every proved lemma about the visits of `P₂(t)` that the proof needs —
BR's `w5b_hd : s7p_SideData M a g.center P₂ r η` (fields `hr hr0 hr1 hη hηr hηr1` are part of the structure), hence
`s7o_kappa_yl_bounds`, `s7p_kappa_va_bounds`, `s7p_kappa_first_bounds`, `w5b_Lκ_*`, `w5b_y_visits`, and BR's
`w5b_gaussIso₁` (through `w5b_hord₁`/`w5b_hbit₁`, which take `hr hr0`) — needs the radius facts for `hloc`'s own
`r η`.  They are NOT derivable from `hloc`: `VertexLocalData.windows` at `u = 0` gives only
`|edgeParameter P a M − r| < η` (`ContactParameterWindows`, third clause), so `hloc`'s `r` is `η`-close to the true
`r*` of `h.1.2.2.2.1`, not equal, and `4η < r`, `4η < 1 − r` are not implied at all.  The true `r*` cannot be
substituted either: `hloc` is for `(r, η)`, not for `(r*, η')`.  The statement is presumably TRUE (the conclusion does
not mention `r η δ`), but proving it from `hloc ht` alone would mean re-deriving the `κ`-windows of `P₂(t)` from
`VertexLocalData` without `s7p_SideData` — the SPLIT/B3 geometry over again.  Method audit (rule "two attempts →
change method"): attempt 1 (read `w5b_gaussIso₁`'s dependencies to see whether `hr hr0` decouple from `hloc`: they do
for the ISOMORPHISM, all uses are `s7r_first_order`/`s7fb_edge_first_smul` with a free `r`, so a `w6k_gaussIso₁` at
`r*` is possible), attempt 2 (the ADJACENCY: every `κ` lemma takes `hd`, and `s7p_SideData (r*, η')` needs
`ContactParameterWindows` for `(r*, η')`, which `hloc` does not give — `3η' < |param − center(r*)|` fails for the
`2η`-window one gets by the triangle inequality).  Decision: corrected form with the six facts (which BR's own
deliverables and the glue `w5_branchData` already carry at exactly this `r η`), per rule 3.

Exact differences `w6k_box_curlData` vs `w5b_box_curlData`: SAME conclusion, SAME `hrec`, SAME `hS₁`; ADDED
`(hr0 : 0 < r) (hr1 : r < 1) (hr : g.center M = edgePoint g.center a r) (hη : 0 < η) (hηr : 4 * η < r)
(hηr1 : 4 * η < 1 - r)` for the `r η` of `hloc`.  Binder order (checked with `#check @SM.w6k_box_curlData`):
`hn g h h₁ t T₀ hloc ht hS₁ hr0 hr1 hr hη hηr hηr1 DA i hrec`.

## 3. For the assembler (W6-GLUE): the one-token swap

`w5b_noninterlacingData` (W6 line 24695; variables `hr0 hr1 hr hη hηr hηr1` are in its `include`) has the line
```
  have hcurl := w5b_box_curlData hn g h h₁ t T₀ hloc ht hS₁ DA i hc₁
```
Replace it by
```
  have hcurl := w6k_box_curlData hn g h h₁ t T₀ hloc ht hS₁ hr0 hr1 hr hη hηr hηr1 DA i hc₁
```
(`w6k_box_curlData` is declared before it, W6 line 24571).  Then `w5b_box_curlData` is on no proved path (dead,
like `w5r_box_branch` / `w5b_box_returnedData`) and the curl is no longer a `sorryAx` source of B2'.  Not done here:
rule 1 allows only the box's own sorry body to be replaced.

## 4. Black boxes consumed: none new.  Interfaces used (all PROVED in the file / library)

BR: `w5b_hd`, `w5b_hcy`, `w5b_L₁`, `w5b_ι₁`, `w5b_gaussIso₁`, `w5b_y_visits`, `w5b_Lκ`, `w5b_Lκ_rot`, `w5b_Lκ_sorted`,
`w5b_mem_Lκ`, `w5b_sorted_split`, `w5b_GaussSplit` (`.w₀`, `.succ_val`, `.pair_w₀_val`, `.nodup`), `w5b_next_split_y`,
`w5b_gauss_pair_val`.  SPLIT/B3: `s7p_SideData`, `s7p_kappa`, `s7p_kappa_first_bounds`, `s7p_kappa_va_bounds`,
`s7o_kappa_yl_bounds`, `s7o_bounds`.  F/E: `s7f_y`, `s7f_hP₂`, `s7f_hQC`, `s7e_va/vl`, `s7e_vl_fst`, `s7e_twin_va/vl`,
`s7e_vl_ne_va`, `s7e_a_ne_leg`.  U110-B: `s7b_img`, `s7b_mem_img`, `s7b_firstCrossingQ_injective`,
`s7b_firstCrossingQ_not_affected`.  Library: `CB.gaussRecord`, `CB.gaussRecord_componentCount`, `CB.label`,
`CB.label_mem`, `CB.label_crossingOf`, `CB.gaussRecord_restrict_iso` (KL3), `CB.positiveLiftRecordIso` (KL1),
`CB.kl3_next_congr`; `Record.arcBetween_restrictCrossings_succ_iff`, `steps_eq_iff`, `steps_lt_card`, `steps_ne_of_ne`,
`steps_eq_zero_iff`, `steps_self`, `pow_card_apply`, `card_M_pos`, `crossKeep_pair_iff`, `crossKeep_or_of_union`,
`not_crossKeep_right_of_left`, `restrictCrossings_univ_iso`, `exists_iso_joinRecord_of_gaps`,
`componentCount_restrictCrossings`, `two_mul_writhe`; `isRealizable_restrictCrossings_of_gapContiguous`,
`IsRealizable.of_iso`, `exists_markedInterval_of_mark`, `MarkedDiagram`, `IsCleanMarkedJoin`, `SM.join.join_value`,
`SM.single_crossing.one_crossing`, `Diagram.card_visit_eq_two_mul`, `Diagram.record_componentCount`,
`Diagram.record_writhe`, `RecordIso.{card_M_eq, componentCount_eq, writhe_eq, joinRecord}`, `Mark.map`,
`P_eq_homfly`, `P_circle`, `positiveLift_isCrossingFreeCircle`, `visits_per_crossing`, `cornerHomfly` (unfolded).

## 5. Verification record

- Prefix olean: `<scratchpad>/w6curl/pfx/W6Prefix.lean` = W5 lines 1-24298 + closers (`end W5BRData`, `end W4Bigon`,
  `end VertexEdge`, `end`, `end SM`), built with `lean -o` from inside `pfx/` (49 s; `lean.sh` = w5asm's explicit
  `LEAN_PATH` wrapper with `w6curl/pfx` appended); pieces `P1.lean` (Part A) and `P2.lean` (Part B) compiled as
  `T2.lean` = header + P1 + the `W4Bigon`/`W5BRData` variable context + P2 + closers, 11 s per probe, 0 errors,
  0 warnings.  Three compile-fix rounds, all mechanical: `rw … ; exact` after a `rw` that already closed the goal;
  `Fintype.card` instance mismatch between a record's `mFin` and `Subtype.fintype` (fixed via `Fintype.card_eq_nat_card`);
  `w5b_y_visits` takes `hd`, not `hn hd`; `w5b_gaussIso₁`'s binder order is `hloc ht hr0 hr`; a `set`-abbreviated
  `s7b_img` needed the `set` equation before `Finset.card_map`.
- `#print axioms` (scratch `AX.lean`, not in the unit file): `SM.w6k_box_curlData`:
  `[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]`; `SM.w6k_P_eq_of_curl`:
  `[propext, Classical.choice, Quot.sound, SM.lp_lm]`; `SM.w6k_curl_adjacent`: `[propext, Classical.choice, Quot.sound]`.
- Full file: `lake env lean ../drafts/corner/W6_CURL.lean` — 0 errors, 10 warnings, all `declaration uses 'sorry'`
  (the same 10 as `W5_Assembled.lean`; textual `grep -c sorry` 22 → 22), 43 s.  `grep -c '^#'` = 0.
- `diff W5_Assembled.lean W6_CURL.lean | grep "^[0-9]"` = `24298a24299,24655` (one insertion, no body replacement).

## 6. Honest state

Closed: none of the four wave-6 boxes by the letter (`w5b_box_curlData`'s sorry stands).  Delivered: the curl box in
the corrected form `w6k_box_curlData` (sorry-free on the registered axioms), whose only difference is the six radius
facts already carried by its consumer; after the §3 swap the noninterlacing deliverable `w5b_noninterlacingData`
depends on `w5b_box_noninterlacingTurnData` (W6-ROT/W6-COR) only.  Open for the other units, unchanged:
`w5r_box_corners`, `w5b_box_interlacingTurnData`, `w5b_box_noninterlacingTurnData`.
