# W3C_SPLITC_REPORT — unit SPLITC (prefix `w3cc_`): `esc_FullSplitData.outer_alternative` and `.uniform`

Prover subagent, 2026-09-15 23:19–23:50 UTC / 7:19–7:50pm ET (bounded window, hard stop 01:45 UTC; audit A-177-2).
File: `work/drafts/moves/W3C_SPLITC.lean` (12803 lines) = `W3B_Assembled.lean` (11851 lines) with ONE pure
insertion: `diff W3B_Assembled.lean W3C_SPLITC.lean` = `10675a10676,11627` (952 lines, `section W3CC_SplitC`,
placed inside `section W3BI_REAL` immediately after the black-box leaf `w3bi_esc_outer_data`).  No frozen
statement, name, docstring or definition was touched; no other unit's `sorry` was touched; the leaf
`w3bi_esc_outer_data` is left as it was (its `sorry` is shared with SPLITA/SPLITB/KNOT, not this unit's to close).

## Compile and checks (mandated)

* `cd work/lean && lake env lean ../drafts/moves/W3C_SPLITC.lean` → exit 0, **0 errors**, 36 s warm.  Exactly 8
  `declaration uses sorry` warnings = the 7 of the base file (at lines 4093, 9237, 9267, 10673, 11729, 11749,
  11874 after the shift) + **1 new**: `w3cc_splitA_corners_data` (line 11623), the black box this unit states for
  unit SPLITA (rule 2).  Other warnings are the base file's deprecation/unused-binder notes.
* `grep -c sorry`: **8 before → 9 after** (the +1 is the new black-box statement's body; no frozen `sorry` changed).
* `check_W3_identity.py Port_GenericTransportSw_draft.lean W3C_SPLITC.lean`: the five frozen blocks IDENTICAL
  (`structure G11_ConfigSw`, `namespace G11_ConfigSw` block, `def G11_core_sw_statement`, `theorem G11_core_sw`
  statement, `theorem esc_switch_riii_of_chain`); the `imports = draft's + SM.BigonDeletion: False` line is the
  base file's own state (W3B_Assembled.lean also imports `RProof.RALedgers`; same output on the base file).
* `check_W3_statements.py W3C_SPLITC.lean`: 42/42 `w3a_..w3h_` statements byte-identical, `w3a_` count 20, no
  skeleton declaration missing.  The `def/structure/theorem w3bi_*` and `w3[a-h]_*` declaration lines are identical
  to the base file's (`diff` of the grep).
* `#print axioms` (on a scratch copy with the prints appended): `w3cc_uniform_of`, `w3cc_outer_alternative_of`,
  `w3cc_central_uniform_of`, `w3cc_central_rot_of`, `w3cc_rot_ledger`, `w3cc_uniform_of_three`,
  `w3cc_fullSplitData_of` all = `[propext, Classical.choice, Quot.sound]` — standard axioms only (no
  `SM.lit_homfly`, no `sorryAx`); `w3cc_splitA_corners_data` = standard + `sorryAx` (the black box).
  `w3bi_extreme_selected`'s axiom set is unchanged (this unit does not enter its chain yet; see "assembly").

## What is PROVED (the unit's two fields, exactly the frozen forms)

Both fields of `esc_FullSplitData` (RProof/RALedgers.lean) are proved from ONE combinatorial interface, the corner
ledger `w3cc_SplitCorners` (below), for a CV-generic `P`, supports `S ⊆ S'` in `Ind`, the contact carrier `q₀` of
`S` and four carriers `A B C Z` of `S'`; `w3cc_fullSplitData_of` instantiates them at `S = Q`,
`S' = Q ∪ triangleCrossings P e f g` and produces the record — its elaboration is the proof that the two theorems'
conclusions ARE the frozen fields (same `hn hG hQ hS`, same `carrierR`/`weight`/`geoCornerPolygon` binders).

* **`w3cc_outer_alternative_of` (line 11452)** : `CarrierUniform q₀ → UniformOrOneDissentCV (poly A) ∧ … B ∧ … C`.
* **`w3cc_uniform_of` (line 11475)** : `CarrierUniform q₀ →` live `(R_A + R_B + R_C = R + 1 ∧ W_A W_B W_C W_Z = −W)`
  `∨` dead `(R_A + R_B + R_C + 1 = R ∧ W_A W_B W_C W_Z = 0)`.
* Bonus for the assembler / SPLITA: **`w3cc_central_uniform_of`** (`CarrierUniform S' Z`) and
  **`w3cc_central_rot_of`** (`carrierR hn hG hS' Z = 1` = the frozen field `central_rot`), and `distinct` is a field
  of the ledger — so `w3cc_fullSplitData_of` (line 11572) needs from the other units only `touching_iff`,
  `central_no_piece` (SPLITA) and `writhe`, `mixed` (SPLITB).

### The mathematics as formalised (ESC §4, (14)–(16); template U-SPLIT (d)–(e), R176 §L0)

Let `τ ≠ 0` be the uniform sign of `q₀` and `ζ ≠ 0` the common sign of the central triangle `Z`.
1. Corner sets (`w3cc_cornerSet S q = {m | owner S m = q ∧ IsTrueCorner S m}`, enumerated once by `geoCornerMark`):
   `cornerSet S' X = insert (inr (twin zX)) (inh X)` for `X ∈ {A, B, C}` (`w3cc_cornerSet_A/B/C`, via the generic
   `w3cc_cornerSet_outer`), where `inh X` = the corners of `q₀` owned by `X` at `S'`; `cornerSet S' Z = {zA, zB, zC}`
   (`w3cc_cornerSet_Z`); the corners of `q₀` are partitioned by `inh A, inh B, inh C` (`w3cc_inh_partition`, as a
   sum identity for any `AddCommMonoid`, used both for ℝ-turns and for ℕ-counts).  Hence `c_Z = 3`
   (`w3cc_cornerCount_Z`) and `c_A + c_B + c_C = c_{q₀} + 3` (`w3cc_cornerCount_ledger`).
2. Turns: the principal turn of the corner polygon at `k` is the mark turn of `geoCornerMark k`
   (`w3cc_principalTurn_eq_mark`, `geoCornerPolygon_edge(_pred)_smul` + `principalAngle_smul`); inherited corners
   keep their turn under `S ⊆ S'` (`w3cc_markPT_mono`: `geoOutSlot_vertex/_selected`); the two smoothing corners of
   a selected crossing cancel (`w3cc_new_turns_cancel`, `principalAngle_swap` copied as `w3cc_principalAngle_swap`),
   so `markTurn (twin v) = −markTurn v` (`w3cc_markTurn_twin`).
3. **Rotation ledger (15)** `w3cc_rot_ledger`: `rot q₀ = rot A + rot B + rot C + rot Z` in ℤ, from lem:turnlift (ii)
   `CV.two_pi_mul_rot` on all five polygons (`w3cc_two_pi_rot`), 1–2, and `mul_left_cancel₀ (2π ≠ 0)` + cast.
4. **Shapes** `w3cc_outer_shape`: each outer `X` has its smoothing corner `k₀` (`geoCornerMark k₀ = inr (twin zX)`)
   of turn `−ζ` and every other corner of turn `τ`.  `w3cc_central_uniform_of`: `Z` is uniform (see 6);
   `w3cc_rot_uniform_three`: `rot Z = ζ` (lem:uniformrot (i), `CV.rot_eq_(neg_)one_of_(pos/neg)_three`).
5. **Branches** on `ζ = τ ∨ ζ = −τ` (`w3cc_signType_eq_or_neg`):
   * live `ζ = −τ`: the outer polygons are uniform of sign `τ` → `UniformOrOneDissentCV`
     (`w3cc_uniformOrOneDissent_of_pattern`), `τ·rot ≥ 1` for `A, B, C, q₀` (`w3cc_one_le_sign_mul_rot`), and
     `rot A + rot B + rot C = rot q₀ + τ` → `|·|` adds (`w3cc_abs_ledger_live`) → (16) via `carrierR_cast`;
     weights: `τ = −1`: `W_A = W_B = W_C = W_{q₀} = 1` (`weight_of_all_right`), `W_Z = (−1)^3` (`weight_of_all_left`)
     → `−1`; `τ = 1`: `W_X = (−1)^{c_X}`, `W_Z = 1`, `(−1)^{c_A + c_B + c_C} = (−1)^{c_{q₀} + 3} = −W_{q₀}` (1).
   * dead `ζ = τ`: one-dissent shape → `UniformOrOneDissentCV`, `τ·rot ≥ 1`, `rot A + rot B + rot C + τ = rot q₀`
     → `w3cc_abs_ledger_dead`; `A` is mixed (`w3cc_mixed_of_shape`: a second index exists since
     `three_le_geoCornerCount`) → `W_A = 0` (`weight_of_mixed`) → product `0`.
6. **A regular triangle is uniform** (`w3cc_uniform_of_three`, lines 10838–10940, NEW beyond the plan): if a corner
   has turn `≤ 0` and the other two `≥ 0`, lem:uniformrot (ii) (`CV.one_le_rot_of_one_dissent`) gives `rot ≥ 1`,
   while the two other principal turns are `< π` each (`principalAngle_bounds`), so `2π·rot = t_a + Σ_{i≠a} t_i < 2π`
   — contradiction (`w3cc_no_dissent_three`; reversal form `w3cc_no_dissent_three'`).  With three indices this
   leaves "all `> 0`" or "all `< 0`" (enumeration over `ZMod 3` by `decide`).  Consequence: the black box needs NO
   sign information about `Z`; `central_uniform`/`central_rot` are derived from "`Z` owns exactly `zA, zB, zC`".

## The black box (rule 2): `w3cc_SplitCorners` — SPLITA's carriers in the form this unit consumes

`structure w3cc_SplitCorners (hP : CrossingGeometry P) (S S') (q₀ : GeoComponent hP S) (A B C Z : GeoComponent hP S')
(zA zB zC : Visit P) : Prop` (line 11070), purely combinatorial (owners and true corners; no signs, no rotation):

| field | content |
|---|---|
| `subset : S ⊆ S'` | `Q ⊆ Q ∪ T` |
| `distinct` | the six inequalities of `esc_FullSplitData.distinct` (same shape) |
| `memA/B/C : zX.1 ∈ S' ∧ zX.1 ∉ S` | the inner visits sit on triangle crossings (selected in `S'`, outside `Q`) |
| `ownZ` | `Z` owns `inr zA, inr zB, inr zC` |
| `ownA/B/C` | `A` owns `inr (visitTwin zA)`, `B` owns `inr (visitTwin zB)`, `C` owns `inr (visitTwin zC)` |
| `inherited` | every true corner of `S` owned by `q₀` is owned at `S'` by `A`, `B` or `C` |
| `cover` | every true corner of `S'` owned by `A, B, C` or `Z` is a `q₀`-corner of `S` or one of the six visits |

Distinctness of the six marks is derived from `distinct` through the owners (`w3cc_zA_ne_zB` etc.), so SPLITA need
not state it.  The Prop `w3cc_splitA_corners` (line 11601; the binders of `w3bi_esc_outer`, conclusion
`∃ A B C Z zA zB zC, w3cc_SplitCorners (geomAt E t' ht'.1) Q' (Q' ∪ T') q₀' A B C Z zA zB zC`) is asserted with
`sorry` as `w3cc_splitA_corners_data` (line 11623) — **SPLITA's content, restated in this unit's vocabulary**; the
natural SPLITA proof: `A = owner (twin zA)`, … with `zA, zB, zC` the inner smoothing-site visits of the three triangle
crossings, `cover`/`inherited` from the geo insert layer (`geoOwner_insert_eq_imp`,
`geoComponentForgetSwitch_fiber_affected`, `geo_selected_visits_separated`, as U-SPLIT (b) used them, three times).
Note that `w3cc_SplitCorners` is stated over a plain `hP : CrossingGeometry P` and general `S S'` — no `∪`, no
`insert`, hence NO `DecidableEq` instance mismatch (U-SPLIT pitfall 1) at the interface; the frozen `Q ∪ T` enters
only as the `S'` argument of `w3cc_fullSplitData_of`.

## Assembly (for the assembler of `w3bi_esc_outer_data`)

`w3cc_fullSplitData_of hn hG e f g hQ hS q₀ A B C Z Λ hC touching_iff central_no_piece writhe mixed :
esc_FullSplitData hn hG e f g hQ hS q₀ A B C Z Λ` (line 11572; fields `distinct`, `central_rot`,
`outer_alternative`, `uniform` come from `hC`).  So the `esc_FullSplitData` conjunct of `w3bi_esc_outer` =
`w3cc_splitA_corners_data … ` (SPLITA) + SPLITA's `touching_iff`, `central_no_piece` + SPLITB's `writhe`, `mixed`
for the SAME `A B C Z` — the assembler should have SPLITA produce `zA zB zC` and `w3cc_SplitCorners` alongside its
own fields (or prove `w3cc_splitA_corners` from SPLITA's characterisation of `A B C Z`).  `w3bi_esc_outer_data`
itself is untouched (shared leaf).

## Unproved

Nothing of this unit's content.  Open: the black box `w3cc_splitA_corners_data` (SPLITA's).

## Helpers added (57 declarations, all `w3cc_`, in file order)

*C0 signs/patterns (10696–10950)*: `w3cc_signType_eq_or_neg`, `w3cc_signType_eq_zero_of_eq_neg`,
`w3cc_sign_principalTurn`, `w3cc_principalTurn_reversal`, `w3cc_Pattern` (def), `w3cc_rot_ray`,
`w3cc_uniformOrOneDissent_of_pattern` (U-SPLIT's `cvt165s_rot_ray`/`_of_pattern`, copied — `CV/SingletonDi.lean`
is NOT in this file's import closure), `w3cc_one_le_sign_mul_rot`, `w3cc_rot_uniform_three`, `w3cc_abs_ledger_live`,
`w3cc_abs_ledger_dead` (R176's `r176l_abs_ledger` with three summands, both branches), `w3cc_no_dissent_three`,
`w3cc_no_dissent_three'`, `w3cc_uniform_of_three`, `w3cc_principalAngle_neg_neg`, `w3cc_principalAngle_swap`
(SM/ZeroRotationSeed.lean's, not in the closure; `principalAngle_reverse` is).
*C1 marks (10952–11058)*: `w3cc_markPT`, `w3cc_markTurn` (defs; the turn sign is `sign (markPT)`, so the twin
relation is `Left.sign_neg`), `w3cc_principalTurn_eq_mark`, `w3cc_turn_eq_mark`, `w3cc_cornerSet`,
`w3cc_mem_cornerSet`, `w3cc_image_cornerMark`, `w3cc_sum_corners`, `w3cc_geoCornerCount_eq_card`,
`w3cc_isTrueCorner_mono`, `w3cc_markPT_mono`, `w3cc_markTurn_mono`, `w3cc_new_turns_cancel`, `w3cc_markTurn_twin`.
*C2 ledger (11070–11290)*: `w3cc_SplitCorners`, `w3cc_inh`, `w3cc_mem_inh`, `w3cc_cornerSet_outer`,
`w3cc_cornerSet_A/B/C`, `w3cc_cornerSet_Z`, `w3cc_zA_ne_zB`, `w3cc_zA_ne_zC`, `w3cc_zB_ne_zC`, `w3cc_cornerCount_Z`,
`w3cc_sum_Z`, `w3cc_twin_notMem_inh`, `w3cc_sum_outer`, `w3cc_sum_inh_eq`, `w3cc_inh_partition`,
`w3cc_cornerCount_ledger`.
*C3 rotation (11294–11565)*: `w3cc_two_pi_rot`, `w3cc_rot_ledger`, `w3cc_markTurn_inner`, `w3cc_outer_shape`,
`w3cc_pattern_of_shape`, `w3cc_mixed_of_shape`, `w3cc_central_uniform_of`, `w3cc_central_rot_of`,
`w3cc_outer_alternative_of`, `w3cc_uniform_of`.
*C5 assembly (11572–11625)*: `w3cc_fullSplitData_of`, `w3cc_splitA_corners` (def), `w3cc_splitA_corners_data` (sorry).

Size: 952 lines against the estimate 1–1.5k; the saving is the generic `w3cc_cornerSet_outer` and the
`AddCommMonoid`-generic sums (one partition lemma serves ℝ-turns and ℕ-counts).

## Pitfalls met (for the assembler / other units)

1. **Import closure.** `CV.SingletonDi` (U-SPLIT's `cvt165s_` helpers) and `SM.ZeroRotationSeed`
   (`principalAngle_swap`, `principalAngle_neg_neg`) are NOT reachable from this file's imports
   (`SM.BigonDeletion`, `RProof.RALedgers`, …); `CV.geoIndependent_of_mem_Ind` is (namespace `CV`);
   `three_le_geoCornerCount` wants `hG : CarrierGeometry P` — `CarrierGeometry.ofCV hG` with `.cg` defeq to
   `hG.crossingGeometry` (`rfl`).  When U-SPLIT's helpers become reachable, C0/C1 can be replaced by them.
2. **`open Classical`.** This file's `namespace SM.Link` has no `open Classical`; the `filter`/`if` in
   `w3cc_cornerSet`, `w3cc_inh`, `w3cc_sum_inh_eq` need `open scoped Classical in`, and proofs using `Finset.sum_insert`
   / `card_insert_of_notMem` (`DecidableEq (Mark P)`) need `classical`.
3. **Section variables.** `include hn hS hS' in` is needed on every theorem whose statement does not mention them
   (`w3cc_markTurn_inner`, `w3cc_outer_shape`, `w3cc_mixed_of_shape`, `w3cc_central_uniform_of`,
   `w3cc_outer_alternative_of`); `include … in` must precede the docstring, not follow it.  `omit hC in` where the
   ledger is not used (`w3cc_twin_notMem_inh`, `w3cc_sum_outer`, `w3cc_sum_inh_eq`, `w3cc_pattern_of_shape`).
4. **Mathlib names at this pin**: `lt_or_ge` (not `lt_or_le`), `Finset.card_insert_of_notMem`, `Left.sign_neg`,
   `Fintype.exists_ne_of_one_lt_card` + `ZMod.card`; `if_pos/if_neg` are deprecated (the partition proof uses
   `rw [h]; simp [distinctness facts]` instead); `rw [hζτ]` on `ζ = -τ` with `τ` a literal closes `-(-1) = 1` by
   `rfl`, so the following `decide` errors "no goals" — use `subst hζτ; decide`.
5. **Prop structures with data**: the inner visits `zA zB zC` are PARAMETERS of `w3cc_SplitCorners` (a Prop structure
   cannot project data fields); the black-box Prop quantifies them existentially.

## Statement audit

The frozen fields are consumed unchanged: `w3cc_fullSplitData_of` builds `esc_FullSplitData hn hG e f g hQ hS q₀ A B
C Z Λ` by `where` with `outer_alternative := w3cc_outer_alternative_of hn hG hQ hS hC` and
`uniform := w3cc_uniform_of hn hG hQ hS hC`, which elaborates only because the two theorems' conclusions are the
fields verbatim (`CV.carrierR hn hG hS A` etc. with `hS : Q ∪ triangleCrossings P e f g ∈ Ind`,
`CV.weight hG.crossingGeometry _ A`, `geoCornerPolygon hG.crossingGeometry _ A`).  Nothing in `RProof/RALedgers.lean`
or under `work/lean` was written.
