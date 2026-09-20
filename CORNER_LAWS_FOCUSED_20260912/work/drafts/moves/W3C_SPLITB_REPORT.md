# W3C_SPLITB_REPORT — unit SPLITB (prefix `w3cb_`): `esc_FullSplitData.writhe` (17) and `.mixed`

Prover subagent, 2026-09-15, 23:19 → 23:54 UTC (7:19pm → 7:54pm ET); hard stop 01:45 UTC (audit A-177-2 window).
File: `work/drafts/moves/W3C_SPLITB.lean` = `W3B_Assembled.lean` (11851 lines) + ONE pure insertion, the block
`section W3CB_SPLITB … end W3CB_SPLITB` (lines 11868–12693, header docstring 11868–11881), placed inside
`section W3BI_REAL` immediately before `end W3BI_REAL`.  12700 lines.  No frozen statement, name, docstring or
definition touched (the five frozen blocks, the 42 `w3a_…w3h_` statements, every `w3bi_` definition); no other
unit's `sorry` touched; the leaf `w3bi_esc_outer_data` keeps its body (it also needs SPLITA's fields and KNOT's
two clauses — see §4).

## 0. Result in one paragraph

**Both SPLITB fields are PROVED** — `writhe` (17) `w = 3 + w_A + w_B + w_C + 2Λ` and `mixed` "if the empty contact
carrier is mixed then `wt(A) wt(B) wt(C) wt(Z) = 0`" — from ONE geometric input, the structure `w3cb_SplitCore`
(§3), by `w3cb_fields_of_residue` / `w3cb_fields_of_splitGeometry` (standard axioms only: `propext,
Classical.choice, Quot.sound`).  Along the way the children clauses of the split ("the marks of `A, B, C` are
marks of `q₀`; every nonlocal mark of `q₀` is a mark of `A`, `B` or `C`") are PROVED from the accepted
one-insertion lemmas iterated three times, and SPLITA's field `central_no_piece` is PROVED from the core's
`central` clause.  `esc_FullSplitData` is assembled by `w3cb_fullSplitData_of_residue` from the core and the
remaining five SPLITA fields (`touching_iff`, `distinct`, `central_rot`, `outer_alternative`, `uniform`) as
hypotheses in the exact field statements.  The single new `sorry` is the event-level black box
`w3cb_split_core_data : w3cb_split_core` (line 12676).

## 1. Compile and checks (mandated)

* `cd work/lean && lake env lean ../drafts/moves/W3C_SPLITB.lean` → **exit 0, 0 errors**, 34 s warm; exactly
  **8 `declaration uses sorry`** = the 7 inherited leaves (lines 4093 `w3b_reparam_switch`, 9237 / 9267
  `w3g_bigonData_smooth_arcST/TS`, 10673 `w3bi_esc_outer_data`, 10777 / 10797 `w3bi_bigonData_smooth_arc*_switch_z`,
  10922 `w3bi_site_data_data`) + 12676 `w3cb_split_core_data`.  The new block emits no warning other than that one `declaration uses sorry` (lines ≥ 11882 of the log).
* `grep -c sorry`: **8 before → 10 after** (the new `sorry` body at 12677 and the header docstring's mention at
  11879 — the count is of lines containing the word).
* `check_W3_identity.py W3C_SPLITB.lean Skeleton_W3.lean`: `structure G11_ConfigSw`, `namespace G11_ConfigSw block`,
  `def G11_core_sw_statement`, `theorem G11_core_sw (statement)`, `theorem esc_switch_riii_of_chain`: all
  **IDENTICAL**; `imports = draft's + SM.BigonDeletion: False` (the documented expected value for any file importing
  `RProof.RALedgers`, W3B_ASSEMBLY_REPORT §8); `G11_core_sw body starts with sorry: False`.
* `check_W3_statements.py W3C_SPLITB.lean`: skeleton statements 42, in target 42, **byte-identical 42**,
  differing/missing `[]`, `w3a_` count 20, missing names `[]`.
* `#print axioms` (scratch copy `S7ax.lean` in the unit's private scratch dir `…/scratchpad/w3cb/`):
  `w3cb_card_retained`, `w3cb_writhe_field`, `w3cb_mixed_field`, `w3cb_inherit_turn`, `w3cb_cover_triangle`,
  `w3cb_markChildren_of`, `w3cb_central_no_piece`, `w3cb_splitGeometry_of_residue`, `w3cb_fields_of_residue`,
  `w3cb_fullSplitData_of` / `_of_residue`, `w3cb_triangle_on_contact_at`, `w3cb_split_geometry_of_core`:
  `[propext, Classical.choice, Quot.sound]`; `w3cb_split_geometry_data`: the same + `sorryAx` (through
  `w3cb_split_core_data` only).
* Iteration: scratch files `S1…S7.lean` (header `import SM.BigonDeletion` + `import RProof.RALedgers`, the file's
  `open`s) in the private scratch dir; each compiled in 8–15 s before splicing; 47 `w3cb_` declarations, ≈ 810
  body lines.

## 2. What is PROVED (file order; line = declaration)

**(a) The retained-set ledger with three children** (the analogue of row 176's `r176l_retained_decomp` /
`r176l_card_retained`, `R176_LEDGER.lean` §L2):
* `structure w3cb_Children hP S' Sf q' A B C` 11886 — `subA/B/C` (a mark of a child is a mark of `q'`), `neAB neAC
  neBC`, `cover` (a visit of a crossing unselected in `Sf` owned by `q'` is owned by `A`, `B` or `C`).
* `w3cb_mixedSet hP S' Sf q'` 11898 — the retained crossings of `q'`, unselected in `Sf`, whose two visits have
  DIFFERENT `Sf`-owners ("the `2Λ` mixed crossings between outer gap strings"); `w3cb_selectedPart` 11903 — the
  retained crossings of `q'` selected in `Sf`.
* `w3cb_retained_decomp` 11914: `geoCarrierCrossings S' q' = gCC Sf A ∪ gCC Sf B ∪ gCC Sf C ∪ mixedSet ∪
  selectedPart`; `w3cb_card_retained` 11957: the five parts are pairwise disjoint, cardinalities add.
* `w3cb_selectedPart_eq` 12004: for `Sf = Q ∪ T` and `T ⊆ gCC Q q₀`, the selected part is exactly `T`.
* `w3cb_writhe_count` 12017: with `groupedWrithe_eq_card_geoCarrierCrossings` (CV/X1.lean) and
  `P1.triangleCrossings_card`, `w_{q₀} = 3 + w_A + w_B + w_C + #mixedSet`; **`w3cb_writhe_field` 12037: (17)** given
  `#mixedSet = 2Λ`.

**(b) The mixed clause** (ESC §4 "were all outer carriers uniform, their common local corner sign `s_o` would force
every inherited nonlocal corner to have sign `s_o`, contrary to mixedness"):
* `structure w3cb_CornerData hP q₀ A B C s` 12052 — `s ≠ 0`; each of `A, B, C` has a corner of turn `s`; every
  corner of `q₀` has a corner of `A`, `B` or `C` with the same turn.  `w3cb_uniform_of_cornerData` 12063 (uniform
  children ⇒ uniform parent), **`w3cb_mixed_field` 12082: `CarrierMixed Q q₀ → wt A * wt B * wt C * wt Z = 0`**
  (via `CV.weight_ne_zero_iff`).
* The corner data from geometry: `w3cb_turnAt hP S m` 12097 (the sign of `det(in-edge, out-slot edge)` at a mark);
  `w3cb_turn_eq_turnAt` 12102 (`turn (geoCornerPolygon S r) k = w3cb_turnAt S (geoCornerMark S r k)`, by
  `geoCornerPolygon_edge_pred_smul` / `_smul` and `sign_mul`); `w3cb_outSlot_eq_of_iff`, `w3cb_turnAt_eq_of_iff`
  12113 / 12123 (unchanged when the support changes without selecting/deselecting the mark's crossing);
  `w3cb_isTrueCorner_mono` 12131; `structure w3cb_MarkChildren` 12140 (= `w3cb_Children` + `coverCorner`: every corner
  mark of `q'` is `Sf`-owned by `A`, `B` or `C`); **`w3cb_inherit_turn` 12147** (an inherited corner keeps its turn);
  `w3cb_inherit_of_markChildren` 12164; `w3cb_local_of_visit` 12178 (a selected visit owned by `r` with `turnAt = s`
  is a corner of `r` with turn `s`); `w3cb_cornerData_of` 12186.

**(c) The bundle and the two fields**: `structure w3cb_SplitGeometry hP e f g q₀ A B C Λ s` 12201 (`children :
w3cb_MarkChildren`, `triangle_on_contact : T ⊆ gCC Q q₀`, `s_ne`, `localA/B/C` — a triangle visit owned by the child
with `turnAt = s`, `mixed_even : #mixedSet = 2Λ`); `w3cb_cornerData_of_splitGeometry` 12217;
**`w3cb_fields_of_splitGeometry` 12230 — the two fields in the exact statements of `esc_FullSplitData`**;
`w3cb_fullSplitData_of` 12251 — `esc_FullSplitData hn hG e f g hQ hS q₀ A B C Z Λ` from the bundle + the six other
fields as hypotheses.

**(d) The event level**: `def w3cb_split_geometry` 12287 (∃ `A B C Λ s`, `w3cb_SplitGeometry` at every configuration,
the binders of `w3bi_esc_outer`); **`w3cb_triangle_on_contact_at` 12310 — `triangle_on_contact` is FREE**: on the
empty side the triangle-touching carrier of `transportSupport hs Q` owns every visit of every triangle crossing
(`esc_contact_owns` after `GT_outsideSupports_transport` / `GT_fullAvail_transport`, `P1.ne_of_isCrossing_pair`).

**(e) The children clauses from three iterated insertions** (the accepted `SM/GeoCarrierCount.lean` lemmas
`geoComponentForgetSwitch_fiber_affected`, `geoOwner_insert_iff_of_unaffected`,
`geoIndependent_remaining_pair_owners`, `geoOwner_eq_of_subset`, `geoInheritsMarkOrder_of_independent`):
`w3cb_geoIndependent_mono` 12329; `w3cb_step_affected` 12342 (a mark of the carrier owning both visits of the
inserted crossing lands on the daughter of `v` or of its twin); `w3cb_stage` 12356 (either case);
**`w3cb_cover_three` 12368** (three insertions of retained crossings of `q₀`: every mark of `q₀` lands on the carrier
of one of the six visits); `w3cb_insert_eq` 12435 (the `DecidableEq`-instance bridge, copy of the accepted
`CV.cvt165s_insert_eq`, not in this import closure); `w3cb_union_triangle_eq` 12441 (`Q ∪ T = insert x_fg (insert x_eg
(insert x_ef Q))`); **`w3cb_cover_triangle` 12449**; **`w3cb_markChildren_of` 12470**: `w3cb_MarkChildren Q (Q ∪ T) q₀
A B C` from "`A, B, C` are the `Q ∪ T`-carriers of triangle visits, pairwise distinct, and the carrier of every
triangle visit is `A`, `B`, `C` or a carrier owning only triangle visits" (`sub` by refinement; `cover` /
`coverCorner` because a mark landing on the central carrier is a triangle visit, hence not an unselected visit
and not a true corner of `Q`).

**(f) The residue**: `structure w3cb_SplitCore` 12530 (§3), `structure w3cb_SplitResidue extends w3cb_SplitCore`
12556 (+ `triangle_on_contact`), `w3cb_residue_of_core` 12561, **`w3cb_splitGeometry_of_residue` 12568**,
**`w3cb_fields_of_residue` 12580**; **`w3cb_central_no_piece` 12601** (a carrier owning only triangle visits carries
no piece: `CV.pieceLabels_nonempty`, `CV.pieceLabels_subset`, `CV.mem_U_iff`); **`w3cb_fullSplitData_of_residue`
12621** (`esc_FullSplitData` from the core, the central-only clause for `Z`, and the five remaining fields);
`def w3cb_split_core` 12655 (event level), `w3cb_split_core_data` 12676 (**the one `sorry`**),
`w3cb_split_geometry_of_core` 12681, `w3cb_split_geometry_data` 12690 (a theorem on the black box).

## 3. The black box (exact content of `w3cb_SplitCore hP e f g q₀ A B C Λ s`, `Sf := Q ∪ triangleCrossings P e f g`)

| clause | statement | who supplies it |
|---|---|---|
| `s_ne` | `s ≠ 0` | SPLITA (sign table (1c): `s = s_o`) |
| `localA` (`B`, `C` alike) | `∃ v : Visit P, v.1 ∈ T ∧ geoOwner hP Sf (inr v) = A ∧ w3cb_turnAt hP Sf (inr v) = s` — `A` is the `Sf`-carrier of a triangle visit at which the turn (sign of `det(edge (geoInEdge v), edge (geoOutSlot Sf (inr v)).1)`) is `s` | SPLITA (the outer smoothing corner of each outer carrier, (1c) `s_o = −σ` via `GenericTableData.extreme_iff_alternating`) |
| `neAB neAC neBC` | `A ≠ B`, `A ≠ C`, `B ≠ C` | SPLITA (`distinct`) |
| `central` | `∀ w : Visit P, w.1 ∈ T → owner (inr w) = A ∨ = B ∨ = C ∨ (∀ m, owner m = owner (inr w) → ∃ v, m = inr v ∧ v.1 ∈ T)` — the carrier of every triangle visit is an outer carrier or owns only triangle visits ("the central triangle owns only the three local corner marks") | SPLITA |
| `mixed_even` | `(w3cb_mixedSet hP Q Sf q₀).card = 2 * Λ` — the retained crossings of `q₀` whose two visits lie on different `Sf`-carriers number `2Λ` | KNOT (the analogue of `r176m_bridge_count`: these crossings are exactly the mixed crossings of `J_L = D_L^{xy}` between the three components, all positive, so `twoLambda J_L = #mixedSet`; `Λ` must be the `Λ` of `three_components`) |

Not in the core because already proved here: `triangle_on_contact` (event level, `w3cb_triangle_on_contact_at`), all
of `w3cb_Children` / `w3cb_MarkChildren`, `central_no_piece`.  The event-level form `w3cb_split_core` quantifies
exactly as `w3bi_esc_outer` up to `q₀, q₀'` and asserts `∃ A B C Λ s, w3cb_SplitCore (geomAt E t' ht'.1) e f g q₀' A B
C Λ s`.

## 4. For the assembler: how this connects to `w3bi_esc_outer_data`

`w3bi_esc_outer` asks, per configuration, for `∃ A B C Z Λ, esc_FullSplitData … ∧ w3bi_knot_after_two … ∧
w3bi_three_components … Λ (groupedPoly A) (groupedPoly B) (groupedPoly C)`.  With SPLITA's `A B C Z` and KNOT's `Λ`:
* `esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' A B C Z Λ :=
  w3cb_fullSplitData_of_residue hn (genericAt E t' ht'.1) e f g hQi' hS' hef' heg' hfg' q₀' A B C Z Λ
  (w3cb_residue_of_core _ hcore (w3cb_triangle_on_contact_at hL ht ht' hop hs hef heg hfg hQ hfull hq₀'))
  hZ touching_iff distinct central_rot outer_alternative uniform` where `hef' := (hs _).mp hef` etc.,
  `hcore : w3cb_SplitCore (geomAt E t' ht'.1) e f g q₀' A B C Λ s` (SPLITA + KNOT's parity), `hZ : ∀ m, geoOwner … m
  = Z → ∃ v, m = inr v ∧ v.1 ∈ T` (SPLITA), and the five fields from SPLITA.  The `GeoComponent (geomAt E t' ht'.1) …`
  and `GeoComponent (genericAt E t' ht'.1).crossingGeometry …` types agree by proof irrelevance (as in
  `w3bi_esc_outer` itself).
* If SPLITA's report (`W3C_SPLITA_REPORT.md`, not present when this unit started) characterises `A, B, C` as the
  `Q' ∪ T'`-owners of the three outer triangle visits and `Z` as the owner of the inner ones, the core's `localA/B/C`
  owner clauses and `central` are its distinctness/ownership statements verbatim; only the `turnAt = s` clauses
  (sign table) and `mixed_even` (KNOT) need a bridge.
* `w3cb_split_geometry_data` is the whole-interface form; if the assembler prefers, `w3cb_split_core_data` can be
  replaced by SPLITA's Prop and the leaf body of `w3bi_esc_outer_data` written as above under the binders.

## 5. Rules / reassessment

* Rule (1): only material prefixed `w3cb_` added, in one block; nothing existing edited.  Rule (2): the black box
  towards SPLITA/KNOT is stated as `w3cb_split_core` with the single sorry'd `w3cb_split_core_data` and reported (§3).
  Rule (3): both SPLITB fields are TRUE as stated; no corrected form needed.  Rule (4): no lemma failed twice; the
  errors met were all elaboration-level (§6) and fixed in one pass each.  Rule (5): done (§1).
* Attempted and not done: nothing of the core — the sign table (1c) for `localA/B/C`, the distinctness of the
  outer carriers and the `central` clause are the empty-triangle successor geometry (SPLITA's, U-SPLIT template
  (b)/(d)); `mixed_even` needs KNOT's record bridge.  No library lemma gives the parity of crossings between two
  carriers directly (searched `Even`/`card` in SM/GeoCarrierCrossings, SM/FlatCarriers, CV/*).

## 6. Pitfalls met (for the assembler / SPLITA)

* The accepted insertion lemmas of `SM/GeoCarrierCount.lean` elaborate `insert` with `Classical.propDecidable`
  (`attribute [local instance] Classical.propDecidable` there) while this file uses the global
  `RProof.instDecidableEqCrossing`; the iterated-insertion lemmas live in a subsection with `attribute [local
  instance high] Classical.propDecidable` and `w3cb_cover_triangle` bridges through `w3cb_insert_eq` (`rw` three
  times, innermost first) — the pattern of the accepted `cvt165s_` unit.  `CV.cvt165s_insert_eq` itself is NOT in
  the import closure of `SM.BigonDeletion` + `RProof.RALedgers`.
* Section-variable order: `hP` precedes the theorem's own binders (`w3cb_turn_eq_turnAt hP hn …`); a theorem that
  re-binds `{S' Sf}` shadows the section's `A B C : GeoComponent hP Sf` (type mismatch `Sf✝`).
* `structure X (…) : Prop extends Y where` (new syntax); the parent projection is `X.toY` with the FULL parent name
  (`tow3cb_Children`), not `toChildren`.
* `triangleCrossings_card`, `mem_triangleCrossings_iff`, `xPair_ef_ne_eg` etc., `ne_of_isCrossing_pair` are
  `RProof.P1.*`; `esc_contact_owns`, `GT_*_transport` take `hef : e ≠ f`-style inequalities, obtained by
  `P1.ne_of_isCrossing_pair`.
* Definitions using `geoCarrierCrossings` / classical filters must be `noncomputable def`.
* The identity checker's `imports` line prints `False` for this file (it imports `RProof.RALedgers`), as documented.

## 7. Times (UTC / ET)

23:19 / 7:19pm start (copy, reading); 23:29 / 7:29pm S1 (ledger + corner-data mixed clause) compiles; 23:35 S2
(turn inheritance, bundle, `esc_FullSplitData` assembler); 23:36 first splice, full compile 0 errors 31 s; 23:39 S3
(event level, free triangle clause); 23:45 S4 (iterated insertions, `w3cb_markChildren_of`); 23:46 S5 (residue);
23:50 S6 (`central_no_piece`); 23:53 S7 (`w3cb_SplitCore`, minimal black box); 23:54 / 7:54pm final splice, full
compile 0 errors 34 s, checks, this report.
