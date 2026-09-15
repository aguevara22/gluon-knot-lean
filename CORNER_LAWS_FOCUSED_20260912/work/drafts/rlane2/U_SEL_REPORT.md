# U_SEL_REPORT — unit SEL, row 172 R:generic_selector (WHOLE row), 2026-09-14 06:56 UTC / 2:56am ET

File: `work/drafts/rlane2/U_SEL.lean` (copy of `Statements_FINAL.lean` + 522 inserted lines; the ONLY
removed/changed line relative to the frozen file is the `sorry` of `RProof.generic_selector`, checked with
`diff Statements_FINAL.lean U_SEL.lean | grep '^<'`). No definition, structure, theorem statement, name,
docstring or import was touched.

Compile: `cd work/lean && lake env lean ../drafts/rlane2/U_SEL.lean` — exit 0, 0 errors, 0 warnings other than
exactly eight `declaration uses sorry` at the eight other row theorems (`exterior`, `availability_zero_one`,
`generic_transport`, `generic_selected`, `extreme_pair_zero`, `extreme_transport`, `extreme_selected`, `cv_R`);
~10 s.

`#print axioms` (temporary copy `/tmp/rl2sel/U_SEL_axioms.lean`):
`RProof.generic_selector`, `SEL_genericSelectorData`, `SEL_row_zero` — `[propext, Classical.choice, Quot.sound,
SM.lit_homfly]` (`lit_homfly` enters only through `rowTerm = CV.X1Summand`, NOTES_FINAL §12 item 12);
`SEL_mixed_of_adjacent`, `SEL_geoMarkSuccessor_eq_of_no_visit_between`, `SEL_sorted_next_of_no_cyclic_between` —
`[propext, Classical.choice, Quot.sound]`.

## Proved

* **`RProof.generic_selector`** (row 172, whole): `∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectorData hn E e f g δ`,
  with `δ := min δ_L δ_G`, `δ_L` the radius of the accepted `localization` (row 164) and `δ_G` that of the
  accepted `generic_table` (row 172-table); both bundles shrunk to `δ` (`F1.localizationData_mono`, new
  `SEL_genericTableData_mono`) and all five fields by `SEL_genericSelectorData`.
* All five fields as standalone lemmas (statement = the field with the row's binders, the bundle hypotheses
  `hL : LocalizationData E e f g δ`, `hG : GenericTableData E e f g δ` in place of the row's event data):
  `SEL_selected_pair_unique hG`, `SEL_corner_signs_opposite hG`, `SEL_mixed_carrier hn hL hG`,
  `SEL_selector_zero hn hL hG`, `SEL_row_zero hn hL hG`.

## Unproved

None in this unit.

## Helpers added (all prefixed `SEL_`, inside `section SEL` with a local `open SM.Carrier`, placed between
`structure GenericSelectorData` and `theorem generic_selector`)

| helper | content |
|---|---|
| `SEL_eq_zero_of_eq_neg`, `SEL_neg_ne_zero`, `SEL_eq_of_not_eq_neg`, `SEL_eq_neg_of_not_eq` | finite `SignType` facts (`decide`): (5) "failure of the selected-condition is `sgn det(u,v) = sgn det(u,w)`" as a nonzero-sign case split |
| `SEL_sorted_next_of_no_cyclic_between` | verbatim port of the accepted `SM.sorted_next_of_no_cyclic_between` (SM/GaussNextFromEmptyArc.lean), which is NOT in the import closure of the statement file; an empty cyclic gap in a finite linear order identifies the `Finset.sort` successor. The assembler may replace it by the library lemma if it adds the import. |
| `SEL_geoMarkSuccessor_eq_of_no_visit_between` | two distinct visits `v, w` on the SAME edge with no crossing visit in the oriented arc `v → w` are consecutive marks: `geoMarkSuccessor hP (inr v) = inr w`. Step 1: `key v < key w` (if `key w < key v` the hypothesis would put every crossing visit, in particular `visitTwin v` on another edge, between them — contradiction via `traversalKey_lt_iff`); Step 2: no original vertex lies strictly between (integer key vs. `(e.val, e.val+1)`); Step 3: the sorted lemma on `Finset.univ : Finset (Mark P)` under `geoMarkLinearOrder hP`, then `geoNextMark_eq_list_next` (instance mismatch closed by `convert … ; rfl`). This is the "arbitrary-`Q` successor lift" for one arc: outside smoothings never touch it since `ρ_S = ρ ∘ selectedMarkPerm` changes only the successors AT selected visits. |
| `SEL_exists_cornerMark` | a true corner owned by `q` is some `geoCornerMark q k` (`geoCornerMark_exists` at an arbitrary name of the carrier) |
| `SEL_carrierMixed_of_two_visits` | "the carrier is mixed regardless of all its other corners": a carrier of an independent support owning two selected visits with opposite nonzero corner turns (`turn_visit_of_traced`, `tracedSuccessor_of_mem_Ind`) is `CarrierMixed` |
| `SEL_visitTwin_visitOn` | the twin of the `v`-visit of a crossing with second edge `u ≠ v` is its `u`-visit (`visitTwin_unique`) |
| `SEL_mixed_of_adjacent` | the one-polygon core of "The mixed carrier": `x = x_{uv}, y = x_{uw} ∈ S`, `AdjacentVisits` of their `u`-visits, signs (5)–(6) ⇒ `MixedSharedStrandCarrier hP S x y …`. Case A (`x`'s `u`-visit first): `ρ_S (x,v) = ρ (x,u) = (y,u)`, co-owned `(x,v),(y,u)`, turns `det(v,u)`, `det(u,w)`; Case B (`y`'s first): `ρ_S (y,w) = ρ (y,u) = (x,u)`, co-owned `(y,w),(x,u)`, turns `det(w,u)`, `det(u,v)` |
| `SEL_wind_eq_zero_of_mixed`, `SEL_rowTerm_eq_zero` | `wind = 0` from a mixed carrier (`weight_of_mixed`, `Finset.prod_eq_zero`); a row whose selector vanishes when present is `0` (`rowTerm_of_mem_Ind` / `rowTerm_of_not_mem_Ind`) |
| `SEL_genericTableData_mono` | `GenericTableData` shrinks to a smaller radius (19 fields, each by `G2.punctured_of_le`) |
| `SEL_strandSigns_ne_zero` | `s_a, s_b, s_c ≠ 0` from `GenericTableData.nonzero` (`sign_ne_zero`) |
| `SEL_selected_pair_unique`, `SEL_corner_signs_opposite`, `SEL_mixed_carrier`, `SEL_selector_zero`, `SEL_row_zero`, `SEL_genericSelectorData` | the five fields and the bundle |

## Ownership convention — kernel check performed BEFORE the proof (as instructed)

`#eval (List.finRange 9).map (LocalTable.succ wordE {a, b}) = [8, 5, 3, 4, 2, 6, 7, 1, 0]` (positions
`0..8 = b(e) a(e) A c(f) a(f) B c(g) b(g) C`): cycles `{0,8}`, `{1,5,6,7}`, `{2,3,4}`; `a(e) = 1` and `b(g) = 7`
co-owned = the SECOND disjunct of `MixedSharedStrandCarrier` for pair `ab` (`(x,u) = a(e)`, `(y,w) = b(g)`); the two
`e`-visits `b(e) = 0`, `a(e) = 1` are on different carriers (B's rejected reading). Also checked:
`succ wordE {b, c} = [8, 2, 3, 7, 5, 6, 4, 1, 0]` (`c(f) = 3`, `b(g) = 7` co-owned, second disjunct) and
`succ wordP {a, c} = [4, 2, 3, 1, 8, 6, 7, 5, 0]` (`a(e) = 0`, `c(f) = 4` co-owned, first disjunct). The geometric
proof reproduces exactly this rule: on the shared edge `u`, the carrier co-owns `(x,v),(y,u)` when `x`'s `u`-visit
precedes `y`'s, and `(y,w),(x,u)` otherwise; on `E` (`b(e)` before `a(e)`) that is the second disjunct, on `P`
(`a(f)` before `c(f)`) the first.

## Fidelity notes

1. The clause hypotheses "generic orbit", "`Q ∈ outsideSupports`", "`FullAvail Q`" of `mixed_carrier`,
   `selector_zero`, `row_zero` are NOT used by the proofs (bound as `_`): the argument needs only the independence
   of `Q ∪ J` (for `TracedSuccessor`), R-LOC-2 adjacency and the sign condition (5) — exactly the text's "arbitrary
   exterior gaps and outside independent support `Q`; no coefficient, exterior-factor division, or nonvanishing
   hypothesis is used". The frozen statements were kept as printed.
2. `corner_signs_opposite` uses only `nonzero`; `selected_pair_unique` uses `generic_iff_nonalternating` +
   `selected_unique` (the graph identification is the accepted `selected_is_graph_selected`, as the docstring says).
3. No statement of row 172 was found false or in need of a stronger hypothesis; no counterexample.
4. `AdjacentVisits` (empty arc among crossing visits, either orientation) suffices without any list-form adjacency:
   the "wrong" orientation is refuted by the twin of the first visit (it lies on another edge), so the accepted
   direction gap → sorted successor (ported) is all that is consumed — rlane NOTES_FINAL §6 risk 7 is closed for
   this row.
5. For the assembler: `generic_selector` consumes the accepted row theorems `localization` and `generic_table`
   (not the `G1`/`G2` internals), plus `F1.localizationData_mono`, `G2.punctured_of_le`, `P1.ne_of_isCrossing_pair`
   from Cores.lean; CV: `tracedSuccessor_of_mem_Ind`, `turn_visit_of_traced`, `weight_of_mixed`; SM:
   `geoSmoothingSuccessor_visit_of_mem`, `geoOwner_successor`, `geoCornerMark_exists`, `geoNextMark_eq_list_next`,
   `geometricVisitPosition_injective`, `traversalKey_injective`, `traversalKey_lt_iff`, `visitTwin_unique/_ne/
   _edge_ne/_involutive`, `crossingSign_swap`, `crossingParameter_interior_of_geometry`.
