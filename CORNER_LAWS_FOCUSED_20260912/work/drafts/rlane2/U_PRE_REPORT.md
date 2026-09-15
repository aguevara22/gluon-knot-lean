# U_PRE_REPORT — unit PRE: the X₁-free presupposition clauses of rows 170, 173, 175, 176, 177

Written 2026-09-14 06:49 UTC / 2:49am ET by the PRE unit (R lane part 2, plan of record `NOTES_FINAL.md` §11 "U-PRE").
File: `work/drafts/rlane2/U_PRE.lean` (1597 lines = `Statements_FINAL.lean` (1178) + 419 inserted lines).
Compile: `cd work/lean && lake env lean ../drafts/rlane2/U_PRE.lean` → exit 0, **0 errors**, exactly the nine
expected `sorry` warnings (the nine row theorems, untouched: L502 `exterior`, L648 `availability_zero_one`,
L796 `generic_selector`, L902 `generic_transport`, L963 `generic_selected`, L1114 `extreme_pair_zero`,
L1254 `extreme_transport`, L1340 `extreme_selected`, L1420 `cv_R`), no other warning (~10 s).
`diff Statements_FINAL.lean U_PRE.lean` is six pure insertion hunks (`225a226,391`, `424a591,646`,
`659a882,900`, `783a1025,1112`, `866a1196,1252`, `918a1305,1337`): **no definition, structure, theorem
statement, name or docstring of the frozen file was changed.**

## 1. Deliverables — twelve field lemmas, each with exactly the field's type

Convention (the accepted `F1.<field>` / `P1.<field>` / `G1.<field>` pattern of work/lean/RProof/Cores.lean):
a field lemma takes the accepted core bundle it needs at the radius `δ` (or nothing) and has verbatim the
field's type, so the assembler discharges the field by `<field> := PRE_<row>_<field> …` in the structure
instance. Checked by compiling structure instances of all five bundles with the PRE lemmas in the presupposition
fields and `sorry` in the X₁ fields (scratch `/tmp/pre/check.lean` = `U_PRE.lean` + the five `example … where`
blocks; exit 0). `#print axioms` on every PRE lemma: `[propext, Classical.choice, Quot.sound]` only — no
`sorryAx`, no `SM.lit_homfly` (the clauses are X₁-free).

| row | field | lemma (U_PRE.lean line) | hypothesis | proof |
|---|---|---|---|---|
| 170 | `fibre_zero` | `PRE_170_fibre_zero E e f g δ` (L597) | none | `𝓐(Q) = ∅` (`Finset.card_eq_zero`); the fibre is the power set of `𝓐(Q)` (`PRE_localFibre_eq_powerset`, availability `≤ 1` ⇒ every subset independent) = `{∅}` |
| 170 | `fibre_one` | `PRE_170_fibre_one E e f g δ` (L607) | none | `𝓐(Q) = {z}` (`Finset.card_eq_one`); power set of `{z}` = `{∅, {z}}` (`Finset.subset_singleton_iff`) |
| 170 | `fibre_correspond` | `PRE_170_fibre_correspond hF` (L622) | `hF : FibrePartitionData E e f g δ` | `hF.avail_same` carries `𝓐(Q)` across the wall; card `≤ 1` on both sides, both fibres are power sets; `Finset.subset_map_iff` + `supportEmb_apply` identify the power set of the image with the image of the power set |
| 173 | `canonical_branch` | `PRE_173_canonical_branch hG` (L887) | `hG : GenericTableData E e f g δ` | `hG.nonzero` (`sign_ne_zero`) + `hG.generic_iff_nonalternating`; the sign case analysis `PRE_selectedAC_iff_all_eq` (`decide` over `SignType³`): nonzero nonalternating ∧ `s_a = s_c` ⇒ `s_b = s_a` |
| 175 | `pair_absent_on_complete` | `PRE_175_pair_absent_on_complete E e f g δ` (L1030) | none | `J = {x, y}` (`Finset.card_eq_two`), both in `T`, distinct ⇒ interlaced on the `K3` side (`PRE_interlaces_of_complete`) ⇒ `Q ∪ J ∉ Ind` (`CV.mem_Ind_iff`). `FullAvail` unused |
| 175 | `pair_present_on_empty` | `PRE_175_pair_present_on_empty E e f g δ` (L1049) | none | `J ∈ Ind` (empty local graph, `PRE_mem_Ind_of_empty`), `J ⊆ 𝓐(Q) = T` ⇒ `F1.compose_geom`. `J.card = 2` unused |
| 175 | `third_singleton_piece` | `PRE_175_third_singleton_piece hPar` (L1067) | `hPar : ParityData E e f g δ` | `z ∈ U(Q ∪ J)` (`PRE_third_mem_U`: `z ∉ Q` by disjointness, `z ∉ J`, no interlacing with `Q` by full availability, none with `J` by the empty graph); `z` isolated in the residual graph: a residual neighbour `c` is outside `T` (a triangle crossing `≠ z` is in `J ⊆ S`, `PRE_mem_of_third`), then `hPar.interlaced_pair` makes its mask a bundle pair of card 2 (`P1.filter_card_two`) whose other member lies in `J`, contradicting `c ∈ U(Q ∪ J)`; isolated ⇒ piece `{z}` (`PRE_pieceLabels_eq_singleton_of_isolated` via `SimpleGraph.ConnectedComponent.eq` and a one-step walk case split) |
| 176 | `singleton_rows_present` | `PRE_176_singleton_rows_present E e f g δ` (L1201) | none | `{j}` independent (`PRE_mem_Ind_of_card_le_one`), `{j} ⊆ 𝓐(Q) = T` ⇒ `F1.compose_geom`. `ExtremeLocal` unused |
| 176 | `graphs_complementary` | `PRE_176_graphs_complementary hL` (L1216) | `hL : LocalizationData E e f g δ` | `hL.complement_on_triangle` at `hs := hL.crossing_set_constant`, applied to the three pairs (`crossingTransport hs (xPair hef) = xPair hef'` definitionally by proof irrelevance); `CompleteLocal ↔ ¬¬AB ∧ ¬¬AC ∧ ¬¬BC` |
| 176 | `sign_branch` | `PRE_176_sign_branch hG` (L1243) | `hG : GenericTableData E e f g δ` | `hG.extreme_iff_alternating` forwards (`IsAlternating` is literally `s_a = s_c ∧ s_b = -s_a`) |
| 177 | `full_present_on_empty` | `PRE_177_full_present_on_empty E e f g δ` (L1311) | none | `T ∈ Ind` on the empty side, `T ⊆ 𝓐(Q) = T` ⇒ `F1.compose_geom` |
| 177 | `full_absent_on_complete` | `PRE_177_full_absent_on_complete E e f g δ` (L1324) | none | `x_ef ≠ x_eg ∈ Q ∪ T` interlace (`EdgeAB`, `hK.1`) |

Row theorems: NOT touched (rule (2)); the remaining fields of these rows are X₁-dependent and belong to
units AV / GT / PZ / ET / ES (NOTES_FINAL.md §11).

## 2. Helper lemmas added (all prefixed `PRE_`, section `PREHelpers`, L226–391, before the row-168 section)

`PRE_mem_Ind_of_subset` (independence hereditary; not used by the field lemmas, kept for the assembler),
`PRE_mem_Ind_of_card_le_one`, `PRE_localFibre_eq_powerset` (availability `≤ 1` ⇒ `Ind(G[𝓐(Q)]) = 𝒫(𝓐(Q))`),
`PRE_selectedAC_iff_all_eq` (`decide`), `PRE_interlaces_of_complete`, `PRE_not_interlaces_of_empty`,
`PRE_mem_Ind_of_empty`, `PRE_union_mem_Ind_of_fullAvail` (the `F1.compose_geom` instance at `𝓐(Q) = T`),
`PRE_mem_of_third` (`T ∖ J = {z}` for a two-element `J ⊆ T`), `PRE_third_mem_U`,
`PRE_eq_of_reachable_of_isolated` (graphs, general), `PRE_pieceLabels_eq_singleton_of_isolated`
(CV:def:pieces: an isolated vertex of the residual graph is a singleton piece).

## 3. Readings checked against the frozen texts (no statement changed; none found false)

* Row 170 (R_ASSEMBLY_SPEC.md:61 "At availability zero or one the local supports themselves correspond"):
  the fibres are `{∅}` / `{∅, {z}}` on BOTH sides (subsets of a `≤ 1`-element set are independent whatever the
  local graph), and the far fibre is the `supportEmb` image — exactly the statements; the cross-wall clause
  needs only `FibrePartitionData.avail_same` (through R-LOC-2 (4)), as NOTES_FINAL §11 predicted.
* Row 173 (R_GENERIC_COMMON_TRANSPORT_PROOF.md (1) "If the `b` sign were opposite, the triple would be one of
  the two alternating triples"): the kernel-checked `decide` confirms the judge's hand check (§13):
  `s_a = s_c ∧ ¬alternating ∧ signs ≠ 0 ⇒ s_b = s_a`, and conversely `s_a = s_b = s_c ⇒ SelectedAC`.
* Row 175 (R_EXTREME_PAIR_ZERO_PROOF.md:22–38): `pair_absent_on_complete` holds for EVERY `Q` (full availability
  is not needed — the pair is already dependent); `pair_present_on_empty` and `third_singleton_piece` use full
  availability exactly as printed (":23–24 … nonadjacent to every member of `Q`", ":27 nonadjacent to `Q` by
  full availability"). The singleton-piece step uses R-PAR (P1) "quantified over every crossing `c` outside
  `T`" (`ParityData.interlaced_pair`, which also names the pair) — the text's own argument (:30–36); the
  additional case "no other local residual crossings, because `x, y` are in the support" (:36–37) is
  `PRE_mem_of_third`. The piece is read through CV:def:pieces (`CV.pieceOf` = the connected component of `z`
  in `G_P[U(S)]`, `CV.pieceLabels`), so the clause states the `{z}` singleton piece literally.
* Row 176 (R_EXTREME_SINGLETON_TRANSPORT_PROOF.md:23–26): `singleton_rows_present` holds on every side (no
  orbit hypothesis needed: "every `Q ∪ {j}` is independent on both sides"); `graphs_complementary` is R-LOC-2
  clause 4's corollary (`LocalizationData.complement_on_triangle`) at the three pairs; `sign_branch` is the
  accepted `extreme_iff_alternating` (the field's conjunction is `IsAlternating` unfolded, so the "(3)" sign
  data `s_x = σ, s_y = −σ, s_z = σ` is exactly `s_a = s_c ∧ s_b = −s_a`).
* Row 177 (R_EXTREME_SELECTED_COUPLE_PROOF.md:27–30): `full_present_on_empty` under full availability;
  `full_absent_on_complete` for every `Q` (":29–30 On `H`, `T` is not independent because its induced graph is
  `K3`"), as the bundle quantifies.

## 4. Notes for the assembler

* Radii: the bundle hypotheses are at the same `δ` as the target bundle; the assembler takes the common radius
  of the accepted rows (`F1.localizationData_mono`, `F1.parityData_mono`, `G2.parityData_of_le` /
  `goodRadius_of_le` patterns in Cores.lean) exactly as `CvTheoremData.of_fibre_identities` expects
  `LocalizationData` + `FibrePartitionData` at one `δ`.
* Instance friction (NOTES_FINAL §12 risk 13) did not arise: `F1.mem_localFibre`, `F1.mem_avail`,
  `G2.mem_interlacedTriangle_iff`, `CV.mem_U_iff`, `CV.mem_pieceLabels` are instance-generic; no `convert` needed.
* `PRE_170_fibre_correspond` states `hF.avail_same` at `transportSupport hs Q` (definitionally
  `Q.map (crossingTransport hs).toEmbedding`) — accepted by `exact` without unfolding.
* Unused-hypothesis remarks (for the review note, not statement changes): `FullAvail` in
  `pair_absent_on_complete`, `J.card = 2` in `pair_present_on_empty`, `ExtremeLocal` in
  `singleton_rows_present` are presuppositions of the printed scene and are simply not consumed.
