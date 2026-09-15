# U_A2_REPORT — unit A2, the assembly lemma `fibre_identities` (R lane part 2)

File: `work/drafts/rlane2/U_A2.lean` = `Statements_FINAL.lean` + one inserted block (lines 1110–2057,
after `end Assembly`, before `hyp_R_of_near_of_chamberinv`). `diff Statements_FINAL.lean U_A2.lean`
is a pure insertion (`1109a1110,2057`; zero lines removed) — no definition, structure, theorem
statement, name or docstring of the frozen file was changed.

Compile (2026-09-14): `cd work/lean && lake env lean ../drafts/rlane2/U_A2.lean` → exit 0, exactly the
nine expected `sorry` warnings at the nine row theorems (L336, 426, 574, 661, 722, 785, 868, 921, 1001),
no other warning. `#print axioms` (scratch copy `/tmp/a2/U_A2_axioms.lean`): `A2_sum_powerset_three`
[propext, Classical.choice, Quot.sound]; `A2_fibreTerm_eq_eight`, `A2_fibre_identity_extreme`,
`A2_fibre_identity_generic`, `A2_fibre_identities`, `A2_cvTheoremData`, `A2_cvTheoremData_of_rows`,
`A2_cvRNear_of_rows` [propext, Classical.choice, Quot.sound, SM.lit_homfly] — the accepted literature
interface reached through `CV.X1` (NOTES_FINAL §12 risk 12); **no `sorryAx` anywhere in the unit** (no
row sorry is consumed: the bundles enter as hypotheses).

## 1. What is proved

### The assembly lemma (the task)

```
theorem A2_fibre_identities (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hF : FibrePartitionData E e f g δ) (hG : GenericTableData E e f g δ)
    (hAv : AvailabilityZeroOneData hn E e f g δ) (hSel : GenericSelectorData hn E e f g δ)
    (hGT : GenericTransportData hn E e f g δ) (hGS : GenericSelectedData hn E e f g δ)
    (hPZ : ExtremePairZeroData hn E e f g δ) (hET : ExtremeTransportData hn E e f g δ)
    (hES : ExtremeSelectedData hn E e f g δ) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t', OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      fibreTerm hn E e f g t ht.1 Q = fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q)
```
Its conclusion is verbatim the field `CvTheoremData.fibre_identities` (so
`CvTheoremData.of_fibre_identities hn hL hF (A2_fibre_identities …)` typechecks: `A2_cvTheoremData`).
Hypotheses: the three accepted cores 164/171/172-table and the seven bundles of rows 170, 172–177, all at
one radius `δ`. Row 168 (`ExteriorData`) is NOT a hypothesis: the assembly never reads it — the exterior
factor enters only inside the proofs of rows 173/174/176/177 (NOTES_FINAL §10), exactly as §11 U-A2
describes ("from the eight bundles" = the rows whose *conclusions* the identities need; 168's
conclusions are consumed by those rows, not by the summation).

Proof shape (R_ASSEMBLY_SPEC.md (4) + the availability paragraph):
* `FibrePartitionData.avail_card`: `|𝓐(Q)| ∈ {3, 1, 0}`. Cases `0`, `1`: `hAv.fibre_identity` verbatim.
* Case `3`: `A2_fullAvail_of_card_three` (`𝓐(Q) ⊆ T`, `|T| = 3` ⇒ `𝓐(Q) = T`, i.e. `FullAvail`).
  Then `A2_fibreTerm_eq_eight`: `Φ(Q) = T(∅) + T(a) + T(b) + T(c) + T(ab) + T(ac) + T(bc) + T(abc)`
  where `T(J) = rowTerm (Q ∪ J)` and absent rows are `0` — proved as `Φ(Q) = Σ_{J ⊆ T} rowTerm (Q ∪ J)`
  (`A2_fibreTerm_eq_sum_powerset`: `localFibre Q ⊆ 𝒫(T)` at full availability and a `J ⊆ T` outside the
  fibre is dependent, so `Q ∪ J ∉ Ind` and its row is `0` by `rowTerm_of_not_mem_Ind`) plus the
  eight-subset expansion `A2_sum_powerset_three` (`Finset.sum_powerset_insert` three times). The far
  fibre is indexed by the *near* triangle (`A2_fibreTerm_far_eq_eight`: `𝒫(T') = 𝒫(T).map (supportEmb hs)`,
  `A2_powerset_transport`, `Finset.sum_map`), so its eight rows are `rowTerm_{t'} (transportSupport hs (Q ∪ J))`
  — the exact form of the cross-wall fields of rows 173/174/176/177.
* The orbit is decided at `t` (`by_cases ExtremeLocal`) and carried to `t'` by
  `A2_extremeLocal_transport` (from `LocalizationData.complement_on_triangle` at the three pairs,
  `A2_edge_transport`); `CompleteLocal t' ↔ EmptyLocal t` likewise (`A2_completeLocal_transport`).
* **Generic orbit** (`A2_fibre_identity_generic`): the selected pair by `hSel.selected_pair_unique`; per
  branch (`_ac` canonical, `_ab`, `_bc` relabelled): `∅` = 173 `empty_row`; the two endpoint singletons =
  173 `endpoint_rows_canonical` (after `canonical_branch` turns `SelectedAC` into `s_a = s_b = s_c`) /
  `endpoint_rows_relabelled`; the two nonselected pairs = 172 `row_zero` on both sides (signs are
  wall-invariant by `GenericTableData.chamber_change`, so the nonselected conditions hold at `t'`; the far
  row is rewritten with `A2_transport_union_two`); `T` = `0` on both sides (`A2_rowTerm_triangle_eq_zero_of_generic`:
  a nonextreme local graph has an edge, so `Q ∪ T` is dependent); centre / selected pair = 174 `couple_*`
  read from the two-edge side, which is identified by `GenericTableData.selected_is_graph_selected`
  — if `t` is the two-edge side directly, if `t'` is, the couple is read at `(t', t)` with `hs.symm`
  and brought back by `A2_transport_back`; the selected pair is absent on the one-edge side (its edge is
  present there: `A2_rowTerm_eq_zero_of_interlaces`). Then `linarith` on the eight-term identity.
* **Extreme orbit** (`A2_fibre_identity_extreme`): singletons = 176 `transport_x/y/z`; the three pairs
  = `0` on both sides (`A2_extreme_pair_rows_zero`: 175 `pair_absent_on_complete` on the `K3` side,
  `pair_row_zero` on the empty side); `∅`/`T` = 177 `couple` read from the `K3` side (`t` or `t'`, by
  `extremeLocal_iff`), with `T` absent on the `K3` side (`full_absent_on_complete`); `linarith`.

### The assembly to row 178 (NOTES_FINAL §11 U-A2, "then `CvRNear`")

* `A2_cvTheoremData … : CvTheoremData hn E e f g δ` (= `CvTheoremData.of_fibre_identities` at the lemma).
* `A2_cvTheoremData_of_rows` : from the ten row *existentials* (`∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ <Bundle> δ`
  for 164, 171, 172-table, 170, 172, 173, 174, 175, 176, 177) to `∃ δ, … ∧ CvTheoremData hn E e f g δ`,
  radius = the minimum of the ten; needs the radius-restriction lemmas `A2_<bundle>_mono` for the nine
  bundles without one (`F1.localizationData_mono` exists).
* `A2_cvRNear_of_rows : (seven row theorems in their fixed shapes) → CvRNear` — the R6 `cv_R_near`.
  The accepted cores `localization`, `fibre_partition`, `generic_table` (sorry-free in Cores.lean) are
  consumed directly. The assembler's one-liners once rows 170, 172–177 are proved:
  `cv_R_near := A2_cvRNear_of_rows availability_zero_one generic_selector generic_transport
  generic_selected extreme_pair_zero extreme_transport extreme_selected` and
  `cv_R := hyp_R_of_near_of_chamberinv cv_R_near chamberinv_ii` (unit U-CV). Not written here, so that
  no row sorry is consumed in this unit.

## 2. Helpers added (all `A2_`-prefixed, all PROVED; 41 declarations, 948 lines)

Finset / transport: `A2_sum_powerset_three`, `A2_triangleCrossings_eq` (`T = {x_ef, x_eg, x_fg}`),
`A2_crossingTransport_xPair` (rfl; documents `crossingTransport hs (xPair h) = xPair ((hs _).mp h)`),
`A2_transportSupport_triangleCrossings`, `A2_transportSupport_union`, `A2_transport_union_one`,
`A2_transport_union_two`, `A2_transport_union_triangle`, `A2_transport_back`, `A2_powerset_transport`.
Event level: `A2_edge_transport`, `A2_extremeLocal_transport`, `A2_completeLocal_transport`,
`A2_rowTerm_eq_zero_of_interlaces`, `A2_rowTerm_triangle_eq_zero_of_generic`, `A2_fullAvail_of_card_three`,
`A2_fullAvail_transport`, `A2_fibreTerm_eq_sum_powerset`, `A2_fibreTerm_far_eq_sum_powerset`,
`A2_fibreTerm_eq_eight`, `A2_fibreTerm_far_eq_eight`.
Cases: `A2_extreme_pair_rows_zero`, `A2_fibre_identity_extreme`, `A2_fibre_identity_generic_ac`,
`A2_fibre_identity_generic_ab`, `A2_fibre_identity_generic_bc`, `A2_fibre_identity_generic`,
`A2_fibre_identity_full`.
Assembly: `A2_fibre_identities`, `A2_cvTheoremData`, `A2_fibrePartitionData_mono`,
`A2_genericTableData_mono`, `A2_availabilityZeroOneData_mono`, `A2_genericSelectorData_mono`,
`A2_genericTransportData_mono`, `A2_genericSelectedData_mono`, `A2_extremePairZeroData_mono`,
`A2_extremeTransportData_mono`, `A2_extremeSelectedData_mono`, `A2_cvTheoremData_of_rows`,
`A2_cvRNear_of_rows`.

## 3. Statement-level findings (nothing false found; no statement changed)

* The eight-row match closes with exactly the fields listed in NOTES_FINAL §11 — no bundle needed a
  stronger hypothesis. In particular the generic-orbit `T`-row and the one-edge-side selected-pair row
  are absent by the local graph alone (no bundle field is needed for them), and the far-side
  nonselected rows use only `row_zero` at `t'` plus the wall-invariance of the strand signs
  (`GenericTableData.chamber_change`).
* `GenericTableData` IS needed by the assembly (not only by the row proofs): `selected_is_graph_selected`
  names the two-edge side for the couple of row 174, and `chamber_change` carries the sign conditions
  across the wall. It is an accepted core, so this costs nothing.
* `ExtremeTransportData.graphs_complementary` and `GenericTransportData.canonical_branch` are consumed
  only as convenience (`canonical_branch` to enter `endpoint_rows_canonical`; the graph complement is
  re-derived from row 164 in `A2_completeLocal_transport`).
* Instance friction (rlane NOTES §6 risk 8): none met; `Finset.map_union/insert/singleton` unify with
  `instDecidableEqCrossing`, proof-irrelevance handles `xPair hef'` vs `xPair ((hs _).mp hef)` in `rw`.
* Unused-hypothesis note: `hL`'s only uses are `triangle_crossings` and `complement_on_triangle`;
  `hF`'s are `avail_card`, `avail_same`, `graph_on_W_same` (via `mem_outsideSupports_transport`).

## 4. Not done / for other units

The row theorems themselves (170, 172–177 and `cv_R`) are untouched (other units). `A2_cvRNear_of_rows`
is the plug for `cv_R_near`; U-CV writes `cv_R`.
