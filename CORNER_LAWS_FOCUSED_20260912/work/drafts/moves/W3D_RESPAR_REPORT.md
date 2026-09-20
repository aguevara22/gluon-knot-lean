# W3D_RESPAR_REPORT.md — unit RESPAR (`w3dp_`): the PARITY clause of `w3cx_outer_residue` and the bridge `2Λ(J_L) = #mixedSet`

Prover: W3D unit RESPAR, 2026-09-19 (no time bound, D-AUTH-20260919 §2; the reassessment discipline kept).
File: `work/drafts/moves/W3D_RESPAR.lean` = `W3C_Assembled.lean` (16 945 lines, sha256 `dbcd1037…`) with ONE pure
insertion after the `sorry` of `w3cx_outer_residue_data` (after line 16426): the block `/-! ## RESPAR … -/` at
16428–17819 (1 392 lines, 70 `w3dp_` declarations, sections `W3DP_Rec`, `W3DP_Geo`, `W3DP_Count`, `W3DP_Site`,
`W3DP_Config`). 18 339 lines, 1498 declarations, sha256 `dec91d520878a95d…`. Nothing existing edited: no statement,
name, docstring or body of the base changed (byte-identical outside the inserted block); nothing under `work/lean`
written; no `lake build`; no import added (the two counting lemmas of the accepted `RProof/ExtremeTransportUnits.lean`
that the task named were restated, ≈ 60 lines, rather than importing that module into the draft).

## 0. Result in one paragraph

**The parity clause (i) of the residue is PROVED at every configuration of the extended interface, on standard axioms
only**: `w3dp_parity_at` (17672) states clause (i) in the residue's exact binders and `w3dp_parity_at_proof` (17694)
proves it — `#print axioms` = `[propext, Classical.choice, Quot.sound]`. The proof is the analogue of row 176's
`r176m_bridge_count`: for every admissible double smoothing `J_L` of the carrier diagram `D_L = carrierDiagram q₀'` at
the double points of `x_ef', x_eg'` (the record-clause binders of `w3ck_three_components_ident_occ`), the crossings of
`J_L` are all positive and its mixed crossings are exactly the retained crossings of `q₀'` outside `Q' ∪ T'` whose two
visits lie on different `Q' ∪ T'`-carriers, so `twoLambda J_L = #w3cb_mixedSet` (`w3dp_twoLambda_eq_card_mixedSet`,
17280; in occurrence-clause form `w3dp_bridge_at`, 17631); an admissible `J_L` exists (`w3dp_exists_admissible`, the
constructed `smoothDiagram`s with `w3h_smooth_record_occ` / `smoothDiagram_record`) and `twoLambda` is even
(mp:zero-link, `w3dp_twoLambda_even`), whence the parity. **The leaf `w3cx_outer_residue_data` keeps its `sorry`**
(clause (ii), KNOT's identification, is unit RESID's black box); the glue for the assembler is
`w3dp_outer_residue_of_ident : w3dp_ident_at → w3cx_outer_residue` (17744) where `w3dp_ident_at` (17719) is clause
(ii) in isolation with its own `Λ`, and — should RESID deliver only the σ/HOMFLY half without `Λ` —
`w3dp_ident_of_homfly : w3dp_homfly_at → w3dp_ident_at` (17800) and `w3dp_outer_residue_of_homfly` (17815) supply
`Λ := #mixedSet / 2` from the parity and `2Λ(J_L) = 2Λ` from the bridge. `grep -c sorry` 6 → 6 (no new `sorry`,
no prose mention); 4 `declaration uses sorry` unchanged (4093, 11689, 13745, 16425); compile 0 errors, 55 s.

| item | result |
|---|---|
| **`work/drafts/moves/W3D_RESPAR.lean`** | 18 339 lines, 1498 declarations (1428 + 70 `w3dp_`), one insertion 16428–17819 |
| compile (`cd work/lean && lake env lean ../drafts/moves/W3D_RESPAR.lean`) | **exit 0, 0 errors**, 55 s; warnings = the inherited ones + my lints (unused section variables `[NeZero n]`, `ite`/deprecation-free); **4 `declaration uses sorry`** at 4093, 11689, 13745, 16425 — identical to the base |
| `grep -c sorry` | 6 before → **6** after; the inserted block contains no occurrence of the word |
| `check_W3_identity.py Port_GenericTransportSw_draft.lean W3D_RESPAR.lean` | 5 frozen blocks **IDENTICAL**; `imports` line `False` (baseline: `import RProof.RALedgers`); `G11_core_sw body starts with sorry: False` |
| `check_W3_statements.py W3D_RESPAR.lean` (cwd `work/drafts/moves`) | **40/42** byte-identical, differing = `['w3g_bigonData_smooth_arcST', 'w3g_bigonData_smooth_arcTS']` — exactly the two deliberately restated sub-leaves of W3C §1.2; `w3a_` 20/20; none missing |
| `#print axioms` (scratch copy, `W3D_RESPAR_AXIOMS.log`) | all `w3dp_` theorems whose statements do not mention `homfly`/`groupedPoly`: `[propext, Classical.choice, Quot.sound]`; `w3dp_outer_residue_of_ident`, `w3dp_ident_of_homfly`, `w3dp_outer_residue_of_homfly`: `+ lit_homfly` (through the Props' statements, as `w3cx_split_ident_of_residue`); `w3cx_outer_residue_data`: unchanged (`+ sorryAx`); `w3ck_extreme_selected`: unchanged |
| closed leaves | none (the leaf body is frozen for the assembler; the PARITY half is proved as `w3dp_parity_at_proof`) |
| black boxes | `w3dp_ident_at` (clause (ii), RESID) — equivalently `w3dp_homfly_at`; the other units' leaves untouched |

## 1. What is PROVED (file order; line = declaration)

**(a) Record level — the two smoothings of non-interlacing chords** (`section W3DP_Rec`, 16433–16773; on a one-circle
record `ρ`, `x : ρ.M`, `w : (ρ.smooth x).M`, KNOT's `w3ck_ArcA ρ x v := ρ.ArcBetween x v (τ x)`):
* `w3dp_steps_succ` (16445, `steps b (succ m) = (steps b m + 1) % |M|`), `w3dp_succ_ne_self`, `w3dp_two_le_card`,
  `w3dp_steps_succ_self`; **`w3dp_arcA_succ`** (16473: one forward step from the open arc `(b → τb)` stays on it or lands
  on `τ b`), **`w3dp_not_arcA_succ`** (16486: from the complementary arc, stays off or lands on `b`);
  `w3dp_smooth_succ_val_of_succ_eq_pair` (16511: the smoothed successor jumps from the predecessor of `τ x` to `succ x`,
  the mirror of the library's `smooth_succ_val_of_succ_eq`).
* Orbit lemmas for a permutation of a finite type: `w3dp_pow_mem`, `w3dp_sameCycle_imp`, **`w3dp_perm_iff`** (a permutation
  mapping `p` into `p` preserves `p` both ways, by `Finite.injective_iff_surjective`), `w3dp_sameCycle_iff`.
* `structure w3dp_NonInterlace ρ x w` (16558): `ArcA x w₀ ↔ ArcA x (τ w₀)` and `ArcA w₀ x ↔ ArcA w₀ (τ x)`.
  **`w3dp_reconnect_arcA_x`** / **`w3dp_reconnect_not_arcA_x`** (Claim A: the two arcs of `x` are carried into themselves
  by the second reconnection `(ρ^x).reconnect w = succ¹ * swap w (τw)`); `def w3dp_W` (`(w₀ → τw₀) ∪ {τw₀}`),
  `w3dp_smooth_succ_mem_W`, **`w3dp_reconnect_W`** (Claim B: `W` is carried into itself; the jumps over `x`, `τ x` stay in
  `W` by the non-interlacing).
* **`w3dp_smooth_comp_eq_iff`** (16673): on `ρ^x`, same circle iff same side of `x` (from KNOT's
  `w3ck_smooth_comp_eq_pair_iff` / `_self_iff` / `w3ck_arc_dichotomy`).
* **`w3dp_comp_eq_iff`** (16709) — **the components of the double smoothing**: for `m, m' : ((ρ^x)^w).M`,
  `comp m = comp m' ↔ (ArcA x m ↔ ArcA x m') ∧ ((ArcA x m ↔ ArcA x w₀) → (ArcA w₀ m ↔ ArcA w₀ m'))`. (→) by
  `Record.smooth_comp_eq_iff` and the two invariant sets; (←) on `w`'s circle by the library's
  `reconnect_sameCycle_self_or_pair` (every occurrence of the circle is on the `s₁`-cycle of `w` or of `τ w`) decided by
  `W`, off `w`'s circle by `reconnect_sameCycle_iff_of_comp_ne`. **No arc computation in the smoothed record is needed**
  — this replaces the `r176s_smoothRestrictIso` / restrict-of-restrict route of KNOT §8 for the component question.

**(b) Geometric level — the owner classes after three insertions** (`section W3DP_Geo`, 16778–17006, under
`attribute [local instance high] Classical.propDecidable` as SPLITB's `W3CB_Classical`):
* `def w3dp_Cell hP a m` (`traversalBetween` of the geometric positions of `a, m, visitTwin a`; definitionally
  `cycBetween` of the geometric keys, `w3dp_cell_iff_key`), `w3dp_cell_complement` (from the library's
  `traversalBetween_complement`).
* **`w3dp_owner_insert_iff`** (16815): one insertion of a retained crossing `a.1` into `T` — the `insert a.1 T`-owner of a
  visit `m` of the affected carrier, off the two visits of `a`, is the daughter of `τa` iff `Cell a m` and the daughter
  of `a` iff not (the library's `geoSmoothingSuccessor_insert_child_data` read through `geoMarkList_filter_left/right_iff`).
* **`w3dp_owner_eq_iff_three`** (16847): three insertions `a.1, b.1, c.1` of retained crossings of `q₀` into `Q`, `Sf`
  independent, a carrier `Z` of `Sf` owning only visits of the three (`hZ`) and owning a visit of `c.1` (`hZc`): for visits
  `m, m'` of `q₀` with crossings outside `Sf`, `owner_Sf m = owner_Sf m' ↔ (Cell a m ↔ Cell a m') ∧ ((Cell a m ↔ Cell a b)
  → (Cell b m ↔ Cell b m'))` — step 1 and 2 by `w3dp_owner_insert_iff` + `geoComponentForgetSwitch_fiber_affected`
  (distinct daughters) + `geoOwner_insert_iff_of_unaffected` + `geoOwner_eq_of_subset`, the pairs kept together by
  `geoIndependent_remaining_pair_owners`; step 3 (the third insertion splits the merged carrier into `Z` and the outer one,
  `Z` carries no retained visit) by `w3cb_step_affected` and `hZ`. The formula is the SAME as (a)'s.

**(c) The count** (`section W3DP_Count`, 17009–17183): `w3dp_IsMixed`, `w3dp_Mixed` (a crossing between different
components), `w3dp_mixedSignSum_eq` (`2ℓ_ij` as a sum over the mixed crossings — the accepted `s7h_mixedSignSum_eq` /
`r176l_mixedSignSum_eq`, neither in this import closure; proof copied), `w3dp_mixedSignSum_eq_card`,
**`w3dp_pair_count`** (over the ordered pairs `i < j` a crossing is mixed between `i, j` exactly once when mixed),
**`w3dp_twoLambda_eq_card_mixed`** (`2Λ` of a positive diagram = the number of its mixed crossings),
**`w3dp_twoLambda_even`** (`∃ Λ : ℤ, twoLambda D = 2Λ`, from `SM.zero_link.half_sum_integer`).

**(d) The bridge at a carrier diagram** (`section W3DP_Site`, 17187–17482, `hn hG hS q` as KNOT's K5): abbreviations
`w3dp_cg`, `w3dp_hT`, `w3dp_lv` (the parent visit `liftVisit`), `w3dp_arcA_iff_cell` (KNOT's `w3ck_arcA_iff_between`
read as a cell — definitionally), `w3dp_eq_or_pair_of_lv_eq`, `w3dp_site_nonInterlace` (the `w3dp_NonInterlace` data from
`¬ GeometricInterlaces` via KNOT's `w3ck_interlaces_iff_arcs` both ways), **`w3dp_site_comp_iff`** ((a) on the parent
visits), `w3dp_iso_comp_iff`, `w3dp_mixed_iff_comp`, and **`w3dp_twoLambda_eq_card_mixedSet`** (17280): for three
pairwise non-interlacing retained crossings `ca, cb, cc` of `q`, `Sf = insert cc (insert cb (insert ca S))` independent
with the `Z`-data, and the record-clause data `x, D₀, ι₀, hι₀, y, J, ι₁` of the double smoothing at the double points
of `ca, cb`: `twoLambda J = #(w3cb_mixedSet hG.cg S Sf q)`. Proof: `ι := ι₁.trans (ι₀.smooth _)` identifies `J.record`
with `(ρ^x)^w`; all crossings of `J` positive (`geoPositiveLift_sign` through `sgn_eq`, `smooth_sgn`);
`Finset.card_bij` with the parent crossing of the over occurrence: a mixed crossing of `J` is not over `cc` (over `cc`
both occurrences share their cells by the two other non-interlacings, hence the component), not over `ca, cb` (kept
occurrences), so its parent is outside `Sf` and by (a) = (b) its two visits have different `Sf`-owners; injective by
`w3dp_eq_or_pair_of_lv_eq`; onto `mixedSet` by `liftVisit_surjective` and the same equivalence backwards.

**(e) The configuration** (`section W3DP_Config`, 17487–17819): `def w3dp_bridge_occ D_L pxL pyL N` (the bridge in the
occurrence-clause binders of `w3ck_three_components_ident_occ`), `def w3dp_Admissible` (an admissible `J_L`),
`w3dp_bridge_occ_spec`, `w3dp_ident_occ_spec`; `w3dp_union_triangle_eq_classical` (`Q ∪ T` as three insertions in the
Classical instance form of `w3cb_insert_eq`, stated once); **`w3dp_bridge_occ_of`**, `w3dp_exists_crossing_over`,
**`w3dp_exists_admissible`** (the constructed `smoothDiagram`s; the second crossing is the image under `ι.Φ.symm` of the
kept occurrence over `cb`, its double point read through the occurrence clause); **`w3dp_bridge_at`** (17631: at every
configuration, with `w3cb_triangle_on_contact_at`, `PRE_176_graphs_complementary` (`EmptyLocal` = the three
`¬ GeometricInterlaces`), `P1.xPair_*_ne_*`, `CV.geoIndependent_of_mem_Ind`, and SPLITA's `w3ca_split_config` →
`core.central` for `Z = w3ca_Z`); **`def w3dp_parity_at`** / **`w3dp_parity_at_proof`**; **`def w3dp_ident_at`** /
**`w3dp_outer_residue_of_ident`**; `def w3dp_HomflyData`, `def w3dp_homfly_occ`, **`def w3dp_homfly_at`** /
**`w3dp_ident_of_homfly`** / **`w3dp_outer_residue_of_homfly`**.

## 2. The interface for unit RESID and for the assembler

* **Clause (i) — done.** `w3dp_parity_at` is byte-for-byte the residue's binders with the conclusion
  `∃ Λ : ℕ, (w3cb_mixedSet (geomAt E t' ht'.1) (transportSupport hs Q) (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) q₀').card = 2 * Λ`
  (the unused binders `_hQi'`, `_hS'` underscore-prefixed, as the residue does with its own unused ones); proved.
* **Clause (ii) — RESID's black box**, stated as the Prop `w3dp_ident_at` (17719): the residue's binders with the
  conclusion `∃ Λ : ℕ, w3ck_three_components_ident_occ (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀') (pt x_ef')
  (pt x_eg') Λ (groupedPoly … w3ca_A …) (… w3ca_B …) (… w3ca_C …)` — verbatim the second conjunct of the residue. No
  sorry'd instance was added (the leaf `w3cx_outer_residue_data` already is the sorry'd black box and the register counts
  its `sorryAx` sources); the assembler closes the leaf by
  `theorem w3cx_outer_residue_data : w3cx_outer_residue := w3dp_outer_residue_of_ident <RESID's theorem : w3dp_ident_at>`.
* **If RESID proves the σ/HOMFLY half only** (the `Λ`-free route of KNOT §5/§8, `knotRestrict (σ i) ≅ …`,
  `r176s_homfly_of_liftBlock`): state it as `w3dp_homfly_at` (17776; conclusion `w3dp_homfly_occ (carrierDiagram_L q₀')
  (pt x_ef') (pt x_eg') fA fB fC`, i.e. the occurrence clauses → `∃ σ : Fin 3 ≃ Fin J_L.Γ.c, homfly (knotRestrict (σ 0)) =
  fA ∧ …`), and the assembler uses `w3dp_outer_residue_of_homfly`. RESID then never needs `twoLambda J_L = 2Λ`: the bridge
  supplies it for `Λ := #mixedSet / 2`.
* **Reusable for RESID's identification** (the components of `J_L`): `w3dp_site_comp_iff` (17252) gives, for two
  occurrences `m, m'` of `(ρ^x)^w` at the carrier diagram, `comp m = comp m' ↔` the cell formula on the parent visits;
  `w3dp_owner_eq_iff_three` gives the same formula for the `Q' ∪ T'`-owners. Together: **an occurrence of `J_L` (via
  `ι := ι₁.trans (ι₀.smooth _)`) lies on the component of another iff their parent visits have the same `Q' ∪ T'`-carrier
  (for parents outside `Q' ∪ T'`)** — the occurrence-level identification of the three components with `A, B, C` that the
  `knotRestrict` isos need (`CV.crossKeep_liftBlock_iff` then reads the self-crossing sets as `liftBlock (gCC (Q'∪T') A)`
  etc.; the component carrying `cc` is the one whose parents are `Q' ∪ T'`-owned by the outer carrier of `cc`'s outer
  visit, with `cc` itself an extra self crossing — the RI-unknot factor of cor:groupedknot (A)/(B)).
* Nothing else of the residue's consumers changes: `w3cx_split_ident_of_residue`, `w3cx_split_core_of_residue`,
  `w3ck_split_ident_data`, `w3cb_split_core_data`, the `w3ck_` chain are untouched.

## 3. Rules

* Rule (1): only `w3dp_`-prefixed material, one insertion; every existing statement, name, docstring and body byte-identical
  (the file outside 16428–17819 is `W3C_Assembled.lean`). Rule (2): the other units' leaves untouched
  (`w3cs_not_kink_site_data`, `w3bi_esc_outer_data`, `w3b_reparam_switch`, and the residue leaf itself); the black box
  `w3dp_ident_at` / `w3dp_homfly_at` stated and reported (§2). Rule (3): the leaf is TRUE as stated as far as this unit
  reaches (clause (i) proved; nothing false found; no corrected form needed). Rule (4): done (§0 table; the private
  scratch files `S1–S3.lean`, `W3D_scratch.lean`, `W3D_axioms_scratch.lean` under the unit's private scratch directory
  `…/scratchpad/respar_private/`, compiled against `SM.BigonDeletion` + `RProof.RALedgers` with the KNOT/SPLITB
  statements restated as `sorry` stubs, then spliced into a full-file copy and compiled; the stubs are not in the file).
* No lemma failed twice (the reassessment audit was not triggered). **One method change, recorded**: the record-level
  component characterisation was first proved in the STRONG form `(ArcA x m ↔ ArcA x m') ∧ (ArcA w₀ m ↔ ArcA w₀ m')`
  (S1 compiled); the geometric side delivers cheaply only the WEAK form (the second clause conditional on being on `b`'s
  side of `a`; the strong form would need the constancy of the `b`-cell on the far side, a six-point cyclic-order lemma),
  so the record theorem was restated in the weak form (same proof, one hypothesis less used) and both sides match.
  This is why (a) and (b) share their formula.
* `RProof.ExtremeTransportUnits` was NOT imported (it is not in the draft's import closure; adding an import would change
  the `imports` line the identity checker reads): the two counting facts used from it (`r176l_IsMixed`,
  `r176l_mixedSignSum_eq`) are restated as `w3dp_IsMixed`, `w3dp_mixedSignSum_eq` (≈ 60 lines). Port-time option: drop
  them by importing.

## 4. Pitfalls met (for RESID and the assembler)

* `Finset.mem_filter` does NOT `rw` on `w3cb_mixedSet` (its `filter` carries the composite `Decidable` instance of
  `open scoped Classical`, not `Classical.propDecidable` directly): use `simp only [w3cb_mixedSet, Finset.mem_filter]`.
* The insertion lemmas of `SM/GeoCarrierCount.lean` and SPLITB's `w3cb_step_affected` elaborate `insert v.1 T` under
  `Classical.propDecidable`; a section using them needs `attribute [local instance high] Classical.propDecidable`, and
  `{e, f} : Finset (ZMod n)` must then NOT be elaborated in that section (it would pick the Classical instance and no
  longer match `xPair`'s `IsCrossing P {e, f}`) — hence `w3dp_union_triangle_eq_classical` outside the section with the
  `Crossing P` instance written out (`@insert _ _ (@Finset.instInsert _ fun x y => Classical.propDecidable (x = y))`),
  proved by `ext; simp only [Finset.mem_union, Finset.mem_insert, P1.mem_triangleCrossings_iff]; tauto` (instance-agnostic).
* `set Sf := insert …` does not abstract inside hypotheses whose TYPE depends on the set (`Z : GeoComponent hP Sf`,
  `hZ`): `revert` them first, `set`, `intro` again (or generalise the statement over `Sf` with a defining equation and
  `subst`, which is what `w3dp_owner_eq_iff_three` does).
* `rw` does not see the `=` inside `≠`: `rw [ne_eq]` first; `ι.pair_eq` needs the pair written as `J.record.pair v`
  — state `have e : ι.Φ (J.underVisit c) = ρ².pair (ι.Φ (J.overVisit c)) := ι.pair_eq (J.overVisit c)` (defeq) and
  rewrite with `e`.
* An anonymous constructor `⟨u, hk⟩` for an element of `(ρ.smooth x).M` elaborates at the subtype and then `rw` fails
  with "motive is not type correct": ascribe the type `(⟨u, hk⟩ : (ρ.smooth x).M)` or use `refine
  (Record.smoothKeep_iff _ _ _).mpr ⟨…⟩` instead of `rw [Record.smoothKeep_iff]`.
* `liftVisit hn hG' hT q v` and the abbreviation `w3dp_lv hn hG hS q v` are defeq but `rw` matches syntactically: keep
  equations in the abbreviation's form (`have hlv : w3dp_lv … = v := hu`).
* `w3ck_arcA_iff_between` IS `w3dp_Cell` on the parent visits by `Iff.rfl`-level defeq (Sigma eta, `visitTwin_crossing`
  rfl): `w3dp_arcA_iff_cell` is a one-liner; likewise `geoMarkPosition hP (Sum.inr v) = geometricVisitPosition hP v`
  (rfl) and `traversalBetween_iff_cycBetween` (Iff.rfl).
* `Record.smooth_comp_eq_iff` (LinkRecord): same circle in `ρ^x` iff `SameCycle` under `reconnect x = succ * swap x (τx)`
  — the components of any smoothing are cycles of a permutation, and the geometric `geoSmoothingSuccessor (insert v.1 T)
  = geoSmoothingSuccessor T * swap (inr v) (inr (twin v))` has literally the same shape; the two sides of this unit are
  the same argument on two types, glued by `cycBetween` of the traversal keys.
* `if_pos`/`if_neg` are deprecated for `ite_eq_left`/`ite_eq_right` (as the assembler's `r176m_card_rest` uses).

## 5. Times (UTC / ET)

05:41 / 1:41am start (author response, register §A-15–A-18, the six reports, the library API: `Record`, `smooth`,
`reconnect`, `steps`, `geoSmoothingSuccessor_insert_child_data`, `liftVisit`, `carrierDiagram`); record level S1
(Claims A/B, `w3dp_comp_eq_iff`) compiled; geometric level S2 compiled; count + site S3 compiled (the site theorem in four
elaboration passes); the full-file scratch with the configuration level compiled first with four elaboration errors, then
0 errors; axioms, checks, install, this report at 07:04 / 3:04am ET (≈ 1 h 25 min). Every compile of the full file 55–62 s; scratch files 10–15 s.
