# W3B_E_REPORT.md — Wave 3b, unit E (the three `w3e_` sub-leaves of the switched G11 assembly)

Written 2026-09-15 22:20 UTC / 6:20pm ET by the unit-E prover (bounded window, audit A-177-1; hard stop
2026-09-16 00:30 UTC not reached — finished at 22:18 UTC).  File: `work/drafts/moves/W3B_E.lean`
(= `W3_A1_Assembled.lean` + unit E; 8011 lines, was 7827).  Nothing under `work/lean` touched; no `lake build`.

## 0. Result

**`w3e_strong_case_sw` is sorry-free on the registered axioms.**  `#print axioms` on the scratch copy
`UE_Axioms.lean` (the file + 7 `#print axioms` lines; exit 0):

| declaration | axioms |
|---|---|
| **`SM.Link.w3e_strong_case_sw`** (row-level, the switched `G11_strong_case`) | `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` — **no `sorryAx`** (identical to `G11_core_sw`'s footprint, assembly report §4) |
| `w3e_xs_point`, `w3e_liftVisit_σD_sw`, `w3e_recordIsoData_sw` | `[propext, Classical.choice, Quot.sound]` |
| `w3be_lift_six`, `w3be_liftVisit_fst_eq_iff` (new helpers) | `[propext, Classical.choice, Quot.sound]` |
| `G11_core_sw` (unchanged) | the six, no `sorryAx` |

Full compile `lake env lean ../drafts/moves/W3B_E.lean`: **0 errors**, 52 s (31 warnings, all pre-existing
`if_pos`/`if_neg` deprecations + the 7 `declaration uses sorry` of the other units, plus 10 new deprecation
warnings in `w3e_xs_point`, see §3).  `grep -c sorry`: **10 → 7** (`W3_A1_Assembled.lean` → `W3B_E.lean`).
`check_W3_identity.py Port_GenericTransportSw_draft.lean W3B_E.lean`: all five frozen blocks IDENTICAL, imports OK.
`check_W3_statements.py W3B_E.lean`: 42/42 `w3*_` statements byte-identical, no skeleton declaration missing.
`diff W3_A1_Assembled.lean W3B_E.lean`: exactly three removed lines, each `  sorry` (lines 7552, 7570, 7603 of the
assembled file); everything else is insertion inside `section W3E`.

## 1. Closed (3 of 3) — what each proof is

| sub-leaf | line (W3B_E) | proof |
|---|---|---|
| `w3e_xs_point` | 7539 | `set C := w3e_configOfSw …`; the three double points `C.D₀.Γ.crossingPoint C.x_mp = crossingPoint (xPair hcef)` etc. from the Sw copies `G11_ParamsSw.gu3_cp_v_mp/mq/pq` (:852–860, `gu3_crossingPoint_symm` on the one-component lift) + `v_mp_fst` + the accepted `gu2_xmp_eq / gu2_xmq_eq / gu2_xpq_eq` (GenericTransport :9849–9871, the double points of the configuration are those of `P`); then `show C.D₀.Γ.crossingPoint C.xs = _`, `rw [C.xs_eq, (rfl : C.sw = sw)]`, `unfold w3e_swPair`, two `by_cases` on `sw` (`if_pos`/`if_neg`).  38 lines. |
| `w3e_liftVisit_σD_sw` | 7618 | verbatim `G11_liftVisit_σD` (:10793–10850) with `gu6_lift_six → w3be_lift_six`, `G11_Params.gu6_σD_apply / gu6_σ_v** / gu6_σ_of_not_local → G11_ParamsSw.*` (the DE copy, :5378–5405).  The accepted `gu6_local_cases`, `gu6_σP_*`, `gu6_σP_of_not_local`, `CV.liftVisit_injective` are `C`-free and reused by name.  47 lines. |
| `w3e_recordIsoData_sw` | 7701 | `G11_recordIsoData` (:10852–10920) with the switched bits: same `ψ`, `Λ`, `hΛ`, `hΛtw`, `hΨtw`; NEW `hΛx : ∀ v, (Λ v).1 = x' ↔ v.1 = x` (from `w3be_liftVisit_fst_eq_iff` on both lifts + `hΛ` + `visitTransport_crossing` + `(crossingTransport hs).injective.eq_iff`); the accepted clause-(c) computation is factored as `hΛbit : ∀ v, G'.overBit (Λ v) = G.overBit v` and `hΛsgn` (both signs `+1`); then (a) as accepted after `change` to the switched `VisitBetween` (defeq, `w3b_visitBetween_switch`), (b) as accepted, (c) `hbit` then `w3b_overBit_switch_of_visitIso Λ x x' hΛx hΛbit`, (d) `hsgn` then `w3b_sign_switch_of_visitIso Λ x x' hΛx hΛsgn`.  `Φ := Ψ.symm.trans Λ` as in the accepted proof.  76 lines. |

New `w3be_` material (2 declarations, both in `section W3E`, both PROVED):
* `w3be_lift_six` (:7581, 36 lines) — `gu6_lift_six` (:10758) restated over `w3e_configOfSw` without `halt`; body verbatim
  (`gu6_liftVisit_symm_eq` ×6, `G11_Params.gu6_isCrossing_comm`).
* `w3be_liftVisit_fst_eq_iff` (:7678, 16 lines) — `(liftVisit v).1 = c ↔ v.1 = x` given `G.Γ.crossingPoint x = crossingPoint c`
  (`CV.liftVisit_fst`, `CV.crossingPoint_liftCrossing`, `Generic.crossingPoint_injective`, `crossingPoint_injective_of_geometry`).
  Generic (no `G11_ConfigSw`); the realiser W3-I may reuse it to identify `x_H`/`x_L` with the consumer's crossings.

Total new lines: 184 (est. was 0.7–0.9k; the switched clauses reduce to the `w3b_*` transport lemmas, so the copy is
much shorter than budgeted).

## 2. Open / black boxes

* Nothing open in unit E.  No new `w3be_` sorry was needed from another unit.
* Untouched (other units, left as black boxes with their `sorry`): `w3b_reparam_switch` (:4094, optional, unit b),
  `w3g_bigonData_smooth_arcST` (:7883), `w3g_bigonData_smooth_arcTS` (:7910), `w3h_record_core` (:7941),
  `w3h_smooth_record_occ` (:7954), `w3h_restrict_switch_deleted` (:7963), `w3h_hrec` (:8004).  These are the 7 remaining
  `sorry`; none reaches `w3e_strong_case_sw`.
* No sub-leaf was found false as stated (rule 3 not triggered).

## 3. Notes / pitfalls for the assembler

* `w3e_recordIsoData_sw` was developed in a scratch file (`scratchpad/unitE/UE_S1.lean`, imports = the file's,
  restating only the four `w3b_*` lemmas it uses) and pasted; the only failure met was `simp only [Equiv.trans_apply]`
  on the switched goal ("not type-correct under `implicit` transparency" — the `switch` layer, skeleton report §5);
  replaced by `change … .VisitBetween (Λ (Ψ.symm v)) …`.  Keep using `change`/`exact` rather than `simp` across
  `switch`.
* The scratchpad directory is SHARED between concurrent sessions: my first `S1.lean` was overwritten by another unit
  within a minute.  Use a private subdirectory (`scratchpad/unitE/`) for scratch files.
* `w3e_xs_point` uses `if_pos`/`if_neg` (10 deprecation warnings, :7570–7575); cosmetic, same pattern as the skeleton's
  `xs_eq`/`w3e_swPair` proofs; fix with `ite_eq_left/right` or `simp [hs0]` at port time if wanted.
* Argument order of the reused accepted lemmas, for the record: `gu2_xmp_eq hn hG hT q hcef htri hmp`,
  `gu2_xmq_eq hn hG hT q hcef hceg htri hmq`, `gu2_xpq_eq hn hG hT q hcef hceg hcfg htri hpq`;
  `G11_ParamsSw.gu3_cp_v_mp (C := C)` (π not included, `C` implicit).
* Times: start 22:01 UTC / 6:01pm ET, unit closed and audited 22:18 UTC / 6:18pm ET.
