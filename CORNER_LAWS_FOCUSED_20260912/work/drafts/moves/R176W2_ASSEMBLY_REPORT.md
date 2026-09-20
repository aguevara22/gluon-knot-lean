# R176W2_ASSEMBLY_REPORT — assembly of the row-176 wave-2 units (CURL + OUTER + MIXED) on the port draft

Row-176 wave-2 assembler, 2026-09-15 23:30–23:50 UTC / 7:30–7:50pm ET.  Inputs: `R176_Port_draft.lean` (6339 lines, md5
`0baaa8470083ebe279e476b380e5dee5`), `R176W2_CURL.lean` (6709), `R176W2_OUTER.lean` (7984), `R176W2_MIXED.lean` (6835) with their
reports.  Output: `R176W2_Assembled.lean` (9013 lines, md5 `6586f5608207439dc0e7ff01875ecbae`), the port modules under
`port/R176/` (`PORT_REPORT.md` there), the generator `assemble_R176W2.py` (+ `R176W2_compose_part.lean`, `R176W2_row_part.lean`,
`R176W2_units_header.txt`, `R176W2_row_header.txt`), the scan `clash_scan_R176W2.py` (+ `clash_scan_R176W2.json`).  Nothing written
under `work/lean`; no `lake build`.

## 0. Result

**Row 176 is CLOSED.**  `RProof.extreme_transport` (FIXED name; statement byte-identical to the Wave1 fixed statement, = `RowShape
@ExtremeTransportData` instantiated) is proved unconditionally; `#print axioms` on a scratch copy of the assembled file and through
the ported modules gives exactly
`[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]`
— the registered standard + literature axioms, **no `sorryAx`**.  `grep -c sorry R176W2_Assembled.lean` = 0 (the draft's header line,
the only earlier hit, is replaced).

| check | result |
|---|---|
| (1) units appended only | yes — CURL `6336a6337,6706`, OUTER `6336a6337,7981` (both inserted before the draft's closing `end`/`end RProof`, inside its last `namespace RProof`/`noncomputable section`), MIXED `6339a6340,6835` (after `end RProof`, self-contained block); 0 `<` lines in every diff; prefixes `r176c_`/`r176o_`/`r176m_` on all 14 / 55 / 24 declarations; no `import`/`set_option`/global `attribute` (OUTER's 3 `attribute [local instance 2000] r176l_decEq` are section-local) |
| (2) assembly | `R176W2_Assembled.lean` = draft 1–6336 (line 1 → new header) + CURL 6337–6706 + OUTER 6337–7981 + draft 6337–6339 + MIXED 6340–6835 + assembler section (122 lines, `r176a_`) + row block (41 lines); 446 declarations, 446 distinct names, 0 duplicates; 0 statement-identical pairs across the three units; nothing renamed |
| (3) the Props | `r176s_curl_removal` PROVED (CURL `r176c_curl_removal_proof`); `r176_mixed_bridge` PROVED (MIXED `r176m_mixed_bridge_proof`); `r176_outer_carriers_L` **FALSE as stated** (OUTER §2) — replaced by the PROVED corrected split `r176o_outer_carriers_L_corrected_proof`, which introduces the mirrored bridge Prop `r176o_mixed_bridge'`; **`r176o_mixed_bridge'` PROVED here** (`r176a_mixed_bridge'_proof`, §2) |
| (4) compile | `cd work/lean && lake env lean ../drafts/moves/R176W2_Assembled.lean` → exit 0, **0 errors**, 44 s; 10 warnings, all `linter.unusedSectionVars` notes inherited from the units (§3) |
| axioms | as above; per piece: `r176c_curl_removal_proof` standard + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness`; `r176m_mixed_bridge_proof`, `r176a_mixed_bridge'_proof`, `r176o_outer_carriers_L_corrected_proof` standard only |
| (5) clash scan | 0 fully-qualified clashes against `work/lean`; 3 informational short-name coincidences (Site_176's `s176_CornerSite.eIn/eOut/eIn_ne_eOut`, pre-existing); `RProof.extreme_transport` declared nowhere in `work/lean` |
| (6) port | `port/R176/RProof/ExtremeTransportUnits.lean` (8988 lines) and `port/R176/RProof/ExtremeTransport.lean` (48 lines), compiled in that order with module semantics (64 s / 24 s / probe 28 s, 0 errors), 0 occurrences of `sorry`/`#print`/`#eval`; `PORT_REPORT.md` |

## 1. Verification of the three unit files: APPENDED ONLY

`diff R176_Port_draft.lean R176W2_<unit>.lean` is a single `a` hunk in each case (no `c`/`d`, no `<` line): CURL 370 added lines
(6337–6706), OUTER 1645 (6337–7981), MIXED 496 (6340–6835).  `assemble_R176W2.py` re-asserts this byte-for-byte (`unit[:6336] ==
draft[:6336]` and `unit[-3:] == ['end', '', 'end RProof']` for CURL/OUTER; `unit[:6339] == draft` for MIXED) and checks every appended
declaration for its prefix and every line for `import`/`set_option`/`universe`/`macro`/`syntax`/`notation`/`elab`, non-local
`attribute`, `sorry`/`#print`/`#eval`/`#check` — all clean.  Section balance: CURL = one `section R176C_Curl … end R176C_Curl`
(`open Classical` inside); OUTER = sections `R176O_*` ending `end R176O_Chain`; MIXED = `namespace RProof / open … / noncomputable
section / sections R176M_Rec, R176M_DA, R176M_Lift, R176M_Event / end / end RProof`.

## 2. What the assembler had to add: the mirrored (14)-bridge (`r176a_mixed_bridge'_proof`, 88 lines)

The OUTER unit found the frozen Prop `r176_outer_carriers_L` false at `y = lift v'` (with `v₀ ↦ v'_c` the arc `A` carries both
occurrences of `lift u'`, which is not in `liftBlock (retained Λ₂)`; with `v₀ ↦ v'_b` one gets `K_A = liftBlock (retained Λ₁)`), while
the composition uses that disjunct (`r176_portDataRest_labelled` case 2 relabels and calls `_case1 … (Or.inr rfl)`).  OUTER proved the
corrected split `r176o_outer_carriers_L_corrected = (y = lift u' → Nonempty r176_OuterDataL) ∧ (y = lift v' → Nonempty
r176o_OuterDataL')` (`r176o_OuterDataL'` = `r176_OuterDataL` with `Λ₁ ↔ Λ₂` in `KA_eq`, `KB_eq`, `r_not`) and replayed the composition
as `r176o_extreme_transport_of_curl_mixed (hcurl : r176s_curl_removal) (hmixed' : r176o_mixed_bridge') (hmixed : r176_mixed_bridge)`,
where `r176o_mixed_bridge'` is `r176_mixed_bridge` word for word with `O : r176o_OuterDataL'`.  The MIXED unit (written against the
frozen data) proved `r176_mixed_bridge` as a COUNT: `r176m_bridge_count` says `mixedSignSum D_A i j + #W₁ + #W₂ + 2 = #retained q`
from `K_A = liftBlock W₂`, `K_B = liftBlock W₁ ∪ {r}`, `r ∉ liftBlock W₁` — symmetric in the children, which are only counted.  So the
mirrored bridge is MIXED's event-level proof `r176m_mixed_bridge_proof` with the call
`r176m_bridge_count … y O.v₀ O.hv₀ _ _ O.subB O.subA O.r O.KA_eq O.KB_eq O.r_not` changed to `… _ _ O.subA O.subB O.r O.KA_eq O.KB_eq
O.r_not` (`W₁ := retained Λ₂`, `W₂ := retained Λ₁`) and the two `card` summands of the ascribed `hcount` exchanged; `hcard'` (the
LEDGER's `#retained q₀' = #Λ₁ + #Λ₂ + #mixedSet + 2`) and the final `linarith` are unchanged.  Generated from
`R176W2_MIXED.lean` 6741–6821 by the script that wrote `R176W2_compose_part.lean` (one failed compile on the way: the first mechanical
swap moved the `+ 2 =` with the wrong block — a type mismatch at the `hcount` ascription, fixed by hand; second compile clean).
Axioms: standard three.

Then, in the same section, `r176a_extreme_transport_rowShape : RowShape @ExtremeTransportData := r176o_extreme_transport_of_curl_mixed
r176c_curl_removal_proof r176a_mixed_bridge'_proof r176m_mixed_bridge_proof`, and in the row block the FIXED-name theorem.

## 3. The row theorem and its statement

The task text asked for `theorem extreme_transport : RowShape @ExtremeTransportData := r176_extreme_transport_of_curl_outer_mixed
<proofs>`.  Two deviations, both deliberate:
* the body cannot go through `r176_extreme_transport_of_curl_outer_mixed` — its hypothesis `r176_outer_carriers_L` is false as stated
  and has no proof; the row goes through OUTER's replay `r176o_extreme_transport_of_curl_mixed` (byte-identical bodies apart from the
  `hy`-split in `_case1` and the mirrored connector `r176o_smoothData_of'`);
* the statement is written in the binder form of the FIXED statement (`work/drafts/cvtail/Wave1_Assembled.lean` 3476–3482, byte-identical;
  the form of the accepted siblings `generic_transport`, `generic_selected`, `extreme_pair_zero` and of the R174 port), of which
  `RowShape @ExtremeTransportData` is RALedgers' "fixed shape" (`RowShape` is that ∀ with `n` explicit; `rowShape_170/172/173` wrap the
  sibling rows the same way).  The literal RowShape-typed theorem is `r176a_extreme_transport_rowShape` (Units file), and
  `extreme_transport := r176a_extreme_transport_rowShape n hn E e f g h3 h4e h4f h4g hE`.  If the checker wants the RowShape-typed
  statement under the fixed name instead, swap the two names in `R176W2_row_part.lean`/`R176W2_compose_part.lean` and re-run
  `assemble_R176W2.py` (one compile).

Warnings (10, all cosmetic `linter.unusedSectionVars`, inherited from the LEDGER's and OUTER's blanket-`include` sections):
RProof.r176l_selectedPart_eq (5154), RProof.r176o_owner_ja (6895), RProof.r176o_exists_k (6900), RProof.r176o_pow_vc (6909), RProof.r176o_succSf_eq_succT (6918), RProof.r176o_pow_ja (6946), RProof.r176o_between_uc_ua_iff (7009), RProof.r176o_between_ua_uc_iff (7029), RProof.r176o_r_not (7287), RProof.r176o_r_not' (7624).

## 4. Files

| file | role |
|---|---|
| `R176W2_Assembled.lean` | the deliverable (9013 lines; row block 8973–9013) |
| `assemble_R176W2.py` | generator + checks (§1) + port emitter; `--no-port` skips the port files |
| `R176W2_compose_part.lean` | the assembler's section (`r176a_`, 122 lines) |
| `R176W2_row_part.lean` | the row block (41 lines) |
| `R176W2_units_header.txt`, `R176W2_row_header.txt` | the port headers |
| `clash_scan_R176W2.py`, `clash_scan_R176W2.json` | the namespace-aware clash scan and its output |
| `port/R176/RProof/ExtremeTransportUnits.lean`, `port/R176/RProof/ExtremeTransport.lean`, `port/R176/PORT_REPORT.md`, `port/R176/port_chain.log`, `port/R176/probe_Assembled.log` | the port |
| scratch (`$SCRATCHPAD/asm_compile2.log`, `probe_R176W2_Assembled.lean`, `r176/{T,O}`) | compile logs, the axiom probe copy, the module-semantics scratch tree |

Superseded / never asserted (kept in the file, no `sorry`): `r176_outer_carriers_L` (false in general), `r176s_outer_carriers`,
`r176s_ledger`, `r176l_smooth_black_box`, and the conditional rows `r176_extreme_transport_of_curl_outer_mixed`,
`r176_extreme_transport_of_curl_outer_ledger`, `r176_extreme_transport_of_rest_uniform`, `r176c_extreme_transport_of_outer_mixed`,
`r176m_extreme_transport_of_curl_outer` — prune at port time or later (PORT_REPORT §5.3).
