# PORT REPORT — row 176 (R:extreme_transport), port-ready modules

Row-176 wave-2 assembler, 2026-09-15 23:45 UTC / 7:45pm ET.  Source: `work/drafts/moves/R176W2_Assembled.lean` (9013 lines, md5
`6586f5608207439dc0e7ff01875ecbae`; compiles with 0 errors, `R176W2_ASSEMBLY_REPORT.md`).  Nothing written under `work/lean`.
Output: two modules under `work/drafts/moves/port/R176/`, laid out as they land (generator `../../assemble_R176W2.py`):

| module (port path → work/lean path) | Assembled lines | lines | md5 | compile (module semantics, §2) | `sorry`/`#print`/`#eval` |
|---|---|---|---|---|---|
| `port/R176/RProof/ExtremeTransportUnits.lean` → `RProof/ExtremeTransportUnits.lean` (library material, no row theorem) | 2–8972 verbatim (+ 17 new header lines) | 8988 | `6845092ffb93bced0280b480417866e9` | 0 errors, 10 linter notes (unused section variables, pre-existing in the units), 64 s (with `-o`/`-i`) | 0 / 0 / 0 |
| `port/R176/RProof/ExtremeTransport.lean` → `RProof/ExtremeTransport.lean` (row 176) | 8973–9013 verbatim (+ 6 new header lines + `import RProof.ExtremeTransportUnits`) | 48 | `b1b8d46a47da0e5f1c35b09ba3a55ebb` | 0 errors, 0 warnings, 24 s (import-bound) | 0 / 0 / 0 |

Import graph: `SM.Smoothing`, `SM.MarkedProducts`, `SM.SingleCrossing`, `CV.FullTwist`, `RProof.GenericTransport`, `RProof.RALedgers`,
`SM.BigonDeletion` (the port draft's import block, verbatim) ← `RProof.ExtremeTransportUnits` ← `RProof.ExtremeTransport`.  No cycle:
nothing in `work/lean` imports either new module (`grep -rn 'import RProof.ExtremeTransport'` empty) and the imported modules are all
already built (`.lake/build/lib/lean/{SM,CV,RProof}`).  Both are matched by the lakefile glob `RProof.+`.

## 1. Contents

### 1.1 `RProof/ExtremeTransportUnits.lean` — everything except the row theorem
Header (17 `--` lines, new; a `<HH:MM>Z` placeholder for the landing time) then, verbatim, `R176W2_Assembled.lean` lines 2–8972 =
`R176_Port_draft.lean` lines 2–6336 (Site_176 `s176_`, HSUCC `r176h_`, SMOOTH `r176s_`, LEDGER `r176l_`, the wave-1 composition
`r176_`), the CURL appendix (`R176W2_CURL.lean` 6337–6706), the OUTER appendix (`R176W2_OUTER.lean` 6337–7981), the draft's closing
`end`/`end RProof` (6337–6339), the MIXED appendix (`R176W2_MIXED.lean` 6340–6835) and the assembler's section
(`R176W2_compose_part.lean`, 122 lines).  All in `namespace RProof` (blocks `open SM SM.GeoCarrier SM.Carrier SM.Link`,
`noncomputable section`).

| block (Units line ≈ Assembled line + 16) | prefix | decls | content |
|---|---|---|---|
| Site_176 (Assembled 10–1867) | `s176_` (+ `s176_CornerSite.*`) | 81 + 25 | the `j`-corner bigon site of `carrierDiagram q₀'` switched at `y`; the weak re-base `s176_est_*_weak` of the `est_` ledger |
| HSUCC (1868–2216) | `r176h_` | 14 | the RII port: `r176h_hrec_wall_proof`, `r176h_est_port_weak` |
| SMOOTH (2217–3126) | `r176s_` | 65 | arcs of a self crossing, the smoothing `r176s_DA`, `r176s_homfly_of_liftBlock(_curl)`, the Prop `r176s_curl_removal`, the SMOOTH-route Props `r176s_outer_carriers`, `r176s_ledger` (superseded, never asserted) |
| LEDGER (3127–5677) | `r176l_` | 148 | `wind(S)`-uniform rotation ledger, `r176l_mixedSet`, `r176l_SmoothData`, the labelled-corner geometry, `r176l_portDataRest_case1` |
| composition (5678–6336) | `r176_` | 18 | `r176_OuterDataL`, the Props `r176_outer_carriers_L` / `r176_mixed_bridge`, `r176_smoothData_of`, `r176_portDataRest_*`, the `wind = 0` split, the conditional rows `r176_extreme_transport_of_*` |
| CURL (6337–6706) | `r176c_` | 14 | **`r176c_curl_removal_proof : r176s_curl_removal`**, `r176c_curl_removal_general`, block realizability, `r176c_restrictRestrictIso` |
| OUTER (6707–8351) | `r176o_` | 55 | lem:carrierword as orbit arithmetic, the arc identities, **`r176o_outer_carriers_L_corrected_proof`** (`r176o_outer_carriers_L_u` + `r176o_outer_carriers_L_v_proof`), the mirrored data `r176o_OuterDataL'`, the Prop `r176o_mixed_bridge'`, the replayed composition **`r176o_extreme_transport_of_curl_mixed`** |
| MIXED (8355–8850) | `r176m_` | 24 | `r176m_bridge_count`, **`r176m_mixed_bridge_proof : r176_mixed_bridge`** |
| assembler (8851–8972) | `r176a_` | 2 | **`r176a_mixed_bridge'_proof : r176o_mixed_bridge'`**, **`r176a_extreme_transport_rowShape : RowShape @ExtremeTransportData`** |

446 declarations (445 here + the row theorem), every one prefixed or inside `s176_CornerSite`; the file is the assembled file minus
the row block and the header.

### 1.2 `RProof/ExtremeTransport.lean` — the row theorem
```lean
import RProof.ExtremeTransportUnits

namespace RProof

open SM SM.GeoCarrier

variable {n : ℕ} [NeZero n]

/-- **Row 176 (ORDER 175), R:extreme_transport** … (the printed obligation quoted verbatim from RProof/X1Rows.lean, row 176) … -/
theorem extreme_transport (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeTransportData hn E e f g δ :=
  r176a_extreme_transport_rowShape n hn E e f g h3 h4e h4f h4g hE

end RProof
```
The seven statement lines are byte-identical to `work/drafts/cvtail/Wave1_Assembled.lean` lines 3476–3482 (without its trailing
` by`) — the FIXED statement of the row theorem that RALedgers' port omitted (`diff` empty) — and to `RProof/GenericSelected.lean`
39–45 modulo the data name; frame identical to RALedgers 22/24/45.  `RowShape @ExtremeTransportData` (RALedgers.lean 29, "the fixed
shape of an X₁-dependent R row") is this statement with `n` explicit; the RowShape form is `r176a_extreme_transport_rowShape` in the
Units file, and the row theorem is its instantiation.  `#check @RProof.extreme_transport` (port_chain.log) prints exactly the
`RowShape` body.

## 2. Compile recipe used (true module semantics without touching `work/lean`)

Scratch tree `T/RProof/{ExtremeTransportUnits,ExtremeTransport,R176Probe}.lean`; `O/RProof/` = symlinks to every file of
`work/lean/.lake/build/lib/lean/RProof/` (45 files); then from `work/lean`, in this order (`port_chain.log`, copied here):
1. `lake env sh -c 'LEAN_PATH="O:$LEAN_PATH" lean --root=T -o O/RProof/ExtremeTransportUnits.olean -i O/RProof/ExtremeTransportUnits.ilean T/RProof/ExtremeTransportUnits.lean'` — exit 0, 0 errors, 10 linter notes, 64 s; olean 16.3 MB.
2. `… lean --root=T -o O/RProof/ExtremeTransport.olean -i … T/RProof/ExtremeTransport.lean` — exit 0, no output, 24 s.
3. `… lean --root=T T/RProof/R176Probe.lean` (`import RProof.ExtremeTransport` + `#print axioms` / `#check`) — exit 0, 28 s:

```
'RProof.extreme_transport' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent,
  SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]
'RProof.r176a_extreme_transport_rowShape' depends on axioms: (the same nine)
'RProof.r176a_mixed_bridge'_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'RProof.r176c_curl_removal_proof' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]
'RProof.r176m_mixed_bridge_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'RProof.r176o_outer_carriers_L_corrected_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Exactly `axiom-policy.json`'s `standard` + `literature`; no `sorryAx`.  The same list was obtained from a scratch copy of the
assembled single file (`probe_Assembled.log`, copied here).  After the executor copies the two files to `work/lean/RProof/`, the
ordinary `lake build` suffices (glob `RProof.+`); build `ExtremeTransportUnits` before `ExtremeTransport` (lake orders it by the import).

## 3. Deviations from verbatim (complete list)

* `ExtremeTransportUnits.lean` lines 1–17: new header comment (replaces the assembled file's one-line header; the port draft's
  own line 1 named a forbidden string).  Lines 18–8988 = Assembled 2–8972, byte-for-byte (`diff` empty).
* `ExtremeTransport.lean` lines 1–6: new header comment; line 7: `import RProof.ExtremeTransportUnits` (new); lines 8–48 = Assembled
  8973–9013 byte-for-byte.
* Nothing else.  No declaration statement or proof differs from the units' files.  Strings `sorry`, `#print`, `#eval`: 0 in both
  files (`grep -cE`).

## 4. Clash scan

Namespace-aware (`clash_scan_R176W2.py ../../lean R176W2_Assembled.lean`, = `clash_scan_R176.py` with a new JSON name): 446
declarations vs every `work/lean/**/*.lean` outside `.lake` — **0 fully-qualified clashes**, 0 internal duplicates; 3 informational
short-name coincidences, all pre-existing from Site_176 (`RProof.s176_CornerSite.eIn / eOut / eIn_ne_eOut` vs
`SM.Link.BigonData.*`, `SM.PLFront.*` — different namespaces).  `RProof.extreme_transport` is declared nowhere in `work/lean`;
`work/lean/RProof/` has neither module file.

## 5. Executor items

1. Copy `port/R176/RProof/ExtremeTransportUnits.lean` and `port/R176/RProof/ExtremeTransport.lean` to `work/lean/RProof/`; fill the
   `<HH:MM>Z` placeholder in line 1 of each; `lake build`.
2. `lean-declarations.json`: the `R:extreme_transport` entry (id 182; currently `module: ""`, `status: pending`) → `declaration:
   RProof.extreme_transport`, `module: RProof.ExtremeTransport`, plus the statement review per the rows' protocol (the statement is the
   Wave1/X1Rows text, so the reviewer input is the seven lines above with the body withheld).
3. AUTHOR_NOTES / D-F11: the frozen interface Prop `r176_outer_carriers_L` is FALSE at `y = lift v'` (R176W2_OUTER_REPORT §2) and
   remains in the Units file only as a definition (never asserted); its consumers `r176_portDataRest_*`,
   `r176_extreme_transport_of_curl_outer_mixed`, `r176c_extreme_transport_of_outer_mixed`, `r176m_extreme_transport_of_curl_outer`
   are conditional theorems whose hypothesis is unsatisfiable in general — harmless, prune at leisure together with the
   SMOOTH-route Props `r176s_outer_carriers` / `r176s_ledger` and `r176l_smooth_black_box`.  The row goes through the corrected
   split `r176o_outer_carriers_L_corrected` and OUTER's replay `r176o_extreme_transport_of_curl_mixed`.
4. F-176-1 (RALedgers): the row still uses the Site-176 weak re-base `s176_est_*_weak` of the `est_` ledger (Site_176_REPORT §4,
   R176_ASSEMBLY_REPORT §7); folding it into RALedgers (`est_PortData.port : est_port_weak` + one call) is the U-176 owner's edit and is
   not needed for the row to land.
5. Optional later refactors (not part of this port): the library candidates listed in R176_ASSEMBLY_REPORT.md §7 (record lemmas of
   SMOOTH §R1–R2, LEDGER §L0–L1, OUTER §O0–O1's orbit arithmetic `r176o_cyc_iff` etc.).
