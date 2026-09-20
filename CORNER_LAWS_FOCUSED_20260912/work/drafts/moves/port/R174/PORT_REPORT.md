# PORT REPORT — row 174 (R:generic_selected), port-ready modules

Row-174 wave-2 assembler, 2026-09-15 ≈ 23:25 UTC / 7:25pm ET.  Source: `work/drafts/moves/R174W2_Assembled.lean` (7369 lines,
md5 `ead93a9663cbd7d36279bb6ea6e6e566`; compiles, `R174W2_ASSEMBLY_REPORT.md`).  Nothing written under `work/lean`.  Output: two
modules under `work/drafts/moves/port/R174/`, laid out as they land (generator `../../assemble_R174W2.py`):

| module (port path → work/lean path) | Assembled lines | lines | md5 | compile | `sorry`/`#print`/`#eval` |
|---|---|---|---|---|---|
| `port/R174/RProof/GenericSelectedUnits.lean` → `RProof/GenericSelectedUnits.lean` (library material, no row theorem) | 11–7327 verbatim (+ 9 new header lines) | 7326 | `951afd2edd5b7df92e45aa1aaaeaa13e` | 0 errors, 0 warnings, 55 s (with `-o`/`-i`) | 0 / 0 / 0 |
| `port/R174/RProof/GenericSelected.lean` → `RProof/GenericSelected.lean` (row 174) | 7328–7369 verbatim (+ 5 new header lines + `import RProof.GenericSelectedUnits`) | 48 | `b45b62fd165fea625b1d2582134fff6a` | 0 errors, 0 warnings, 28 s (import-bound) | 0 / 0 / 0 |

Import graph: `SM.BigonDeletion`, `RProof.RALedgers` ← `RProof.GenericSelectedUnits` ← `RProof.GenericSelected`.  No cycle:
`RALedgers` imports `RProof.X1Rows/X1Rows2/GenericTransport`, `CV.ChamberInvRow/FullTwist/HomflyRows/CarrierFloor`, `Bridge.SmR`;
`BigonDeletion` imports `SM.Smoothing/MarkedProducts/SingleCrossing`, `CV.FullTwist`, `RProof.GenericTransport`; neither imports the
other, and nothing in `work/lean` imports the two new modules.  Both are matched by the lakefile glob `RProof.+`.

## 1. Contents

### 1.1 `RProof/GenericSelectedUnits.lean` — everything except the row theorem
Header (9 `--` lines, new; a `<HH:MM>Z` placeholder for the landing time) then, verbatim from the assembled file (= the port draft
`R174_Port_GenericSelectedUnits_draft.lean` lines 10–6843 = Site_174 + the five wave-1 unit appendices + the composition, plus the
wave-2 unit ARCV = `R174W2_ARCV.lean` lines 6844–7326): `import SM.BigonDeletion`, `import RProof.RALedgers`, and nine
`namespace SM.Link … end SM.Link` blocks (each `open SM SM.GeoCarrier SM.Carrier RProof`, `noncomputable section`):

| block (module docstring line in the port file) | prefix | declarations | content |
|---|---|---|---|
| Site 174 (I-174) (14) | `s174_` | 55 | the generic bigon-site core `s174_core`, the `GT_Endpoint` wrapper `s174_site`, `s174_order`, `s174_fulltwist_of_hrec`, the consumer `s174_hrec_prop` |
| HREC (1088) | `r174h_` | 30 | the wall record transport `r174h_recordIso` (identity on parent visits through `visitTransport`), `r174h_hrec_tau`, `r174h_fulltwist`, the retained-crossing correspondence `r174h_retained_of_mem_q`, `r174h_cyc` |
| CARRIERS (1538) | `r174c_` | 149 | `gsc_Ledger` item 1: `r174c_qC`, `r174c_qAB`, `r174c_qC'`, `r174c_qA`, `r174c_qB`, the `h*` fields, `r174c_ρ*`, spectators, `r174c_owner_qAB_iff`, the first-hit permutation tools |
| SITEIN (3037) | `r174x_` | 17 | the site inputs `r174x_hx'_tau`, `r174x_hw'_tau` |
| WALL (3230) | `r174w_` | 197 | items 2–3: `r174w_omega_wall_ledger`, `r174w_writhe_wall_ledger`, `r174w_sigma`/`r174w_hsigma`, `r174w_omega_C`, `r174w_weight_C/AB`, `r174w_carrierR_add`, Part B (`r174w_tau`, `r174w_theta`, `r174w_F_split`, …), Part C (`r174w_child`, `r174w_split_x`, `r174w_Split`, `r174w_sp`), `r174w_qC'`/`r174w_qC'_unique`, the local instance `r174w_decEqCrossing` |
| SMOOTH (5686; sub-headings C/A/D/E at 6000, 6256, 6318, 6461) | `r174s_` (+ `Record.r174s_KeepArc` in `namespace Record`) | 42 | the smoothing `D₀`, items 4–6 `r174s_ledger_fields`, the arc-record interface `r174s_arc_rec_prop`, `r174s_ArcVisitData`, `r174s_recordIso_of_arcVisitData`, `r174s_arc_rec_of_visitData` |
| ASSEMBLY (6692) | `r174_` | 6 | `r174_qC'_eq`, `r174_arc_rec`, `r174_ledger_nonempty`, `r174_arc_rec_moves` (the Prop), `r174_gsc_moves_of_arc_rec`, `r174_generic_selected_of_arc_rec` |
| ARCV (6845) | `r174v_` | 15 | Route V: `r174v_interlaces_keys`, `r174v_not_both_inArc`, `r174v_xA_not_w`, `r174v_arcA_of_owner`, `r174v_arcB_of_owner`, `r174v_nonLocal_of_not_tri`, `r174v_cyc_transport`, `r174v_retained_qAB_of_xw`, `r174v_arcData`, `r174v_dataA`, `r174v_dataB`, `r174v_arc_rec_at`, **`r174v_arc_rec_moves_proof : r174_arc_rec_moves`**, **`r174v_gsc_moves : gsc_moves`**, `r174v_generic_selected` (the row in the fixed signature, under the unit's name) |

513 declarations, every one prefixed; the file is the assembled file minus the row block and the header.  (`r174v_generic_selected`
duplicates the row theorem's content under a unit name — harmless; prune at leisure.)

### 1.2 `RProof/GenericSelected.lean` — the row theorem
```lean
import RProof.GenericSelectedUnits

namespace RProof

open SM SM.GeoCarrier

variable {n : ℕ} [NeZero n]

/-- **Row 174 (ORDER 182), R:generic_selected** … (the printed obligation quoted verbatim from RProof/X1Rows.lean 1422–1430) … -/
theorem generic_selected (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ :=
  SM.Link.r174_generic_selected_of_arc_rec SM.Link.r174v_arc_rec_moves_proof hn E e f g h3 h4e h4f h4g hE

end RProof
```
The seven statement lines are byte-identical to `work/drafts/cvtail/Wave1_Assembled.lean` lines 2543–2548 and 2549 (without its
trailing ` by`) — the FIXED statement of the row theorem that RALedgers' port omitted (`diff` empty) — and to the binder/type lines of
`gsc_generic_selected_of_moves` (RALedgers.lean 778–785).  Frame identical to Wave1 1772/1774/1795 (= RALedgers 22/24/45).

## 2. Compile recipe used (true module semantics without touching `work/lean`)

Scratch tree `T/RProof/{GenericSelectedUnits,GenericSelected,R174Probe}.lean`; `O/RProof/` = symlinks to every file of
`work/lean/.lake/build/lib/lean/RProof/` (35 files); then from `work/lean`, in this order (`port_chain.log`):
1. `lake env sh -c 'LEAN_PATH="O:$LEAN_PATH" lean --root=T -o O/RProof/GenericSelectedUnits.olean -i O/RProof/GenericSelectedUnits.ilean T/RProof/GenericSelectedUnits.lean'` — exit 0, no output, 55 s; olean 12.6 MB.
2. `… lean --root=T -o O/RProof/GenericSelected.olean -i … T/RProof/GenericSelected.lean` — exit 0, no output, 28 s.
3. `… lean --root=T T/RProof/R174Probe.lean` (`import RProof.GenericSelected` + `#print axioms` / `#check`) — exit 0, 26 s:

```
'RProof.generic_selected' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent,
  SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]
'SM.Link.r174v_arc_rec_moves_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.Link.r174_gsc_moves_of_arc_rec' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]
```
Exactly `axiom-policy.json`'s `standard` + `literature`; no `sorryAx`.  The same list was obtained from a scratch copy of the
assembled single file (`probe_Assembled.log`).  After the executor copies the two files to `work/lean/RProof/`, the ordinary
`lake build` suffices (glob `RProof.+`); build `GenericSelectedUnits` before `GenericSelected` (lake orders it by the import).

## 3. Deviations from verbatim (complete list)

* `GenericSelectedUnits.lean` lines 1–9: new header comment (replaces the draft's nine `--` header lines, which named the
  forbidden strings).  Lines 10–7326 = assembled 11–7327 = draft 10–6843 + ARCV 6844–7326, byte-for-byte (`diff` empty).
* `GenericSelected.lean` lines 1–5: new header comment; line 6: `import RProof.GenericSelectedUnits` (new); lines 7–48 = assembled
  7328–7369 byte-for-byte.
* Nothing else.  No declaration statement or proof differs from the units' files.  Strings `sorry`, `#print`, `#eval`: 0 in both
  files (`grep -cE`).

## 4. Clash scan

Namespace-aware (`clash.py`, scratchpad): 513 + 1 declarations vs every `work/lean/**/*.lean` outside `.lake` — 0 full-name
clashes, 0 same-short-name declarations in any namespace, 0 duplicates.  `work/lean/RProof/` has neither module file.

## 5. Executor items

1. Copy `port/R174/RProof/GenericSelectedUnits.lean` and `port/R174/RProof/GenericSelected.lean` to `work/lean/RProof/`; fill the
   `<HH:MM>Z` placeholder in line 1 of each; `lake build`.
2. `lean-declarations.json`: the `R:generic_selected` entry (currently `module: ""`, `status: pending`) → `declaration:
   RProof.generic_selected`, `module: RProof.GenericSelected`, plus the statement review per the rows' protocol (the statement is
   the Wave1/RALedgers text, so the reviewer input is the seven lines above with the body withheld).
3. AUTHOR_NOTES: the orientation dependence of `σ` (`r174w_sigma = −τ(m_AB)`; R174_ASSEMBLY_REPORT.md §8.1) — the docstrings of
   `gsc_Ledger`/`gsc_moves` read `σ` as `crossingSign ℓ₁ ℓ₂`, which holds in the printed orientation only.
4. Optional later refactors (not part of this port): prune the duplicated helper pairs and `r174v_generic_selected`; move the
   library material (`s174_core`, `r174h_recordIso`, WALL Part B, SMOOTH §B/§E, the `r174s_writhe_*` copies of
   SM/CornerChainUnits.lean) to shared homes — R174_ASSEMBLY_REPORT.md §7.
5. Independent check available: `work/drafts/moves/R174W2_ARCR.lean` (Route R, prefix `r174r_`) proves the same Prop
   `r174_arc_rec_moves` from the port draft alone, same axioms; not part of the port.
