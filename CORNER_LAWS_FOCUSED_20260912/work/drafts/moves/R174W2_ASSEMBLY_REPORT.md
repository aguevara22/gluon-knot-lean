# R174W2_ASSEMBLY_REPORT — row 174 (R:generic_selected), wave-2 assembly: the row is CLOSED

Assembler (subagent), 2026-09-15 ≈ 23:25 UTC / 7:25pm ET (hard stop 01:15 UTC).  Nothing written under `work/lean`;
compiles by `cd work/lean && lake env lean …` only; scratch (probe copies, the scratch object tree of the port test, logs,
`clash.py`) in the session scratchpad `…/scratchpad/w2/`.  Generator: `assemble_R174W2.py` (next to this file; the three
output files ARE its output, re-runnable).

## 0. Result

| item | result |
|---|---|
| **`r174_arc_rec_moves`** (the ONE open Prop of row 174 after R174_ASSEMBLY_REPORT.md) | **PROVED twice, independently**: Route V `r174v_arc_rec_moves_proof` (R174W2_ARCV.lean) and Route R `r174r_arc_rec_moves_proof` (R174W2_ARCR.lean); each on `propext, Classical.choice, Quot.sound` alone |
| route kept | **Route V (ARCV)**: 479 appended lines, 15 declarations — shorter than Route R (597 lines, 36 declarations).  Route R is recorded as the independent check (§2) and stays in its unit file, not assembled |
| **`R174W2_Assembled.lean`** | 7369 lines, md5 `ead93a9663cbd7d36279bb6ea6e6e566` = header (10 lines) + R174W2_ARCV.lean lines 10–7326 verbatim (= the port draft's lines 10–6843 + the ARCV block) + the row block (lines 7328–7369): `namespace RProof … theorem generic_selected … end RProof` |
| compile `cd work/lean && lake env lean ../drafts/moves/R174W2_Assembled.lean` | **exit 0, 0 errors, 0 warnings**, 30.6 s |
| **`RProof.generic_selected`** | declared UNCONDITIONALLY with the FIXED name and the FIXED statement (byte-identical to work/drafts/cvtail/Wave1_Assembled.lean lines 2543–2549, the statement of the omitted row theorem; `diff` empty), `:= SM.Link.r174_generic_selected_of_arc_rec SM.Link.r174v_arc_rec_moves_proof hn E e f g h3 h4e h4f h4g hE` |
| **axioms of `RProof.generic_selected`** (scratch copy, `#print axioms`) | **`[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]`** — exactly the registered standard + literature axioms of `work/lean/axiom-policy.json`; **no `sorryAx`** |
| clash scan (namespace-aware, against every `work/lean/**/*.lean` outside `.lake`) | 514 declarations in the assembled file, **0 full-name clashes**, 0 same-short-name collisions in any namespace, 0 duplicates inside the file; every declaration except `RProof.generic_selected` carries one of the prefixes `s174_ r174h_ r174c_ r174x_ r174w_ r174s_ r174_ r174v_`; `work/lean` has no declaration named `generic_selected` (RALedgers deliberately omitted the row theorem) and no module `RProof/GenericSelected*.lean` |
| port | **ready**: `port/R174/RProof/GenericSelectedUnits.lean` (7326 lines) + `port/R174/RProof/GenericSelected.lean` (48 lines) + `port/R174/PORT_REPORT.md`; both modules compiled in dependency order with true module semantics (scratch object tree, §5); 0 occurrences of the strings `sorry`, `#print`, `#eval` in either file |
| remaining for row 174 | **nothing open in Lean.**  Executor items only: copy the two modules into `work/lean/RProof/`, `lake build`, fill the `R:generic_selected` entry of `lean-declarations.json` (`module: RProof.GenericSelected`), statement review per the rows' protocol; AUTHOR_NOTES entry on the orientation dependence of `σ` (R174_ASSEMBLY_REPORT.md §8.1) |

## 1. Step (1) — the units only appended prefixed material

Port draft `R174_Port_GenericSelectedUnits_draft.lean`: 6847 lines, md5 `9417bdbc2f8637ec606109bb5b432248`; its lines 6844–6847
are the trailer `‹blank› end ‹blank› end SM.Link`.

| unit | md5 | lines | relation to the draft (verified with `cmp`/`diff`) | appended block | declarations | non-prefixed names | `sorry`/`axiom`/`admit`/`native_decide` in the block |
|---|---|---|---|---|---|---|---|
| `R174W2_ARCV.lean` (Route V) | `e921240992e5bdf781f2d58cf0b81f41` | 7326 | lines 1–6843 byte-identical to draft lines 1–6843; the draft's trailer (`end`, `end SM.Link`) moved to the file's end, i.e. the block is INSERTED inside the last `namespace SM.Link … noncomputable section` before its closing lines; nothing else differs | 6844–7322 (479 lines; sections `R174VCyc`, `R174VArcP`, `R174VData` ⊃ `R174VArcData`, `R174VMoves`) | 15, all `r174v_` | none | 0 |
| `R174W2_ARCR.lean` (Route R) | `5784d99f7febed327968bd36d12335d7` | 7444 | lines 1–6847 byte-identical to the whole draft; the block is a self-contained `namespace SM.Link … end SM.Link` appended after it | 6848–7444 (597 lines; sections `R174RArcs`, `R174RWall`, `R174RData`, `R174RMain`, `R174RMoves`) | 36, all `r174r_` | none | 0 |

Both units' own compile claims were re-run here on scratch copies with `#print axioms` appended (`probe_ARCV.log`, `probe_ARCR.log`):
both exit 0, no errors, no warnings; `r174v_arc_rec_moves_proof` and `r174r_arc_rec_moves_proof`: `propext, Classical.choice,
Quot.sound`; `r174v_gsc_moves` and `r174r_gsc_moves`: + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness`; `r174v_generic_selected`
and `r174r_generic_selected`: the full registered list of nine (as for `RProof.generic_selected` below).  The frozen Prop
`r174s_arc_rec_prop` / `r174_arc_rec` / `r174_arc_rec_moves` was edited by neither unit (the prefix identity proves it).

## 2. Step (2) — route choice

Both routes prove the same Prop from the same frozen material, with no black box and no `sorry`:

* **Route V (kept).**  `r174v_arc_rec_moves_proof : r174_arc_rec_moves := by intro …; exact r174v_arc_rec_at hn hG hG' D hSm hSm'
  hsgn hSxw _ rfl (r174x_hx'_tau …) (r174x_hw'_tau …) (r174w_sp hG hG' D)`.  The arc datum `r174v_arcData` (ψ := `visitTransport`
  restricted to the retained visits; inverse through `r174h_retained_of_mem_q` and the arc characterisation; `x'` excluded by
  strictness of the arc, `w'` by `D.compl` through `r174v_not_both_inArc`; twins by `visitTransport_visitTwin`; key order by
  `r174h_cyc` / `r174v_cyc_transport` (`GT_Wall.key_lt` on the three non-reversed pairs); bits by `GT_Endpoint.sign_eq`) is
  instantiated twice (`r174v_dataA` at `qA`, arc `(τ (twin xA), τ xA)`; `r174v_dataB` at `qB`, arc `(τ xA, τ (twin xA))`) and fed to
  SMOOTH's `r174s_arc_rec_of_visitData`.  The `P`-side arcs come from WALL's Split record `r174w_Split` (`r174v_arcA_of_owner`,
  `r174v_arcB_of_owner`; `r174v_xA_not_w`).  Uses WALL's instance hygiene locally (`attribute [local instance high]
  r174w_decEqCrossing` inside section `R174VArcP` only) — the ledger-facing sections stay clean, as R174_WALL_REPORT §6.2 asks.
* **Route R (independent check, not assembled).**  `r174r_arc_rec_moves_proof := by intro …; exact r174r_arc_rec hn hG hG' D hsgn hSm
  hSxw hSm'`, built from the port draft alone (no ARCV material): the occurrence correspondence `r174r_mem_iff` (retained by `qX` ↔
  transported visit retained by `τ qAB` and inside the arc with its twin), `r174r_w'_not_inArc` via `GT_Endpoint.compl`,
  `r174r_cyc_x` via `GT_Wall.key_lt`, the ownership converse via CARRIERS' `r174c_owner_qAB_iff`, then `r174r_arcVisitData :
  Nonempty (r174s_ArcVisitData …)` and `r174r_arc_rec_at` at a variable `q'` with `hq'`.  Same axioms, same conclusion.  It is
  kept as `R174W2_ARCR.lean` (+ `R174W2_ARCR_REPORT.md`) for the reviewer; nothing in the assembled file or the port depends on it.

Why V over R: 479 vs 597 lines, 15 vs 36 declarations, and the shorter proof term for the Prop; both compile in ≈ 35 s.

## 3. Step (3) — the row theorem

Assembled lines 7328–7369, verbatim (also `port/R174/RProof/GenericSelected.lean` lines 7–48):

```lean
namespace RProof

open SM SM.GeoCarrier

variable {n : ℕ} [NeZero n]

/-- **Row 174 (ORDER 182), R:generic_selected** (FIXED name and statement; …printed obligation quoted… ) -/
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

* The seven statement lines are the FIXED statement: `diff` against Wave1_Assembled.lean lines 2543–2548 + line 2549 without its
  trailing ` by` is empty (checked for the assembled file and for the port file).  They are also byte-identical to the binder/type
  lines of `gsc_generic_selected_of_moves` (RALedgers.lean 778–785) and of `r174_generic_selected_of_arc_rec` (draft 6832–6839),
  which is why the term-mode body type-checks without any `show`/`exact` conversion.
* Frame: the same `namespace RProof / open SM SM.GeoCarrier / variable {n : ℕ} [NeZero n]` as Wave1 lines 1772/1774/1795 and
  RALedgers.lean 22/24/45, so `remote` = `SM.remote`, `GenericSelectedData` = `RProof.GenericSelectedData` exactly as in the fixed
  text; `#check @RProof.generic_selected` prints the expected type (`probe_Assembled.log`).
* The body is the one the ledger's docstring prescribes (`gsc_generic_selected_of_moves hmove CV.carrierSlotFloor …` with
  `hmove := r174_gsc_moves_of_arc_rec r174v_arc_rec_moves_proof`, folded through `r174_generic_selected_of_arc_rec`).

## 4. Step (4) — compile and axioms

* `cd work/lean && lake env lean ../drafts/moves/R174W2_Assembled.lean`: exit 0, empty output (0 errors, 0 warnings), 30.6 s
  (`compile_Assembled.log`).
* Scratch copy `probe_Assembled.lean` = the assembled file + `#print axioms` lines (`probe_Assembled.log`, exit 0, 36.6 s):

```
'RProof.generic_selected' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent,
  SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact]
'SM.Link.r174v_arc_rec_moves_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.Link.r174v_gsc_moves' depends on axioms: [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness]
'SM.Link.r174_generic_selected_of_arc_rec' depends on axioms: [the same nine as RProof.generic_selected]
```

  The nine are exactly `axiom-policy.json`'s `standard` (3) + `literature` (6); **no `sorryAx`**.  The three literature axioms beyond
  the ledger's `Ω₁` reads (`lit_homfly_descent`, `ng_finite_word`, `src_contact`) enter only through `CV.carrierSlotFloor`
  (`carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC`), as predicted in R174_ASSEMBLY_REPORT.md.

## 5. Step (5) — clash scan

`clash.py` (scratchpad): tracks `namespace`/`section`/`end` nesting, extracts every `theorem/lemma/def/abbrev/structure/inductive/
instance/class/opaque/axiom` name with its full namespace, and compares with the same extraction over every `work/lean/**/*.lean`
outside `.lake` (also lists same-short-name declarations in any namespace, and duplicates within the file).
Assembled: 514 declarations (55 `s174_`, 30 `r174h_`, 149 `r174c_`, 17 `r174x_`, 197 `r174w_`, 42 `r174s_` incl.
`Record.r174s_KeepArc`, 6 `r174_`, 15 `r174v_`, 1 `RProof.generic_selected`); **0 full-name clashes, 0 short-name collisions,
0 duplicates**.  Port files: the same for `GenericSelectedUnits.lean` (513) and `GenericSelected.lean` (1).  Module names:
`work/lean/RProof/` has no `GenericSelectedUnits.lean`/`GenericSelected.lean`; the lakefile globs `RProof.+` pick both up.

## 6. Step (6) — the port (`port/R174/`, see `port/R174/PORT_REPORT.md`)

| file | lines | md5 | content | compile (scratch object tree, true module semantics) |
|---|---|---|---|---|
| `RProof/GenericSelectedUnits.lean` | 7326 | `951afd2edd5b7df92e45aa1aaaeaa13e` | 9 header comment lines (new) + assembled lines 11–7327 verbatim (`import SM.BigonDeletion`, `import RProof.RALedgers`, the site, the seven blocks) — everything except the row theorem | see PORT_REPORT §2 |
| `RProof/GenericSelected.lean` | 48 | `b45b62fd165fea625b1d2582134fff6a` | 5 header lines (new) + `import RProof.GenericSelectedUnits` + assembled lines 7328–7369 verbatim (the row block; docstring quotes the printed obligation from RProof/X1Rows.lean 1422–1430) | see PORT_REPORT §2 |

`grep -cE 'sorry|#print|#eval'` → 0 and 0.  The only non-verbatim lines are the headers (the draft's nine header comment lines,
which mentioned the forbidden strings, are replaced).  The units' own module docstrings ("Everything below is NEW (nothing above
changed)") are kept verbatim as instructed; they read as drafting notes and can be reworded at landing time.

## 7. Notes for FINAL_REVIEW

1. Row 174 is closed on the registered axioms; the interface Prop `gsc_moves` of RALedgers is realised (`SM.Link.r174v_gsc_moves`),
   so `RProof.cv_R_of_rows` / `Bridge.sm_R_of_rows` lose one hypothesis once rows 176/177 close.
2. Two independent proofs of the open Prop exist (V kept, R as check); a reviewer wanting a second derivation can compile
   `R174W2_ARCR.lean` (36 s) — its `r174r_generic_selected` has the same nine axioms.
3. Findings recorded in R174_ASSEMBLY_REPORT.md §8 stand (σ orientation-dependent — `r174w_sigma`, not `crossingSign ℓ₁ ℓ₂`;
   `s174_hrec_prop` provable only at the ledger's binding; `qC'` case-dependent; the site inputs need no arc argument).  None
   required editing a frozen statement; rule (4) was never invoked in wave 2 either.
4. Not done here (deliberately): pruning the duplicated helper pairs listed in R174_ASSEMBLY_REPORT.md §7 and moving the library
   material (`s174_core`, `r174h_recordIso`, WALL Part B, SMOOTH §B/§E) to shared homes — verbatim port first, refactor later.
