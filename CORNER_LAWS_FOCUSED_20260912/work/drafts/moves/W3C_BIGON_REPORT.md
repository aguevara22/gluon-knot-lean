# W3C_BIGON_REPORT.md — Wave 3c, Unit BIGON: the switch-at-`z₀` bigon forms (row 177 (6))

Written 2026-09-15, 23:36 UTC / 7:36pm ET (bounded window, HARD STOP 01:45 UTC; audit A-177-2) by the Unit-BIGON prover.
File: `work/drafts/moves/W3C_BIGON.lean` = `W3B_Assembled.lean` (11851 lines) + the `w3cz_` block (303 lines, section
`W3BI_REAL`, right before the frozen docstring of `w3bi_bigonData_smooth_arcST_switch_z`) + two `w3cz_` consumer
variants (right after `w3bi_bigon_of_site`) + the two owned `sorry` bodies reduced to `hk5`.  12154 lines.  Compiles with
`lake env lean ../drafts/moves/W3C_BIGON.lean` in ≈ 45 s, **0 errors**; the two identity checks pass
(`check_W3_identity.py Port_GenericTransportSw_draft.lean W3C_BIGON.lean`: 5/5 frozen blocks IDENTICAL, the `imports`
line prints `False` as it does on `W3B_Assembled.lean` itself — `RProof.RALedgers` is imported, pre-existing;
`check_W3_statements.py W3C_BIGON.lean`: 42/42 skeleton statements byte-identical, no skeleton declaration missing).
`grep -c sorry`: **8 before, 8 after** (7 `sorry` terms before and after; line 7856 is unit G's comment).  Nothing under
`work/lean` touched; `lake build` never run.

## 0. Result in one paragraph

Both owned leaves, `w3bi_bigonData_smooth_arcST_switch_z` (:11007) and `w3bi_bigonData_smooth_arcTS_switch_z` (:11030),
are **FALSE as stated, for exactly unit G's reason** (rule 3): `BigonData.hk : j + 3 ≤ (D.Γ.comp i).k` is a condition
on the SHADOW `Γ₀`, and the shadow does not see which crossing is switched (`Diagram.switch_Γ` is `rfl`); G's kink
counterexample (`t = s − 2` on one component, `k = 4` on the component of `cutStartS`, W3B_G_REPORT §2) satisfies every
hypothesis of the switch_z statements too — they have exactly the hypothesis list of `w3g_*`, `clear_vertex` included.
**Everything else is proved**, by the preferred route (a `BigonData` transfer, not a copy of G's 520-line proofs):
`w3cz_bigonData_switch_transfer` moves any bigon whose two crossings are `{y₀, z₀}` from `(D^x).switch y₀` to
`(D^x).switch z₀` (27 of the 28 fields copied verbatim; only `same_over` reads the over data, and for these crossings
it is symmetric in which one is switched — `w3cz_same_over_switch_swap`).  Delivered: `w3cz_bigonData_smooth_arcST_switch_z_of_five`
/ `_arcTS_switch_z_of_five` (the frozen statements plus G's `hk5 : 5 ≤ k`) and **`w3cz_bigonData_smooth_arcST_switch_z_of_not_kink`
/ `_arcTS_switch_z_of_not_kink`** (plus G's non-kink hypothesis `⟨s.1, s.2−1⟩ ≠ ⟨t.1, t.2+1⟩` resp.
`⟨t.1, t.2−1⟩ ≠ ⟨s.1, s.2+1⟩`, the same shape as `w3bg_…_of_not_kink`, which SITE derives), all sorry-free,
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.  The rule-3 verdict is made formal:
`w3cz_switch_z_arcST_iff_hk5` / `_arcTS_iff_hk5` prove that under its own hypotheses each frozen conclusion is
**equivalent** to `hk5` (`w3cz_hk5_of_conclusion`: any such bigon forces `5 ≤ k`).  Following unit G's accepted precedent
the two frozen bodies are `exact w3cz_…_switch_z_of_five … (by sorry)`, so they carry `sorryAx` through `hk5` only
(revert to a bare `sorry` at :11027 / :11049 if the parent prefers the untouched body).  As a bonus for assembly,
`w3cz_bigon_of_site_model_of_not_kink` and `w3cz_bigon_of_site_of_not_kink` are the frozen consumers
`w3bi_bigon_of_site_model` / `w3bi_bigon_of_site` **on standard axioms only**, given the two non-kink conditions (needed
only in the self case `(sS D x).1 = (tS D x).1`; the mixed case uses `w3bg_not_kink_of_ne_comp`).

## 1. Closed / open / black boxes

| declaration | line | state |
|---|---|---|
| `w3bi_bigonData_smooth_arcST_switch_z` (frozen leaf) | :11007, sorry :11027 | **open, FALSE as stated**; body = reduction to `hk5 : 5 ≤ (Γ₀.comp (M.strandOf cutStartS _).1).k` (one `(by sorry)`) |
| `w3bi_bigonData_smooth_arcTS_switch_z` (frozen leaf) | :11030, sorry :11049 | **open, FALSE as stated**; body = reduction to `hk5` on the component of `cutStartT` |
| `w3cz_same_over_switch_swap` | :10785 | PROVED — `same_over` moves across the two switches when `{y₀, z₀}` are the bigon's crossings |
| `w3cz_bigonData_switch_transfer` | :10807 | **PROVED** — the BigonData transfer `D₀.switch y₀ → D₀.switch z₀`, both orientations (`(B.y, B.z) = (y₀, z₀)` or `(z₀, y₀)`); returns `j, y, z, s, ⟨i, a⟩, K` unchanged |
| `w3cz_site_y_ne_z`, `w3cz_lift_ne` | :10829, :10839 | PROVED — `y ≠ z` from `sS ≠ tS`, `g ≠ sS`; `y₀ ≠ z₀` through `origCrossing` |
| `w3cz_bigonData_smooth_arcST_switch_z_of_five`, `_arcTS_switch_z_of_five` | :10847, :10893 | **PROVED** — the switch_z statements + `hk5`, via the transfer from `w3bg_…_of_five` |
| `w3cz_bigonData_smooth_arcST_switch_z_of_not_kink`, `_arcTS_switch_z_of_not_kink` | :10871, :10917 | **PROVED** — the switch_z statements + G's non-kink hypothesis (the deliverable) |
| `w3cz_hk5_of_conclusion` | :10938 | PROVED — any `j = 2` bigon with entering edge `u` on `(D^x).switch c` gives `5 ≤ (Γ₀.comp u.1).k` |
| `w3cz_switch_z_arcST_iff_hk5`, `_arcTS_iff_hk5` | :10951, :10976 | PROVED — the frozen conclusions are **equivalent** to `hk5` under the frozen hypotheses (rule 3, formal) |
| `w3cz_bigon_of_site_model_of_not_kink` | :11132 | PROVED — `w3bi_bigon_of_site_model` (:11073) with `hkST hkTS`, consuming `w3bg_…_of_not_kink` + `w3cz_…_switch_z_of_not_kink`; no `sorryAx` |
| `w3cz_bigon_of_site_of_not_kink` | :11174 | PROVED — `w3bi_bigon_of_site` (:11112) on the library smoothing with `hk : (sS D x).1 = (tS D x).1 → hkST ∧ hkTS`; no `sorryAx` |

All 13 `w3cz_` theorems: `#print axioms` = `[propext, Classical.choice, Quot.sound]` (scratch copy with `#print axioms`
appended, exit 0).  `w3bi_bigonData_smooth_arcST/TS_switch_z`, `w3bi_bigon_of_site_model`, `w3bi_bigon_of_site` →
`[propext, sorryAx, Classical.choice, Quot.sound]` (through `hk5` at the two switch_z sites and through `w3g_*`).

Black boxes consumed: none of the other units' leaves.  Used from unit G (all PROVED, standard axioms):
`w3bg_bigonData_smooth_arcST_of_five`, `w3bg_bigonData_smooth_arcTS_of_five`, `w3bg_hk5_arcST_of_not_kink`,
`w3bg_hk5_arcTS_of_not_kink`, `w3bg_bigonData_smooth_arcST/TS_of_not_kink`, `w3bg_not_kink_of_ne_comp`.  From the
library: `Diagram.switch_overStrand_self / _of_ne`, `over_ne_under`, `under_ne_over`, `eq_over_of_mem_of_ne`,
`eq_under_of_mem_of_ne` (SM/LinkDiagram), `sS_ne_tS`, `toDiagram`, `origCrossing_liftCrossing`,
`crossingPoint_origCrossing` (SM/Smoothing), `BigonData` (SM/BigonDeletion).  Other units' leaves untouched:
`w3bi_esc_outer_data` (:10673), `w3bi_site_data_data` (:11225), `w3g_bigonData_smooth_arcST/TS` (:9237/:9267, G's `hk5`),
unit B's optional leaf (:4093).

## 2. The transfer (why only `same_over` moves)

`D₀.switch c` is `⟨D₀.Γ, D₀.generic, Function.update D₀.overStrand c (D₀.underStrand c), _⟩`, so `(D₀.switch y₀).Γ` and
`(D₀.switch z₀).Γ` are both `D₀.Γ` by `rfl`.  Of `BigonData`'s 28 fields, 27 mention only `.Γ` (`i a j hj hk s y z hy hz
run_free no_io ty tz tsy tsz hty htz htsy htsz K K_convex K_compact run_mem in_iff out_iff s_iff clear`) and are copied
by name into a structure instance (`{ i := B.i, …, same_over := key, … }`; the expected types are defeq to `B`'s, and
`exact` accepts them).  `same_over` on `D₀.switch y₀` with `B.y = y₀`, `B.z = z₀`, `s ∈ y₀.val ∩ z₀.val` reads
`(D₀.underStrand y₀ = s ∧ D₀.overStrand z₀ = s) ∨ (≠ ∧ ≠)` after `switch_overStrand_self / _of_ne`; on `D₀.switch z₀` it
reads `(D₀.overStrand y₀ = s ∧ D₀.underStrand z₀ = s) ∨ (≠ ∧ ≠)`.  Each is "the over bit of `s` at `y₀` is opposite to
the over bit at `z₀` in `D₀`": case 1 → case 2 by `over_ne_under`/`under_ne_over`; case 2 → case 1 by
`eq_over_of_mem_of_ne`/`eq_under_of_mem_of_ne` (`s` is in both crossings by `B.hy`, `B.hz`).  For `arcTS` the bigon has
`B.y = z₀`, `B.z = y₀`; the transfer takes `(B.y = y₀ ∧ B.z = z₀) ∨ (B.y = z₀ ∧ B.z = y₀)` and swaps the conjuncts with
`Or.imp And.symm And.symm`.  `y₀ ≠ z₀` (needed for `switch_overStrand_of_ne`) comes from `y ≠ z` (`{sS, g} ≠ {tS, g}`
since `sS ≠ tS` and `g ≠ sS`) through `origCrossing`.  Total ≈ 60 lines for the transfer; the four switch_z forms are
5-line wrappers (`obtain` from `w3bg_…_of_five`, transfer, `Eq.trans` the six equalities).  This confirms the frozen
docstring's claim ("`same_over` holds after switching EITHER of `y, z`, by `hover`; no other field sees the over data").

## 3. Rule 3: the frozen switch_z statements are false as stated (same kink reason as unit G)

The two switch_z statements have exactly the hypotheses of `w3g_bigonData_smooth_arcST/TS` (`clear_vertex` included);
their conclusion asks for a `BigonData` on `(D^x).switch z₀` with `j = 2` and `⟨B.i, B.a⟩ = M.strandOf cutStartS` (resp.
`cutStartT`).  `BigonData.hk` then forces `5 ≤ (Γ₀.comp (M.strandOf cutStartS _).1).k` (`w3cz_hk5_of_conclusion`,
`Γ₀ = ((D^x).switch z₀).Γ` by `rfl`).  In G's counterexample (`compB` of the self model with `b = a − 2`, `k = 4`:
`P(a−2) = (0,0)`, `P(a−1) = (2,0)`, `P(a) = (1,1)`, `P(a+1) = (1,−1)`, `g` through `y = (1, ½)`, `z = (1½, 0)`) every
hypothesis holds and `5 ≤ 4` fails; the over data at `y, z` and the switch at `z₀` play no role in `hk`.  So the frozen
statements are false as stated, and `w3cz_switch_z_arcST_iff_hk5` / `_arcTS_iff_hk5` show they are exactly `hk5` in
disguise: `(∃ B, …frozen conclusion…) ↔ 5 ≤ k`.  Per rule 3 the statements are untouched; the bodies follow unit G
(`exact w3cz_…_switch_z_of_five … (by sorry)`), which keeps the `sorry`-term count at 7 and pins the remaining gap to
`hk5`.  The counterexample is not formalised (as in unit G).

## 4. What the realiser / SITE must supply

* The corrected forms take G's non-kink hypothesis in `D`'s terms: `hkink : (⟨(sS D x).1, (sS D x).2 - 1⟩ : D.Γ.Strand)
  ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩` for `arcST`, `(⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩`
  for `arcTS` — identical to `w3bg_bigonData_smooth_arcST/TS_of_not_kink`, so whatever SITE derives for G's forms serves
  the switch_z forms unchanged.  On a one-component lift it says the smoothed crossing `x = e ∩ f` is not a kink
  (`f ≠ e − 2` resp. `e ≠ f − 2`); in the mixed case both are trivial (`w3bg_not_kink_of_ne_comp`).
* `w3cz_bigon_of_site_of_not_kink` is a drop-in for `w3bi_bigon_of_site` with one extra hypothesis
  `hk : (sS D x).1 = (tS D x).1 → hkST ∧ hkTS`; `w3bi_bigon_pair_of` (:11229) consumes `w3bi_bigon_of_site` and the
  frozen def `w3bi_SiteData` has no kink field, so wiring the sorry-free chain needs the parent's decision (a `w3bi_SiteData`
  variant with the non-kink condition, or the condition derived at the configuration where SITE builds the site data — it is a
  statement about `D`, `x` alone, so it can sit next to `hsite`).  Not done here (outside the unit).
* `clear_vertex` is consumed by none of the corrected forms (as in unit G).

## 5. Checks, numbers, pitfalls

* Final file 12154 lines (11851 + 303).  Full compile 0 errors, ≈ 45 s (last run 23:35–23:36 UTC / 7:35pm ET); exactly the
  7 `declaration uses sorry` warnings expected (:4093 B, :9237/:9267 G, :10673 OUTER, :11007/:11030 the two switch_z
  leaves through `hk5`, :11225 SITE).  `sorry` lines: 4095, 7856 (G's comment), 9257, 9286, 10674, 11027, 11049, 11226.
* Identity: `check_W3_identity.py` 5/5 IDENTICAL; `check_W3_statements.py` 42/42, `w3a_` 20, nothing missing.  Two docstrings
  of mine originally said "without `sorryAx`" and made `grep -c sorry` read 10; reworded to "on standard axioms only" so the
  count is 8 = 8 (the terms were 7 = 7 throughout).
* Scratch: `/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/bigon/`
  (`T1/T2.lean` the transfer, `T3.lean` the `hk5` exactness, `W3C_BIGON_Axioms.lean` the `#print axioms` copy).
  Iteration files import `SM.BigonDeletion` (+ `SM.Smoothing`) only and compile in ≈ 10 s.
* Pitfalls met: (i) a multi-line structure instance `{ i := B.i, …` needs its continuation lines at a column ≥ the first
  field's (`sepByIndent`/`colGe`) — a 4-space continuation gives "unexpected identifier; expected '}'"; (ii) `rw [h] at h1 h2 ⊢`
  fails if any location lacks the pattern (`hmz` had no `B.y`) — rewrite per hypothesis; (iii) `{ B with same_over := … }`
  cannot be used since `BigonData (D₀.switch y₀)` and `BigonData (D₀.switch z₀)` are different types — write all fields;
  (iv) `dif_pos/dif_neg` are deprecated (warnings only), kept to mirror the frozen `w3bi_bigon_of_site` proof.
* Time: started 23:19 UTC, transfer compiled in scratch 23:26, first full compile clean 23:29, exactness/iff + consumer
  variants clean 23:35, report 23:38 (all UTC; ET = −4h).  Well inside the 01:45 UTC hard stop.
