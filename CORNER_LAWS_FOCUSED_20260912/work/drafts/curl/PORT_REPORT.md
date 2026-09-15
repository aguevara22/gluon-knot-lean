# PORT_REPORT — cf:lem-curl (row 98), port file `Curl_Port.lean`

Port subagent, 2026-09-14 08:22 UTC / 4:22 am ET. Directory: `work/drafts/curl/`. Nothing written under `work/lean`; no
`lake build`. Compile command (the only one used): `cd work/lean && lake env lean ../drafts/curl/Curl_Port.lean`.

**Result.** `Curl_Port.lean` (8379 lines, sha256 a6eb134cccda48f3…) = `Curl_Assembled.lean` (8353 lines, 117d5e885abcce88…)
with the two residual issues repaired and the optional fidelity field added: **0 errors** (exit 0, 25 s wall), **0 occurrences of
the placeholder string** (`grep -ci` = 0, code and prose; the checker regex `^\s*(axiom|sorry|admit)\b|\bnative_decide\b` has no
hit), **no `#print`**, and on a /tmp copy
`#print axioms SM.cf_lem_curl` = **`[propext, Classical.choice, Quot.sound, SM.lp_lm]`** (no `sorryAx`, no new axiom).
Logs: `/workspace/scratch/curl_port_compile.log`, `/workspace/scratch/curl_port_axioms.log`; generator script
`/workspace/scratch/curl_port.py` (deterministic string replacements on `Curl_Assembled.lean`, each asserted to match exactly once);
diff `/workspace/scratch/curl_port.diff` (18 hunks, listed in §5).

## 1. Residual issue (1): the two false leaves — REPAIRED WITH THE HYPOTHESIS `α' ≤ β'` (not deleted)

`SM.Curl.ξ_strictMonoOn` and `SM.Curl.ξ_strictAntiOn` (Port lines 872-895) now read

```
theorem ξ_strictMonoOn {α' β' : ℝ} (hα : S.α ≤ α') (hβ : β' ≤ S.β) (hab : α' ≤ β')
    (hθ : ∀ t ∈ Icc α' β', |θrel S t| < Real.pi / 2) : StrictMonoOn (ξ S) (Icc α' S.t₀)
theorem ξ_strictAntiOn {α' β' : ℝ} (hα : S.α ≤ α') (hβ : β' ≤ S.β) (hab : α' ≤ β')
    (hθ : ∀ t ∈ Icc α' β', |θrel S t| < Real.pi / 2) : StrictAntiOn (ξ S) (Icc S.t₀ β')
```

- The only change to each statement is the added explicit hypothesis `(hab : α' ≤ β')`, inserted after `hβ` (so any future
  caller passing arguments positionally supplies `hα hβ hab hθ`). Without it both are false in the degenerate case `β' < α'`
  (unit-circle counterexample, U_G_REPORT.md; ASSEMBLY_REPORT.md §3).
- Proofs: the first branch of U_G's partial bodies (U_G.lean lines 823-858), verbatim except that `hα'αβ` is now
  `⟨hα, hab.trans hβ⟩` instead of `⟨hα, by linarith [ht.1, ht.2, S.lt_β]⟩` — this uses `hβ`, so neither leaf produces an
  unused-variable warning. Each reduces to the proved restricted form `g_ξ_strictMonoOn` / `g_ξ_strictAntiOn` after showing
  `|θrel| < π/2` on `[α', t₀]` (resp. `[t₀, β']`) from `hθ α'` (resp. `hθ β'`) and the monotonicity of `θrel` on the arc.
  Time: about 10 minutes.
- `#print axioms` of both = `[propext, Classical.choice, Quot.sound]`.
- Dependents: none — the assembler had already redirected the four uses in `r_glued_off` to the `g_` forms; that stays as it
  was (only re-wrapped, §4). The leaves are chain lemmas, not target rows; suggested AUTHOR_NOTES entry (FR-C8 style chain
  repair): "cf:lem-curl chain: `SM.Curl.ξ_strictMonoOn` / `ξ_strictAntiOn` carry the hypothesis `α' ≤ β'` that the printed
  'ξ increases strictly for s < 0 and decreases strictly for s > 0' (sm-3:3972-3974) takes for granted (the chart interval
  `[α', β']` is nonempty); without it the statements are false when `β' < α'` makes the angle bound vacuous."

## 2. Residual issue (2): the two prose mentions — REWORDED

- Header docstring (Assembled line 17, Port lines 18-19): "§7 the chain of leaf lemmas (all `<placeholder>`, grouped by …)" →
  "§7 the chain of leaf lemmas (all proved, grouped by the seven prover units U1-U7 of PLAN_FINAL.md §4, assembled 2026-09-14)".
- Section header (Assembled line 518, Port line 525): "/-! ## 7. The chain of leaf lemmas (all `<placeholder>`; unit split and
  estimates in PLAN_A.md §5) -/" → "/-! ## 7. The chain of leaf lemmas (unit split and estimates in PLAN_A.md §5) -/".
- Also in the header (prose only, not declarations): title "… replacement: SKELETON (judge's FINAL)" → "… replacement (judge's FINAL
  skeleton, proved and ported)"; the check line names `Curl_Port.lean`; the sentence "Sections 1-4 are the statement text of
  Statements_FINAL.lean verbatim" gained "(plus the field `CurlWitness.old_crossingPoint` and its conjunct in `CurlData.i`,
  PREREVIEW.md FR-C1 (a))"; and two sentences recording the leaf repair were appended.

## 3. Optional fidelity improvement — ADDED (`CurlWitness.old_crossingPoint`)

The construction provides it directly: `KinkInsertion` (Port line 481 ff.) has the field
`old_point : ∀ x, D'.Γ.crossingPoint (old x).1 = S.D.Γ.crossingPoint x`, and `curlWitness` sets `D' := K.D'`, `old := K.old`,
so the new field is `K.old_point` with no coercion or rewriting. Changes:

- `structure CurlWitness` (Port lines 245-247), inserted between `old_point` and `old_sign`:
  ```
    /-- … the polygonal crossings of `D'` that correspond to the old ones sit at the same points of
    the plane as before (so the polygon is modified only at the kink; from `KinkInsertion.old_point`) … -/
    old_crossingPoint : ∀ x : S.D.Γ.Crossing, D'.Γ.crossingPoint (old x).1 = S.D.Γ.crossingPoint x
  ```
- `structure CurlData`, field `i` (Port line 330): the conjunct `W.D'.Γ.crossingPoint (W.old x).1 = S.D.Γ.crossingPoint x ∧`
  inserted between the `old_point` conjunct and the `old_sign` conjunct inside the `∀ x : S.D.Γ.Crossing` clause. No other
  `CurlData` field touched.
- `def curlWitness` (Port line 8325): `old_crossingPoint := K.old_point`.
- `theorem cf_lem_curl`, field `i` (Port line 8372): `fun x => ⟨W.old_point x, W.old_crossingPoint x, W.old_sign x⟩`.

Effect: when the input site comes from a `Carried` record (the consumer's case, `CurlSite.ofCarried`), the output is now provably
`Carried`-like at every old crossing — `F'.γ (τ' (overVisit (old x))) = F.γ (τ (overVisit x)) = D.Γ.crossingPoint x = D'.Γ.crossingPoint
(old x)` — and record-level only at the kink, which is the one unavoidable deviation (PREREVIEW.md §2c). No hypothesis was added
anywhere; the field is a strengthening of the conclusion.

## 4. Other edits (proof text / file hygiene only)

- The four >140-character lines of the assembler's `r_glued_off` repair (Assembled 2664, 2667, 2686, 2691) are wrapped over
  three lines each (Port 2689-2691, 2693-2695, 2713-2715, 2719-2721); same terms, same statement.
- The three trailing `#print axioms` commands are dropped (every `work/lean/SM/*.lean` module header says "#print lines removed";
  no library module contains a `#print`). They live in the /tmp copy instead (§6).
- Nothing else: no helper lemma was needed; no name was added other than the field `old_crossingPoint` (checked: no
  `old_crossingPoint` anywhere under `work/lean/SM`).

## 5. Diff `Curl_Assembled.lean` → `Curl_Port.lean` (all 18 hunks; `diff` line numbers)

| hunk | what |
|---|---|
| 5c5 | header title (prose) |
| 14c14,15 · 17,18c18,19 · 20c21 · 22c23,25 | header prose: "verbatim (plus …)", "(all proved, …)", check line, leaf-repair note |
| 241a245,247 | `CurlWitness.old_crossingPoint` (field + docstring) |
| 323a330 | `CurlData.i`: the `crossingPoint` conjunct |
| 518c525 | §7 header (prose) |
| 865c872 · 867,868c874,884 | `ξ_strictMonoOn`: `hab` + proof |
| 870c886,895 | `ξ_strictAntiOn`: `hab` + proof |
| 2664,2665c2689,2691 · 2667,2668c2693,2695 · 2686,2687c2713,2715 · 2691,2692c2719,2721 | line wrapping in `r_glued_off` |
| 8295a8325 | `curlWitness`: `old_crossingPoint := K.old_point` |
| 8342c8372 | `cf_lem_curl`, field `i`: the new projection |
| 8350,8353d8379 | trailing `#print axioms` ×3 removed |

## 6. Compile, placeholder count, axioms

- `cd work/lean && lake env lean ../drafts/curl/Curl_Port.lean`: **exit 0, 0 errors**, 25.0 s wall (1 m 31 s user).
  Warnings (all inherited from the assembled file, none new): `hlam` ×3, `hη`, `hβ'`, `hα'`, `hs`, `hr`, `hpos`, `hneg`
  unused (frozen leaf statements), `<;>` linter ×2, `dif_pos`/`dif_neg` deprecation ×2. No `declaration uses sorry`.
- `grep -ci` for the placeholder string: **0**. `grep -nE '^\s*(axiom|sorry|admit)\b|\bnative_decide\b|#print'`: no hit.
- /tmp copy `/tmp/Curl_Port_axioms.lean` (= Port + seven `#print axioms`), exit 0, 0 errors:
  `SM.cf_lem_curl`, `SM.CurlData`, `SM.Curl.curlWitness`, `SM.exists_curl_main` → `[propext, Classical.choice, Quot.sound, SM.lp_lm]`;
  `SM.Curl.ξ_strictMonoOn`, `SM.Curl.ξ_strictAntiOn`, `SM.Carried.toRecordCarried` → `[propext, Classical.choice, Quot.sound]`.
  `SM.lp_lm` enters through `P_reidemeister_I` (`poly_eq`), as in the assembled file; it is the literature axiom of
  `axiom-policy.json`.

## 7. Byte-compare with `Statements_FINAL.lean` (script `/workspace/scratch/curl_stmt_compare.py`)

Blank-line-separated paragraphs of `Statements_FINAL.lean` containing a `structure/def/theorem/lemma/abbrev/instance`
(docstrings included): **26**; **23 occur byte-for-byte** in `Curl_Port.lean` (`RecordCarried`, `smoothSign`, `smoothWrithe`,
`smoothSign_eq`, `smoothWrithe_eq`, `no_triple`, `doublePoints_eq`, `Carried.toRecordCarried`, `CurlSite`, `CurlSite.p`,
`CurlSite.T`, `T_eq_tangentLoop`, `u_unit`, `CurlSite.one`, `T_eq_u_iff`, `CurlWitness.curve`, `CurlWitness.T`,
`smooth`/`periodic`/`regular`, `CurlWitness.one`, `kink_smoothSign`, `old_smoothSign`, `CurlWitness.smoothWrithe_eq`,
`CurlSite.ofCarried`). **Exactly three differ**, each only as follows:

1. `structure CurlWitness` — three added lines (the `old_crossingPoint` field and its two docstring lines); every other line
   identical.
2. `structure CurlData` — one added line (the `crossingPoint` conjunct in field `i`); every other line identical.
3. `theorem cf_lem_curl : CurlData` — head identical; docstring `/-- cf:lem-curl. -/` → the skeleton's
   `/-- cf:lem-curl, assembled from the chain; … -/`, body `:= by <placeholder>` → the proved `where` instance (inherited from
   Skeleton_FINAL; the row's name and type are unchanged).

Line-level: every non-blank line of `Statements_FINAL.lean` from `namespace SM` on occurs in order in `Curl_Port.lean` except
the three row lines (380-382). Names/types of `CurlSite`, `RecordCarried`, all other `CurlData` fields, and the row head are
byte-identical.

## 8. Notes for the port to `work/lean/SM/Curl.lean`

- Imports `SM.Rounding`, `SM.LinkMoves`, `SM.PolynomialBlock` (unchanged from the assembly).
- Because `CurlWitness` gained a field and `CurlData.i` a conjunct, the fixed-statement record for row 98 should point at
  `Curl_Port.lean`'s §1-4 (or Statements_FINAL.lean + this report §3) rather than Statements_FINAL.lean alone.
- PREREVIEW.md recommendation 2 still applies at port time: amend or annotate Rounding.lean §4's "one smooth-diagram notion
  for … cf:lem-curl" sentence (the curl output is `RecordCarried`, `Carried`-like at old crossings by `old_crossingPoint`) and
  record in AUTHOR_NOTES that the RI disc `U` of `ri : RI D D'` is unrelated to `Δ`. Not done here (outside this task's scope;
  no file outside `work/drafts/curl` was touched).
