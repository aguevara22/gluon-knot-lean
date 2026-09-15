# HYPR_PLAN.md — row hyp:R → `SM.hyp_R` (statement of SM's Hypothesis R)

Draft: `work/drafts/hypr/HypR.lean` (this directory). Compile check 2026-09-14:
`cd work/lean && lake env lean ../drafts/hypr/HypR.lean` → exit 0, 0 errors, 0 warnings, no `sorry`
(log copy: /tmp/hypr_compile.log).
`#print axioms SM.hyp_R` = `propext, Classical.choice, Quot.sound, SM.lit_homfly` (the Prop mentions
`cornerStateSum`, hence the HOMFLY interface — identical to `CV.hyp_R`'s axiom list in work/reviews/cv-ax-R.json).
`#print axioms SM.sm_R_of_cv_R` adds `SM.lp_lm, SM.lp_lm_uniqueness` (through the accepted `Bridge.B4`).

## 0. What kind of row this is

`hyp:R` is a `\status{hyp}` row: the DEFINITION of a proposition, not a claim. It has no proof in the source
("The source calls R a hypothesis. This deliverable must prove it." TARGETS.md:27-29; PROOF_PLAN.md step 1
"Treat `hyp:R` and `CV:ax:R` as propositions whose truth is to be proved"). Its twin CV:ax:R was accepted
2026-09-14 as the Prop definition `CV.hyp_R` (work/lean/RProof/X1Rows.lean:124-133, review
work/reviews/cv-ax-R.json, verdict faithful, 3 lenses + 2 refuters). The same treatment applies here:
declare `def SM.hyp_R : Prop`, statement-review it against sm-4-knotlaws.tex:1149-1151, accept; never declare
an axiom (axiom-policy `mode: explicit_parameter`: consumers take it as an explicit hypothesis or prove it).

## 1. The definition (verbatim from HypR.lean)

```lean
def hyp_R : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (e f k : ZMod n), g.TripleAt e f k →
    ∀ tp tm : g.SideParameter,
      cornerStateSum hn (g.sideTuple true tp).property =
        cornerStateSum hn (g.sideTuple false tm).property
```

## 2. Clause map

Printed sentence (reference/SM/sm-4-knotlaws.tex:1149-1151; EXTRACTS.json segment 1149-1151, sha256
58c0b3811763d8192e99a9038330c1e7e73305f4d978a205948c01da9e51a50e; STATEMENTS_AND_PROOFS.md:8692-8700):

```tex
\begin{hypothesis}[R]\label{hyp:R}
At every simple triple wall, $C(P_+)=C(P_-)$. \status{hyp}
\end{hypothesis}
```

| printed | presupposed definition (source, accepted row → Lean) | in `SM.hyp_R` |
|---|---|---|
| "wall" | def:germ "wall germ; sides" sm-1-polygons.tex:680-695 → row def:germ `SM.wall_germ_definition` (SM.GermDefinition), object `SM.WallGerm n` (SM/WallGerm.lean:13-19: `radius > 0`, continuous `curve : Ioo (-radius) radius → LabelledTuple n`, `generic_punctured`, `nongeneric_center`) | `(g : WallGerm n)` |
| "simple ... wall" | def:walls sm-1:737-777 "A wall germ is *simple of one of the following types*" → row def:walls `SM.named_walls_definition` (SM.NamedWallsDefinition; its field `triple_predicate` ties `TripleAt` to the centre kind + sign changes); "simple of type (T)" = `g.HasWallKind .triple = ∃ e f k, g.TripleAt e f k` (SM/WallCenterKinds.lean:47-56) | antecedent `g.TripleAt e f k` with `e f k` universally quantified (∀g,(∃efk,A)→B ⇔ ∀g efk,A→B; recorded as `hyp_R_iff_hasWallKind`) |
| "triple wall (at {e,f,g})" | def:walls (T) sm-1:762-766: `Z_pt = ∅`, `Z_c = {{e,f,g}}`, on each of the three edges the difference of the two crossing parameters of the other two edges changes sign at 0 (their existence: lem:triple-sides sm-1:697, row `SM.triple_sides`) | `WallGerm.TripleAt e f k` (SM/NamedWallPredicates.lean:30-34): `g.pointZeros = ∅ ∧ g.concurrences = {{e, f, k}} ∧ SignChanges (edgeParameter · e f − edgeParameter · e k) ∧ … f … ∧ … k …`; `pointZeros/concurrences` = `pointZeroTriples/concurrenceTriples g.center` (GermDefinition.lean:12-14; `ConcurrenceTriple` = pairwise remote with a common interior point, ZeroTriples.lean); `SignChanges φ := ∃ δ, 0<δ ∧ δ≤radius ∧ ∀ t∈(0,δ), φ(P(t))·φ(P(−t)) < 0` (GermSignChange.lean:10-12) = def:germ's "changes sign at 0" |
| "the sides P₊, P₋" | def:germ sm-1:683-686 "Its *sides* P₋ and P₊ are the chambers containing P((−ε,0)) and P((0,ε)); each … lies in one chamber. For a function F that is constant on chambers, F(P_±) denotes its value on the respective side." | `g.sideTuple true tp` (= `⟨g.curve (+tp), _⟩`, WallGerm.lean:34-50) and `g.sideTuple false tm` (= `⟨g.curve (−tm), _⟩`) for all `tp tm : g.SideParameter = Ioo 0 g.radius` — the convention of the accepted prop:C-silent (`CSilentData.extension/cut`, SM/CSilent.lean; same printed phrase "C(P₊)=C(P₋)"), thm:uniqueness (d) (`UniquenessHypotheses.triple`, SM/Uniqueness.lean:65-69) and cor:A-lawful (`ALawfulData.triple_law`, SM/ALawful.lean:114-118). Well-definedness of the chamber value: each side image lies in one chamber (`WallGerm.sidePolygon_mem_side`, SM/GermSides.lean) and C is constant there (prop:C-chamber sm-4:36-40, row `SM.prop_C_chamber`) — `hyp_R_iff_base` proves the point-value form ⇔ the value at the side base point `radius/2`, i.e. on `g.side b = chamber (g.sidePolygon b g.sideBase)` |
| "C" | def:C sm-3-statesum.tex:1688-1700 → row def:C `SM.corner_state_sum_definition` (SM.CornerStateSum), object `cornerStateSum hn hP : ℤ` (line 166) on a generic labelled polygon | `cornerStateSum hn (g.sideTuple b t).property` |
| "=" | — | `=` in `ℤ`; symmetric in the sides as printed |
| (presupposition) | C needs `n ≥ 3` and `ZMod n` indexing needs `NeZero n` | binders `[NeZero n] (hn : 3 ≤ n)`, as in prop:C-silent and CV.hyp_R (R6); no printed content lost: `TripleAt` needs a pairwise remote triple (`adjacent i j := j−i ∈ {−1,0,1}`, Polygon.lean:63), impossible for n < 6 |

Every printed word has a Lean counterpart and every binder is a printed clause or a labelled presupposition.

## 3. Relation to `RProof.smR_shape_of_hyp_R` (X1Rows.lean:2982) and to `Bridge.sm_R`

* `smR_shape_of_hyp_R`'s conclusion is NOT literally `SM.hyp_R`: it is the DIAGONAL form
  `∀ … g.TripleAt e f k → ∀ t : g.SideParameter, C (g.sideTuple true t).2 = C (g.sideTuple false t).2`,
  which HypR.lean names `SM.HypRDiagonal` (`smR_shape_conclusion_is_diagonal` type-checks by `rfl`).
  `SM.hyp_R` (independent `tp tm`, the accepted C-row convention) is syntactically stronger; the two are
  equivalent by prop:C-chamber (`hyp_R_iff_diagonal`, PROVED), as is the chamber-value form (`hyp_R_iff_base`).
* The stronger form costs the bridge nothing: `CV.hyp_R` is itself in the independent-`tp tm` R6 form, so the
  proof of `smR_shape_of_hyp_R` run with `g.sideTime true tp`, `g.sideTime false tm` gives
  `hyp_R_of_cv_hyp_R : CV.hyp_R → (B4 pointwise) → SM.hyp_R` (PROVED, same 14 lines), and with the accepted
  `Bridge.B4.pointwise`: `sm_R_of_cv_R : CV.hyp_R → SM.hyp_R` (PROVED). This is exactly BRIDGE.md §3 (19)-(21)
  with `SM.hyp_R` as the literal conclusion.
* Consequence for the Bridge lane: row Bridge:theorem (`Bridge.sm_R : SM.hyp_R`, ORDER.md #187, pending, blocked
  on `RProof.cv_R` = R:cv_theorem, GAP-2) becomes the one-liner `theorem Bridge.sm_R : SM.hyp_R := SM.sm_R_of_cv_R RProof.cv_R`.
  Recommendation: when porting, move Part 3 of HypR.lean into `work/lean/Bridge/SmR.lean` (importing
  `SM.HypR`, `RProof.X1Rows`, `Bridge.B4`) and either leave `smR_shape_of_hyp_R` untouched (its docstring
  already says "This is the shape of `Bridge.sm_R`, not the fixed row itself") or add a one-line remark that
  its conclusion is `SM.HypRDiagonal`. Do not edit the accepted X1Rows.lean for this.

## 4. Fidelity risks

* **FR-HR-1 (all-sides vs one representative vs chamber value).** Printed `C(P₊)=C(P₋)` is an equality of
  chamber values (def:germ's `F(P_±)`), well defined only through prop:C-chamber. Three renderings: all pairs of
  side points (`hyp_R`), one common parameter (`HypRDiagonal`), the base points (`HypRBase`). All three are
  PROVED equivalent in HypR.lean via the accepted `SM.prop_C_chamber` + `sidePolygon_mem_side`; the chosen
  form is the one used by the accepted prop:C-silent for the identical phrase and by CV:ax:R (R6; its review
  lists the same point as non-blocking "stronger_than_source"). Review note to carry: "stronger than one
  representative per side; equivalent to the printed chamber-value equality under prop:C-chamber, which the
  printed notation presupposes; not a domain change."
* **FR-HR-2 (class of walls).** Only SIMPLE TRIPLE walls: def:walls (T) = `TripleAt`, which includes the three
  sign-change conditions ("the sign-change conditions exclude tangential germs", sm-1:776-777). Not
  `TripleCenterAt` alone (the centre kind without sign changes), not every germ with `Z_c` a single triple
  (lem:triple-sides' wider hypothesis), not CV's `IsSimpleRIII` (the CV class; B1-B3 prove SM-(T) ⊆ CV-RIII, the
  converse is not asserted, BRIDGE.md §4). The triple is unordered (`{{e,f,k}}`; `tripleAt_support_iff`), so no
  representative-order hypothesis appears (unlike `CV.hyp_R`'s `rep e < rep f < rep g`, which B1's
  `exists_sorted_tripleAt` supplies on the CV side).
* **FR-HR-3 (`hn : 3 ≤ n`, `[NeZero n]`).** Labelled presuppositions (C's binder; ZMod indexing), same as
  prop:C-silent and `CV.hyp_R`; vacuous restriction since `TripleAt` forces n ≥ 6.
* **FR-HR-4 (labelled vs quotient).** `cornerStateSum` is defined on labelled generic tuples; the printed sides
  are chambers of the cyclic quotient `𝓤_n/(ℤ/n)`. `g.sideTuple b t` is a labelled representative of a point of
  the side `g.side b ⊆ GenericPolygon n`; prop:C-chamber (stated on `GenericTuple` via `polygonProjection` /
  `chamber`) is exactly what identifies representatives' values with the chamber value. Same convention as every
  accepted C row.
* **FR-HR-5 (orientation of the sides).** `true` ↔ `P((0,ε))` = P₊, `false` ↔ `P((−ε,0))` = P₋ (def:germ
  sm-1:683-684; `sideTime`). The equation is symmetric, so a swap would not change the proposition.
* **FR-HR-6 (no shrinking clause).** The printed hypothesis has no "after shrinking the interval"; `hyp_R`
  asserts the equality for every side parameter inside the germ's radius — legitimate because each whole
  punctured side lies in one chamber (def:germ), i.e. no δ-form is needed (contrast `SignChanges`, which is a
  δ-form because the source says "there is δ>0").
* **FR-HR-7 (evaluation on generic sides).** C is only defined on generic polygons; the sides are generic by
  `generic_punctured` (`sideTuple`'s proof component). No value at the nongeneric centre enters. (The weak
  state sum def:C-weak is not involved.)
* **FR-HR-8 (hypothesis, not claim; no axiom).** `SM.hyp_R` must be a `def … : Prop`; the audit records kind
  "definition" (as for `CV.hyp_R`). Nobody may `axiom SM.hyp_R`; the policy mode is `explicit_parameter`.
  thm:comparison (row 132, pending; deps include `hyp:R`) and the final assembly consume it as an explicit
  argument or via `Bridge.sm_R`.

## 5. Porting and review recipe (definition row, like CV:ax:R / def:C)

1. **Modules.** `work/lean/SM/HypR.lean` ← Part 1 (+ Part 2) of HypR.lean; imports `SM.CornerStateSum`,
   `SM.NamedWallPredicates`, `SM.WallCenterKinds` (Part 1) and `SM.GermSides`, `SM.CChamber` (Part 2).
   `work/lean/Bridge/SmR.lean` ← Part 3 (imports `SM.HypR`, `RProof.X1Rows`, `Bridge.B4`); it will later
   receive `theorem Bridge.sm_R : SM.hyp_R := SM.sm_R_of_cv_R RProof.cv_R`. Drop the `#print axioms` lines
   (port convention); add the "Ported … from work/drafts/hypr/HypR.lean" header line only.
2. **Map the row.** `python3 work/port/map_row.py implement hyp:R SM.hyp_R SM.HypR` (the declaration name is
   pre-filled and checker-fixed; any other name fails `fixed declaration name mismatch: hyp:R`,
   tools/check_lean.py:108). Run `python3 tools/check_lean.py work/lean` (development stage; this is the only
   place `lake build` is run, by the tool). The receipt work/checks/declaration-audit.json then carries the
   statement hash `statement_hashes['hyp:R']`.
3. **Statement review** (a definition row: `parameters_reviewed` and `definition_equivalence_reviewed` both
   get set by acceptance). Prepare: excerpt `work/reviews/hyp-R-source-excerpt-lines-1149-1151.tex.txt`
   (= sm-4-knotlaws.tex 1149-1151 verbatim); reviewer input
   `work/reviews/hyp-R-reviewer-input-statement.lean.txt` (`python3 work/port/strip_proofs.py` on SM/HypR.lean —
   there are only definitions and short proofs of the sanity lemmas; the row itself has no proof); prompt
   `work/port/review_prompt_hyp-R.md` modelled on `review_prompt_prop-C-silent.md` / `review_prompt_cv-axioms.md`
   with the reading list: sm-4:1149-1151 (the row), sm-1:680-695 (def:germ, sides), sm-1:737-777 (def:walls,
   esp. (T) 762-766), sm-1:697-703 (lem:triple-sides statement), sm-3:1688-1700 (def:C), sm-4:36-40
   (prop:C-chamber, for the well-definedness of C(P±)); Lean definition modules SM/WallGerm.lean,
   GermDefinition.lean, GermSignChange.lean, NamedWallPredicates.lean, WallCenterKinds.lean, GermSides.lean,
   CornerStateSum.lean, Chambers.lean, CChamber.lean (statement only), CSilent.lean (statement only, as the
   accepted precedent for the side convention). Lenses: `literal`, `definitions`, `strength` + 2 refuters
   (the CV:ax:R pattern). Point the reviewers at FR-HR-1 (ask them to label the all-sides form non-blocking or
   to reject it) and FR-HR-2 (is `TripleAt` exactly def:walls (T)?).
4. **Accept.** `python3 work/port/summarize_review.py …` → `work/reviews/hyp-R-review-workflow-raw.json`; then
   `python3 work/port/write_review_and_accept.py hyp:R hyp-R SM.hyp_R SM.HypR reference/SM/sm-4-knotlaws.tex
   "reference/SM/sm-4-knotlaws.tex:1149-1151 (hyp:R, Hypothesis R)" reviews/hyp-R-source-excerpt-lines-1149-1151.tex.txt
   reviews/hyp-R-reviewer-input-statement.lean.txt 0 literal,definitions,strength "<kernel text>" "<notes>"`.
   Kernel text to record: `#print axioms SM.hyp_R = propext, Classical.choice, Quot.sound, SM.lit_homfly`; the
   row is a Prop definition, no proof; `sm_R_of_cv_R` proves `CV.hyp_R → SM.hyp_R` from accepted rows.
5. **Afterwards.** Update STATE_OF_WORK.md ("2 hypotheses to state" → both stated) and OPEN_WORK/Bridge notes:
   Bridge:theorem = `SM.sm_R_of_cv_R RProof.cv_R`, waiting only on R:cv_theorem.

## 6. Tool indexing facts for hyp:R (as found 2026-09-14)

* blueprint/NODES.tsv line 119 (header is line 1): `hyp:R  hypothesis  HYPOTHESIS  hyp  sm-4-knotlaws.tex
  reference/SM/sm-4-knotlaws.tex  1149  0  Y  (deps: none)  stage1=Y  labels=hyp:R`. blueprint/STAGE1.tsv line
  119: identical. Kind: env `hypothesis`, action `HYPOTHESIS`, status_class `hyp`, 0 proofs, in closure.
* blueprint/ORDER.md: position **7** (`7. hyp:R`, after def:germ #2, def:walls #4, CV:def:event #6); its
  consumers (DEPENDENCIES.json) are `Bridge:theorem` #187 and `thm:comparison` #189; related rows: `CV:ax:R` #76,
  `R:cv_theorem` #185. (`thm:uniqueness` #188 is not a consumer: its clause (d) is a hypothesis on a free `F`.)
* blueprint/EXTRACTS.json: `{"action": "HYPOTHESIS", "id": "hyp:R", "segments": [{"source":
  "reference/SM/sm-4-knotlaws.tex", "start": 1149, "end": 1151, "sha256": "58c0b381…a50e"}]}` (line 1876).
* blueprint/DEPENDENCIES.json: `"hyp:R": []` (no dependencies, line 448); listed as a dependency of
  `Bridge:theorem` (line 54) and `thm:comparison` (line 731); present in the two closure lists at lines 790
  and 1001. blueprint/STATEMENTS_AND_PROOFS.md:8692 `## hyp:R — HYPOTHESIS` with the tex block.
  blueprint/AXIOM_REGISTRY.md does not mention it (it is not an axiom).
* work/lean/axiom-policy.json: `"hypothesis": {"declaration": "SM.hyp_R", "label": "hyp:R", "mode":
  "explicit_parameter"}` (top of file); `targets` has `"CV:ax:R": "CV.hyp_R"`, `"Bridge:theorem": "Bridge.sm_R"`,
  `"R:cv_theorem": "RProof.cv_R"`.
* tools/check_lean.py:104 and tools/bootstrap.py:33: `fixed = policy['literature'] | policy['targets'] |
  {'hyp:R': 'SM.hyp_R'}` — the name is enforced at every check (`fixed declaration name mismatch`).
* tools/claims.py:28 `SKIP = {'AXIOM', 'HYPOTHESIS', 'SKIP', 'CERTIFICATE'}`: hyp:R is not a claim unit and is
  not listed by `claims.py`; lines 50/57: unaccepted HYPOTHESIS dependencies are not counted against consumers
  (so thm:comparison/Bridge:theorem are not "blocked" on it in the claims view). tools/progress.py:62 counts only
  PROVE rows. tools/scope.py:41 keeps it in scope (action not SKIP/CERTIFICATE) — it is one of the 192 mapped rows.
* work/lean/lean-declarations.json: index **117** (0-based) `{"id": "hyp:R", "labels": ["hyp:R"], "source":
  "reference/SM/sm-4-knotlaws.tex", "line": 1149, "stage1": true, "declaration": "SM.hyp_R", "module": "",
  "status": "pending", …}` — declaration pre-filled by bootstrap, module empty, never implemented.
* work/port/*.json: `lane_orders.json` and `rereview_rows.json` do not mention hyp:R (grep empty); no
  `review_prompt_hyp-R.md` exists yet.
* STATE_OF_WORK.md:84-85 "2 hypotheses to state (`hyp:R`, `CV:ax:R`)" — CV:ax:R is done (accepted
  2026-09-14T07:49Z), hyp:R is this draft.
