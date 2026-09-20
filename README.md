# corner-laws-lean

A Lean 4 formalization of the wall laws and the soft theorem for the corner state sum `C`, from the paper
*Corner state sum: wall laws and soft theorem* (source frame SM15). One final theorem, `SM.corner_laws_and_soft`,
kernel-checked on Mathlib plus five results admitted from the literature. No `sorry`. Complete.

| | |
|---|---|
| Final theorem | `SM.corner_laws_and_soft`, in `CORNER_LAWS_FOCUSED_20260912/work/lean/SM/CornerLawsAndSoft.lean` |
| Source statements formalized | 192 checklist rows (132 claims, 60 definitions / interfaces / hypotheses), all accepted |
| Lean library | 712 modules, 366,040 lines, namespaces `SM`, `CV`, `RProof`, `Bridge` |
| Placeholders (`sorry`, `admit`, `native_decide`) | none |
| Axioms beyond Lean's three standard ones | 6 constants for 5 literature interfaces (section 2) |
| Pins | Lean `leanprover/lean4:v4.34.0-rc2`, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0` |
| Checker | `python3 tools/check_lean.py work/lean --all` PASS (191 mapped rows, 49,207 declarations audited) |

---

## 1. What is proved

`P` is a labelled closed polygon with `n` vertices in the plane. The generic polygons form an open set whose
connected components are the *chambers*; the walls between chambers are classified by what degenerates on
them (flat, vertex–edge of bigon or sliding type, triple, cusp, exterior extension, pure cut). The corner state
sum `C(P) ∈ ℤ` (def:C, `SM.cornerStateSum`) is computed from the link diagrams the polygon carries and their
HOMFLY-PT polynomials. The theorem says exactly how `C` changes at every kind of wall, and how it behaves under
the soft insertion of a vertex.

| Clause | Identity (printed domain) | Field | Proved as |
|---|---|---|---|
| Chamber constancy | `C` is constant on every chamber | `chamber` | prop:C-chamber |
| Silence | `C(P₊) = C(P₋)` at a simple exterior-extension wall or a simple pure cut | `silent` | prop:C-silent |
| Flat law | `C(P_right) − C(P_left) = C(P(0) \ j)` at a simple flat wall at `j`, `n ≥ 4` | `flat` | thm:C-S3 |
| Vertex–edge law | `C(P₊) − C(P₋) = s · C(λ₁) · C(λ₂)` at a simple vertex–edge wall at `(M; a)`, bigon or sliding, `λ₁, λ₂` the deletion halves, `s` the contact sign | `vertex_edge` | thm:C-S7 |
| Triple invariance | `C(P₊) = C(P₋)` at every simple triple wall — Hypothesis R of the paper, here *proved* | `triple` | Bridge:theorem |
| Cusp law | `C(P_loop) − C(P_no) = −κ · C(P(0) \ j)` at a simple cusp whose deletion satisfies G1, threaded cusps included | `cusp` | cor:C-inherits |
| Empty-cusp zero | `C(P_no) = 0` at a simple empty cusp | `empty_cusp` | thm:C-S5 |
| Soft theorem | `C(P_ε) = (χ₋ + χ₊)/2 · C(P)` for all sufficiently small `ε > 0`, `P_ε` the soft insertion at vertex `j` in admissible direction `q`, `χ±` its attachment signs | `soft` | thm:C-soft |
| Normalizations | the reversal, cyclic and triangle identities inherited with cor:A-lawful | `reversal`, `cyclic`, `triangles` | cor:C-inherits, def:C |

In Lean the conclusion is a `Prop` structure with one field per clause, and the final theorem is that structure,
with Hypothesis R discharged by the proved bridge theorem rather than assumed:

```lean
structure CornerLawsAndSoftData : Prop where
  chamber     : CChamberData
  silent      : CSilentData
  flat        : CS3Data
  vertex_edge : CS7Data
  triple      : hyp_R
  cusp        : CuspLawC
  empty_cusp  : CS5Data
  soft        : CSoftData
  reversal    : ReversalLawC
  cyclic      : CyclicLawC
  triangles   : TrianglesC

theorem corner_laws_and_soft : CornerLawsAndSoftData :=
  corner_laws_and_soft_of Bridge.sm_R thm_C_S7 thm_C_soft (cor_C_inherits Bridge.sm_R)
```

The eight named results it assembles, with their fixed Lean names (`work/lean/axiom-policy.json`):

| Source result | Lean name | Module |
|---|---|---|
| prop:C-chamber | `SM.prop_C_chamber` | `SM/CChamber.lean` |
| prop:C-silent | `SM.prop_C_silent` | `SM/CSilent.lean` |
| thm:C-S3 | `SM.thm_C_S3` | `SM/CS3.lean` |
| thm:C-S5 | `SM.thm_C_S5` | `SM/CS5.lean` |
| thm:C-S7 | `SM.thm_C_S7` | `SM/CS7.lean` |
| thm:C-soft | `SM.thm_C_soft` | `SM/CSoft.lean` |
| Bridge:theorem (Hypothesis R for SM) | `Bridge.sm_R` | `Bridge/SmRRow.lean` |
| SM:corner_laws_and_soft | `SM.corner_laws_and_soft` | `SM/CornerLawsAndSoft.lean` |

Every intermediate statement of the paper's proof route is formalized too: the 192 rows of
`work/lean/lean-declarations.json` map each printed definition, lemma, theorem and obligation to its Lean
declaration. `GLOSSARY.md` translates the paper's notation to Lean names.

---

## 2. What it rests on

The trusted base is the Lean 4 kernel, Mathlib at the pinned commit, and **five results admitted from the
literature as axioms**. These are the only unproved nonstandard inputs; the paper's own statements are all
proved. The final theorem is therefore established *modulo* these five:

| Interface | Lean constant | What it asserts | Source |
|---|---|---|---|
| lit:homfly | `SM.lit_homfly` | a HOMFLY-PT map on oriented link diagrams: the skein relation `a·H(D₊) − a⁻¹·H(D₋) = z·H(D₀)`, value 1 on the crossing-free circle, invariance under planar isotopy and the three Reidemeister moves | Lickorish–Millett |
| lit:homfly, descent sentence | `SM.lit_homfly_descent` | "its value depends only on the oriented link presented by `D`": equal values along smooth isotopies of the presented links | Reidemeister's theorem |
| lp:lm | `SM.lp_lm` | the exact Lickorish–Millett local construction `F_D(l, m)`, with its skein relation and initialization | Lickorish–Millett, §1 |
| lp:lm-uniqueness | `SM.lp_lm_uniqueness` | uniqueness of that function over its own coefficient ring | Lickorish–Millett |
| ng:finite-word | `SM.ng_finite_word` | finite front-word reduction: every finite front word admits a finite principal chain of front moves | Ng; Rutherford |
| src:contact | `SM.src_contact` | the front and positive-pushoff formulas of contact topology: the classical invariants of an oriented Legendrian front from its cusp and crossing counts | Etnyre |

Each is declared as a single `axiom` in existential form over a structure of the printed clauses
(`SM/LinkInterfaces.lean`, `SM/LitHomflyDescent.lean`, `SM/FrontInterfaces.lean`, `SM/SrcContact.lean`), registered
in `work/lean/axiom-policy.json`, and was itself reviewed against the printed text like every other row. The
registry with the printed statements is `blueprint/AXIOM_REGISTRY.md`.

**The point to be aware of:** lit:homfly is two constants. The first covers Reidemeister moves between
polygonal diagrams; the paper's closing sentence, descent to the oriented link under smooth isotopy, is declared
separately as `SM.lit_homfly_descent` (on the author's decision, since proving Reidemeister's theorem for smooth
isotopies was out of scope). 21 of the 192 rows, the final theorem among them, depend on that second constant.
A reader who prefers not to admit it should read those rows as "proved modulo Reidemeister's theorem for smooth
isotopies with isotopy extension". `FINAL_REVIEW.md` §4.3 lists the axiom footprint of every row.

`#print axioms SM.corner_laws_and_soft` gives exactly `propext`, `Classical.choice`, `Quot.sound` and the six
constants above; the checker rejects `sorryAx`, `native_decide` and any unregistered axiom anywhere in the library.

---

## 3. Reading the statement without the proofs

A Lean theorem means what its statement means; the proofs do not enter. To read `SM.corner_laws_and_soft` one reads
the definitions its type unfolds to. The checker's audit lists them: **383 declarations, all in the `SM`
namespace, in 73 files**, on top of Mathlib — 234 definitions, 26 inductive types, 26 structures and instances, 96
lemmas that definitions use (well-definedness, decidability), and the axiom `SM.lit_homfly`, whose chosen witness
is the HOMFLY map inside the definition of `C`. The full list, by file, is
[`docs/statement_closure.md`](docs/statement_closure.md). Nothing from `CV`, `RProof` or `Bridge` appears in it:
those namespaces serve the proof of Hypothesis R only.

For every one of the 192 rows the reviewers' inputs are kept in `work/reviews/`: the Lean statement with every
proof replaced by `sorry` (`*-reviewer-input-statement.lean.txt`) and the source excerpt it was checked against.

---

## 4. How it was checked

**Kernel and axiom audit.** `tools/check_lean.py` builds every mapped module, then runs `Supplemental.auditProject`
inside Lean: each declaration of the library is checked against the registered axiom list, and each row's
statement is hashed together with its semantic dependencies. Its receipts are `work/checks/stage-1.json` and
`work/checks/stage-development.json`; they bind the hashes of all 716 Lean files, the 191 review records and the
frozen source files.

**Independent review of every row.** Before a row was accepted, reviewers who had not written it and did not see
its proof compared the Lean statement with the printed source: three lenses (literal, definitions, strength) plus
two adversarial refuters; acceptance required three "faithful" verdicts and no refutation. Every fidelity risk
was recorded before the row was stated; every strengthening or weakening the reviewers noted is in the record.
The records are `work/reviews/<row>.json`, with the hashes of everything the reviewers read. **All reviewers were
AI sessions** (Claude, the same model family as the prover), disclosed in each record; no human has read them.

**Reproducing the check.** On a machine with 8 cores and 32 GB of RAM:

```sh
cd CORNER_LAWS_FOCUSED_20260912
bash setup.sh                                   # installs elan + the toolchain, fetches the Mathlib cache, builds, runs the checker
python3 tools/check_lean.py work/lean --all     # expected: "all_required_stages_passed": true; 191 mapped, 49207 audited
python3 verify_bundle.py                        # expected: FOCUSED BUNDLE VERIFIED: 191 files
```

Without Lean, the static audit (about a minute) confirms that the sources on disk are the ones the receipts were
issued for:

```sh
python3 tools_extra/static_audit.py CORNER_LAWS_FOCUSED_20260912
```

```
lean files: 712 | lines: 366040
code-level sorry/admit/native_decide: 0
axiom declarations: ng_finite_word, lit_homfly, lp_lm, lp_lm_uniqueness, lit_homfly_descent, src_contact
final receipt: passed=True mapped=192 audited=49212 | files hashed 716, mismatching 0, unhashed .lean 0
declaration map: {'accepted': 192}
accepted statement hashes vs shipped audit: 192/192 match
fixed-name declarations absent: 0
verify_bundle.py: PASS
RESULT: PASS (0 warnings)
```

---

## 5. Layout

The package `CORNER_LAWS_FOCUSED_20260912/` is self-contained: the frozen source extracts, the Lean library, the
checker, every review record and receipt.

```
work/lean/
  SM/            the paper's objects and results, roughly in the paper's order:
                   Polygon, Chirotope, Generic (the generic locus), Crossings, CyclicChambers (chambers),
                   WallGerm, NamedWallsDefinition (walls), DeletionHalvesDefinition, TreeCoefficient (tree amplitude),
                   LinkDiagram, LinkMoves, LinkInterfaces (diagrams, Reidemeister moves, the HOMFLY interface),
                   GaussRecordDefinition, PositiveLiftDefinition, Carrier*, CornerStateSum (def:C),
                   HypR (Hypothesis R), CChamber, CSilent, CS3, CS5, CS7, CSoft (the laws),
                   ComparisonRows (thm:comparison, cor:C-inherits), CornerLawsAndSoft (the final theorem)
  CV/            the companion document's polygons, events, carriers and records, used to prove Hypothesis R
  RProof/        the R obligations and the CV form of the R theorem (RProof.cv_R)
  Bridge/        the bridge lemmas B1–B4 between the CV and SM conventions, and Bridge.sm_R
  Supplemental/  Audit.lean, the axiom-audit program the checker runs
  lean-declarations.json   the map: one entry per row (status, Lean name, module, review record, statement hash)
  axiom-policy.json        the registered axioms and the fixed names of the eight targets
work/reviews/    one review record per row, with the reviewer inputs
work/checks/     checker receipts and logs
work/drafts/     provenance of every module: plans, frozen statements, prover units, assembly reports
work/AUTHOR_NOTES.md, FINAL_REVIEW.md   the decision log and the completed fidelity review (honest gap list in §5)
blueprint/, reference/, provenance/     frozen: the selected source statements, the axiom registry, the dependency
                                        graph, the TeX extracts of frame SM15 and the pins that tie them to the manuscript
tools/           claims.py (the worklist), check_lean.py (the checker), progress.py
SOURCES/         the literature behind the five interfaces (third-party PDFs: keep this repository private)
```

Outside the package: `docs/` (the statement-closure listing, the dependency graph and its generators),
`handover/` (execution notes), `tools_extra/static_audit.py`, `RESEARCH_LOG.md`.

The package is byte-identical to the delivered archive `RESULT_FINAL_20260919_1554Z.tgz`
(sha256 `40c1be0b6f709aa80d2b79026d3c10764a21a9bb132009eac63bab0a06b4baae`) except for two repo-only edits: its
`.gitignore` line `work/` is removed (it would keep the whole library out of git) and the root `MANIFEST.sha256`
line for `.gitignore` is refreshed accordingly.

---

## 6. Caveats that matter

1. **Five admitted results.** Section 2. In particular the descent sentence of lit:homfly is an axiom of its
   own, on which 21 rows including the final theorem depend.
2. **All reviews are AI reviews.** The fidelity of each Lean statement to the printed text was judged by AI
   reviewers under the protocol of section 4; no human has read any of the 192 records.
3. **Some library structures carry literal fields that are false or unrealisable as stated** (in
   `RProof/RALedgers.lean`: `est_PortData.port`, `.rot`, `.alt₁`, `.alt₂`, `esc_MoveData.rii_after_smoothing`; in
   `SM/CornerChainUnits.lean`: `s7b_SlidingTransport.ret`; in `RProof/GenericTransport.lean`: `G11_Config.trans`).
   No accepted proof uses them: the rows that needed them were closed through proved weaker forms or a trans-free
   copy, and the accepted modules were left unedited by policy. `FINAL_REVIEW.md` §5 item 4 lists each case.
4. **The full Lean rebuild has been run only on the machine that produced the package.** Elsewhere the
   verification so far is static: the sources match the receipts' hashes file by file, the review records match
   the receipt, and every row's statement hash matches the shipped audit (section 4).

---

## 7. Provenance

The formalization was produced between 2026-09-13 and 2026-09-19 by an autonomous Claude Code agent working one
printed statement at a time, with the review protocol of section 4, and completed on 2026-09-19 at 15:55 UTC.
The complete record is in the package (`FINAL_REVIEW.md`, `work/AUTHOR_NOTES.md`, `work/STATUS.md`) and, on the
owner's side, in [`RESEARCH_LOG.md`](RESEARCH_LOG.md) and `handover/`.

Dependency structure of the 192 rows, prerequisites on the left, wired by the 443 blueprint edges
([interactive version](docs/corner_laws_proof_graph.html); regenerate both with `docs/graph/build_dag.py` and
`docs/graph/render_svg.py`):

![Dependency graph of the 192 rows](docs/proof-graph-full.svg)
