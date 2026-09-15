# State of the work at handover — 2026-09-12 (frame SM15)

Read this before touching work/. The numbers below were re-verified on the
origin machine on 2026-09-12 (VERIFICATION_ON_ORIGIN.md): the library builds,
the development checker passes, and every accepted row's statement hash matches
a fresh audit. Nothing here is a claim that the mathematics is finished.

| Measure | Value |
|---|---|
| Claims verified (kernel-checked and independently reviewed) | 20 / 132 (15.2%) |
| Checklist rows accepted | 40 / 192: 19 definitions, 20 claims, 1 extra supporting lemma |
| Final targets accepted | 0 / 8 |
| Lean modules in work/lean/SM | 328 (about 27,000 lines) |
| sorry in work/lean | 0 |
| Axioms used | propext, Classical.choice, Quot.sound; no literature interface declared yet |
| Declarations audited by the checker | 4,271 |
| Review files | 268, all written by AI reviewer sessions (section 4); the newest, lem:shift, by a Claude reviewer subagent during the cold-start test |
| Candidate lane, work/checks (shipped without the previous executor's checkpoint dumps and logs) | 481 Lean bodies, 2,714 kernel-checked theorems, none accepted yet; reuse them |
| Checkpoints of the previous executor | 105, 2026-09-10 to 2026-09-12 |

## 1. What is verified

Definitions (19):

| row | declaration | module | source |
|---|---|---|---|
| `def:polygon` | `SM.polygonData` | SM.Polygon | sm-1-polygons.tex:27 |
| `def:chirotope` | `SM.chirotopeData` | SM.Chirotope | sm-1-polygons.tex:63 |
| `def:generic` | `SM.Generic` | SM.Generic | sm-1-polygons.tex:100 |
| `def:crossings` | `SM.crossingData` | SM.CrossingEquiv | sm-1-polygons.tex:138 |
| `def:chamber` | `SM.chamber_definition` | SM.CyclicChambers | sm-1-polygons.tex:206 |
| `def:gauss` | `SM.gauss_definition` | SM.GaussDefinition | sm-1-polygons.tex:249 |
| `def:interlace` | `SM.interlacement_definition` | SM.InterlaceDefinition | sm-1-polygons.tex:259 |
| `def:visible` | `SM.visible_signature_definition` | SM.VisibleDefinition | sm-1-polygons.tex:270 |
| `def:weak` | `SM.weak_definition` | SM.WeakGeneric | sm-1-polygons.tex:279 |
| `def:regular` | `SM.regular_definition` | SM.RegularDefinition | sm-1-polygons.tex:386 |
| `def:shift` | `SM.reversal_definition` | SM.Reversal | sm-1-polygons.tex:398 |
| `def:admissible` | `SM.admissible_definition` | SM.Admissible | sm-1-polygons.tex:539 |
| `def:germ` | `SM.wall_germ_definition` | SM.GermDefinition | sm-1-polygons.tex:680 |
| `def:walls` | `SM.named_walls_definition` | SM.NamedWallsDefinition | sm-1-polygons.tex:737 |
| `def:deletion-halves` | `SM.deletion_halves_definition` | SM.DeletionHalvesDefinition | sm-1-polygons.tex:1254 |
| `def:root` | `SM.rootData` | SM.RootBoundary | sm-2-amplitude.tex:10 |
| `def:gates` | `SM.gatesData` | SM.Gates | sm-2-amplitude.tex:29 |
| `def:treesum` | `SM.treesumData` | SM.TreeCoefficient | sm-2-amplitude.tex:66 |
| `def:nearfar` | `SM.nearfarData` | SM.NearFar | sm-2-amplitude.tex:137 |

Claims (20; `lem:shift` was proved as printed on SM15 during the cold-start test of 2026-09-12, module SM.ShiftTheorem, declaration `SM.shift_reversal`):

| row | declaration | module | source |
|---|---|---|---|
| `lem:chi-basic` | `SM.chi_basic` | SM.Chirotope | sm-1-polygons.tex:72 |
| `lem:g1` | `SM.g1` | SM.G1Consequences | sm-1-polygons.tex:110 |
| `lem:crossing-test` | `SM.crossing_test` | SM.Crossings | sm-1-polygons.tex:148 |
| `lem:wall-segment-stability` | `SM.wall_segment_stability` | SM.WallSegmentStability | sm-1-polygons.tex:178 |
| `prop:chambers` | `SM.chambers` | SM.ChamberPaths | sm-1-polygons.tex:213 |
| `lem:rot` | `SM.rotation_number` | SM.RotationTheorem | sm-1-polygons.tex:407 |
| `lem:uniformrot` | `SM.uniform_rotation` | SM.UniformRotation | sm-1-polygons.tex:440 |
| `lem:fibres` | `SM.nonempty_fibres` | SM.Fibres | sm-1-polygons.tex:547 |
| `lem:triple-sides` | `SM.triple_sides` | SM.TripleSides | sm-1-polygons.tex:697 |
| `lem:flat-sides` | `SM.flat_sides` | SM.FlatSides | sm-1-polygons.tex:778 |
| `lem:wall-sides` | `SM.wall_sides` | SM.WallSides | sm-1-polygons.tex:923 |
| `lem:cusp-sides` | `SM.cusp_sides_of_continuous_curve` | SM.CuspCurve | sm-1-polygons.tex:1051 |
| `lem:children` | `SM.children` | SM.Children | sm-1-polygons.tex:1269 |
| `lem:transport-polynomials` | `SM.transport_polynomials` | SM.TransportPolynomials | sm-1-polygons.tex:1319 |
| `thm:relgp` | `SM.relative_general_position` | SM.RelativeGeneralPosition | sm-1-polygons.tex:1412 |
| `lem:gates-nonzero` | `SM.gates_nonzero` | SM.Gates | sm-2-amplitude.tex:46 |
| `lem:treesum-trees` | `SM.treesum_trees` | SM.PlaneTreeFormal | sm-2-amplitude.tex:84 |
| `prop:A-chamber` | `SM.A_chamber` | SM.TreeChamber | sm-2-amplitude.tex:121 |
| `lem:farout` | `SM.farout` | SM.Farout | sm-2-amplitude.tex:151 |

Extra supporting lemma, tracked but outside the 132: `lem:weak-open`
(`SM.weak_open`, SM.WeakOpen).

The accepted rows cover the polygon, chirotope, generic locus, crossings,
chambers as connected components with the cyclic quotient, Gauss words,
interlacement, visible and weakly generic loci, regular locus and rotation
number, admissible directions and fibres, wall germs, named walls and their
sides, deletion halves, children, transport polynomials, relative general
position, and the tree amplitude prerequisites (root, gates, tree sum, chamber
constancy, near/far data, far-out lemma).

## 2. What is pending

94 source claims plus all 19 R/bridge/final obligations, 33
definitions, 5 literature interfaces, 2 hypotheses to state (`hyp:R`, `CV:ax:R`).
Chapter 3 of the source (independent supports, carriers, decorated records,
positive lifts, corner coefficients, the state sum C itself) has no accepted
definition yet; the previous executor began the carrier construction only in
the candidate lane. The R assembly and the bridge B1 to B4 are not started.
The five literature interfaces are not declared; their sources are in SOURCES/
(LITERATURE.md lists what is on file). `python3 tools/claims.py
--pending-only` gives the ordered list. The dependency columns come from
explicit references only; read the source context around each statement for
unlabelled prerequisites before starting it.

## 3. The previous executor and its candidate lane

It kept a canonical library (work/lean, accepted rows only) and a candidate
lane (work/checks): each candidate is a `.body.lean` importing canonical
modules, a self-contained `.prototype.lean` that was kernel-checked with
`lake env lean`, a `-prototype-result.json` receipt and a `-kernel.log`.
Failed attempts are kept with `-failed` or `-first-draft` names. Ledgers per
checkpoint are in work/checkpoints/goal-turn-NNN-candidates.json; the
narrative is in work/reports and work/decisions; decisions on ambiguities are
in work/AUTHOR_NOTES.md.

In its last day it produced about 2,700 candidate theorems and accepted no new
claim. Do not repeat that pattern: prove one claim, review it, accept it, then
the next. Candidates worth reading before proving the corresponding claims:

- `thm:A-soft` (soft theorem of the tree amplitude): complete source candidate
  `SM.SoftDuplication.soft_amplitude_source` in
  work/checks/SoftAmplitudeSource.body.lean, receipt
  SoftAmplitudeSource-prototype-result.json, checkpoint 097; it rests on the
  SoftDuplication*, SoftGeometric* and SoftAmplitude* bodies.
- `lem:soft-generic`: candidate `SM.soft_family_generic_source` in
  work/checks/SoftFamilyAssembly.body.lean, checkpoint 091.
- The marked traversal, carrier cycles and true corners of the corner state sum:
  Carrier*.body.lean, checkpoints 098 to 105, unfinished.

To reuse a candidate, port its body into a module under work/lean, then
transcribe, prove, review and accept the claim as for any other row. Nothing in
the lane counts until then.

## 4. Reviews are AI reviews

Every review file was written by an AI session of the same model family as the
implementer; identities are recorded in each file. They satisfy the package's
independence rule (no authorship of the statement) and were disclosed as AI
reviews, but no human has read them. Before stage acceptance, re-review the 39
accepted rows with a separate reviewer session of your own and record the
countersignature in the review file. Keep the map statuses meanwhile. The three
rows whose wording changed in SM15 (`lem:chi-basic`, `lem:g1`, `prop:A-chamber`)
additionally carry a re-read by a different model family (Claude) in their
`source_realignment.re_review` field, with a countersign request.

## 5. Source frame

The previous run used frame SM12. The author re-issued the source as frame SM15
on 2026-09-12 after the previous executor found that `lem:shift` clause (iii)
was false off the generic locus; this package was realigned to SM15 in place.
See SM15_REALIGNMENT.md for what changed and what was refreshed. No task is
blocked: `lem:shift` has been proved exactly as printed and accepted.

## 6. Infrastructure notes

- Pins: Lean `leanprover/lean4:v4.34.0-rc2`, Mathlib commit
  `85e3a25e006c35636f0e53b0e9296caca2685bc0`, resolved lake-manifest.json in
  work/lean. `lake exe cache get` then `lake build`; 32 GB RAM or more.
- work/checkpoints and some files under work/checks mention the origin
  machine's paths and the previous executor's sandbox paths (`/root/...`).
  They are evidence, not instructions. The previous executor's per-checkpoint
  checker logs and audit dumps (work/checks/checkpoint-*, *.log, tagged
  *-declaration-audit.json; 4 GB) are not in the shipped copy; nothing reads
  them and the checker rewrites the current receipts on every run.
- work/claim_progress.py is the previous executor's claim counter; it needs the
  checker receipts under work/checks. tools/progress.py now reports the same
  figure (claims verified / 132) and is the one to use.
- DELIVERY_AUDIT.md and VALIDATION.md describe the 2026-09-10 infrastructure
  audit of the package, not the mathematics.
