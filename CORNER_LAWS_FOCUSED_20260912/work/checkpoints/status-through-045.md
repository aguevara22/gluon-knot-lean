# Execution checkpoint — 2026-09-10

Accepted ORIGINAL source proofs: 13/132 (9.85%).
Accepted ORIGINAL checklist: 27/191 (14.14%): thirteen proofs and fourteen definitions.
Additional accepted support: lem:weak-open, absent from the frozen focused DAG.
Expanded checklist: 28/192 (14.58%; standard reporter rounds to 14.6%).
Main targets: 0/8. The state-sum wall laws, soft theorem and unconditional R
remain incomplete. The goal remains active. Helpers never add original proofs.

Original accepted proofs:
lem:chi-basic, lem:children, lem:crossing-test, lem:cusp-sides, lem:fibres,
lem:flat-sides, lem:g1, lem:rot, lem:triple-sides, lem:uniformrot,
lem:wall-segment-stability, lem:wall-sides, prop:chambers.
Accepted definitions:
def:admissible, def:chamber, def:chirotope, def:crossings, def:deletion-halves,
def:gauss, def:generic, def:germ, def:interlace, def:polygon, def:regular,
def:shift, def:visible, def:weak.

## Latest full source acceptance: deletion/halves and children

Original def:deletion-halves is accepted as SM.deletion_halves_definition
in lean/SM/DeletionHalvesDefinition.lean, source sm-1-polygons.tex:1227–1240.
Original lem:children is accepted as SM.children in lean/SM/Children.lean,
source sm-1-polygons.tex:1242–1287. Both rows passed independent full review.

The actual deletion omits exactly the marked vertex and retains induced cyclic
order, every ordinary edge and the fused closing edge. For contact distance
d=(a-M).val, the actual half sizes are d+1 and n-d. The four source excluded
labels imply both sizes are in [3,n-2], including the minimal n=5 parent.
Their actual coordinate maps retain the printed vertex order and directed
closing/opening cuts. All ranges, label injectivity, successor identities,
closed segment inclusions and strict interior inclusions are proved.

The first half excludes a+1 and the second excludes a, so neither contains
the parent's only zero point triple. Actual inherited determinants give G1.
Cut parameters r*t and r+(1-r)*t lie in the parent edge interior for 0<r,t<1.
Injective parent-edge maps then lift every alleged child triple concurrence
to the actual parent G2 contradiction. Both halves are Generic. The full
children aggregate retains both size bounds and same-parent Regular.

The flat deletion/chamber branch reuses its accepted geometric proof: the
whole sufficiently small deletion curve, including zero, is Generic and lies
in the central genuine labelled and quotient connected-component chambers.
Parent cyclic relabelling preserves the actual marked children; the halves'
HEq only transports their proved equal sizes before coordinatewise equality.
No assumed child embedding, extra regular-path premise or new axiom is used.

Definition review: reviews/def-deletion-halves.json; exact 53-file source/body closure.
SHA256: b97f5c7bee5b68b84a1bd4dca5cff7a6b3c3ce99ad665e899ceb9d574861b4d0.
Main semantic hash (58 entries):
932349e3386701e37af93fd5aa18a31ecd60fd08916c2583f38066f3026fa0ae.
Children review: reviews/lem-children.json; exact 63-file source/body closure.
SHA256: 8ca72825e3e0bf6f44df9a134c13aea4a1de38b136f60cf14ab06e100c7d0841.
Main semantic hash (66 entries):
69f94f71788e7139d4b6a464ee04ac2f940861482e961af825fb841156e6824e.
Both signed by review_chirotope-independent-20260910, not the Lean author.

## Current verification: checkpoint045

Candidate044 and final045 passed. Current inventory: 213 SM modules,
2090 local declarations, 28 mapped claims, 219 project files, 38 frozen files.
All exact project/frozen inventories and hashes match. All 28 accepted reviews
and complete supporting-file bindings are current. All 203 pre-children SM files
are unchanged; all 213 candidate SM files are unchanged in final045. Only
propext, Classical.choice, Quot.sound occur; no literature input. Full-stage acceptance remains false.

Receipt: checks/checkpoint-045-output.json.
SHA256: 48af0260937e22bad3628a38418cfefe3382198853a73a5d28bfb7d6f2310e21.
Verification: checks/checkpoint-045-verification.json.
Actual type/definition/axiom trace: checks/children-types.log.
Trace SHA256: b707681914fb8ded6af61db5d6cd8f11e61815d763723d7d2c6216ef2f492df4.
Original handles: audit044 session41344, trace54339, audit045 session65314;
all terminal exit0. No ordinary build or audit remains live.
Previous cumulative statuses are archived in checkpoints/status-through-038.md,
status-through-041.md and status-through-043.md. Full cusp and wall-sides reviews
remain current; their proof bodies and supporting closures are unchanged.

## Next actual work

Execute decisions/named-wall-definition-after-children.md for full def:walls,
source sm-1-polygons.tex:710–750. Existing F/V/T/E/C and K predicates are reviewed
as dependencies, but the whole definition remains pending/unmapped. Prove the
six kinds' exclusivity, centre-determination among simple germs, F right/left
and V contact-sign conventions, K newborn/loop/empty well-definedness, and
cyclic compatibility. Reuse completed geometry and full Gauss-cycle transport;
no literature interface is needed. Do not redo any completed cusp or children
plan. After this gap, the much larger transport-polynomial/relative-general-
position chain still remains, as do all main state-sum targets and R.

Original lem:shift remains locally unaccepted: its unrestricted left-count
reversal is false at zero turns. The reviewed regular quadrilateral gives
counts 3 and 0, whereas n-left is 1. The separate reviewed repair has an explicit
nonzero-turn premise, proved for Generic consumers. Its evidence is unchanged
in repairs/index.json, now bound to045. It does not block independent work.

## Runtime and reporting

Lake: /Users/aguevaragonzalez/.elan/bin/lake.
Lean: leanprover/lean4:v4.34.0-rc2.
Mathlib: 85e3a25e006c35636f0e53b0e9296caca2685bc0.
.lake/packages uses /tmp/lean-handoff-mathlib-smoke/lean/.lake/packages with
those exact pins. Eventual delivery must not depend on this temporary cache.

python3 work/claim_progress.py reports ORIGINAL proofs; python3 tools/progress.py
--once reports the separate EXPANDED checklist. Latest checkpoint and hourly report at 23:00 UTC:
9.85% original, 14.6% expanded. User-requested hourly reporting overrides the
handoff's ten-minute default. Automation hourly-lean-formalization-progress is
active. Keep one watcher: session 42482 confirmed live at 23:00:58 UTC. Its hourly
report at 23:00:09 UTC was relayed with original counts; next report is 00:00 UTC. Poll the actual handle
before any replacement. A timeout is not terminal; never restart solely for it.

## Sources and autonomy

The sources addendum is sufficient to continue. Its verified intake covers
8 checks, 11 PDFs and 103 manifest entries; see reports/sources-addendum-review.md.
Optional full originals improve figure/page verification; existing extracts
suffice now. Reidemeister proof-depth review remains open, with Queffelec 2024
already supplied. The five-interface policy is unchanged and none is used.
No author question is needed. Keep source/reference/provenance/templates and
ZIPs unchanged; implement only in work/. Record nonblocking decisions locally.
