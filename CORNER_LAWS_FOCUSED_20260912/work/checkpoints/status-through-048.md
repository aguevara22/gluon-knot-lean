# Execution checkpoint — 2026-09-10, audit048

Accepted ORIGINAL source proofs: 13/132 (9.85%).
Accepted ORIGINAL checklist: 28/191 (14.66%): thirteen proofs and fifteen definitions.
Additional accepted support: lem:weak-open, absent from the frozen focused DAG.
Expanded checklist: 29/192 (15.10%; standard reporter rounds to 15.1%).
Main targets: 0/8. The state-sum wall laws, soft theorem and unconditional R
remain incomplete. The goal remains active. Helpers never add original proofs.

Original accepted proofs:
lem:chi-basic, lem:children, lem:crossing-test, lem:cusp-sides, lem:fibres,
lem:flat-sides, lem:g1, lem:rot, lem:triple-sides, lem:uniformrot,
lem:wall-segment-stability, lem:wall-sides, prop:chambers.
Accepted definitions:
def:admissible, def:chamber, def:chirotope, def:crossings, def:deletion-halves,
def:gauss, def:generic, def:germ, def:interlace, def:polygon, def:regular,
def:shift, def:visible, def:walls, def:weak.

## New mathematical progress: actual area and direction polynomials

Four new modules are compiled, independently source/body reviewed and audited:
SM.DeterminantPolynomial, SM.PolynomialShear, SM.CoordinatePolynomials,
SM.DirectionPolynomials. They prove the actual Δ and auxiliary H are irreducible
and nonzero in the full real scalar-coordinate polynomial ring. Every extra
coordinate remains in that ring. Actual tuple/scalar assignments are mutually
inverse, and evaluation equals the printed geometric determinants. Coordinate
substitutions are proved algebra automorphisms with explicit inverse maps.
Remote-edge endpoint inequalities discharge the head/tail separation condition.
The source n≥3 discharges H's Nontrivial(ZMod n) instance, independently checked.
No pointwise nonvanishing is inferred from formal polynomial nonzeroness.

Independent partial review: reviews/transport-area-direction-partial.json.
Reviewer: review_chirotope-independent-20260910; implementation author:
root-implementation-20260910. Exact SM source/body import closure:8files.
Review SHA256:1d7a694418f01787171bd5b0b491c8082dda1e4732f309edd82140d0b42395df.
Independent type/axiom trace: checks/transport-area-direction-review-types.log,
session83654 terminal0; thirteen inspected declaration axiom sets contain only
propext,Classical.choice,Quot.sound. Trace SHA256:
ffdfe9202b97412bddec9a45ebaa534b8eaa978d5d3633afd3a478c55d1aacc9.
Successful module build sessions:1865,64893,49138,99378, all terminal0.
Initial determinant and direction elaboration failures were corrected before
those successful builds; the final logs are the ones bound by the review.

This is PARTIAL SOURCE WORK, not acceptance of lem:transport-polynomials.
T, family/nonassociation, coordinate-affinity, nonzero slopes/resultants, and
specialized-root clauses remain open. The separate Bool⊕Bool determinant
prototype is also reviewed (reviews/transport-determinant-core-prototype.json),
but the new actual-coordinate implementation supersedes it for Δ/H transport.

## Current whole verification: checkpoint048

Whole audit048 passed, session43424 terminal exit0. Exact current inventory:
230 SM modules,2407 local declarations,29 mapped claims,236 project files,
38 frozen files. All226 prior SM modules are byte-for-byte unchanged. The four
new modules are added; Supplemental.lean adds only their root import.
All29 accepted reviews and supporting-file bindings are current. No literature
interface is used. Development success is not complete-stage acceptance.

Receipt: checks/checkpoint-048-output.json.
SHA256:35530b5abc6934f5ffd1e7f3077816b243eba168451e4cdbe982fa25724b14eb.
Declaration audit SHA256:
56ce57278aa35a3ee7ba181f97984f4c1916b36b9623f8ac435c0f823757b13a.
Verification: checks/checkpoint-048-verification.json,
checks/checkpoint-048-area-direction-files.json, and
checks/checkpoint-048-partial-review-verification.json. Reproduce with
python3 work/checks/verify_area_direction.py. The separate named-walls verifier
also passed on048 and checked all existing accepted reviews. Its older213-file
comparison is strengthened by the new226-file comparison. No build/audit is live.

The latest accepted original source row remains def:walls, implemented as
SM.named_walls_definition with exact92-file closure and134 semantic entries.
Its unchanged review SHA256:
1c337dbfccd7961c2360b02e97433d4ec2b4909ed50bf6dd9b8489836f00c0e0.
Detailed named-wall, children, deletion-halves, cusp and earlier source
acceptances are preserved in checkpoints/status-through-047.md and its archives.

## Next executable work

Continue decisions/transport-after-area-direction.md. First define the actual
multivariate line rows and T, prove evaluation to SM.LineConcurrence's actual
concurrenceDet, prove three-edge head/tail separation and the exact polynomial
expansion under the existing shear. Then prove T irreducibility. The new plan
records an explicitly UNPROVED candidate using primitive linear irreducibility
twice and degree comparisons; inspect and discharge every premise.
Preserve all230 audited/reviewed SM files; implement further steps in new modules.

The complete original lemma at sm-1-polygons.tex:1292–1383 still requires every
clause in decisions/transport-polynomials-after-walls.md. Only full independent
source review may accept it. Then execute the full thm:relgp, followed by the
remaining polynomial/carrier, transport/comparison and state-sum chains.

The original unrestricted lem:shift remains locally unaccepted: its left-count
reversal is false at a zero turn. The reviewed exact quadrilateral counterexample
and explicit nonzero-turn repair remain unchanged; repairs/index.json binds048.
This local issue does not block the current polynomial chain or independent work.

## Runtime, reporting and sources

Lake:/Users/aguevaragonzalez/.elan/bin/lake.
Lean:leanprover/lean4:v4.34.0-rc2.
Mathlib:85e3a25e006c35636f0e53b0e9296caca2685bc0.
.lake/packages uses the disclosed /tmp/lean-handoff-mathlib-smoke/lean/.lake/packages
cache with these pins. Eventual delivery must not depend on the temporary cache.

python3 work/claim_progress.py reports ORIGINAL proofs; python3 tools/progress.py
--once reports the separate EXPANDED checklist. User-requested hourly reporting
supersedes the ten-minute handoff default. Hourly automation remains active.
One watcher only: session42482 reported at00:00:09UTC on2026-09-11 and remains live;
next report01:00UTC. Original-claim report at00:01:15UTC remains13/132(9.85%).
Poll its actual handle before replacement; an observation timeout is not terminal.

Sources addendum reverified this turn:8checks,11PDF hashes,103manifest entries,
all pass. Intake:reports/sources-addendum-review.md. Existing extracts suffice
to continue; optional originals are LM1987, Lickorish1997pp168–172 and Geiges2008
pp108–132 for page/figure verification. Reidemeister proof-depth review remains
open, with Queffelec2024 supplied. No author question is needed. Keep frozen
reference/provenance/blueprint, original SM/R/BRIDGE, templates and ZIPs unchanged.
