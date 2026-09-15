# Execution checkpoint — 2026-09-10

Accepted ORIGINAL source proofs: 11/132 (8.33%).
Accepted ORIGINAL checklist: 24/191 (12.57%): eleven proofs and thirteen definitions.
Additional accepted support: lem:weak-open, absent from the frozen focused DAG.
Expanded checklist: 25/192 (13.02%; standard reporter rounds to 13.0%).
Main targets: 0/8. The state-sum wall laws, soft theorem and unconditional R
certificate remain incomplete. The goal remains active.

Original accepted proofs:
lem:chi-basic, lem:crossing-test, lem:fibres, lem:flat-sides, lem:g1, lem:rot,
lem:triple-sides, lem:uniformrot, lem:wall-segment-stability, lem:wall-sides,
prop:chambers.
Accepted definitions:
def:admissible, def:chamber, def:chirotope, def:crossings, def:gauss, def:generic,
def:germ, def:interlace, def:polygon, def:regular, def:shift, def:visible, def:weak.
Helpers never add to the fixed 132-proof denominator.

## Latest accepted source result

Full original lem:wall-sides is independently accepted as SM.wall_sides in
lean/SM/WallSides.lean, source reference/SM/sm-1-polygons.tex:896–1020.
Every F/V/T/E/C branch is covered for the same arbitrary actual wall germ.
Each branch supplies one common positive radius for its local conclusions.
This is the geometric named-wall sides lemma, not a state-sum polynomial law.

- F/E/C: actual crossing sets, complete sorted visits, genuine cyclic Gauss
  words and every same-edge parameter comparison persist, including at zero.
  The nongeneric centres use proved actual segment geometry.
- V: exact two-pair symmetric difference, both/neither or one/exchanged patterns,
  complete persistence elsewhere, and a finite common contact neighbourhood.
  IsInteriorCrossing at the centre is proved equivalent to raw IsCrossing
  excluding the two endpoint-contact supports. The actual nearby visits in the
  windows are exactly the affected visits. The full persistent-visit equivalence
  preserves supports, edges and every same-edge actual parameter comparison.
- T: a tie of distinct partners occurs exactly at the actual concurrence
  support. All other orders persist; all six permutations of the three source
  sign changes give exactly the selected reversals. The classification covers
  every actual visit pair. The selected visits are adjacent in the complete
  actual Gauss list on the common punctured interval. No central Generic word
  or central G2 is asserted.

Side comparisons permit independently chosen positive and negative parameters
on the actual connected Generic sides. No derivative or supplied crossing/word
correspondence is a premise. All previously accepted proof files are unchanged.
The 14 new modules complete the geometry left partial at checkpoint038.

## Latest development checkpoint041

Nine new cusp modules compile and are imported through SM.CuspLocal. They prove
both exclusive central cases; the correct cyclic indices including n=4; actual
nonzero Delta; the negative-real central rotor and all other regular corners;
both endpoint-distance formulas -T/Delta; continuity and both finite-segment
bounds; the exact newborn crossing/turn-sign iff; both needle-turn patterns;
actual unused-pair disjointness; and exhaustive preservation of every other
unordered crossing support. No thread-order claim is made.

SM.WallGerm.cusp_local_geometry combines the results on one common positive
radius. Delta is controlled including at zero. Crossing and needle conclusions
use punctured Generic, and other-support comparisons allow independently chosen
small nonzero parameters of either sign. No central G1 or Regular premise is
inserted. All nine modules passed preliminary independent source/type/body
review. Full original lem:cusp-sides is still pending and unmapped.

Audit041 passed: 185 SM modules, 1805 local declarations, 25 mapped claims,
191 project files and 38 frozen files. Every one of the 176 prior SM modules
is unchanged. Exact project inventory, all project/frozen hashes and all 25
accepted review/support bindings are current. Only propext, Classical.choice
and Quot.sound occur; no literature interface or new project axiom is used.
Full-stage acceptance remains false.

Receipt: checks/checkpoint-041-output.json.
SHA256: c945ac2921c6457c6c05c15355af2ef45cb1b120e147be318d9a5e61fa59fc41.
Verification: checks/checkpoint-041-verification.json.
Type/definition/axiom trace: checks/cusp-local-types.log, SHA256
6593ef483262a99119a7bc0c25b2768a54ab9b4d3e6b41f2ae1bcd77c81df3d0.
Original handles: audit79204 and trace56701 both terminal exit0.
Partial review: reviews/lem-cusp-sides-partial-checkpoint041.json.
SHA256: 739a695123698560ab186f95599e279db218147794a600644f9feebe6779c90c.
The reviewer independently verified all 47 supporting source/body files.
No Lean/map edits or original claim acceptance are part of this partial review.

Full named-wall acceptance remains bound to reviews/lem-wall-sides.json,
SHA256 2dfb995b053b40092a740b00127e33524ab0b15b15a9bc1e5bd820ede26958ff;
its complete 107-file supporting closure is unchanged. Audit040 and its
verification remain historical evidence for that acceptance. The old cumulative
status is archived at checkpoints/status-through-038.md.

## Next work and local source obstruction

Continue full lem:cusp-sides, source sm-1-polygons.tex:1024–1225; execute
decisions/cusp-sides-next.md and decisions/cusp-after-local041.md.
The next executable step is to derive the unique loop side from actual turn
SignChanges and generic-side constancy, so independent side parameters have
the stated opposite signs and exactly one newborn crossing. Then prove the
actual short traversal arc, its partner-in-complement property, the cyclic
adjacency/empty implication, and the signed principal-angle rotation jump.
None of these remaining clauses is assumed by the compiled local geometry.

Do not redo decisions/named-wall-sides-next.md or named-wall-localization-next.md:
both plans are completed. Full def:walls stays pending/unmapped until K,
newborn/loop/empty and other side conventions, mutual exclusivity, centre
classification and cyclic transport are proved. Its F/V/T/E/C predicates have
been reviewed as dependencies of the accepted lemma, not as the full definition.

Original lem:shift remains pending because its printed unrestricted reversal
count is false with zero turns. A kernel-checked regular quadrilateral has
left count 3 and reversed left count 0, whereas n-left is 1. The proposed
SM.shift_reversal_corrected explicitly requires nonzero turns for that formula;
its Generic corollary discharges the condition. Use only the reviewed repair
with its actual premises. This local source error does not stop other work.

## Run and report

Run python3 work/claim_progress.py for evidence-backed ORIGINAL proof percentage.
Run python3 tools/progress.py --once for the EXPANDED checklist. These are
separate metrics; neither measures elapsed work or certifies a full stage.
Refresh both at checkpoints. Latest files are progress/claims-latest.json and
progress/latest.json. A changed proof requires a new audit and current review.

Use /Users/aguevaragonzalez/.elan/bin/lake from work/lean.
Lean: leanprover/lean4:v4.34.0-rc2.
Mathlib: 85e3a25e006c35636f0e53b0e9296caca2685bc0.
The .lake/packages link points to the exact cache at
/tmp/lean-handoff-mathlib-smoke/lean/.lake/packages. If it disappears, restore
those exact pinned dependencies; eventual delivery must not rely on this cache.

Hourly automation hourly-lean-formalization-progress is active. User-requested
hourly reporting overrides the handoff ten-minute default. Keep the single file
watcher session42482 (confirmed live at 21:51:21 UTC). Last hourly report 21:00:09 UTC
was relayed with ORIGINAL counts. Next hourly report: 22:00 UTC. Poll its actual
handle before starting any replacement; a timeout is not terminal.

## Source availability

The sibling LEAN_HANDOFF_20260909_SOURCES_ADDENDUM passed 8 checks: 11 PDF hashes
and 103 manifest entries. See reports/sources-addendum-review.md. Existing
extracts suffice to continue; full Lickorish–Millett 1987, Lickorish 1997
pp.168–172 and Geiges 2008 pp.108–132 originals would improve page/figure checks.
Reidemeister proof-depth review is still open; Queffelec 2024 is already supplied.
The five-interface axiom policy is unchanged and none is used so far.
No author answer is required; record nonblocking decisions in AUTHOR_NOTES.md.
