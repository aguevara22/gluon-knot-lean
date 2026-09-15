#!/usr/bin/env python3
"""Produce FrontRows_W2_Clean.lean from Skeleton_W2.lean by deleting the five open leaves and everything
that depends on them (line ranges are Skeleton_W2.lean, 1-based, inclusive).  Rerunnable."""
import sys
SRC = "/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/drafts/frontrows/Skeleton_W2.lean"
DST = "/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/drafts/frontrows/FrontRows_W2_Clean.lean"

# (start, end, label) -- each range includes the docstring and the trailing blank line
DELETE = [
    (57, 73,   "structure NgCommutationClauses"),
    (74, 76,   "structure NgFrontIClauses"),
    (77, 84,   "structure NgFrontIIClauses"),
    (85, 92,   "structure NgFrontIIIClauses"),
    (93, 102,  "structure NgDeletionsClauses"),
    (119, 122, "structure NgLocalFrontBoundClauses"),
    (11085, 11092, "L-geo section docstring (replaced by a note)"),
    (11093, 11102, "theorem typeIII_site (open leaf)"),
    (11103, 11112, "theorem typeII_move (open leaf)"),
    (11113, 11120, "theorem typeI_move (open leaf)"),
    (11121, 11129, "theorem crossedCusp_move (open leaf)"),
    (14568, 14574, "theorem represent (open leaf)"),
    (14619, 14643, "theorems P_typeIII, P_typeII, P_typeI, P_crossedCusp"),
    (14741, 14804, "theorems ng_commutation, ng_front_I, ng_front_II, ng_front_III, ng_deletions"),
    (14842, 14877, "namespace FrontRows block: certificate_laws, word_bound"),
    (14878, 14890, "theorem ng_local_front_bound"),
]
HEADER_RANGE = (15, 40)   # the old module docstring, replaced

NEW_HEADER = '''/-! # Front certificate rows — wave-2 clean subset: rows 81 ng:circle and 82 ng:cusp-skein

Wave-2 clean subset of the front certificate rows lane: rows 81 ng:circle and 82 ng:cusp-skein and the shared
infrastructure.  Derived from `work/drafts/frontrows/Skeleton_W2.lean` (the wave-2 merge, MERGE2_REPORT.md) by
removing the five open leaves of that skeleton and everything that depends on them; the exact list of removed
declarations (names and Skeleton_W2 line ranges) is `work/drafts/frontrows/W2_CLEAN_REPORT.md`.  Every declaration
in this module is fully proved: `#print axioms SM.ng_circle`, `SM.ng_cusp_skein`, `SM.ng_cusp_skein_both` give
`[propext, Classical.choice, Quot.sound, SM.lp_lm]` (`lp_lm` is the accepted literature interface reached through `P`).

Contents:
* **Statements**: `SmoothFront.NonsingularDeformation`, `NgCircleClauses` (row 81), `NgCuspSkeinClauses` (row 82),
  and the nonemptiness helpers in `SM.FrontWord`.
* **Leaves** (section `FrontRows.Leaves`), all proved:
  L-deg (U1): Laurent-degree arithmetic on `R` — `delta_ne_zero`, `degAZ_delta`, `degAZ_le_of_eq_pos/neg`;
  L-cnt (U1): the count changes of every pattern on the realization — `comm_counts`, `typeI_counts`,
  `typeII_counts`, `typeIII_counts`, `zigzag_counts`, `crossedCusp_counts`, `circleDeletion_counts`, `skein_counts`;
  L-rec (U3 on the record core U2): `comm_recordIso`, `zigzag_recordIso`, `circle_recordIso_addFree`,
  `skein_site`, `skein_unique`;
  the geometry core U4 (`SM.FrontRows.U4`: polygons, segments, the moved slot diagram, `MatchData`, arcs, exits,
  congruences) — infrastructure for the disc-local moves of rows 77-80, none of which is in this module;
  L-PL (U7): `PLFront.IsStandardCircles.downCount_eq_c_general`;
  L-smooth (U8D): `deform_downCount`, `deform_writhe`, `deform_P`; and the U8R infrastructure
  (`SM.FrontRows.U8R`: cyclic successor, `frontRecord`, `markingRecordIso`, the reductions `represent_of_*`, the
  x-velocity and cusp-arc analysis) towards the representation theorem of row 76, which is not in this module.
* **Glue**: `degAZ_delta_pow`, `switch_of_recursion_pos/neg`, `P_comm`, `P_zigzag`, `P_circleDeletion`,
  `PLFront.IsStandardCircles.defect_eq_zero`, `base_defect_nonneg`, `skein_ineq_forward/backward`.
* **Rows**: `SM.ng_circle` (row 81), `SM.ng_cusp_skein` (row 82), `SM.ng_cusp_skein_both`.

Not in this module (a later delta module imports this one and re-declares exactly these, once the remaining
leaves are proved): the row statements `NgCommutationClauses`, `NgFrontIClauses`, `NgFrontIIClauses`,
`NgFrontIIIClauses`, `NgDeletionsClauses`, `NgLocalFrontBoundClauses`; the leaves `typeIII_site`, `typeII_move`,
`typeI_move`, `crossedCusp_move`, `represent`; their consumers `P_typeIII`, `P_typeII`, `P_typeI`, `P_crossedCusp`;
the rows `ng_commutation`, `ng_front_I`, `ng_front_II`, `ng_front_III`, `ng_deletions`, `certificate_laws`,
`word_bound`, `ng_local_front_bound`.

Checked with `cd work/lean && lake env lean`. -/'''

LGEO_NOTE = '''/-! ### L-geo (units U5, U6 on the geometry core U4) — not in this module.  The four disc-local move leaves
(`typeIII_site`, `typeII_move`, `typeI_move`, `crossedCusp_move`) and their polynomial consumers are re-declared by
the delta module (W2_CLEAN_REPORT.md); the U4 geometry core above is the infrastructure they consume. -/
'''

lines = open(SRC, encoding="utf-8").read().split("\n")
assert len(lines) == 14892 and lines[-1] == "", len(lines)   # 14891 lines + trailing newline
n = 14891

# sanity: check the first line of each deleted range starts as expected
expect = {
    57: "structure NgCommutationClauses", 74: "structure NgFrontIClauses", 77: "structure NgFrontIIClauses",
    85: "structure NgFrontIIIClauses", 93: "structure NgDeletionsClauses", 119: "structure NgLocalFrontBoundClauses",
    11085: "/-! ### L-geo", 11093: "/-- LEAF (ng:front-III", 11103: "/-- LEAF (ng:front-II", 11113: "/-- LEAF (ng:front-I",
    11121: "/-- LEAF (ng:deletions", 14568: "/-- LEAF = THE REPRESENTATION", 14619: "/-- ng:front-III:",
    14741: "/-- **ng:commutation**", 14842: "namespace FrontRows", 14878: "/-- **ng:local-front-bound**",
    15: "/-! # Front certificate rows 76-83",
}
for ln, pref in expect.items():
    assert lines[ln-1].startswith(pref), (ln, lines[ln-1][:60])
# the line after each range should be what we expect (blank or the next block)
after = {73: "structure NgFrontIClauses", 76: "structure NgFrontIIClauses", 84: "structure NgFrontIIIClauses",
         92: "structure NgDeletionsClauses", 102: "structure NgCircleClauses", 122: "/-! ### Nonemptiness",
         11092: "/-- LEAF (ng:front-III", 11102: "/-- LEAF (ng:front-II", 11112: "/-- LEAF (ng:front-I",
         11120: "/-- LEAF (ng:deletions", 11129: "/-! ### L-PL", 14574: "end Leaves", 14643: "/-! ### The base",
         14804: "/-- **ng:circle**", 14877: "/-- **ng:local-front-bound**", 14890: "end SM", 40: ""}
for ln, pref in after.items():
    assert lines[ln].startswith(pref), (ln+1, lines[ln][:60])
assert lines[HEADER_RANGE[1]-1].endswith("-/"), lines[HEADER_RANGE[1]-1]

drop = set()
for a, b, _ in DELETE:
    drop.update(range(a, b+1))
out = []
for i in range(1, n+1):
    if i == HEADER_RANGE[0]:
        out.append(NEW_HEADER); continue
    if HEADER_RANGE[0] < i <= HEADER_RANGE[1]:
        continue
    if i == 11085:
        out.append(LGEO_NOTE.rstrip("\n")); out.append(""); continue
    if i in drop:
        continue
    out.append(lines[i-1])
text = "\n".join(out) + "\n"
open(DST, "w", encoding="utf-8").write(text)
print("wrote", DST, "lines:", text.count("\n"))
print("deleted ranges:")
for a, b, lab in DELETE:
    print(f"  L{a}-L{b} ({b-a+1} lines): {lab}")
