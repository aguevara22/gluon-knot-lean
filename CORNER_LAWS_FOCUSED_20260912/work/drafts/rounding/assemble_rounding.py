#!/usr/bin/env python3
"""Assemble Rounding_Assembled.lean = Skeleton_FINAL.lean + every unit's proved hunks.

For each unit file U_<u>.lean we compute the line diff against the skeleton and require that
  * every skeleton line removed is exactly `  sorry`, and belongs to a leaf of that unit;
  * the replacement lines add only helper declarations (theorem/lemma, unit-prefixed or private)
    and proof bodies -- no def/structure/abbrev/instance/axiom/set_option/sorry;
  * edit ranges of different units are pairwise disjoint in skeleton coordinates.
Then the edits are applied in one pass, helpers are de-duplicated (identical text) / renamed (clash),
and each inserted block is checked to occur contiguously in the result.
"""
import difflib, re, sys, json, pathlib

D = pathlib.Path('/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/drafts/rounding')
skel = (D / 'Skeleton_FINAL.lean').read_text().split('\n')

UNITS = {
  'P':  ['smoothTransition_strictMonoOn','deriv_smoothTransition_pos','iteratedDeriv_eq_zero_of_const_left','iteratedDeriv_eq_zero_of_const_right'],
  'A':  ['dirOf_injOn_of_lt_pi','M_pos','juncLen_pos','integral_juncDir','juncArc_mem_disc','juncArc_mem_open_disc','juncArc_injOn'],
  'G1': ['dirOf_θu','dirOf_θu_add_turn','three_mul_lt_edgeLength'],
  'G2': ['Θ_smooth','Θ_on_junction','Θ_on_straight','integral_tangentField_junction','integral_tangentField_straight','integral_tangentField_period','curveMap_a','curveMap_b','curveMap_on_junction','curveMap_on_straight'],
  'G3': ['liftAt_strictMonoOn','liftAt_strictAntiOn','deriv_liftAt_ne_zero','tangent_injOn_junction'],
  'E':  ['clearance_pos','cornerDisc_isDisc','mem_interior_cornerDisc','cornerDisc_disjoint','cornerDisc_disjoint_edge','crossingPoint_notMem_cornerDisc','cornerDisc_inter_edge_out','cornerDisc_inter_edge_in','three_mul_lt_dist_crossing'],
  'X':  ['curveMap_junction_mem_disc','curveMap_straight_notMem_discs','range_curveMap_outside','τ_mem_straight','τ_mem_Ico','curveMap_τ','deriv_curveMap_τ','τ_injective','doubles_curveMap','transverse_τ','order_τ','sign_τ','cover','iteratedDeriv_curveMap_a','iteratedDeriv_curveMap_b'],
}
DECL = re.compile(r'^\s*(private\s+|protected\s+)?(noncomputable\s+)?(theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|opaque|example|macro|syntax|notation)\s+([^\s:({\[]+)?')
FORBID = re.compile(r'\b(axiom|sorry|native_decide|unsafe|implemented_by|set_option|opaque)\b')

def owning_leaf(idx):
    """name of the theorem whose body contains skeleton line idx (0-based)"""
    for k in range(idx, -1, -1):
        m = DECL.match(skel[k])
        if m and m.group(3) == 'theorem':
            return m.group(4)
    return None

edits = []   # (i1, i2, unit, replacement_lines)
violations = []
helpers = {} # name -> (unit, text)
for u, leaves in UNITS.items():
    lines = (D / f'U_{u}.lean').read_text().split('\n')
    sm = difflib.SequenceMatcher(None, skel, lines, autojunk=False)
    proved = set()
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal':
            continue
        removed = skel[i1:i2]
        added = lines[j1:j2]
        for r_off, r in enumerate(removed):
            if r.strip() != 'sorry':
                violations.append(f'U_{u}: removed non-sorry skeleton line {i1+r_off+1}: {r!r}')
            leaf = owning_leaf(i1 + r_off)
            if leaf not in leaves:
                violations.append(f'U_{u}: removed sorry of leaf {leaf} (line {i1+r_off+1}) not owned by unit')
            proved.add(leaf)
        for a_off, a in enumerate(added):
            if FORBID.search(a):
                violations.append(f'U_{u}: forbidden token in added line {j1+a_off+1}: {a!r}')
            m = DECL.match(a)
            if m:
                kind, name = m.group(3), m.group(4)
                if kind not in ('theorem', 'lemma'):
                    violations.append(f'U_{u}: added non-theorem declaration at line {j1+a_off+1}: {a!r}')
                if not (m.group(1) and 'private' in m.group(1)) and not name.startswith(u + '_'):
                    violations.append(f'U_{u}: added helper {name} lacks unit prefix {u}_')
        edits.append((i1, i2, u, added))
    missing = set(leaves) - proved
    if missing:
        print(f'U_{u}: leaves still sorry (not touched): {sorted(missing)}')

# disjointness of edit ranges (in skeleton coordinates); insertions at the same index also clash
edits.sort(key=lambda e: (e[0], e[1]))
for (a1, a2, ua, _), (b1, b2, ub, _) in zip(edits, edits[1:]):
    if ua != ub and not (a2 <= b1 and not (a1 == a2 == b1 == b2)):
        violations.append(f'overlapping edits: {ua}[{a1},{a2}) vs {ub}[{b1},{b2})')
    if ua != ub and a2 == b1 and a1 == a2:
        violations.append(f'two insertions at the same skeleton index {a1}: {ua}, {ub}')

# helper de-duplication / clash detection (by declared name, across units)
def helper_blocks(added):
    """split an added hunk into (name, text) blocks at declaration headers"""
    blocks, cur, name = [], [], None
    for a in added:
        m = DECL.match(a)
        if m:
            if name is not None:
                blocks.append((name, '\n'.join(cur)))
            name, cur = m.group(4), [a]
        else:
            cur.append(a)
    if name is not None:
        blocks.append((name, '\n'.join(cur)))
    return blocks

seen = {}
dedup_notes = []
for k, (i1, i2, u, added) in enumerate(edits):
    for name, text in helper_blocks(added):
        if name in seen:
            u0, text0 = seen[name]
            if text.strip() == text0.strip():
                dedup_notes.append(f'duplicate identical helper {name} in {u0} and {u}: dropping the copy in {u}')
                # remove the block from this hunk
                new_added, skip = [], False
                for a in added:
                    m = DECL.match(a)
                    if m:
                        skip = (m.group(4) == name)
                    if not skip:
                        new_added.append(a)
                edits[k] = (i1, i2, u, new_added)
            else:
                newname = f'{u}_{name}' if not name.startswith(u + '_') else f'{name}_{u}dup'
                dedup_notes.append(f'CLASH helper {name} in {u0} and {u} with different text: renaming the {u} copy to {newname}')
                edits[k] = (i1, i2, u, [re.sub(r'\b' + re.escape(name) + r'\b', newname, a) for a in added])
        else:
            seen[name] = (u, text)

if violations:
    print('VIOLATIONS:')
    for v in violations:
        print('  ' + v)
    sys.exit(1)

# apply
out, pos = [], 0
for i1, i2, u, added in edits:
    out.extend(skel[pos:i1])
    out.extend(added)
    pos = i2
out.extend(skel[pos:])
text = '\n'.join(out)
(D / 'Rounding_Assembled.lean').write_text(text)

# contiguity check: every inserted block occurs as consecutive lines in the result
for i1, i2, u, added in edits:
    if added and '\n'.join(added) not in text:
        print(f'NON-CONTIGUOUS block from {u} at skeleton [{i1},{i2})'); sys.exit(1)

# every skeleton line except the removed sorries survives, in order
skel_kept = [l for k, l in enumerate(skel) if not any(i1 <= k < i2 for i1, i2, _, _ in edits)]
it = iter(out)
assert all(any(l == o for o in it) for l in skel_kept), 'skeleton lines lost'

summary = {
  'edits': len(edits),
  'per_unit': {u: sum(1 for e in edits if e[2] == u) for u in UNITS},
  'removed_sorries': sum(i2 - i1 for i1, i2, _, _ in edits),
  'added_lines': sum(len(a) for _, _, _, a in edits),
  'helpers': len(seen),
  'dedup_notes': dedup_notes,
  'lines_out': len(out),
}
print(json.dumps(summary, indent=1, ensure_ascii=False))
