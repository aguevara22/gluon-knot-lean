#!/usr/bin/env python3
"""Assemble Moves_Assembled.lean from Skeleton_W1.lean + the seven unit files W1_M*.lean.
Every unit file is diffed against the skeleton (difflib, line-level); hunks are validated:
  - no 'delete' opcode;
  - 'replace' opcodes remove only lines that are exactly a `sorry` body (or the statement line
    of a sub-leaf whose statement text up to `:=` is unchanged);
  - 'insert' opcodes add only declarations whose names carry the unit prefix um<N>_ (plus
    comments / blank lines / `variable (B) in`).
Hunks are then applied in skeleton order; two units may not touch the same skeleton line.
"""
import sys, re, difflib, os, json
D = sys.argv[1]
skel = open(os.path.join(D, 'Skeleton_W1.lean'), encoding='utf-8').read().split('\n')
units = ['M1','M2','M3','M4','M5','M6','M7']
decl_re = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\s+([^\s(:{\[]+)')
struct_re = re.compile(r'^\s*(section|namespace|end|open|set_option|attribute|macro|syntax|notation|universe|variable|axiom|import)\b')
# skeleton position -> list of (unit, kind, new_lines, old_lines)
hunks = []   # (i1, i2, unit, kind, newlines)
violations = []
helper_names = {}
for u in units:
    lines = open(os.path.join(D, f'W1_{u}.lean'), encoding='utf-8').read().split('\n')
    sm = difflib.SequenceMatcher(a=skel, b=lines, autojunk=False)
    n = int(u[1:])
    prefix = f'um{n}_'
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal':
            continue
        old = skel[i1:i2]; new = lines[j1:j2]
        if tag == 'delete':
            violations.append((u, f'DELETE of skeleton lines {i1+1}-{i2}: {old}'))
            continue
        if tag == 'replace':
            for k, ol in enumerate(old):
                if ol.strip() == 'sorry':
                    continue
                # allow the statement line itself when identical up to ':='
                if ':=' in ol and k + 1 < len(old) and old[k+1].strip() == 'sorry':
                    stmt_old = ol.split(':=')[0]
                    # the new hunk must contain the same statement text
                    if not any(nl.startswith(stmt_old) for nl in new):
                        violations.append((u, f'statement line {i1+k+1} changed: {ol!r}'))
                    continue
                violations.append((u, f'REPLACE removes non-sorry skeleton line {i1+k+1}: {ol!r}'))
        # inspect new lines for declarations
        for nl in new:
            m = decl_re.match(nl)
            if m:
                name = m.group(2)
                if name.startswith(prefix):
                    helper_names.setdefault(u, []).append(name)
                elif tag == 'replace' and name.split('.')[-1] in ('m5_moveMatch',) :
                    pass  # the sub-leaf's own statement line re-emitted with a term body
                elif tag == 'replace' and any(name in ol for ol in old):
                    pass
                else:
                    violations.append((u, f'unprefixed new declaration {name!r} (skel {i1+1}, tag {tag})'))
            s = struct_re.match(nl)
            if s and not nl.strip().startswith('variable (B) in'):
                violations.append((u, f'structural line added: {nl!r} (skel {i1+1})'))
        hunks.append((i1, i2, u, tag, new))
# overlap check
hunks.sort(key=lambda h: (h[0], h[1]))
for a, b in zip(hunks, hunks[1:]):
    # a = (i1,i2,...) ; inserts have i1==i2
    if b[0] < a[1] or (a[0] == b[0] and a[1] == b[1] and a[1] > a[0]):
        violations.append(('ALL', f'overlapping hunks: {a[:4]} vs {b[:4]}'))
    if a[0] == b[0] and a[1] == a[0] and b[1] == b[0] and a[2] != b[2]:
        violations.append(('ALL', f'two units insert at the same skeleton line {a[0]}: {a[2]}, {b[2]}'))
if violations:
    print('VIOLATIONS:')
    for v in violations: print('  ', v)
    sys.exit(2)
# apply
out = []
pos = 0
for i1, i2, u, tag, new in hunks:
    out.extend(skel[pos:i1])
    out.extend(new)
    pos = i2
out.extend(skel[pos:])
open(os.path.join(D, 'Moves_Assembled.lean'), 'w', encoding='utf-8').write('\n'.join(out))
print(f'assembled {len(out)} lines from {len(hunks)} hunks')
for u in units:
    print(f'  {u}: {len(helper_names.get(u, []))} helpers')
# de-duplication scan: identical helper names across units
allnames = [(u, nm) for u, l in helper_names.items() for nm in l]
seen = {}
for u, nm in allnames:
    if nm in seen and seen[nm] != u:
        print('DUP NAME across units:', nm, seen[nm], u)
    seen[nm] = u
json.dump(helper_names, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'helper_names.json'), 'w'), indent=1)

# ---------------------------------------------------------------------------------------------
# Step 2: de-duplication of statement-identical helpers across unit prefixes.
# (keep, drop): `drop` is declared later, has the same statement text and the same binder
# structure at every use site (all uses are dot-notation `B.…` / explicit `C`), so its uses are
# renamed to `keep` and its declaration (docstring + `variable (B) in` line + body) is removed.
DEDUP = [
    ('um2_adjacent_iff',        'um3_adjacent_iff'),
    ('um2_strand_succ_j',       'um3_strand_succ_j'),
    ('um2_strand_j_sub_one',    'um3_strand_pred_j'),
    ('um2_seg_subset_seg_orig', 'um3_seg_subset_seg_orig'),
    ('um2_seg_mid_subset_U',    'um3_mid_seg_subset_U'),
    ('um2_cutIn_disj_cutOut',   'um3_cutIn_disjoint_cutOut'),
    ('um1_s_ne_strand',         'um4_s_ne_strand'),
    ('um1_not_adjacent_in_out', 'um2_not_adjacent_eIn_eOut'),
]
def decl_extent(lines, name):
    """[start, end) line range of the top-level declaration `name`, including its docstring, any
    attribute lines and a preceding `variable (B) in` line; the body runs to the next column-0
    non-blank line (proof bodies are indented)."""
    idx = [i for i, l in enumerate(lines) if re.match(rf'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:theorem|def|abbrev)\s+{re.escape(name)}\b', l)]
    assert len(idx) == 1, (name, idx)
    s = idx[0]
    def is_mod(l): return l.startswith('variable (B) in') or l.startswith('@[') or l.startswith('open scoped Classical in')
    b = s
    while b > 0 and is_mod(lines[b-1]): b -= 1
    if b > 0 and lines[b-1].rstrip().endswith('-/'):
        j = b - 1
        while j >= 0 and not lines[j].startswith('/--') and not lines[j].startswith('/-!'): j -= 1
        if j >= 0 and lines[j].startswith('/--'):
            b = j
            while b > 0 and is_mod(lines[b-1]): b -= 1
    e = s + 1
    while e < len(lines) and (lines[e].strip() == '' or lines[e].startswith(' ') or lines[e].startswith('\t')):
        e += 1
    while e - 1 > s and lines[e-1].strip() == '' and lines[e-2].strip() == '':
        e -= 1
    return b, e
removed = []
for keep, drop in DEDUP:
    b, e = decl_extent(out, drop)
    removed.append((drop, keep, b + 1, e - b))
    del out[b:e]
    pat = re.compile(rf'\b{re.escape(drop)}\b')
    n = 0
    for i, l in enumerate(out):
        if pat.search(l):
            out[i] = pat.sub(keep, l); n += 1
    removed[-1] = removed[-1] + (n,)
open(os.path.join(D, 'Moves_Assembled.lean'), 'w', encoding='utf-8').write('\n'.join(out))
print(f'de-duplicated {len(removed)} helpers; file now {len(out)} lines')
for r in removed: print(f'   dropped {r[0]} (kept {r[1]}; {r[3]} lines at former line {r[2]}; {r[4]} use lines renamed)')
