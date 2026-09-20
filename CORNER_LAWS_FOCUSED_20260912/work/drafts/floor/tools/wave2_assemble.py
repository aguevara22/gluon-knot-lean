#!/usr/bin/env python3
"""Wave-2 assembler for the floor lane.

usage: python3 tools/wave2_assemble.py <floor dir> <base.lean> <unit1,unit2,...> <out.lean>
  units are the suffixes of W2_<unit>.lean.

Rules enforced (a unit is REJECTED, and the run reports PROBLEMS, on any violation):
  * every removed base line must be exactly `  sorry` (the leaf body);
  * every `c` hunk replaces exactly one base line, which must be `  sorry`;
  * no `d` hunks;
  * every `a` hunk sits at a declaration boundary (the next base line starts a docstring `/--`,
    a `/-!` block, a declaration keyword, or is blank);
  * added lines contain none of: sorry, admit, native_decide, axiom, set_option, @[simp], attribute,
    unsafe, implemented_by, extern;
  * every added declaration name carries the unit's prefix (given in PREFIX below);
  * no two units add the same declaration name; no added name coincides with a base name;
  * the `theorem <leaf>` header line of every base leaf survives byte-identically exactly once.
Then: assemble by one walk of the base, and verify that every hunk block occurs contiguously in the
output, that the base prefix/suffix outside the hunks are byte-identical, and print the sorry count.
"""
import re, sys, subprocess
D, BASE, UNITS, OUT = sys.argv[1], sys.argv[2], sys.argv[3].split(','), sys.argv[4]
PREFIX = {'B3': 'ub3_', 'EQ': 'ueq_', 'LIFT3': 'ul3_', 'C': 'uc_'}
base_path = f'{D}/{BASE}'
skel = open(base_path).read().split('\n')
if skel[-1] == '': skel = skel[:-1]
N = len(skel)
hdr = re.compile(r'^(\d+)(?:,(\d+))?([acd])(\d+)(?:,(\d+))?$')
decl_re = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(theorem|lemma|def|structure|abbrev|instance|axiom|opaque|class|inductive)\s+([A-Za-z_][\w.\'₀-₉!?]*)')
forbidden = re.compile(r'sorry|admit|native_decide|axiom|set_option|@\[simp\]|attribute|unsafe|implemented_by|extern')
base_names = {m.group(2) for l in skel for m in [decl_re.match(l)] if m}
repl = {}        # base line -> (unit, added lines)
ins = {}         # after base line -> [(unit, added lines)]
blocks = []      # (unit, added, hunk string)
new_names = {}   # name -> unit
ok = True
def viol(msg):
    global ok; ok = False; print('VIOLATION', msg)
for u in UNITS:
    upath = f'{D}/W2_{u}.lean'
    ulines = open(upath).read().split('\n')
    if ulines[-1] == '': ulines = ulines[:-1]
    out = subprocess.run(['diff', base_path, upath], capture_output=True, text=True).stdout.split('\n')
    i = 0; nh = 0
    while i < len(out):
        m = hdr.match(out[i])
        if not m: i += 1; continue
        s1 = int(m.group(1)); s2 = int(m.group(2) or s1); op = m.group(3)
        t1 = int(m.group(4)); t2 = int(m.group(5) or t1)
        i += 1; nh += 1
        removed = []
        while i < len(out) and out[i].startswith('<'):
            removed.append(out[i][2:]); i += 1
        if i < len(out) and out[i] == '---': i += 1
        added = []
        while i < len(out) and out[i].startswith('>'):
            added.append(out[i][2:] if len(out[i]) > 1 else ''); i += 1
        h = f'{s1},{s2}{op}{t1},{t2}'
        if op in 'ac':
            assert added == ulines[t1-1:t2], (u, h, 'added lines do not match unit file slice')
        if op == 'd': viol(f'W2_{u}: pure deletion hunk {h}')
        for r in removed:
            if r != '  sorry': viol(f'W2_{u} hunk {h}: removed non-sorry line {r!r}')
        if op == 'c':
            if s1 != s2: viol(f'W2_{u} hunk {h}: multi-line replacement')
            if skel[s1-1] != '  sorry': viol(f'W2_{u} hunk {h}: replaced base line is not `  sorry`: {skel[s1-1]!r}')
            if s1 in repl: viol(f'W2_{u} hunk {h}: replacement conflicts with W2_{repl[s1][0]}')
            repl[s1] = (u, added)
        elif op == 'a':
            nxt = skel[s1] if s1 < N else ''
            if not (nxt.strip() == '' or nxt.startswith('/--') or nxt.startswith('/-!') or decl_re.match(nxt)):
                viol(f'W2_{u} hunk {h}: insertion not at a declaration boundary (next base line {nxt!r})')
            ins.setdefault(s1, []).append((u, added))
        for k, l in enumerate(added):
            if forbidden.search(l): viol(f'W2_{u} hunk {h}: forbidden token in added line {t1+k}: {l!r}')
            dm = decl_re.match(l)
            if dm:
                name = dm.group(2)
                if not name.startswith(PREFIX[u]): viol(f'W2_{u} hunk {h}: added declaration without prefix {PREFIX[u]}: {name}')
                if name in base_names: viol(f'W2_{u} hunk {h}: added declaration shadows a base name: {name}')
                if name in new_names: viol(f'W2_{u} hunk {h}: duplicate helper name {name} (also in W2_{new_names[name]})')
                new_names[name] = u
        blocks.append((u, added, h))
        print(f'W2_{u}: hunk {h}: removed {removed}, added {len(added)} lines, decls {sum(1 for l in added if decl_re.match(l))}')
    print(f'W2_{u}: {nh} hunks')
# assemble
res = []; i = 1
while i <= N:
    if i in repl:
        res.extend(repl[i][1])
    else:
        res.append(skel[i-1])
    for (uu, add) in ins.get(i, []): res.extend(add)
    i += 1
text = '\n'.join(res) + '\n'
open(f'{D}/{OUT}', 'w').write(text)
# verifications
def contiguous(block, lines):
    n = len(block)
    for k in range(len(lines) - n + 1):
        if lines[k:k+n] == block: return k + 1
    return None
for u, added, h in blocks:
    p = contiguous(added, res)
    print(f'  block W2_{u} {h}: {"contiguous at assembled line %d" % p if p else "NOT FOUND CONTIGUOUSLY"}')
    ok = ok and bool(p)
# every base line except the replaced sorries survives in order
j = 0; missing = []
for k, l in enumerate(skel, 1):
    if k in repl: continue
    while j < len(res) and res[j] != l: j += 1
    if j >= len(res): missing.append(k); break
    j += 1
if missing: viol(f'base line {missing[0]} not found in order in the output')
else: print(f'all {N - len(repl)} non-replaced base lines present in order; {len(repl)} sorry bodies replaced')
# leaf headers
for s1, (u, added) in sorted(repl.items()):
    # find the theorem header above the sorry in the base
    k = s1 - 1
    while k > 0 and not decl_re.match(skel[k-1]): k -= 1
    hdrline = skel[k-1]
    c = sum(1 for l in res if l == hdrline)
    print(f'  leaf header for W2_{u} (base l.{k}): {hdrline[:90]!r} -> {c} occurrence(s) in output')
    if c != 1: viol(f'leaf header of W2_{u} occurs {c} times')
print('helpers added:', len(new_names))
open(f'{D}/tools/wave2_new_names.txt', 'w').write('\n'.join(f'{n} {u}' for n, u in new_names.items()) + '\n')
print('assembled lines:', len(res), ' lines containing sorry:', sum(1 for l in res if 'sorry' in l))
print('OK' if ok else 'PROBLEMS')
