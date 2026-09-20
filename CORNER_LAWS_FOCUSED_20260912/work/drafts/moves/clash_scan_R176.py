#!/usr/bin/env python3
"""Namespace-aware clash scan: every declaration of R176_Assembled.lean (with its enclosing
namespace, tracking `namespace X` / `end X`, ignoring sections) against every declaration in
work/lean/**/*.lean (excluding .lake).  A clash = same fully-qualified name declared in work/lean.
Also reports SHORT-name coincidences inside the same namespace family (informational)."""
import os, re, sys, json
ROOT = sys.argv[1]; ASM = sys.argv[2]
decl_re = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:open\s+[^\n]*?\bin\s+)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\s+([^\s(:{\[]+)')
ns_re = re.compile(r'^\s*namespace\s+([\w.₀-₉\'ΓΨσ]+)')
end_re = re.compile(r'^\s*end\s+([\w.₀-₉\'ΓΨσ]+)\s*$')
def decls(path):
    out = []
    stack = []
    try:
        txt = open(path, encoding='utf-8').read().split('\n')
    except Exception as e:
        return out
    for ln, l in enumerate(txt, 1):
        m = ns_re.match(l)
        if m: stack.append(m.group(1)); continue
        m = end_re.match(l)
        if m and stack and stack[-1] == m.group(1): stack.pop(); continue
        m = decl_re.match(l)
        if m:
            kind, name = m.group(1), m.group(2)
            if kind == 'instance' and not re.match(r'[A-Za-z_]', name): continue
            if name.startswith('_root_.'):
                fq = name[len('_root_.'):]
            else:
                fq = '.'.join(stack + [name]) if stack else name
            out.append((fq, kind, ln, name))
    return out
asm = decls(ASM)
asm_fq = {}
for fq, kind, ln, name in asm: asm_fq.setdefault(fq, []).append(ln)
dups = {k: v for k, v in asm_fq.items() if len(v) > 1}
print(f'declarations in assembled file: {len(asm)}; distinct fq names: {len(asm_fq)}; internal duplicates: {dups}')
lib = {}
short = {}
for dp, dn, fn in os.walk(ROOT):
    if '.lake' in dp: continue
    for f in fn:
        if not f.endswith('.lean'): continue
        p = os.path.join(dp, f)
        for fq, kind, ln, name in decls(p):
            lib.setdefault(fq, []).append((os.path.relpath(p, ROOT), ln))
            short.setdefault(name.split('.')[-1], []).append((fq, os.path.relpath(p, ROOT), ln))
clashes = []
for fq, kind, ln, name in asm:
    if fq in lib:
        clashes.append((fq, ln, lib[fq]))
print(f'FULLY-QUALIFIED CLASHES: {len(clashes)}')
for c in clashes: print('  ', c)
# informational: same short name in a different namespace within work/lean (only for the new helpers/API)
info = []
for fq, kind, ln, name in asm:
    sn = name.split('.')[-1]
    if sn in short:
        others = [o for o in short[sn] if o[0] != fq]
        if others: info.append((fq, ln, others[:3]))
print(f'short-name coincidences (different namespace, informational): {len(info)}')
json.dump({'clashes': clashes, 'short_coincidences': info, 'n_decls': len(asm)}, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'clash_scan_R176.json'), 'w'), indent=1, default=str)
for i in info[:40]: print('  ', i)
