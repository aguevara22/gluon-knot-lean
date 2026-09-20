#!/usr/bin/env python3
"""Statement byte-identity check: every declaration of Statements_FINAL.lean must appear in
Skeleton_W1.lean with a byte-identical statement (text from the declaration keyword up to the body
separator `:=`); the prefix up to the insertion point must be byte-identical; the suffix may differ
only in the body of `exists_rii_deletion`."""
import re, sys, difflib
A = open(sys.argv[1], encoding='utf-8').read()   # Statements_FINAL.lean
Bf = open(sys.argv[2], encoding='utf-8').read()  # Skeleton_W1.lean
alines = A.split('\n'); blines = Bf.split('\n')
# 1. prefix identity (lines 1..136 of Statements_FINAL)
NPRE = 136
pre_ok = alines[:NPRE] == blines[:NPRE]
print(f"prefix (lines 1-{NPRE}) byte-identical: {pre_ok}")
# 2. declaration statements
decl_re = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(theorem|def|structure|abbrev|inductive)\s+([\w.₀-₉\'ΓΨσ]+)', re.M)
def statements(text):
    out = {}
    for m in decl_re.finditer(text):
        kind, name = m.group(1), m.group(2)
        start = m.start()
        rest = text[start:]
        # statement ends at the first top-level ' :=' / ' where' (structures: whole block up to blank line)
        if kind == 'structure' or kind == 'inductive':
            end = rest.find('\n\n')
            stmt = rest[:end]
        else:
            # find ':=' not inside a docstring; declarations here have the body after ':= by' or ':='
            idx = None
            for mm in re.finditer(r':=', rest):
                idx = mm.start(); break
            stmt = rest[:idx].rstrip()
        out.setdefault(name, []).append(stmt)
    return out
sa, sb = statements(A), statements(Bf)
bad = 0
for name, stmts in sa.items():
    if name not in sb:
        print(f"MISSING in skeleton: {name}"); bad += 1; continue
    for st in stmts:
        if st not in sb[name]:
            print(f"STATEMENT CHANGED: {name}"); bad += 1
            for l in difflib.unified_diff(st.split('\n'), sb[name][0].split('\n'), lineterm=''):
                print('   ', l)
print(f"declarations in Statements_FINAL: {sum(len(v) for v in sa.values())}; changed/missing: {bad}")
# 3. the suffix: everything of Statements_FINAL after the prefix must appear in the skeleton in order,
#    except the body of exists_rii_deletion
suffix = '\n'.join(alines[NPRE:])
body_old = "      Nonempty (RecordIso D'.record B.reducedRecord) := by\n  sorry"
assert body_old in suffix
sfx_a, sfx_b = suffix.split(body_old)
tail = '\n'.join(blines[NPRE:])
ok3 = tail.endswith(sfx_b) and sfx_a in tail
print(f"suffix identical except the body of exists_rii_deletion: {ok3}")
sys.exit(0 if (pre_ok and bad == 0 and ok3) else 1)
