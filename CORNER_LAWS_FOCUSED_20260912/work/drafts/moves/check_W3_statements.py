import re,sys
def stmts(path):
    T=open(path,encoding='utf-8').read()
    out={}
    for m in re.finditer(r'^theorem (w3[a-h]_[^\s:({\[]+)(.*?):= by\n', T, re.S|re.M):
        out[m.group(1)] = m.group(0)
    return out
S=stmts('Skeleton_W3.lean'); A=stmts(sys.argv[1])
print("skeleton w3 statements:", len(S), " in target:", len(A))
bad=[n for n in S if A.get(n)!=S[n]]
print("byte-identical:", len(S)-len(bad), " differing/missing:", bad)
w3a=[n for n in S if n.startswith('w3a_')]; print("w3a_ count:", len(w3a))
# every non-w3 skeleton declaration name still declared
def decls(path):
    return {m.group(2) for m in re.finditer(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |nonrec )*(theorem|lemma|def|abbrev|structure|instance|inductive|class|opaque)\s+([^\s:({\[]+)', open(path,encoding='utf-8').read(), re.M)}
missing = decls('Skeleton_W3.lean') - decls(sys.argv[1])
print("skeleton declaration names missing in target:", sorted(missing))
