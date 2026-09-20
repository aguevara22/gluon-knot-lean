import re, sys, subprocess
D='/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/drafts/contact'
units=['CIRCLE','SL','READING','LEG','FAM','TRANS']
skel=open(f'{D}/Skeleton_FINAL.lean').read().split('\n')
if skel[-1]=='': skel=skel[:-1]          # keep trailing newline handling explicit
N=len(skel)
hdr=re.compile(r'^(\d+)(?:,(\d+))?([acd])(\d+)(?:,(\d+))?$')
allowed_removed={'  sorry','theorem u_circle : U_circle := by'}
repl={}      # start line -> (end line, unit, added lines)
ins={}       # after line -> list of (unit, added lines)
blocks=[]    # (unit, added lines) for contiguity check
ok=True
for u in units:
    ulines=open(f'{D}/U_{u}.lean').read().split('\n')
    if ulines[-1]=='': ulines=ulines[:-1]
    out=subprocess.run(['diff',f'{D}/Skeleton_FINAL.lean',f'{D}/U_{u}.lean'],capture_output=True,text=True).stdout.split('\n')
    i=0
    while i<len(out):
        m=hdr.match(out[i])
        if not m: i+=1; continue
        s1=int(m.group(1)); s2=int(m.group(2) or s1); op=m.group(3); t1=int(m.group(4)); t2=int(m.group(5) or t1)
        i+=1
        removed=[]
        while i<len(out) and out[i].startswith('<'):
            removed.append(out[i][2:]); i+=1
        if i<len(out) and out[i]=='---': i+=1
        added=[]
        while i<len(out) and out[i].startswith('>'):
            added.append(out[i][2:] if len(out[i])>1 else ''); i+=1
        # cross-check added against unit file lines t1..t2
        if op in 'ac':
            assert added==ulines[t1-1:t2], (u,s1,s2,op,t1,t2)
        if op=='d': print(f'VIOLATION U_{u}: pure deletion hunk {out[i]}'); ok=False
        if not (549<=s1<=572 and s2<=572): print(f'VIOLATION U_{u}: hunk outside §5.4: {s1},{s2}{op}{t1},{t2}'); ok=False
        for r in removed:
            if r not in allowed_removed: print(f'VIOLATION U_{u}: removed non-sorry line: {r!r}'); ok=False
        if op=='c':
            if any(s in repl for s in range(s1,s2+1)): print(f'CONFLICT U_{u}: replacement overlaps {s1}-{s2}'); ok=False
            repl[s1]=(s2,u,added)
            if 'theorem u_circle : U_circle := by' in removed:
                assert any(l.startswith('theorem u_circle : U_circle :=') for l in added), 'u_circle statement lost'
        else:
            ins.setdefault(s1,[]).append((u,added))
        blocks.append((u,added,f'{s1},{s2}{op}{t1},{t2}'))
        print(f'U_{u}: hunk {s1},{s2}{op}{t1},{t2}: removed {removed}, added {len(added)} lines')
# assemble
res=[]; i=1
while i<=N:
    if i in repl:
        s2,u,added=repl[i]
        res.extend(added)
        for j in range(i,s2+1):
            for (uu,add) in ins.get(j,[]): res.extend(add)
        i=s2+1
    else:
        res.append(skel[i-1])
        for (uu,add) in ins.get(i,[]): res.extend(add)
        i+=1
text='\n'.join(res)+'\n'
open(f'{D}/Contact_Assembled.lean','w').write(text)
# verifications
assert res[:550]==skel[:550], 'prefix 1-550 differs'
assert res[-(N-572):]==skel[572:], 'suffix 573-end differs'
print('prefix lines 1-550 and suffix lines 573-%d byte-identical to skeleton'%N)
def contiguous(block,lines):
    n=len(block)
    for k in range(len(lines)-n+1):
        if lines[k:k+n]==block: return k+1
    return None
for u,added,h in blocks:
    p=contiguous(added,res)
    print(f'  block U_{u} {h}: {"contiguous at assembled line %d"%p if p else "NOT FOUND CONTIGUOUSLY"}')
    ok=ok and bool(p)
# leaf statements present exactly once
leaves=['u_circle','u_sl_radius','u_sl_family','u_sl_reparam','u_sl_isotopy','u_legendrianFront','u_spatialOf','u_reading','u_transport','u_regular','u_family']
for L in leaves:
    c=sum(1 for l in res if l.startswith(f'theorem {L} : U_{L[2:]} :='))
    stmt=[l for l in res if l.startswith(f'theorem {L} ')]
    print(f'  leaf {L}: {c} statement line(s): {stmt}')
    ok=ok and c==1
print('assembled lines:',len(res),' sorry lines:',sum(1 for l in res if 'sorry' in l))
print('OK' if ok else 'PROBLEMS')
