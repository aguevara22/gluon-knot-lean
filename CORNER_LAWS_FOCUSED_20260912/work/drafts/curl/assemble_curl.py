# Assembler script for Curl_Assembled.lean (cf:lem-curl), 2026-09-14.  Run: python3 assemble_curl.py  (reads Skeleton_FINAL.lean + U_*.lean here, writes Curl_Assembled.lean; report JSON to /workspace/scratch/curl_assembly_report.json)
import difflib, re, json, sys
D='/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/drafts/curl/'
sk=open(D+'Skeleton_FINAL.lean').read().split('\n')
units=['MF','G','HT','R','K1','K2','CA']
UNPROVED={'ξ_strictMonoOn','ξ_strictAntiOn'}
# dedupe: dropped name -> (unit, kept name)
DEDUPE={
        'r_planeDot_smul_left':('R','g_planeDot_smul_left'),
        'ca_deriv_eq_of_eqOn_Icc':('CA','ht_deriv_eq_of_eqOn_Icc')}
decl_re=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|structure|abbrev|instance|example|class|inductive|opaque|axiom)\s+([^\s:({\[]+)')
cur=None; sk_sorry={}
for i,l in enumerate(sk):
    m=decl_re.match(l)
    if m: cur=m.group(2)
    if re.match(r'^\s*sorry\s*$',l): sk_sorry[i]=cur
assert len(sk_sorry)==54
IDCH=r"[A-Za-z0-9_'!?₀-₉ᵢ-ᵪₐ-ₜÀ-ɏͰ-Ͽ]"
def remove_block(lines,name):
    """remove the declaration `name` (with its immediately preceding docstring) from lines; return (new_lines, removed_text)"""
    heads=[i for i,l in enumerate(lines) if decl_re.match(l) and decl_re.match(l).group(2)==name]
    assert len(heads)==1,(name,heads)
    h=heads[0]; s=h
    # preceding docstring
    if s>0 and lines[s-1].rstrip().endswith('-/'):
        j=s-1
        while j>=0 and not lines[j].lstrip().startswith('/--'): j-=1
        assert j>=0; s=j
    e=h+1
    while e<len(lines) and lines[e].strip()!='' and lines[e][0] in ' \t': e+=1
    # swallow one following blank line if the block is preceded by a blank line too (keep single blank)
    if e<len(lines) and lines[e].strip()=='' and s>0 and lines[s-1].strip()=='': e+=1
    removed=lines[s:e]
    return lines[:s]+lines[e:], removed
edits=[]  # (a1,a2,kind,unit,leaf,block)
report={'hunks':{}, 'dedupe':{}, 'kept_sorry':[]}
for u in units:
    ul=open(D+f'U_{u}.lean').read().split('\n')
    sm=difflib.SequenceMatcher(None, sk, ul, autojunk=False)
    hl=[]
    for tag,a1,a2,b1,b2 in sm.get_opcodes():
        if tag=='equal': continue
        removed=sk[a1:a2]
        for x in removed: assert re.match(r'^\s*sorry\s*$',x), (u,tag,a1,x)
        if tag=='replace':
            assert a2-a1==1, (u,a1,a2)
            leaf=sk_sorry[a1]
            if leaf in UNPROVED:
                report['kept_sorry'].append((u,leaf,a1+1)); hl.append((tag,a1+1,a2,leaf,'KEPT sorry')); continue
            edits.append([a1,a2,'replace',u,leaf,ul[b1:b2]])
            hl.append((tag,a1+1,a2,leaf,b2-b1))
        elif tag=='insert':
            edits.append([a1,a2,'insert',u,None,ul[b1:b2]])
            hl.append((tag,a1+1,a2,None,b2-b1))
        else: raise SystemExit(('delete hunk?!',u,a1,a2))
    report['hunks'][u]=hl
# dedupe
for dropped,(u,kept) in DEDUPE.items():
    done=False
    for e in edits:
        if e[3]!=u: continue
        if any(decl_re.match(l) and decl_re.match(l).group(2)==dropped for l in e[5]):
            e[5],rem=remove_block(e[5],dropped); done=True
            report['dedupe'][dropped]={'kept':kept,'removed_lines':len(rem),'removed_text':'\n'.join(rem)}
    assert done,dropped
    pat=re.compile(r'(?<!'+IDCH+r')'+re.escape(dropped)+r'(?!'+IDCH+r')')
    n=0
    for e in edits:
        if e[3]!=u: continue
        new=[pat.sub(kept,l) for l in e[5]]
        n+=sum(1 for a,b in zip(e[5],new) if a!=b)
        e[5]=new
    report['dedupe'][dropped]['renamed_refs_lines']=n

# --- assembler gap fix (2026-09-14): Unit R's helper r_glued_off used the two Unit-G leaves
# ξ_strictMonoOn / ξ_strictAntiOn as black boxes; those leaves are FALSE as stated in the degenerate case
# β' < α' (G report) and stay `sorry`.  In r_glued_off the CutFit `cf` gives α' ≤ s₁ < t₀ < s₂ ≤ β', so the
# proved Unit-G helpers g_ξ_strictMonoOn / g_ξ_strictAntiOn apply with hθ restricted.  Proof text only.
MONO_OLD='ξ_strictMonoOn S hα hβ hθ'
MONO_NEW="g_ξ_strictMonoOn S hα (fun t ht => hθ t ⟨ht.1, ht.2.trans (cf.lt_s₂.trans_le cf.le_β').le⟩)"
ANTI_OLD='ξ_strictAntiOn S hα hβ hθ'
ANTI_NEW="g_ξ_strictAntiOn S hβ (fun t ht => hθ t ⟨(cf.α'_le.trans_lt cf.s₁_lt).le.trans ht.1, ht.2⟩)"
nfix=0
for e in edits:
    if e[3]!='R': continue
    new=[]
    for l in e[5]:
        l2=re.sub(r'(?<!'+IDCH+r')'+re.escape(MONO_OLD), MONO_NEW, l)
        l2=re.sub(r'(?<!'+IDCH+r')'+re.escape(ANTI_OLD), ANTI_NEW, l2)
        if l2!=l: nfix+=1
        new.append(l2)
    e[5]=new
print('gap-fix call sites rewritten:', nfix)
report['gap_fix']={'call_sites':nfix,'mono':MONO_NEW,'anti':ANTI_NEW}

# order & overlap check
edits.sort(key=lambda e:(e[0], 0 if e[2]=='insert' else 1))
for x,y in zip(edits,edits[1:]):
    assert x[1]<=y[0], ('overlap',x[:5],y[:5])
out=[]; pos=0
for a1,a2,kind,u,leaf,block in edits:
    out+=sk[pos:a1]; out+=block; pos=a2
out+=sk[pos:]
text='\n'.join(out)
open(D+'Curl_Assembled.lean','w').write(text)
# contiguity check
bad=[(u,leaf,kind) for a1,a2,kind,u,leaf,block in edits if '\n'.join(block) not in text]
print('edits applied:', len(edits), ' replace:', sum(1 for e in edits if e[2]=='replace'), ' insert:', sum(1 for e in edits if e[2]=='insert'))
print('non-contiguous blocks:', bad)
print('kept sorry:', report['kept_sorry'])
for d,v in report['dedupe'].items(): print('dedupe', d, '->', v['kept'], '| removed lines', v['removed_lines'], '| renamed ref lines', v['renamed_refs_lines']); print(v['removed_text'])
print('lines:', len(out))
json.dump(report, open('/workspace/scratch/curl_assembly_report.json','w'), indent=1, default=str)
