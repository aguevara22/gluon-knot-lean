from pathlib import Path
from hashlib import sha256
import re,json
base=Path(__file__).resolve().parents[2]
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def load(p):return json.loads((base/p).read_text())
old=load('work/checks/boundary-gate-stability-review-preparation.json')
new=['WallArrayNeighborhood','WallGapValues','BoundaryGapGates','GeometricGapResponse','FullSpanGermResponse','RestrictedCriticalG1']
order=old['body_order']+new;receipts={};files={};bybody={}
for n in order:
 f='work/checks/'+n+'-prototype-result.json';r=load(f);assert r['exit_code']==0
 for p,h in r['files_sha256'].items():assert sha(p)==h,(n,p);files[p]=h
 assert (base/('work/checks/'+n+'.body.lean')).read_text() in (base/('work/checks/'+n+'.prototype.lean')).read_text()
 receipts[f]=sha(f);bybody[n]=r['printed_declarations']
names=sum(bybody.values(),[]);assert len(names)==len(set(names))==42
roots=old['SM_import_roots']+['SM.GermNeighborhood'];closure={}
def visit(m):
 f='work/lean/'+m.replace('.','/')+'.lean'
 if f in closure:return
 assert (base/f).is_file(),f
 closure[f]=sha(f)
 for i in re.findall(r'^import\s+(\S+)',(base/f).read_text(),re.M):
  if i.startswith('SM.'):visit(i)
for m in roots:visit(m)
examplefiles=[old['example_file'],'work/checks/geometric-gap-response-review-examples.lean']
examples=list(old['additional_examples'])+['GeometricGapResponseIndependentReview.'+n for n in re.findall(r'^theorem (\S+)',(base/examplefiles[1]).read_text(),re.M)]
assert len(examples)==31,len(examples)
transparent=old['transparent_definitions_printed']+['SM.wallGapU','SM.wallGapV','SM.cutWeightedSum',
 'SM.IncreasingBoundaryTriple.fixedFarGate','SM.restrictedVertexIndex','SM.restrictedWordTuple','SM.WallGerm',
 'SM.WallGerm.sideTime','SM.WallGerm.sideTuple','SM.WallGerm.center','SM.WallGerm.zeroParameter']
support=old['supporting_types_printed']+['SM.WallGerm.eventually_center_iff_radius','SM.treeCoefficient_farOnly',
 'SM.farOnlyOutput_restricted_tree','SM.restrictedWord_closing_edge','SM.BoundaryInterval.globalPosition_strict',
 'SM.BoundaryInterval.globalPosition_bounds']
s=''.join('import '+m+'\n' for m in roots)+'import Mathlib.Tactic\nimport Mathlib.Data.Sign.Basic\n\nset_option maxRecDepth 10000\nset_option maxHeartbeats 12000000\nset_option pp.universes false\n\n'
for n in order:s+=(base/('work/checks/'+n+'.body.lean')).read_text()+'\n'
for f in examplefiles:s+=(base/f).read_text()+'\n'
for n in names:s+='#check '+n+'\n#print axioms '+n+'\n'
for n in transparent:s+='#print '+n+'\n'
for n in support:s+='#check '+n+'\n'
for n in examples:s+='#print axioms '+n+'\n'
tf='work/checks/geometric-gap-response-review-types.lean';(base/tf).write_text(s)
for f,h in old['all_327_canonical_SM_files_sha256'].items():assert sha(f)==h
bindings=dict(old['prior_checkpoint_bindings_sha256'])
for f in ['work/reviews/boundary-gate-stability-prototype.json','work/checks/boundary-gate-stability-reviewed-types.json']:
 bindings[f]=sha(f)
p={'state':'prepared, independent kernel pending','source_id':'thm:single-triple','source':old['source'],
 'source_lines':'229-269,271-283,290-317; full-span branch and nonleaf closed-gap G1, proper propagation excluded',
 'sources_sha256':old['sources_sha256'],'body_order':order,'new_body_order':new,'checked_declarations':names,
 'checked_declarations_by_body':bybody,'additional_examples':examples,'new_consumer_count':12,
 'transparent_definitions_printed':transparent,'supporting_types_printed':support,'trace':tf,'trace_sha256':sha(tf),
 'example_files_sha256':{f:sha(f) for f in examplefiles},'SM_import_roots':roots,'SM_closure_files_sha256':closure,
 'SM_closure_count':len(closure),'all_327_canonical_SM_files_sha256':old['all_327_canonical_SM_files_sha256'],
 'root_receipts_sha256':receipts,'root_files_sha256':files,'prior_checkpoint_bindings_sha256':bindings,
 'scope':'Six new frozen external bodies with15 new declarations over the reviewed five-body27 prefix. Actual common germ radius, signed U/V gap sums, actual geometric critical response, full-span rooted tree response on close punctured sides, and actual restricted-word G1. No proper-span contraction/propagation or whole wall theorem acceptance. The literal half-difference prefactor is not separately proved +/-1 here.'}
(base/'work/checks/geometric-gap-response-review-preparation.json').write_text(json.dumps(p,indent=2)+'\n')
print('Prepared42 declarations (27old+15new)+31 consumers (19old+12new);',len(closure),'canonical SM dependency modules;327 canonical files unchanged. No kernel launched.')
