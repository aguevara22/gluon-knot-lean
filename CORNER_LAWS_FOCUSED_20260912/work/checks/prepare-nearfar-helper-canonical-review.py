from pathlib import Path
from hashlib import sha256
import json,re
base=Path(__file__).resolve().parents[2]
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def load(p):return json.loads((base/p).read_text())
mfile='work/checks/nearfar-helper-port-preparation.json';m=load(mfile);ports={}
assert len(m['prior_SM_files_sha256'])==299
assert all(sha('work/lean/'+f)==h for f,h in m['prior_SM_files_sha256'].items())
for dest,v in m['new_modules'].items():
 assert sha(v['candidate'])==v['candidate_sha256']
 blocks=[]
 for f in v['source_fragments']:
  assert sha(f['source'])==f['source_sha256'];blocks.append((base/f['source']).read_text())
 s=(base/v['candidate']).read_text();assert s[s.index('namespace SM'):]== '\n'.join(blocks)
 ports[dest]=dict(v,fragment_bodies_byte_for_byte_equal=True,imports=re.findall(r'^import (\S+)',s,re.M))
p=load('work/checks/nearfar-refinement-review-preparation.json');q=load('work/checks/composition-cut-set-review-closure.json')
names=q['checked_declarations']+p['checked_declarations'];examples=q['additional_examples']+p['additional_examples'];assert len(names)==len(set(names))==62 and len(examples)==22
imports=['SM.GeometricNearFar','SM.MarkedRefinement','SM.InteriorCutIndex','SM.NearFarCutExpansion','SM.TriangularPolynomial','Mathlib.Order.Interval.Finset.Fin','Mathlib.Tactic']
transparent=['SM.BoundaryCutSet','SM.BoundaryCutSet.toComposition','SM.IntervalComposition.cutSet','SM.IntervalComposition.cutSetEquiv']+p['transparent_definitions_printed']
s='\n'.join('import '+n for n in imports)+'\n\nset_option maxRecDepth 10000\nset_option maxHeartbeats 12000000\nset_option pp.universes false\n\n'
for f in [q['examples'],p['examples']]:s+=(base/f).read_text()+'\n'
for n in names:s+='#check '+n+'\n#print axioms '+n+'\n'
for n in transparent:s+='#print '+n+'\n'
for n in examples:s+='#print axioms '+n+'\n'
tf='work/checks/nearfar-helper-canonical-review-types.lean';(base/tf).write_text(s)
seen={}
def visit(n):
 if n in seen:return
 dest='work/lean/'+n.replace('.','/')+'.lean';f=ports[dest]['candidate'] if dest in ports else dest;seen[n]={'canonical':dest,'read_from':f,'sha256':sha(f)}
 for child in re.findall(r'^import (\S+)',(base/f).read_text(),re.M):
  if child.startswith('SM.'):visit(child)
for n in imports:
 if n.startswith('SM.'):visit(n)
binding={f:sha(f) for f in ['work/reviews/geometric-nearfar-prototype.json','work/reviews/nearfar-refinement-prototype.json','work/reviews/composition-cut-set-prototype.json','work/checks/nearfar-refinement-reviewed-types.json','work/checks/composition-cut-set-reviewed-types.json',p['examples'],q['examples']]}
for f,h in m['external_reviews_sha256'].items():assert sha('work/reviews/'+f)==h
out={'state':'candidate source comparison and canonical trace prepared; installation/audit/independent kernel pending','port_manifest':mfile,'port_manifest_sha256':sha(mfile),'ports':ports,'prior_SM_count':299,'all_299_prior_SM_unchanged':True,
 'checked_declarations':names,'additional_examples':examples,'transparent_definitions_printed':transparent,'trace':tf,'trace_sha256':sha(tf),
 'SM_import_roots':[n for n in imports if n.startswith('SM.')],'predicted_import_closure':seen,'predicted_import_closure_count':len(seen),'external_review_binding':binding,
 'scope':'Eight canonical helper modules only. No new mapped source claims or full factorization/farout acceptance. ConsecutiveCuts is outside this batch.'}
(base/'work/checks/nearfar-helper-canonical-review-preparation.json').write_text(json.dumps(out,indent=2)+'\n')
print('Prepared62 declaration checks+22 consumers; eight exact candidate bodies;',len(seen),'predicted SM import-closure modules; no kernel launched.')
