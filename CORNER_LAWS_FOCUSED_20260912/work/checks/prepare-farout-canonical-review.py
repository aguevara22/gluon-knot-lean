from pathlib import Path
from hashlib import sha256
import json,re
base=Path(__file__).resolve().parents[2]
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def load(p):return json.loads((base/p).read_text())
mfile='work/checks/farout-port-preparation.json';m=load(mfile);ports={}
assert len(m['prior_SM_files_sha256'])==307
assert all(sha('work/lean/'+f)==h for f,h in m['prior_SM_files_sha256'].items())
for dest,v in m['new_modules'].items():
 assert sha(v['candidate'])==v['candidate_sha256']
 blocks=[]
 for f in v['source_fragments']:
  assert sha(f['source'])==f['source_sha256'];blocks.append((base/f['source']).read_text())
 s=(base/v['candidate']).read_text();assert s[s.index('namespace SM'):]== '\n'.join(blocks)
 ports[dest]=dict(v,fragment_bodies_byte_for_byte_equal=True,imports=re.findall(r'^import (\S+)',s,re.M))
p=load('work/checks/farout-review-preparation.json')
names=p['checked_declarations'];examples=p['additional_examples'];assert len(names)==len(set(names))==127 and len(examples)==48
imports=['SM.Farout','Mathlib.Data.Fintype.Powerset','Mathlib.Tactic']
transparent=p['transparent_definitions_printed']
s='\n'.join('import '+n for n in imports)+'\n\nset_option maxRecDepth 10000\nset_option maxHeartbeats 12000000\nset_option pp.universes false\n\n'
for f,h in p['example_files_sha256'].items():assert sha(f)==h;s+=(base/f).read_text()+'\n'
for n in names:s+='#check '+n+'\n#print axioms '+n+'\n'
for n in transparent:s+='#print '+n+'\n'
for n in examples:s+='#print axioms '+n+'\n'
tf='work/checks/farout-canonical-review-types.lean';(base/tf).write_text(s)
seen={}
def visit(n):
 if n in seen:return
 dest='work/lean/'+n.replace('.','/')+'.lean';f=ports[dest]['candidate'] if dest in ports else dest;seen[n]={'canonical':dest,'read_from':f,'sha256':sha(f)}
 for child in re.findall(r'^import (\S+)',(base/f).read_text(),re.M):
  if child.startswith('SM.'):visit(child)
visit('SM.Farout')
assert len(seen)==32
binding=dict(p['inherited_review_binding'])
for f in ['work/reviews/farout-prototype.json','work/checks/farout-reviewed-types.json','work/checks/farout-review-closure.json']:binding[f]=sha(f)
for f,h in m['external_reviews_sha256'].items():assert sha('work/reviews/'+f)==h
out={'state':'candidate source comparison and canonical trace prepared; audit/independent kernel pending','port_manifest':mfile,'port_manifest_sha256':sha(mfile),'ports':ports,'prior_SM_count':307,'all_307_prior_SM_unchanged':True,
 'checked_declarations':names,'additional_examples':examples,'transparent_definitions_printed':transparent,'trace':tf,'trace_sha256':sha(tf),
 'SM_import_roots':['SM.Farout'],'predicted_import_closure':seen,'predicted_import_closure_count':32,'external_review_binding':binding,
 'scope':'Twelve exact canonical ports and full lem:farout source acceptance review, pending current audit and independent import-only kernel. No map or implementation changes by this reviewer.'}
(base/'work/checks/farout-canonical-review-preparation.json').write_text(json.dumps(out,indent=2)+'\n')
print('Prepared127 declaration checks+48 consumers;12 exact candidate bodies;32 predicted SM import-closure modules; no kernel launched.')
