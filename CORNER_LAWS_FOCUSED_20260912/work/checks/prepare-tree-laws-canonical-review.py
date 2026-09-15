from pathlib import Path
from hashlib import sha256
import json,re
base=Path(__file__).resolve().parents[2]
def load(p):return json.loads((base/p).read_text())
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
m=load('work/checks/tree-laws-port-preparation-with-chamber.json');ports={}
for dest,v in m['new_modules'].items():
 p=v['candidate'];assert sha(p)==v['candidate_sha256']
 bodies=[]
 for f in v['source_fragments']:
  assert sha(f['source'])==f['source_sha256'];bodies.append((base/f['source']).read_text())
 s=(base/p).read_text();assert s[s.index('namespace SM'):]== '\n'.join(bodies),dest
 ports[dest]=dict(v,fragment_bodies_byte_for_byte_equal=True,imports=re.findall(r'^import (\S+)',s,re.M))
assert all(sha('work/lean/'+p)==h for p,h in m['prior_SM_files_sha256'].items())
names=[]
for f in ['tree-coefficient-prototype','plane-tree-prototype','tree-chamber-claim-prototype']:
 for n in load('work/reviews/'+f+'.json')['evidence']['checked_declarations']:
  if n not in names:names.append(n)
assert len(names)==58
t='import SM.PlaneTreeFormal\nimport SM.TreeChamber\n\nset_option pp.fullNames true\nset_option pp.universes false\n\n'
t+='\n'.join('#check '+n+'\n#print axioms '+n for n in names)+'\n'
transparent=load('work/checks/tree-definition-and-shape-review-closure.json')['transparent_definitions_printed']+['SM.TreeDataEqual']
t+='\n'.join('#print '+n for n in transparent)+'\n';examples=[]
for f,ns in [('tree-definition-and-shape-review-examples.lean','TreeDefinitionIndependentReview'),('tree-chamber-claim-review-examples.lean','TreeChamberClaimIndependentReview')]:
 s=(base/'work/checks'/f).read_text();new=[ns+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M)];examples+=new
 t+=s+'\n'+'\n'.join('#print axioms '+n for n in new)+'\n'
assert len(examples)==20
trace='work/checks/tree-laws-canonical-review-types.lean';(base/trace).write_text(t)
d={'state':'exact candidate body comparison and canonical trace preparation complete; installation, audit and independent canonical kernel pending',
 'port_manifest':'work/checks/tree-laws-port-preparation-with-chamber.json','port_manifest_sha256':sha('work/checks/tree-laws-port-preparation-with-chamber.json'),
 'ports':ports,'prior_SM_count':288,'all_288_prior_SM_unchanged':True,
 'checked_declarations':names,'additional_examples':examples,'transparent_definitions_printed':transparent,
 'trace':trace,'trace_sha256':sha(trace),'prototype_reviews_sha256':{p:sha(p) for p in ['work/reviews/tree-coefficient-prototype.json','work/reviews/plane-tree-prototype.json','work/reviews/tree-chamber-claim-prototype.json']}}
(base/'work/checks/tree-laws-canonical-review-preparation.json').write_text(json.dumps(d,indent=2)+'\n')
print('Exact six candidate bodies match eight frozen fragments; old288 unchanged; prepared58 declarations and20 consumers.')
