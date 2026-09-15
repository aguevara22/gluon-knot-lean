from pathlib import Path
from hashlib import sha256
import json,re
base=Path(__file__).resolve().parents[2]
def load(p):return json.loads((base/p).read_text())
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
m=load('work/checks/nearfar-port-preparation.json');old=load('work/checks/nearfar-inverse-review-closure.json');ports={}
for dest,v in m['new_modules'].items():
 assert sha(v['candidate'])==v['candidate_sha256'];blocks=[]
 for f in v['source_fragments']:
  assert sha(f['source'])==f['source_sha256'];blocks.append((base/f['source']).read_text())
 s=(base/v['candidate']).read_text();assert s[s.index('namespace SM'):]== '\n'.join(blocks)
 ports[dest]=dict(v,fragment_bodies_byte_for_byte_equal=True,imports=re.findall(r'^import (\S+)',s,re.M))
assert all(sha('work/lean/'+p)==h for p,h in m['prior_SM_files_sha256'].items())
names=old['checked_declarations'];examples=old['additional_examples'];assert len(names)==37 and len(examples)==11
t='import SM.TriangularPolynomial\n\nset_option pp.fullNames true\nset_option pp.universes false\n\n'
t+='\n'.join('#check '+n+'\n#print axioms '+n for n in names)+'\n'
t+='\n'.join('#print '+n for n in old['transparent_definitions_printed'])+'\n'
t+=(base/old['examples']).read_text()+'\n'+'\n'.join('#print axioms '+n for n in examples)+'\n'
trace='work/checks/nearfar-canonical-review-types.lean';(base/trace).write_text(t)
new={p.replace('work/lean/','')[:-5].replace('/','.'):v['candidate'] for p,v in m['new_modules'].items()}
def closure(root):
 seen={}
 def visit(n):
  if n in seen:return
  p=new.get(n,'work/lean/'+n.replace('.','/')+'.lean');seen[n]=p
  for q in re.findall(r'^import (\S+)',(base/p).read_text(),re.M):
   if q.startswith('SM.'):visit(q)
 visit(root);return sorted(seen)
closures={n:closure(n) for n in ['SM.NearFar','SM.TriangularPolynomial']}
assert [len(v) for v in closures.values()]==[7,11]
d={'state':'exact five candidate body comparison and canonical trace complete; installation, audit and independent kernel pending',
 'port_manifest':'work/checks/nearfar-port-preparation.json','port_manifest_sha256':sha('work/checks/nearfar-port-preparation.json'),
 'ports':ports,'prior_SM_count':294,'all_294_prior_SM_unchanged':True,'checked_declarations':names,'additional_examples':examples,
 'transparent_definitions_printed':old['transparent_definitions_printed'],'trace':trace,'trace_sha256':sha(trace),
 'predicted_import_closures':closures,'external_review_binding':{p:sha(p) for p in ['work/reviews/nearfar-prototype.json','work/reviews/triangular-polynomial-inverse-prototype.json']},
 'scope':'Only def:nearfar may be accepted. The canonical inverse helpers remain partial farout(i) evidence and cannot accept full farout.'}
(base/'work/checks/nearfar-canonical-review-preparation.json').write_text(json.dumps(d,indent=2)+'\n')
print('Exact five candidates match six body fragments; old294 unchanged;37 declarations/11 consumers; predicted7/11 SM closures.')
