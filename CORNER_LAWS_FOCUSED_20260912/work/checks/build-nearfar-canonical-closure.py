from pathlib import Path
from hashlib import sha256
import json,re
base=Path(__file__).resolve().parents[2]
def load(p):return json.loads((base/p).read_text())
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
m=load('work/checks/nearfar-port-preparation.json');p=load('work/checks/nearfar-canonical-review-preparation.json');ports={}
for dest,v in m['new_modules'].items():
 assert (base/dest).read_bytes()==(base/v['candidate']).read_bytes() and sha(dest)==v['candidate_sha256']
 blocks=[]
 for f in v['source_fragments']:
  assert sha(f['source'])==f['source_sha256'];blocks.append((base/f['source']).read_text())
 s=(base/dest).read_text();assert s[s.index('namespace SM'):]== '\n'.join(blocks)
 ports[dest]=dict(p['ports'][dest],installed_module_sha256=sha(dest),installed_equals_candidate=True)
assert all(sha('work/lean/'+f)==h for f,h in m['prior_SM_files_sha256'].items())
current={str(f.relative_to(base)):sha(str(f.relative_to(base))) for f in sorted((base/'work/lean/SM').glob('*.lean'))}
assert len(current)==299 and set(current)=={'work/lean/'+f for f in m['prior_SM_files_sha256']}|set(ports)
def closure(root):
 seen={}
 def visit(n):
  if n in seen:return
  f='work/lean/'+n.replace('.','/')+'.lean';seen[n]=f
  for q in re.findall(r'^import (\S+)',(base/f).read_text(),re.M):
   if q.startswith('SM.'):visit(q)
 visit(root);return {seen[n]:sha(seen[n]) for n in sorted(seen)}
cl=closure('SM.TriangularPolynomial');definition=closure('SM.NearFar');assert len(cl)==11 and len(definition)==7
sup=(base/'work/lean/Supplemental.lean').read_bytes();cuts=[k for k in range(1,150) if sha256(sup[:-k]).hexdigest()==m['prior_Supplemental_sha256']];assert len(cuts)==1
delta=sup[-cuts[0]:].decode();assert re.findall(r'^import (\S+)',delta,re.M)==['SM.TriangularPolynomial']
d={'ports':ports,'prior_SM_count':294,'all_294_prior_SM_unchanged':True,'canonical_SM_count':299,'canonical_SM_files_sha256':current,
 'SM_import_roots':['SM.TriangularPolynomial'],'SM_closure_files_sha256':cl,'SM_closure_count':11,
 'definition_import_closure':definition,'definition_import_closure_count':7,'sole_Supplemental_append':delta,'Supplemental_sha256':sha('work/lean/Supplemental.lean'),
 'port_manifest':'work/checks/nearfar-port-preparation.json','port_manifest_sha256':sha('work/checks/nearfar-port-preparation.json'),
 'port_installation':'work/checks/nearfar-port-installed.json','port_installation_sha256':sha('work/checks/nearfar-port-installed.json'),
 'checked_declarations':p['checked_declarations'],'additional_examples':p['additional_examples'],'trace':p['trace'],'trace_sha256':sha(p['trace']),
 'scope':'Only def:nearfar source acceptance; inverse helpers remain partial farout evidence.'}
(base/'work/checks/nearfar-canonical-review-closure.json').write_text(json.dumps(d,indent=2)+'\n')
print('Installed exact five ports; old294 unchanged;299 total; exact7 definition and11 combined SM closures.')
