from pathlib import Path
from hashlib import sha256
import json,re
base=Path(__file__).resolve().parents[2]
def load(p):return json.loads((base/p).read_text())
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
p=load('work/checks/nearfar-helper-canonical-review-preparation.json');m=load(p['port_manifest']);ports={}
for dest,v in p['ports'].items():
 assert (base/dest).read_bytes()==(base/v['candidate']).read_bytes() and sha(dest)==v['candidate_sha256']
 blocks=[]
 for f in v['source_fragments']:
  assert sha(f['source'])==f['source_sha256'];blocks.append((base/f['source']).read_text())
 s=(base/dest).read_text();assert s[s.index('namespace SM'):]== '\n'.join(blocks)
 ports[dest]=dict(v,installed_module_sha256=sha(dest),installed_equals_candidate=True)
assert all(sha('work/lean/'+f)==h for f,h in m['prior_SM_files_sha256'].items())
assert sha('work/lean/lean-declarations.json')==m['prior_map_sha256']
current={str(f.relative_to(base)):sha(str(f.relative_to(base))) for f in sorted((base/'work/lean/SM').glob('*.lean'))}
assert len(current)==307 and set(current)=={'work/lean/'+f for f in m['prior_SM_files_sha256']}|set(ports)
def closure(root):
 seen={}
 def visit(n):
  if n in seen:return
  f='work/lean/'+n.replace('.','/')+'.lean';seen[n]=f
  for q in re.findall(r'^import (\S+)',(base/f).read_text(),re.M):
   if q.startswith('SM.'):visit(q)
 visit(root);return {seen[n]:sha(seen[n]) for n in sorted(seen)}
cl={}
individual={}
for root in p['SM_import_roots']:
 individual[root]=closure(root);cl.update(individual[root])
assert len(cl)==20
for n,v in p['predicted_import_closure'].items():assert sha(v['canonical'])==v['sha256']
sup=(base/'work/lean/Supplemental.lean').read_bytes();cuts=[k for k in range(1,300) if sha256(sup[:-k]).hexdigest()==m['prior_Supplemental_sha256']];assert len(cuts)==1
delta=sup[-cuts[0]:].decode();added=re.findall(r'^import (\S+)',delta,re.M)
assert set(added)=={'SM.GeometricNearFar','SM.NearFarCutExpansion','SM.MarkedRefinement','SM.InteriorCutIndex'} and len(added)==4
out={'ports':ports,'prior_SM_count':299,'all_299_prior_SM_unchanged':True,'canonical_SM_count':307,'canonical_SM_files_sha256':current,
 'SM_import_roots':p['SM_import_roots'],'SM_closure_files_sha256':cl,'SM_closure_count':20,'individual_import_closures':individual,
 'Supplemental_append':delta,'Supplemental_sha256':sha('work/lean/Supplemental.lean'),'source_map_unchanged':True,'source_map_sha256':sha('work/lean/lean-declarations.json'),
 'port_manifest':p['port_manifest'],'port_manifest_sha256':sha(p['port_manifest']),'port_installation':'work/checks/nearfar-helper-port-installed.json','port_installation_sha256':sha('work/checks/nearfar-helper-port-installed.json'),
 'checked_declarations':p['checked_declarations'],'additional_examples':p['additional_examples'],'trace':p['trace'],'trace_sha256':sha(p['trace']),
 'scope':'Eight helpers only; all source rows unchanged, no new original acceptance and full farout unaccepted.'}
(base/'work/checks/nearfar-helper-canonical-review-closure.json').write_text(json.dumps(out,indent=2)+'\n')
print('Installed eight exact bodies; all299 old files and declaration map unchanged;307 total;20-module actual closure;4 expected Supplemental imports.')
