from pathlib import Path
from hashlib import sha256
import json,re
base=Path(__file__).resolve().parents[2]
def sha(f):return sha256((base/f).read_bytes()).hexdigest()
def load(f):return json.loads((base/f).read_text())
mfile='work/checks/critical-response-port-preparation.json';m=load(mfile);ports={}
assert len(m['prior_SM_files_sha256'])==319
assert all(sha('work/lean/'+f)==h for f,h in m['prior_SM_files_sha256'].items())
assert sha('work/lean/lean-declarations.json')==m['prior_map_sha256']
for dest,v in m['new_modules'].items():
 assert sha(v['source_body'])==v['source_body_sha256']
 assert sha(v['root_receipt'])==v['root_receipt_sha256']
 assert sha(dest)==sha(v['candidate'])==v['candidate_sha256']
 s=(base/dest).read_text();assert s[s.index('namespace SM'):]==(base/v['source_body']).read_text()
 assert re.findall(r'^import (\S+)',s,re.M)==v['imports']
 ports[dest]=dict(v,installed_equals_candidate=True,namespace_body_byte_for_byte_equal=True)
assert len(ports)==8
current={str(f.relative_to(base)):sha(str(f.relative_to(base))) for f in sorted((base/'work/lean/SM').glob('*.lean'))}
assert len(current)==327 and set(current)=={'work/lean/'+f for f in m['prior_SM_files_sha256']}|set(ports)
seen={}
def visit(n):
 if n in seen:return
 f='work/lean/'+n.replace('.','/')+'.lean';seen[n]=f
 for q in re.findall(r'^import (\S+)',(base/f).read_text(),re.M):
  if q.startswith('SM.'):visit(q)
visit('SM.CriticalSourceResponse');cl={seen[n]:sha(seen[n]) for n in sorted(seen)};assert len(cl)==40
sup=(base/'work/lean/Supplemental.lean').read_bytes();cuts=[k for k in range(1,100) if sha256(sup[:-k]).hexdigest()==m['prior_Supplemental_sha256']];assert len(cuts)==1
delta=sup[-cuts[0]:].decode();assert re.findall(r'^import (\S+)',delta,re.M)==['SM.CriticalSourceResponse']
p=load('work/checks/critical-source-review-preparation.json');names=p['checked_declarations'];examples=p['additional_examples']
assert len(names)==53 and len(examples)==41
s='import SM.CriticalSourceResponse\nimport Mathlib.Tactic\n\nset_option maxRecDepth 10000\nset_option maxHeartbeats 12000000\nset_option pp.universes false\n\n'
for f,h in p['example_files_sha256'].items():assert sha(f)==h;s+=(base/f).read_text()+'\n'
for n in names:s+='#check '+n+'\n#print axioms '+n+'\n'
for n in p['transparent_definitions_printed']:s+='#print '+n+'\n'
for n in examples:s+='#print axioms '+n+'\n'
tf='work/checks/critical-source-canonical-review-types.lean';(base/tf).write_text(s)
binding=dict(p['inherited_review_binding'])
for f in ['work/reviews/critical-source-response-prototype.json','work/checks/critical-source-reviewed-types.json','work/reviews/critical-inverse-difference-independent.json','work/reviews/single-triple-n3-domain-note.json']:binding[f]=sha(f)
out={'state':'installed exact ports and canonical trace prepared; audit070 and independent kernel pending','port_manifest':mfile,'port_manifest_sha256':sha(mfile),'port_installation':'work/checks/critical-response-port-installed.json','port_installation_sha256':sha('work/checks/critical-response-port-installed.json'),'ports':ports,'prior_SM_count':319,'all_319_prior_SM_unchanged':True,'canonical_SM_count':327,'canonical_SM_files_sha256':current,'SM_import_roots':['SM.CriticalSourceResponse'],'SM_closure_files_sha256':cl,'SM_closure_count':40,'Supplemental_append':delta,'Supplemental_sha256':sha('work/lean/Supplemental.lean'),'source_map_unchanged':True,'source_map_sha256':sha('work/lean/lean-declarations.json'),'checked_declarations':names,'additional_examples':examples,'transparent_definitions_printed':p['transparent_definitions_printed'],'trace':tf,'trace_sha256':sha(tf),'external_review_binding':binding,'scope':'Eight algebraic wall-response helpers only; no original-source map or acceptance changes. Geometric wall theorem, epsilon identification and propagation remain incomplete.'}
(base/'work/checks/critical-response-canonical-review-preparation.json').write_text(json.dumps(out,indent=2)+'\n')
print('Eight exact installed bodies;319 old unchanged;327total;40-module actual closure;map unchanged;53types+41consumers prepared; no kernel.')
