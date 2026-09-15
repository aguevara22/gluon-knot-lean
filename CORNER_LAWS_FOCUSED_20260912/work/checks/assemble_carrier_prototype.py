"""Assemble a fresh actual-carrier prototype from exact frozen candidate bodies."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,re
ap=argparse.ArgumentParser();ap.add_argument('stem');ap.add_argument('--deps',nargs='*',default=[]);ap.add_argument('--imports',nargs='*',default=[]);ap.add_argument('--scope',required=True);ap.add_argument('--author',default='/root');a=ap.parse_args()
root=Path(__file__).resolve().parents[2];c=root/'work/checks'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rel(p):return str(p.relative_to(root))
assert re.fullmatch('[A-Za-z][A-Za-z0-9]*',a.stem)
imports=[];bodies=[];receipts=[]
for dep in a.deps:
 rp=c/f'{dep}-prototype-result.json';r=json.loads(rp.read_text());assert r['exit_code']==0 and r['source_claim_acceptance_increment']==0;receipts.append(rp)
 proto=(c/f'{dep}.prototype.lean').read_text()
 for line in re.findall(r'^import .+$',proto,re.M):
  if line not in imports:imports.append(line)
 ordered=[]
 for name,h in r['files_sha256'].items():
  q=root/name;assert sha(q)==h,name
  if name.endswith('.body.lean'):assert proto.count(q.read_text())==1;ordered.append((proto.index(q.read_text()),q))
 for _,q in sorted(ordered):
  if q not in bodies:bodies.append(q)
for name in a.imports:
 assert re.fullmatch('[A-Za-z0-9_.]+',name)
 if 'import '+name not in imports:imports.append('import '+name)
b=c/f'{a.stem}.body.lean';bodies.append(b);src=b.read_text()
assert src.startswith('namespace SM.Carrier\n') and src.rstrip().endswith('end SM.Carrier')
names=['SM.Carrier.'+s for s in re.findall(r'^(?:noncomputable )?(?:theorem|def|abbrev|instance) (\w+)',src,re.M)];assert names and len(names)==len(set(names))
proto='\n'.join(imports)+'\n\n'+'\n\n'.join(p.read_text() for p in bodies)+'\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
p=c/f'{a.stem}.prototype.lean';assert not p.exists();p.write_text(proto)
for kind in ['body','prototype']:
 q=c/f'{a.stem}-first-draft.{kind}.lean';assert not q.exists();q.write_bytes((c/f'{a.stem}.{kind}.lean').read_bytes())
dp=c/f'{a.stem}-body-dependencies.json';assert not dp.exists();dp.write_text(json.dumps([rel(q) for q in bodies],indent=2)+'\n')
paths=bodies+[p,c/f'{a.stem}-first-draft.body.lean',c/f'{a.stem}-first-draft.prototype.lean',dp]+receipts
r={'utc':datetime.now(timezone.utc).isoformat(),'author':a.author,'state':'First authored draft; no kernel run yet.','source_scope':a.scope,'declarations':names,'ordered_body_dependencies':[rel(p) for p in bodies],'files_sha256':{rel(p):sha(p) for p in paths},'source_claim_acceptance_increment':0,'stronger_model_statement_fidelity_approval':False}
q=c/f'{a.stem}-draft-dependency-bindings.json';assert not q.exists();q.write_text(json.dumps(r,indent=2)+'\n')
print(f'Assembled {a.stem}:{len(names)} declarations;{len(bodies)} exact ordered bodies;{len(imports)} imports.')
print(' '.join(p.name.removesuffix('.body.lean') for p in bodies))
