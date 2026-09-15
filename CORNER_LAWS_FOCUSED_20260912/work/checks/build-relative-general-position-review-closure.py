from pathlib import Path
import re,json,hashlib
base=Path(__file__).resolve().parents[2]; chk=base/'work/checks'; sm=base/'work/lean/SM'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rel(p):return str(p.relative_to(base))
def imps(p):return re.findall(r'^import (\S+)',p.read_text(),re.M)
p=chk/'RelativeGeneralPosition.prototype.lean';roots=[x for x in imps(p) if x.startswith('SM.')];seen={}
def visit(m):
 if m in seen:return
 f=base/'work/lean'/Path(m.replace('.','/')+'.lean');seen[m]=f
 for x in imps(f):
  if x.startswith('SM.'):visit(x)
for m in roots:visit(m)
prior=json.loads((chk/'relgp-port-preparation.json').read_text())['prior_SM_files_sha256']
actual={rel(p):sha(p) for p in sorted(sm.glob('*.lean'))}
assert set(actual)=={'work/lean/'+k for k in prior}
prior_valid=all(sha(base/'work/lean'/k)==v for k,v in prior.items());assert prior_valid
full=p.read_text().split('\n#print axioms SM.RelativeGeneralPositionPath')[0]
trace=(chk/'relative-general-position-review-types.lean').read_text();assert trace.startswith(full)
pins={rel(p):sha(p) for p in [base/'work/lean/lean-toolchain',base/'work/lean/lake-manifest.json']}
files=['RegularWallKinds.body.lean','RegularWallKinds.prototype.lean','RelativeGeneralPosition.body.lean','RelativeGeneralPosition.prototype.lean','PointControlGeometry.prototype.lean','PointControlWalls.body.lean','PointControlWalls.prototype.lean','ConcurrenceOrder.prototype.lean']
support=['global-event-port','single-control-centers-port','point-control-geometry-prototype','point-control-walls-prototype','concurrence-order-prototype']
d={'prototype':rel(p),'prototype_sha256':sha(p),'root_imports':roots,'SM_closure_count':len(seen),'SM_closure_files_sha256':{rel(seen[m]):sha(seen[m]) for m in sorted(seen)},'canonical_SM_count':len(actual),'all_canonical_SM_files_sha256':actual,'all_280_prior_frozen_SM_hashes_verified':prior_valid,'pin_files_sha256':pins,'source_sha256':sha(base/'reference/SM/sm-1-polygons.tex'),'external_inputs_sha256':{rel(chk/f):sha(chk/f) for f in files},'inherited_review_hashes':{rel(base/'work/reviews'/(f+'.json')):sha(base/'work/reviews'/(f+'.json')) for f in support},'full_prototype_mathematical_prefix_unchanged_in_trace':True,'prototype_body_extraction':'Entire prototype before final #print axioms SM.RelativeGeneralPositionPath; copied byte-for-byte, no implementation edits.'}
(chk/'relative-general-position-review-closure.json').write_text(json.dumps(d,indent=2)+'\n')
print('SM closure',len(seen),'current',len(actual),'prior matches',prior_valid)
