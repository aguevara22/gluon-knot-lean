from pathlib import Path
from hashlib import sha256
import re,json
base=Path(__file__).resolve().parents[2]
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def load(p):return json.loads((base/p).read_text())
order=['CollinearGateSigns','BoundaryGateSigns','BoundaryTripleSupports','FarOnlyOutputLocality','BoundaryArrayStability']
receipts={};files={};bybody={}
for n in order:
 f='work/checks/'+n+'-prototype-result.json';r=load(f)
 assert r['exit_code']==0 and r['first_run_passed']
 for p,h in r['files_sha256'].items():assert sha(p)==h;files[p]=h
 assert (base/('work/checks/'+n+'.body.lean')).read_text() in (base/('work/checks/'+n+'.prototype.lean')).read_text()
 receipts[f]=sha(f);bybody[n]=r['printed_declarations']
names=sum(bybody.values(),[]);assert len(names)==len(set(names))==27
roots=['SM.CriticalSourceResponse','SM.FiniteChiStability']
closure={}
def visit(m):
 f='work/lean/'+m.replace('.','/')+'.lean'
 if f in closure:return
 assert (base/f).is_file(),f
 closure[f]=sha(f)
 for i in re.findall(r'^import\s+(\S+)',(base/f).read_text(),re.M):
  if i.startswith('SM.'):visit(i)
for m in roots:visit(m)
ef='work/checks/boundary-gate-stability-review-examples.lean'
examples=['BoundaryGateStabilityIndependentReview.'+n for n in re.findall(r'^theorem (\S+)',(base/ef).read_text(),re.M)]
assert len(examples)==19,len(examples)
transparent=['SM.pointFarSign','SM.wallLeftEpsilon','SM.wallRightEpsilon','SM.IncreasingBoundaryTriple',
 'SM.IncreasingBoundaryTriple.positionSet','SM.IncreasingBoundaryTriple.vertexSet','SM.boundaryIndex',
 'SM.boundaryWord','SM.geometricBoundaryArray','SM.PointZeroTriple','SM.pointZeroTriples','SM.chi',
 'SM.farOnlyCoordinates','SM.farOnlyOutput','SM.farTransform','SM.nearFarTransform',
 'SM.IntervalComposition.nearFarWeight','SM.BoundaryInterval','SM.IncreasingBoundaryTriple.leftInterval',
 'SM.IncreasingBoundaryTriple.rightInterval']
support=['SM.boundaryIndex_injective','SM.chi_nonzero_outside_singleton','SM.chi_locally_constant_of_ne_zero',
 'SM.finite_nonzero_chi_persists','SM.farOnlyCoordinates_local','SM.farOnlyCoordinates_unchanged_off_critical',
 'SM.IntervalComposition.part_bounds']
s=''.join('import '+m+'\n' for m in roots)+'import Mathlib.Tactic\n\nset_option maxRecDepth 10000\nset_option maxHeartbeats 12000000\nset_option pp.universes false\n\n'
for n in order:s+=(base/('work/checks/'+n+'.body.lean')).read_text()+'\n'
s+=(base/ef).read_text()+'\n'
for n in names:s+='#check '+n+'\n#print axioms '+n+'\n'
for n in transparent:s+='#print '+n+'\n'
for n in support:s+='#check '+n+'\n'
for n in examples:s+='#print axioms '+n+'\n'
tf='work/checks/boundary-gate-stability-review-types.lean';(base/tf).write_text(s)
sources={f:sha(f) for f in ['reference/SM/sm-2-amplitude.tex','reference/SM/sm-1-polygons.tex']}
prior={f:sha(f) for f in ['work/reviews/critical-response-port.json','work/reviews/critical-source-response-canonical-partial.json',
 'work/reviews/single-triple-n3-domain-note.json','work/checks/checkpoint-070-output.json',
 'work/checks/checkpoint-070-declaration-audit.json','work/checks/checkpoint-070-lean-check.log']}
allsm={str(f.relative_to(base)):sha(str(f.relative_to(base))) for f in sorted((base/'work/lean/SM').glob('*.lean'))}
assert len(allsm)==327
p={'state':'prepared, independent kernel pending','source_id':'thm:single-triple','source':'reference/SM/sm-2-amplitude.tex',
 'source_lines':'229-244,271-283,290-301','sources_sha256':sources,'body_order':order,'checked_declarations':names,
 'checked_declarations_by_body':bybody,'additional_examples':examples,'transparent_definitions_printed':transparent,
 'supporting_types_printed':support,'trace':tf,'trace_sha256':sha(tf),'example_file':ef,'example_file_sha256':sha(ef),
 'SM_import_roots':roots,'SM_closure_files_sha256':closure,'SM_closure_count':len(closure),
 'all_327_canonical_SM_files_sha256':allsm,'root_receipts_sha256':receipts,'root_files_sha256':files,
 'prior_checkpoint_bindings_sha256':prior,'scope':'Five frozen external bodies,27 declarations,19 independent consumers. Actual supports and noncritical common-neighborhood geometric stability, far-output locality, exact collinear epsilon identities. No full wall theorem or later wall-radius/gap-value/propagation bodies reviewed.'}
(base/'work/checks/boundary-gate-stability-review-preparation.json').write_text(json.dumps(p,indent=2)+'\n')
print('Prepared27 declarations+19 consumers;',len(closure),'canonical SM dependency modules;327 canonical files bound; no kernel launched.')
