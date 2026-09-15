from pathlib import Path
from hashlib import sha256
import re,json
base=Path(__file__).resolve().parents[2]
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def load(p):return json.loads((base/p).read_text())
old=load('work/checks/boundary-gate-stability-review-preparation.json')
order=['BoundaryTripleSupports','CriticalContractionPositions','CriticalContractionBounds','ContractedGeometricWord',
 'ContractedIntervals','ContractedCompositions','OffLeafContraction','ContractedGeometricArray','UniqueChangingChild','ContractedChildResponse']
new=['OffLeafContraction','ContractedGeometricArray','ContractedChildResponse'];receipts={};files={};bybody={}
for n in order:
 receipt_name='CriticalContractionBounds' if n=='CriticalContractionPositions' else n
 f='work/checks/'+receipt_name+'-prototype-result.json';r=load(f);assert r['exit_code']==0
 for p,h in r['files_sha256'].items():assert sha(p)==h,(n,p);files[p]=h
 assert (base/('work/checks/'+n+'.body.lean')).read_text() in (base/('work/checks/'+receipt_name+'.prototype.lean')).read_text()
 receipts[f]=sha(f)
 if n in new:bybody[n]=r['printed_declarations']
names=sum(bybody.values(),[]);assert len(names)==len(set(names))==19
roots=old['SM_import_roots'];closure=old['SM_closure_files_sha256']
for f,h in closure.items():assert sha(f)==h
for f,h in old['all_327_canonical_SM_files_sha256'].items():assert sha(f)==h
ef='work/checks/off-leaf-contraction-review-examples.lean'
examples=['OffLeafContractionIndependentReview.'+n for n in re.findall(r'^theorem (\S+)',(base/ef).read_text(),re.M)]
assert len(examples)==19,len(examples)
transparent=['SM.IncreasingBoundaryTriple.erasedInteriorCount','SM.IncreasingBoundaryTriple.contractedSize',
 'SM.IncreasingBoundaryTriple.expandPosition','SM.IncreasingBoundaryTriple.contractPosition',
 'SM.IncreasingBoundaryTriple.expandInterval','SM.IncreasingBoundaryTriple.expandTriple','SM.IncreasingBoundaryTriple.contractedLeaf',
 'SM.IntervalComposition.expandComposition','SM.IntervalComposition.contractComposition','SM.IntervalComposition.SurvivingCuts',
 'SM.IntervalComposition.offLeafCompositionEquiv','SM.IntervalComposition','SM.IntervalComposition.part',
 'SM.IntervalComposition.nearFarWeight','SM.nearFarTransform','SM.triangularTransform','SM.farOnlyCoordinates','SM.farOnlyOutput',
 'SM.boundaryUnitArray','SM.contractedTripleArray','SM.contractedVertexIndex','SM.contractedWordTuple','SM.geometricBoundaryArray']
support=['SM.IntervalComposition.part_leaves_lt','SM.IntervalComposition.part_bounds','SM.IntervalComposition.expandComposition_part',
 'SM.IntervalComposition.expandComposition_nearTriple','SM.IntervalComposition.expandComposition_farTriple',
 'SM.IncreasingBoundaryTriple.expandInterval_contains','SM.IncreasingBoundaryTriple.expandPosition_strict',
 'SM.IntervalComposition.containingCompositionEquiv','SM.IntervalComposition.child_product_difference',
 'SM.IntervalComposition.other_part_excludes','SM.nearFarTransform_eq_triangular','SM.farOnlyCoordinates_equation',
 'SM.contractedWord_G1','SM.contractedWord_physical_root','SM.IncreasingBoundaryTriple.contractedSize_of_proper']
s=''.join('import '+m+'\n' for m in roots)+'import Mathlib.Tactic\n\nset_option maxRecDepth 10000\nset_option maxHeartbeats 12000000\nset_option pp.universes false\n\n'
for n in order:s+=(base/('work/checks/'+n+'.body.lean')).read_text()+'\n'
s+=(base/ef).read_text()+'\n'
for n in names:s+='#check '+n+'\n#print axioms '+n+'\n'
for n in transparent:s+='#print '+n+'\n'
for n in support:s+='#check '+n+'\n'
for n in examples:s+='#print axioms '+n+'\n'
tf='work/checks/off-leaf-contraction-review-types.lean';(base/tf).write_text(s)
bindings=dict(old['prior_checkpoint_bindings_sha256'])
for f in ['work/reviews/boundary-gate-stability-prototype.json','work/reviews/contracted-geometric-word-independent.json',
 'work/reviews/critical-contraction-child-independent.json']:
 d=load(f)
 for x,h in d.get('files_sha256',{}).items():assert sha(x)==h
 bindings[f]=sha(f)
p={'state':'prepared, independent kernel pending; fresh interval/composition27 review to bind before sealing',
 'source_id':'thm:single-triple','source':old['source'],'source_lines':'319-354, especially345-347; contracted geometric output361-364',
 'sources_sha256':old['sources_sha256'],'body_order':order,'new_body_order':new,'checked_declarations':names,
 'checked_declarations_by_body':bybody,'additional_examples':examples,'transparent_definitions_printed':transparent,
 'supporting_types_printed':support,'trace':tf,'trace_sha256':sha(tf),'example_file':ef,'example_file_sha256':sha(ef),
 'SM_import_roots':roots,'SM_closure_files_sha256':closure,'SM_closure_count':len(closure),
 'all_327_canonical_SM_files_sha256':old['all_327_canonical_SM_files_sha256'],'root_receipts_sha256':receipts,
 'root_files_sha256':files,'prior_checkpoint_bindings_sha256':bindings,
 'scope':'OffLeafContraction10 establishes actual recursive off-leaf inverse transport; ContractedGeometricArray6 identifies actual contracted geometry, formal leaf and proper root output; ContractedChildResponse3 proves an explicit conditional product step and zero nonsurviving differences. No completed propagation or original source acceptance.'}
(base/'work/checks/off-leaf-contraction-review-preparation.json').write_text(json.dumps(p,indent=2)+'\n')
print('Prepared19 new declarations+19 consumers;10 exact bodies;54 canonical dependency modules;327 preserved canonical files. No kernel launched.')
