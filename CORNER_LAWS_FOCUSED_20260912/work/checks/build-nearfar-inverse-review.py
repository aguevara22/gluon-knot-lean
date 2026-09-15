from pathlib import Path
from hashlib import sha256
import json,re
base=Path(__file__).resolve().parents[2]
def load(p):return json.loads((base/p).read_text())
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
groups={
 'NearFar':['IncreasingBoundaryTriple','TripleArray','IntervalArray','IntervalComposition.nearTriple','IntervalComposition.farTriple','IntervalComposition.nearFarWeight','nearFarTransform','farTransform','nearTransform','boundaryUnitArray','geometricBoundaryArray','geometricBoundaryArray_near','geometricBoundaryArray_far','nearfarData'],
 'UnaryComposition':['IntervalComposition.eq_single_of_parts_eq_one','IntervalComposition.parts_eq_one_iff_eq_single','IntervalComposition.single_part','IntervalComposition.single_product','IntervalComposition.nonSingleEquiv'],
 'TriangularInverse':['triangularTransform','triangularInverse','triangularTransform_inverse','triangularInverse_transform_apply','triangularInverse_transform','triangular_solution_unique','triangularEquiv'],
 'NearFarTriangular':['IntervalComposition.nearFarWeight_one','nearFarTransform_eq_triangular','nearFarInverse','nearFarTransform_inverse','nearFarInverse_transform','nearFar_solution_unique'],
 'TriangularPolynomial':['map_triangularInverse','triangularInversePolynomial','triangularInversePolynomial_eval','nearFar_has_polynomial_inverse'],
 'NearFarEquivariance':['geometricBoundaryArray_shift']}
roots=['SM.Gates','SM.FiniteCompositions']
t=''.join('import '+n+'\n' for n in roots)+'import Mathlib.Tactic\nimport Mathlib.Algebra.MvPolynomial.Eval\n\nset_option pp.fullNames true\nset_option pp.universes false\n\n'
names=[];files={};receipts={}
for m,decls in groups.items():
 receipt='work/checks/'+m+'-prototype-result.json';d=load(receipt)
 assert d.get('exit_code',d.get('subprocess_exit_code'))==0
 for p,h in d['files_sha256'].items():assert sha(p)==h;files[p]=h
 receipts[receipt]=sha(receipt)
 body='work/checks/'+m+'.body.lean';prototype='work/checks/'+m+'.prototype.lean'
 assert (base/prototype).read_text().count((base/body).read_text())==1
 t+=(base/body).read_text()+'\n';new=['SM.'+n for n in decls];names+=new
 t+='\n'.join('#check '+n+'\n#print axioms '+n for n in new)+'\n'
transparent=['SM.IncreasingBoundaryTriple','SM.TripleArray','SM.IntervalArray','SM.IntervalComposition.nearTriple','SM.IntervalComposition.farTriple','SM.IntervalComposition.nearFarWeight','SM.nearFarTransform','SM.farTransform','SM.nearTransform','SM.boundaryUnitArray','SM.geometricBoundaryArray','SM.nearfarData','SM.triangularTransform','SM.triangularInverse','SM.nearFarInverse','SM.triangularInversePolynomial']
t+='\n'.join('#print '+n for n in transparent)+'\n'
ep='work/checks/nearfar-inverse-review-examples.lean';e=(base/ep).read_text();ex=['NearFarInverseIndependentReview.'+n for n in re.findall(r'^theorem (\w+)',e,re.M)]
t+=e+'\n'+'\n'.join('#print axioms '+n for n in ex)+'\n';tp='work/checks/nearfar-inverse-review-types.lean';(base/tp).write_text(t)
seen={}
def visit(n):
 if n in seen:return
 p='work/lean/'+n.replace('.','/')+'.lean';seen[n]=p
 for q in re.findall(r'^import (\S+)',(base/p).read_text(),re.M):
  if q.startswith('SM.'):visit(q)
for n in roots:visit(n)
c={'state':'prepared; independent kernel pending','checked_declarations':names,'additional_examples':ex,
 'frozen_prototype_body_and_root_log_sha256':files,'root_receipts_sha256':receipts,
 'trace':tp,'trace_sha256':sha(tp),'examples':ep,'examples_sha256':sha(ep),
 'transparent_definitions_printed':transparent,'SM_import_roots':roots,'SM_closure_files_sha256':{seen[n]:sha(seen[n]) for n in sorted(seen)},
 'canonical_SM_files_sha256':{str(p.relative_to(base)):sha(str(p.relative_to(base))) for p in sorted((base/'work/lean/SM').glob('*.lean'))},
 'source':'reference/SM/sm-2-amplitude.tex','source_sha256':sha('reference/SM/sm-2-amplitude.tex'),
 'scope':'Full def:nearfar including geometric shift; ONLY two-sided polynomial inverse portion of lem:farout(i). No factorization, geometric output, restricted-interval clauses or full farout acceptance.'}
(base/'work/checks/nearfar-inverse-review-closure.json').write_text(json.dumps(c,indent=2)+'\n')
print('Prepared',len(names),'declarations and',len(ex),'consumer checks; actual SM closure',len(seen))
