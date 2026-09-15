from pathlib import Path
from hashlib import sha256
import re,json
base=Path(__file__).resolve().parents[2]
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def load(p):return json.loads((base/p).read_text())
old=load('work/checks/refinement-transport-review-preparation.json')
order=old['body_order']+['RefinedInterior','RefinedOuter','RefinedWeights','NearFarFactorization','FarOnlyOutput'];new=order[4:]
extra={'RefinedInterior':['SM.IntervalComposition.RefinementUnmarked','SM.IntervalComposition.refinedInteriorIndex','SM.IntervalComposition.refinedUnmarkedIndex'],'RefinedOuter':['SM.IntervalComposition.RefinementMarked','SM.IntervalComposition.refinedOuterIndex','SM.IntervalComposition.refinedMarkedIndex'],'RefinedWeights':['SM.IntervalComposition.refinementMarks','SM.IntervalComposition.refinementMarkIndices']}
extra.update({'NearFarFactorization':['SM.IntervalComposition.nestedSummand','SM.IntervalComposition.markedSummand'],'FarOnlyOutput':['SM.farOnlyCoordinates','SM.farOnlyOutput']})
files={};receipts={};names=dict(old['checked_declarations_by_body'])
for n in order:
 f='work/checks/'+n+'-prototype-result.json';d=load(f);assert d.get('exit_code',d.get('subprocess_exit_code'))==0
 for p,h in d['files_sha256'].items():assert sha(p)==h;files[p]=h
 receipts[f]=sha(f)
 assert (base/('work/checks/'+n+'.body.lean')).read_text() in (base/('work/checks/'+n+'.prototype.lean')).read_text()
 if n in new:names[n]=extra[n]+d['printed_declarations']
allnames=[x for n in order for x in names[n]];assert len(set(allnames))==len(allnames)==93
newnames=[x for n in new for x in names[n]];assert len(newnames)==52
transparent=old['transparent_definitions_printed']+[x for n in new for x in extra[n]]+['SM.IntervalComposition.refinedUnmarkedEquiv','SM.IntervalComposition.refinedMarkedEquiv']
ef='work/checks/refined-weights-review-examples.lean';examples=old['additional_examples']+['RefinedWeightsIndependentReview.'+n for n in re.findall(r'^theorem (\S+)',(base/ef).read_text(),re.M)];factor_examples='work/checks/nearfar-factorization-review-examples.lean'
examples+=['NearFarFactorizationIndependentReview.'+n for n in re.findall(r'^theorem (\S+)',(base/factor_examples).read_text(),re.M)];assert len(examples)==30
imports=['SM.MarkedRefinement','SM.InteriorCutIndex','SM.GeometricNearFar','SM.NearFarCutExpansion','SM.TriangularPolynomial','Mathlib.Data.Fintype.Powerset','Mathlib.Tactic']
s='\n'.join('import '+n for n in imports)+'\n\nset_option maxRecDepth 10000\nset_option maxHeartbeats 12000000\nset_option pp.universes false\n\n'
for n in order:s+=(base/('work/checks/'+n+'.body.lean')).read_text()+'\n'
for f in [old['examples'],ef,factor_examples]:s+=(base/f).read_text()+'\n'
for n in allnames:s+='#check '+n+'\n#print axioms '+n+'\n'
for n in transparent:s+='#print '+n+'\n'
for n in examples:s+='#print axioms '+n+'\n'
tf='work/checks/refined-weights-review-types.lean';(base/tf).write_text(s)
seen={}
def visit(n):
 if n in seen:return
 f='work/lean/'+n.replace('.','/')+'.lean';seen[n]=f
 for q in re.findall(r'^import (\S+)',(base/f).read_text(),re.M):
  if q.startswith('SM.'):visit(q)
for n in imports:
 if n.startswith('SM.'):visit(n)
cl={seen[n]:sha(seen[n]) for n in sorted(seen)}
binding=dict(old['inherited_review_binding'])
for f in ['work/reviews/refinement-transport-prototype.json','work/checks/refinement-transport-reviewed-types.json',old['examples']]:binding[f]=sha(f)
d={'status':'prepared; independent kernel not yet run','source':old['source'],'source_sha256':sha(old['source']),'source_lines':'Source lemma146-168 and proof170-227: full polynomial-map factorization, all actual coefficients and child products, solution-level far-only output, geometric full-root coefficient and leaf/nonleaf values. Restricted nonleaf word/closing-root identification remains absent.','body_order':order,'new_body_names':new,'root_receipts_sha256':receipts,'root_files_sha256':files,'checked_declarations_by_body':names,'checked_declarations':allnames,'new_checked_declarations':newnames,'transparent_definitions_printed':transparent,'additional_examples':examples,'additional_example_count':30,'factorization_examples':factor_examples,'factorization_examples_sha256':sha(factor_examples),'new_examples':ef,'new_examples_sha256':sha(ef),'previous_examples':old['examples'],'previous_examples_sha256':sha(old['examples']),'trace':tf,'trace_sha256':sha(tf),'SM_import_roots':[n for n in imports if n.startswith('SM.')],'SM_closure_files_sha256':cl,'SM_closure_count':len(cl),'inherited_review_binding':binding,'scope':'Five new external coefficient/factorization/far-only bodies with four frozen predecessors. Full factorization and solution-level output independence are reviewed; restricted-word nonleaf root identification remains absent, so no whole original lem:farout acceptance. Two marking-transport fragments have disclosed reviewer-derived provenance.'}
(base/'work/checks/refined-weights-review-preparation.json').write_text(json.dumps(d,indent=2)+'\n')
print('Prepared93 declarations (52 new)+30 consumers;',len(cl),'canonical dependency modules; no kernel launched.')
