from pathlib import Path
from hashlib import sha256
import re,json
base=Path(__file__).resolve().parents[2]
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def load(p):return json.loads((base/p).read_text())
old=load('work/checks/refined-weights-review-preparation.json')
new=['IntervalRestriction','RestrictedWordRoot','Farout'];order=old['body_order']+new
extra={'IntervalRestriction':['SM.BoundaryInterval.'+n for n in ['globalPosition','localPosition','liftInterval','liftTriple']]+['SM.IntervalComposition.'+n for n in ['liftComposition','lowerComposition']]+['SM.restrictTripleArray','SM.restrictIntervalArray'], 'RestrictedWordRoot':['SM.restrictedWordTuple'],'Farout':[]}
files={};receipts={};names=dict(old['checked_declarations_by_body'])
for n in order:
 f='work/checks/'+n+'-prototype-result.json';d=load(f)
 assert d.get('exit_code',d.get('subprocess_exit_code'))==0
 for p,h in d['files_sha256'].items():assert sha(p)==h;files[p]=h
 receipts[f]=sha(f)
 assert (base/('work/checks/'+n+'.body.lean')).read_text() in (base/('work/checks/'+n+'.prototype.lean')).read_text()
 if n in new:names[n]=extra[n]+d['printed_declarations']
allnames=[x for n in order for x in names[n]];assert len(set(allnames))==len(allnames)==127
newnames=[x for n in new for x in names[n]];assert len(newnames)==34
transparent=old['transparent_definitions_printed']+[x for n in new for x in extra[n]]+['SM.IntervalComposition.restrictionEquiv']
ef='work/checks/farout-review-examples.lean';examples=old['additional_examples']+['FaroutIndependentReview.'+n for n in re.findall(r'^theorem (\S+)',(base/ef).read_text(),re.M)];assert len(examples)==48
imports=['SM.MarkedRefinement','SM.InteriorCutIndex','SM.GeometricNearFar','SM.NearFarCutExpansion','SM.TriangularPolynomial','Mathlib.Data.Fintype.Powerset','Mathlib.Tactic']
s='\n'.join('import '+n for n in imports)+'\n\nset_option maxRecDepth 10000\nset_option maxHeartbeats 12000000\nset_option pp.universes false\n\n'
for n in order:s+=(base/('work/checks/'+n+'.body.lean')).read_text()+'\n'
examplefiles=[old['previous_examples'],old['new_examples'],old['factorization_examples'],ef]
for f in examplefiles:s+=(base/f).read_text()+'\n'
for n in allnames:s+='#check '+n+'\n#print axioms '+n+'\n'
for n in transparent:s+='#print '+n+'\n'
for n in examples:s+='#print axioms '+n+'\n'
tf='work/checks/farout-review-types.lean';(base/tf).write_text(s)
binding=dict(old['inherited_review_binding'])
for f in ['work/reviews/nearfar-factorization-far-only-prototype.json','work/checks/refined-weights-reviewed-types.json','work/reviews/marked-transport-independent.json','work/reviews/triangular-polynomial-inverse-canonical-partial.json']+examplefiles:binding[f]=sha(f)
for f,h in old['SM_closure_files_sha256'].items():assert sha(f)==h
d={'status':'prepared; independent kernel not yet run','source':old['source'],'source_sha256':sha(old['source']),'source_lines':'Full lemma146-168 and proof170-227, including local-G1 restricted-word tree coefficient at actual closing edge.','body_order':order,'new_body_names':new,'root_receipts_sha256':receipts,'root_files_sha256':files,'checked_declarations_by_body':names,'checked_declarations':allnames,'new_checked_declarations':newnames,'transparent_definitions_printed':transparent,'additional_examples':examples,'additional_example_count':48,'example_files_sha256':{f:sha(f) for f in examplefiles},'trace':tf,'trace_sha256':sha(tf),'SM_import_roots':old['SM_import_roots'],'SM_closure_files_sha256':old['SM_closure_files_sha256'],'SM_closure_count':20,'inherited_review_binding':binding,'scope':'Full original lem:farout external review. Canonical port, semantic audit and source acceptance remain pending. Earlier marking-transport fragment provenance is retained with fresh independent fragment review.'}
(base/'work/checks/farout-review-preparation.json').write_text(json.dumps(d,indent=2)+'\n')
print('Prepared127 declarations (34 new)+48 consumers;20 canonical dependency modules; no kernel launched.')
