from pathlib import Path
from hashlib import sha256
import json,re
base=Path(__file__).resolve().parents[2]
def sha(f):return sha256((base/f).read_bytes()).hexdigest()
def load(f):return json.loads((base/f).read_text())
order=['CriticalCutSplit','FarOnlyLocality','CriticalFarOccurrence','GapSplitProducts','CriticalInverseDifference','FixedEndpointGate','CoefficientResponse','CriticalSourceResponse']
new=order[4:];files={};receipts={};bybody={}
for n in order:
 f='work/checks/'+n+'-prototype-result.json';r=load(f);assert r['exit_code']==0
 for p,h in r['files_sha256'].items():assert sha(p)==h;files[p]=h
 receipts[f]=sha(f);bybody[n]=r['printed_declarations']
 assert (base/('work/checks/'+n+'.body.lean')).read_text() in (base/('work/checks/'+n+'.prototype.lean')).read_text()
old=load('work/checks/critical-cut-review-preparation.json');bybody['CriticalCutSplit']=old['checked_declarations_by_body']['CriticalCutSplit']
names=sum(bybody.values(),[]);assert len(names)==len(set(names))==53
examplefiles=['work/checks/far-only-locality-review-examples.lean','work/checks/critical-cut-review-examples.lean','work/checks/gap-split-products-review-examples.lean','work/checks/critical-source-review-examples.lean']
namespaces=['FarOnlyLocalityIndependentReview','CriticalCutIndependentReview','GapSplitProductsIndependentReview','CriticalSourceIndependentReview'];examples=[]
for f,ns in zip(examplefiles,namespaces):examples += [ns+'.'+n for n in re.findall(r'^theorem (\S+)',(base/f).read_text(),re.M)]
assert len(examples)==41
transparent=old['transparent_definitions_printed']+['SM.IncreasingBoundaryTriple.gapBaseComposition','SM.IncreasingBoundaryTriple.gapRefinement','SM.farOnlyCoordinates','SM.farOnlyOutput','SM.cutWeightedSum','SM.IncreasingBoundaryTriple.fixedFarGate','SM.coefficientDifferenceSum']
s='import SM.Farout\nimport Mathlib.Tactic\n\nset_option maxRecDepth 10000\nset_option maxHeartbeats 12000000\nset_option pp.universes false\n\n'
for n in order:s+=(base/('work/checks/'+n+'.body.lean')).read_text()+'\n'
for f in examplefiles:s+=(base/f).read_text()+'\n'
for n in names:s+='#check '+n+'\n#print axioms '+n+'\n'
for n in transparent:s+='#print '+n+'\n'
for n in examples:s+='#print axioms '+n+'\n'
tf='work/checks/critical-source-review-types.lean';(base/tf).write_text(s)
c=old['SM_closure_files_sha256']
for f,h in c.items():assert sha(f)==h
binding={f:sha(f) for f in ['work/reviews/lem-farout.json','work/reviews/marked-transport-independent.json','work/reviews/far-only-locality-prototype.json','work/reviews/critical-cut-split-occurrence-prototype.json','work/reviews/gap-split-products-prototype.json','work/checks/far-only-locality-reviewed-types.json','work/checks/critical-cut-reviewed-types.json','work/checks/gap-split-products-reviewed-types.json']}
p={'state':'prepared; independent kernel not yet run','source':old['source'],'source_sha256':sha(old['source']),'source_lines':'thm:single-triple229-269, proof281-317. Exact algebraic critical inverse/output responses with fixed-endpoint gap sums; geometric E/B identification and propagation remain outside scope.','body_order':order,'new_body_names':new,'checked_declarations':names,'checked_declarations_by_body':bybody,'additional_examples':examples,'new_example_count':10,'transparent_definitions_printed':transparent,'trace':tf,'trace_sha256':sha(tf),'example_files_sha256':{f:sha(f) for f in examplefiles},'SM_import_roots':['SM.Farout'],'SM_closure_files_sha256':c,'root_receipts_sha256':receipts,'root_files_sha256':files,'inherited_review_binding':binding,'scope':'Four new external response bodies with four frozen predecessor bodies;53 declarations and41 consumers. No full wall geometry, contracted propagation or original-source acceptance. Fresh CriticalInverseDifference review to resolve conceptual overlap with prior reviewer proper-child consumer will be bound before sealing.'}
(base/'work/checks/critical-source-review-preparation.json').write_text(json.dumps(p,indent=2)+'\n')
print('Prepared53 declarations (36 old+17 new)+41 consumers;32 unchanged canonical modules; no kernel launched.')
