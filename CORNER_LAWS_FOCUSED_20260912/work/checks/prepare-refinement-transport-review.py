from pathlib import Path
from hashlib import sha256
import json,re
base=Path(__file__).resolve().parents[2]
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def load(p):return json.loads((base/p).read_text())
order=['ConsecutiveCuts','ConsecutiveTriples','RefinedChildren','MarkedCutIndex'];files={};receipts={};names={}
extra={'ConsecutiveCuts':['SM.BoundaryCutSet.Consecutive'],'ConsecutiveTriples':['SM.IncreasingBoundaryTriple.leftInterval','SM.IncreasingBoundaryTriple.rightInterval'],'RefinedChildren':['SM.IntervalComposition.refinementInner','SM.IntervalComposition.refinedChildIndex'],'MarkedCutIndex':['SM.IntervalComposition.indexMarks','SM.IntervalComposition.markIndices']}
for n in order:
 f='work/checks/'+n+'-prototype-result.json';d=load(f);assert d.get('exit_code',d.get('subprocess_exit_code'))==0
 for p,h in d['files_sha256'].items():assert sha(p)==h;files[p]=h
 receipts[f]=sha(f);names[n]=extra[n]+d['printed_declarations']
 assert (base/('work/checks/'+n+'.body.lean')).read_text() in (base/('work/checks/'+n+'.prototype.lean')).read_text()
allnames=[x for n in order for x in names[n]];assert len(allnames)==41
transparent=[*extra['ConsecutiveCuts'],*extra['ConsecutiveTriples'],*extra['RefinedChildren'],*extra['MarkedCutIndex'],'SM.IntervalComposition.partConsecutiveEquiv','SM.IntervalComposition.refinedChildrenEquiv','SM.IntervalComposition.marksIndexEquiv']
ef='work/checks/refinement-transport-review-examples.lean';examples=['RefinementTransportIndependentReview.'+n for n in re.findall(r'^theorem (\S+)',(base/ef).read_text(),re.M)];assert len(examples)==14
imports=['SM.MarkedRefinement','SM.InteriorCutIndex','SM.NearFar','SM.UnaryComposition','Mathlib.Data.Fintype.Powerset','Mathlib.Tactic']
s='\n'.join('import '+n for n in imports)+'\n\nset_option maxRecDepth 10000\nset_option maxHeartbeats 12000000\nset_option pp.universes false\n\n'
for n in order:s+=(base/('work/checks/'+n+'.body.lean')).read_text()+'\n'
s+=(base/ef).read_text()+'\n'
for n in allnames:s+='#check '+n+'\n#print axioms '+n+'\n'
for n in transparent:s+='#print '+n+'\n'
for n in examples:s+='#print axioms '+n+'\n'
tf='work/checks/refinement-transport-review-types.lean';(base/tf).write_text(s)
seen={}
def visit(n):
 if n in seen:return
 f='work/lean/'+n.replace('.','/')+'.lean';seen[n]=f
 for q in re.findall(r'^import (\S+)',(base/f).read_text(),re.M):
  if q.startswith('SM.'):visit(q)
for n in imports:
 if n.startswith('SM.'):visit(n)
cl={seen[n]:sha(seen[n]) for n in sorted(seen)}
binding={f:sha(f) for f in ['work/reviews/nearfar-helper-port.json','work/reviews/nearfar-refinement-canonical-partial.json','work/reviews/composition-cut-set-canonical-partial.json','work/reviews/def-nearfar.json']}
d={'status':'prepared independent check; no kernel result yet','source':'reference/SM/sm-2-amplitude.tex','source_sha256':sha('reference/SM/sm-2-amplitude.tex'),'source_lines':'Source refinement180-199, especially actual neighboring positions190-193 and full child product194.','body_order':order,'root_receipts_sha256':receipts,'root_files_sha256':files,'checked_declarations_by_body':names,'checked_declarations':allnames,'transparent_definitions_printed':transparent,'additional_examples':examples,'additional_example_count':14,'examples':ef,'examples_sha256':sha(ef),'trace':tf,'trace_sha256':sha(tf),'SM_import_roots':[n for n in imports if n.startswith('SM.')],'SM_closure_files_sha256':cl,'SM_closure_count':len(cl),'inherited_review_binding':binding,'scope':'Four external helper bodies. Actual consecutive pairs/triples, full refined child index/product transport, and all marked-set index/complement/product/sum transport. No full inner-near/outer-far coefficient transport or factorization acceptance.'}
(base/'work/checks/refinement-transport-review-preparation.json').write_text(json.dumps(d,indent=2)+'\n')
print('Prepared41 declarations+14 consumers;',len(cl),'canonical dependency modules; no original acceptance.')
