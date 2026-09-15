from pathlib import Path
from hashlib import sha256
import json,re
base=Path(__file__).resolve().parents[2]
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def load(p):return json.loads((base/p).read_text())
def write(p,d):(base/p).write_text(json.dumps(d,indent=2)+'\n')
order=['CompositionCutSet','InteriorCutSet','CompositionSegments','NestedCutSets','MarkedRefinement','InteriorCutIndex','NearFarCutExpansion','GeometricNearFar']
new=order[1:];receipts={};files={}
for n in order:
 p='work/checks/'+n+'-prototype-result.json';d=load(p)
 assert d.get('exit_code',d.get('subprocess_exit_code',None))==0,n
 for f,h in d['files_sha256'].items():assert sha(f)==h;files[f]=h
 receipts[p]=sha(p)
 # Source body is exactly present, never reconstructed from the successful log.
 assert (base/('work/checks/'+n+'.body.lean')).read_text() in (base/('work/checks/'+n+'.prototype.lean')).read_text()
names={
 'GeometricNearFar':['SM.gate_pair_cast','SM.IntervalComposition.ordinaryWeight_cast','SM.IntervalComposition.rootWeight_cast','SM.IntervalComposition.parts_eq_one_of_leaves_eq_one','SM.geometric_nearFar_open','SM.geometric_nearFar_root'],
 'InteriorCutSet':['SM.InteriorCutSet','SM.BoundaryCutSet.interior','SM.BoundaryCutSet.ofInterior','SM.BoundaryCutSet.interior_ofInterior','SM.BoundaryCutSet.ofInterior_interior','SM.BoundaryCutSet.interiorEquiv','SM.BoundaryCutSet.restrict','SM.BoundaryCutSet.mem_restrict','SM.BoundaryCutSet.restrict_self','SM.BoundaryCutSet.restrict_restrict','SM.IntervalComposition.interiorCutSetEquiv'],
 'CompositionSegments':['SM.IntervalComposition.part_bounds','SM.IntervalComposition.part_order','SM.IntervalComposition.exists_halfOpen_part','SM.IntervalComposition.exists_closed_part','SM.IntervalComposition.part_interior_unique'],
 'NearFarCutExpansion':['SM.IntervalComposition.nearFarWeight_marked_expansion'],
 'NestedCutSets':['SM.RefiningCutSet','SM.IntervalComposition.halfOpen_part_unique','SM.IntervalComposition.flattenCutSets','SM.IntervalComposition.mem_flattenCutSets','SM.IntervalComposition.outer_cuts_subset_flatten','SM.IntervalComposition.flattenRefinement','SM.IntervalComposition.unflattenCutSets','SM.IntervalComposition.unflatten_flatten','SM.IntervalComposition.flatten_unflatten','SM.IntervalComposition.nestedCutSetEquiv','SM.IntervalComposition.nestedCompositionEquiv'],
 'MarkedRefinement':['SM.MarkedCuts','SM.BoundaryCutSet.cuts_subset_iff_interior_subset','SM.BoundaryCutSet.outerFromMarks','SM.BoundaryCutSet.outerFromMarks_subset','SM.BoundaryCutSet.outerMarkedEquiv','SM.swapSigmaSubtype','SM.IntervalComposition.outerCompositionMarkedEquiv','SM.IntervalComposition.nestedMarkedCutEquiv'],
 'InteriorCutIndex':['SM.IntervalComposition.interiorPosition','SM.IntervalComposition.interiorPosition_injective','SM.IntervalComposition.interiorPosition_mem','SM.IntervalComposition.mem_interior_iff_exists_index','SM.IntervalComposition.interiorPositionEquiv']}
allnames=[v for n in new for v in names[n]];assert len(allnames)==47
transparent=['SM.InteriorCutSet','SM.BoundaryCutSet.interior','SM.BoundaryCutSet.ofInterior','SM.BoundaryCutSet.restrict','SM.RefiningCutSet','SM.IntervalComposition.flattenCutSets','SM.IntervalComposition.flattenRefinement','SM.IntervalComposition.unflattenCutSets','SM.IntervalComposition.nestedCompositionEquiv','SM.MarkedCuts','SM.BoundaryCutSet.outerFromMarks','SM.BoundaryCutSet.outerMarkedEquiv','SM.IntervalComposition.nestedMarkedCutEquiv','SM.IntervalComposition.interiorPosition','SM.IntervalComposition.interiorPositionEquiv']
ef='work/checks/nearfar-refinement-review-examples.lean';examples=['NearFarRefinementIndependentReview.'+n for n in re.findall(r'^theorem (\S+)',(base/ef).read_text(),re.M)];assert len(examples)==16
imports=['SM.TreeCoefficient','SM.TriangularPolynomial','Mathlib.Data.Finset.Sort','Mathlib.Algebra.BigOperators.Ring.Finset','Mathlib.Tactic']
s='\n'.join('import '+n for n in imports)+'\n\nset_option maxRecDepth 10000\nset_option maxHeartbeats 12000000\nset_option pp.universes false\n\n'
for n in order:s+=(base/('work/checks/'+n+'.body.lean')).read_text()+'\n'
s+=(base/ef).read_text()+'\n'
for n in allnames:s+='#check '+n+'\n#print axioms '+n+'\n'
for n in transparent:s+='#print '+n+'\n'
for n in examples:s+='#print axioms '+n+'\n'
tf='work/checks/nearfar-refinement-review-types.lean';(base/tf).write_text(s)
seen={}
def visit(n):
 if n in seen:return
 p='work/lean/'+n.replace('.','/')+'.lean';seen[n]=p
 for q in re.findall(r'^import (\S+)',(base/p).read_text(),re.M):
  if q.startswith('SM.'):visit(q)
for n in imports:
 if n.startswith('SM.'):visit(n)
cl={seen[n]:sha(seen[n]) for n in sorted(seen)}
reviewbinding={p:sha(p) for p in ['work/reviews/composition-cut-set-prototype.json','work/reviews/def-nearfar.json','work/reviews/triangular-polynomial-inverse-canonical-partial.json','work/reviews/def-treesum.json','work/reviews/def-gates.json','work/reviews/lem-gates-nonzero.json']}
write('work/checks/nearfar-refinement-review-preparation.json',{'status':'prepared; no independent kernel dispatched','source':'reference/SM/sm-2-amplitude.tex','source_sha256':sha('reference/SM/sm-2-amplitude.tex'),'body_order':order,'new_body_names':new,'root_receipts_sha256':receipts,'root_files_sha256':files,'checked_declarations_by_body':names,'checked_declarations':allnames,'transparent_definitions_printed':transparent,'additional_examples':examples,'additional_example_count':16,'examples':ef,'examples_sha256':sha(ef),'trace':tf,'trace_sha256':sha(tf),'SM_import_roots':[n for n in imports if n.startswith('SM.')],'SM_closure_files_sha256':cl,'SM_closure_count':len(cl),'inherited_review_binding':reviewbinding,'scope':'External helper review only: actual two geometric identities and full cut/refinement indexing with local binomial expansion; no complete factorization or farout acceptance.'})
print('Prepared',len(allnames),'declaration checks,',len(examples),'consumers;',len(cl),'canonical SM dependency modules; no kernel launched.')
