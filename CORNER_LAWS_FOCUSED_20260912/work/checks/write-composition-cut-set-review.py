from pathlib import Path
from hashlib import sha256
import json,re,datetime
base=Path(__file__).resolve().parents[2]
def load(p):return json.loads((base/p).read_text())
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def write(p,d):(base/p).write_text(json.dumps(d,indent=2)+'\n')
c=load('work/checks/composition-cut-set-review-closure.json')
for field in ['frozen_files_sha256','root_receipts_sha256','SM_closure_files_sha256']:
 assert all(sha(p)==h for p,h in c[field].items())
assert sha(c['trace'])==c['trace_sha256'] and sha(c['examples'])==c['examples_sha256']
assert sha(c['source'])==c['source_sha256']
logfile='work/checks/composition-cut-set-review-types.log';s=(base/logfile).read_text()
assert not re.search(r'error[:(]',s) and 'sorryAx' not in s
names=c['checked_declarations'];examples=c['additional_examples'];types={};axioms={}
assert len(names)==15 and len(examples)==6
for n in names+examples:
 m=re.search("'"+re.escape(n)+r"' depends on axioms:\s*\[([^]]*)\]",s)
 if m:axioms[n]=[v.strip() for v in m[1].split(',') if v.strip()]
 else:
  assert "'"+n+"' does not depend on any axioms" in s,n
  axioms[n]=[]
 assert set(axioms[n])<={'propext','Classical.choice','Quot.sound'}
for n in names:
 m=re.search(r'^'+re.escape(n)+r'(?:\.\{[^}]+\})?(?=\s)',s,re.M);assert m,n
 i=m.start();j=s.index("'"+n+"'",i);types[n]=s[i:j].strip()
old=load('work/checks/nearfar-inverse-reviewed-types.json')
for n in names[:5]:assert types[n]==old['types'][n]
typefile='work/checks/composition-cut-set-reviewed-types.json'
write(typefile,{'types':types,'type_sha256':{n:sha256(t.encode()).hexdigest() for n,t in types.items()},'axioms':axioms,'all_five_UnaryComposition_predecessor_types_unchanged':True})
d={'review_schema':'independent-partial-source-prototype-review-v1','id':'composition-cut-set-prototype','source_id':'lem:farout',
 'source':c['source'],'source_sha256':c['source_sha256'],'source_lines':'Original composition definition23-27; cut/refinement proof180-193, helper scope only',
 'reviewer':'review_relgp_full-independent-20260911','implementer':'root-implementation-20260910','verdict':'faithful','implemented_scope_verdict':'faithful',
 'parameters_reviewed':True,'definition_equivalence_reviewed':True,'source_claim_accepted':False,'statement_sha256':None,'in_theorem_library':False,
 'prototype_file':'work/checks/CompositionCutSet.prototype.lean','prototype_sha256':sha('work/checks/CompositionCutSet.prototype.lean'),
 'main_declarations':names[5:],
 'reason':'Faithful representation helper: all raw strictly increasing compositions of an interval are equivalent to all bounded finite cut sets containing both endpoints. Sorting and taking the image are inverse on the complete source domain, preserving the exact natural part count and ordered cuts. Unary endpoint sets and full interval cut sets are independently checked, including maximal full-cut arity. Kernel62454 passes15 implementation declarations and6 substantive consumers with standard axioms only. This helper does not yet prove the marked-cut/nested-composition bijection or factorization and accepts no original farout claim.',
 'mathematical_justification':[
  {'clause':'Complete cut-set domain','assessment':'BoundaryCutSet contains a Finset of actual Fin n boundary positions, both interval endpoints, and only the printed closed-interval bounds. It requires or forbids no interior position. The endpoints are distinct because BoundaryInterval is increasing; their two-element subset proves card>=2. The independent every_raw_cut_set_admitted test starts with any such finite set and returns an actual raw composition with exactly that cut set and part count plus one equal to its cardinality.'},
  {'clause':'Sorted reconstruction','assessment':'toComposition sets the part count to card(cuts)-1, derives positivity from the two endpoints, and uses orderEmbOfFin to enumerate every set element strictly increasingly. Its first value is the left endpoint: monotonicity places it no higher than the index of that endpoint, while the set bounds place it no lower. The analogous maximum argument proves the last value is the right endpoint. Thus the reconstruction is an original IntervalComposition, without an arity cap or additional geometric premise. The independent exact_cut_membership test proves all and only the original set elements occur among its cuts.'},
  {'clause':'No loss of the ordered raw composition','assessment':'cutSet takes the image of all actual cut-list positions; first/last membership and interval bounds follow from the existing fields and strict monotonicity. Injectivity of the cut map gives cutSet.card=parts+1. Two raw compositions with equal cut sets therefore have equal natural part counts. Each strictly increasing cut function is the unique increasing enumeration of this same finite set, so the entire dependent cut functions agree; proof irrelevance then gives equality of the structures. The independent same_cut_set_iff_same_composition and complete_raw_roundtrip checks verify exact recovery, rather than only equal cardinality or a surjective encoding.'},
  {'clause':'Both inverse laws and boundary cases','assessment':'The image of the sorted enumeration is exactly the original finite set, yielding toComposition_cutSet by BoundaryCutSet extensionality. Cut-set injectivity then yields cutSet_toComposition for every raw composition. These form the explicit equivalence. The independent unary_cut_set_is_exactly_endpoints checks that the endpoint-only set reconstructs the unique one-part composition and vice versa. The independent full_cut_coverage checks that every interval position is retained by the maximal cut set and its reconstructed part count equals the actual interval leaf count, using the finite interval cardinality formula. Both extreme marked-cut possibilities remain available to future factorization work.'},
  {'clause':'Verified scope and remaining mathematics','assessment':'The exact frozen body and the separately reviewed UnaryComposition predecessor are copied unchanged over the actual five-module canonical import closure. All15 declaration checks and6 consumer theorems pass on the first independent run with only standard axioms; all five predecessor printed types exactly match their earlier trace. This is the composition/cut-set equivalence only. Restricting a refined composition to outer parts, recovering marked subsets, matching adjacent near triples, the coefficient expansion, and every remaining farout clause require their own proofs and reviews.'}],
 'reviewed_files_sha256':{**c['SM_closure_files_sha256'],**c['frozen_files_sha256']},'import_closure_roots':['SM.FiniteCompositions'],'import_closure_file_count':5,
 'inherited_review_binding':{p:sha(p) for p in ['work/reviews/def-root.json','work/reviews/finite-compositions-prototype.json','work/reviews/triangular-polynomial-inverse-prototype.json']},
 'pins':load('work/reviews/def-root.json')['pins'],
 'independence':'Reviewer did not author or edit the implementation, source, canonical modules, declaration map or previous reviews. Only new independent raw-domain and boundary-case consumer checks, trace/closure/type evidence and this helper review were written.',
 'evidence':{'independent_trace_source':c['trace'],'independent_trace_source_sha256':sha(c['trace']),'independent_trace_log':logfile,'independent_trace_log_sha256':sha(logfile),
  'independent_kernel_command':'lake env lean ../checks/composition-cut-set-review-types.lean','independent_kernel_session':62454,'independent_kernel_exit_code':0,'first_independent_run_passed':True,
  'checked_declarations':names,'declaration_axioms':{n:axioms[n] for n in names},'additional_examples':examples,'additional_example_count':6,
  'additional_examples_passed':True,'additional_example_axioms':{n:axioms[n] for n in examples},'transparent_predicates_printed':['SM.BoundaryCutSet','SM.BoundaryCutSet.toComposition','SM.IntervalComposition.cutSet'],
  'printed_types':typefile,'printed_types_sha256':sha(typefile),'all_five_UnaryComposition_predecessor_types_unchanged':True,
  'independent_closure_evidence':'work/checks/composition-cut-set-review-closure.json','independent_closure_evidence_sha256':sha('work/checks/composition-cut-set-review-closure.json'),
  'root_receipts_sha256':c['root_receipts_sha256'],'frozen_files_sha256':c['frozen_files_sha256'],'successful_root_kernel_session':97447,'successful_root_kernel_exit_code':0},
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'accounting':{'original_claims_accepted':0,'proof_increment':0,'full_farout_accepted':False,'stage_complete':False},
 'not_certified':['No full factorization or marked-cut/nested-composition equivalence.','No geometric output, restricted-interval farout clause, original farout acceptance, wall law, soft theorem, R theorem or stage completion.']}
write('work/reviews/composition-cut-set-prototype.json',d)
print('CompositionCutSet helper faithful; SHA',sha('work/reviews/composition-cut-set-prototype.json'))
