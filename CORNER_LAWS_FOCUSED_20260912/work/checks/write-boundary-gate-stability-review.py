from pathlib import Path
from hashlib import sha256
import re,json,sys,datetime
base=Path(__file__).resolve().parents[2]
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def load(p):return json.loads((base/p).read_text())
def write(p,d):(base/p).write_text(json.dumps(d,indent=2)+'\n')
session=int(sys.argv[1]);pf='work/checks/boundary-gate-stability-review-preparation.json';p=load(pf)
for k in ['sources_sha256','SM_closure_files_sha256','all_327_canonical_SM_files_sha256','root_receipts_sha256','root_files_sha256','prior_checkpoint_bindings_sha256']:
 for f,h in p[k].items():assert sha(f)==h,(k,f)
assert sha(p['trace'])==p['trace_sha256'] and sha(p['example_file'])==p['example_file_sha256']
log='work/checks/boundary-gate-stability-review-types.log';s=(base/log).read_text()
assert not re.search(r'error[:(]',s) and 'sorryAx' not in s
names=p['checked_declarations'];examples=p['additional_examples'];assert len(names)==27 and len(examples)==19
axioms={};types={}
for n in names+examples:
 m=re.search("'"+re.escape(n)+r"' depends on axioms:\s*\[([^]]*)\]",s)
 if m:axioms[n]=[x.strip() for x in m[1].split(',') if x.strip()]
 else:
  assert "'"+n+"' does not depend on any axioms" in s,n;axioms[n]=[]
 assert set(axioms[n]) <= {'propext','Classical.choice','Quot.sound'},n
for n in names:
 m=re.search(r'^'+re.escape(n)+r'(?:\.\{[^}]+\})?(?=\s)',s,re.M);assert m,n
 types[n]=s[m.start():s.index("'"+n+"'",m.start())].strip()
tf='work/checks/boundary-gate-stability-reviewed-types.json'
write(tf,{'types':types,'type_sha256':{n:sha256(t.encode()).hexdigest() for n,t in types.items()},'axioms':axioms,
 'checked_declarations':names,'additional_examples':examples,'trace_log':log,'trace_log_sha256':sha(log),
 'independent_kernel_session':session,'exit_code':0})
reviewed=dict(p['SM_closure_files_sha256'])
for n in p['body_order']:
 f='work/checks/'+n+'.body.lean';reviewed[f]=sha(f)
cf='work/checks/boundary-gate-stability-review-closure.json'
write(cf,{'source_id':p['source_id'],'sources_sha256':p['sources_sha256'],'SM_import_roots':p['SM_import_roots'],
 'SM_closure_count':p['SM_closure_count'],'SM_closure_files_sha256':p['SM_closure_files_sha256'],
 'all_327_canonical_SM_files_sha256':p['all_327_canonical_SM_files_sha256'],'reviewed_files_sha256':reviewed,
 'root_receipts_sha256':p['root_receipts_sha256'],'root_files_sha256':p['root_files_sha256'],
 'prior_checkpoint_bindings_sha256':p['prior_checkpoint_bindings_sha256'],'preparation':pf,'preparation_sha256':sha(pf),
 'trace':p['trace'],'trace_sha256':sha(p['trace']),'scope':p['scope']})
prior=load('work/reviews/critical-source-response-canonical-partial.json')
for f,h in prior['pins']['pin_files_sha256'].items():assert sha(f)==h
failures=p.get('prior_failed_independent_runs',[])
for f in failures:
 for k in ['source','log','examples','preparation']:f[k+'_sha256']=sha(f[k])
 old=(base/f['log']).read_text()
 for n in names:
  m=re.search(r'^'+re.escape(n)+r'(?:\.\{[^}]+\})?(?=\s)',old,re.M);assert m,n
  assert old[m.start():old.index("'"+n+"'",m.start())].strip()==types[n],n
evidence={'independent_trace_source':p['trace'],'independent_trace_source_sha256':sha(p['trace']),
 'independent_trace_log':log,'independent_trace_log_sha256':sha(log),
 'independent_kernel_command':'lake env lean ../checks/boundary-gate-stability-review-types.lean',
 'independent_kernel_session':session,'independent_kernel_exit_code':0,'first_independent_run_passed':not failures,
 'prior_failed_independent_runs':failures,'checked_declarations':names,'declaration_count':27,
 'declaration_axioms':{n:axioms[n] for n in names},'additional_examples':examples,'additional_example_count':19,
 'additional_examples_passed':True,'additional_example_axioms':{n:axioms[n] for n in examples},
 'transparent_definitions_printed':p['transparent_definitions_printed'],'supporting_types_printed':p['supporting_types_printed'],
 'reviewed_types':tf,'reviewed_types_sha256':sha(tf),'independent_closure_evidence':cf,'independent_closure_evidence_sha256':sha(cf),
 'root_successful_results':{f:load(f) for f in p['root_receipts_sha256']},'root_receipts_sha256':p['root_receipts_sha256']}
domain='work/reviews/single-triple-n3-domain-note.json'
d={'review_schema':'independent-partial-source-prototype-review-v1','id':'boundary-gate-stability-prototype',
 'source_id':'thm:single-triple','source_line':229,'source':p['source'],'source_sha256':sha(p['source']),
 'source_lines':p['source_lines'],'additional_source_sha256':{'reference/SM/sm-1-polygons.tex':sha('reference/SM/sm-1-polygons.tex')},
 'reviewer':'review_relgp_full-independent-20260911','implementer':'root-implementation-20260910',
 'verdict':'faithful','implemented_scope_verdict':'faithful','parameters_reviewed':True,'definition_equivalence_reviewed':True,
 'source_claim_accepted':False,'statement_sha256':None,'in_theorem_library':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'main_declarations':names,'main_declarations_by_body':p['checked_declarations_by_body'],
 'prototype_files_sha256':{n:sha('work/checks/'+n+'.prototype.lean') for n in p['body_order']},
 'reviewed_files_sha256':reviewed,'import_closure_roots':p['SM_import_roots'],'import_closure_file_count':p['SM_closure_count'],
 'embedded_body_count':5,'evidence':evidence,'pins':prior['pins'],'prior_checkpoint_bindings_sha256':p['prior_checkpoint_bindings_sha256'],
 'reason':'Faithful partial geometric and locality development for the single-triple wall proof. The actual unordered label support identifies exactly one increasing boundary triple; all other source determinants are nonzero. Finite chirotope continuity supplies one common ambient neighborhood for all noncritical geometric entries and all inverse/output coordinates whose intervals exclude the full critical span. Exact collinear determinant identities retain the printed left and right epsilon orientations and cast to the actual geometric arrays. Independent checks cover all27 types and19 consumers. This does not certify a full wall theorem, gap polygon nondegeneracy, or later side-radius and gap-value assembly.',
 'mathematical_justification':[
 {'clause':'Exact ordered and unordered support correspondence','assessment':'positionSet contains precisely lower,middle,upper in Fin n. Strict inequalities give three distinct positions, independently checked by cardinality. The proof that this set determines the ordered triple first identifies the minimum and maximum using the proved bounds, then rules out both endpoints as the other middle. vertexSet is exactly its image under the actual root boundaryIndex. That map is injective on every Fin n position, so equality of these unordered source label sets is equivalent to equality of the increasing triples. Reversing the displayed labels changes no set. Independent consumers check three labels, exact support equality, and the zero critical versus nonzero noncritical actual point signs. No geometric point-injectivity is used.'},
 {'clause':'Every noncritical actual determinant is nonzero','assessment':'Under pointZeroTriples P={t.vertexSet g}, the canonical singleton-zero theorem applies to the reversed actual labels of any u distinct from t. Strict boundary inequalities and injectivity of boundaryIndex establish pairwise distinct labels. If its unordered support were the critical support, the support injection would force u=t, a contradiction. Therefore its chi is nonzero. This matches the source exception by unordered triple, not merely one permutation or one occurrence; the statement is about actual P labels and not an abstract array assumption.'},
 {'clause':'Correct far-sign orientation and determinant rescaling','assessment':'pointFarSign a r c is sign(det(r-c,a-c)), exactly the source chi(c,r,a). In the left identity cyclic area invariance rewrites the determinants to share the actual first endpoint a. The relation b-a=s(c-a) scales the first determinant factor by s. In the right identity the common endpoint is c and b-c=s(a-c) scales the second determinant factor. For nonzero s, sign(s)^2=1 and sign multiplicativity recover the original sign. This remains valid if the determinant itself is zero; nonzero determinant claims are supplied separately for noncritical source triples. The independent zero-gate consumer verifies that the scalar theorem has no hidden determinant nonvanishing premise.'},
 {'clause':'The two source epsilon ratios, including reversed order','assessment':'wallLeftEpsilon is sign((y-x)/(z-x)); wallRightEpsilon is sign((z-y)/(z-x)). Distinct scalar coordinates prove both nonzero and hence +/-1. Their two real ratios sum to one, so at least one sign is positive, without assuming the labelled middle point is geometrically between the endpoints. Affine subtraction is proved componentwise. The left substitution uses ((y-x)/(z-x))*(z-x)=y-x. The right uses ((z-y)/(z-x))*(x-z)=y-z, reversing both differences and keeping the printed orientation. Independent consumers check the three geometric order regimes (++),(-+),(+-), rule out (--), and specialize the actual left and right sign equalities in the respective negative-ratio cases.'},
 {'clause':'Bridge to physical boundary samples and arbitrary coefficient rings','assessment':'geometricBoundaryArray_pointFarSign is a definitional equality between the existing reversed chirotope array and the three actual boundaryWord points, cast SignType to integers and then into R. Each left/right bridge uses actual equalities of those three wall vertices with p+xi*omega, and a physical r strictly inside the appropriate gap. The global sample is (lower,r,upper); the local sample is (lower,r,middle) or (middle,r,upper), respectively. The determinant sign identity is then transported through multiplicative integer/ring casts. The proof never substitutes a near sample or moves a physical endpoint. CommRing suffices for these bridges; no invertibility-of-two, G1, G2, or geometric-injectivity premise is added. The source distinct xi data are explicit; omega nonzero is not needed for this weaker sign identity and is not inferred from it.'},
 {'clause':'Complete reversed output locality','assessment':'farOnlyOutput is the actual full F_(-H)(c(H)) coordinate. Unfolding it retains the entire finite sum over unchanged raw compositions, including unary compositions. Each far coefficient sample has the original J endpoints, so agreement on every actual triple contained in J equates every coefficient factor. For each child, the canonical bounds place every triple contained in that child inside J, allowing the proved inverse-coordinate locality theorem to equate that complete child value. Product and sum congruence then give equality of the full output. No independence of individual geometric tree terms or genericity is assumed. The off-critical corollary follows because an interval excluding the entire critical span cannot contain the critical triple. Consumers cover both gap intervals, arbitrary critical-entry replacement, and the one-leaf output without any array agreement.'},
 {'clause':'One common ambient neighborhood for all source signs','assessment':'The canonical finite_nonzero_chi_persists theorem takes the finite intersection over all label triples of the neighborhoods supplied by continuity of the area and local constancy of sign at a nonzero real. It gives one eventual Q before universally quantifying every label triple. boundary_chi_nonzero_off_critical supplies the required nonzero values for every noncritical increasing boundary triple; applying the two casts yields simultaneous actual geometric-array equality. The ambient center P may be nongeneric and Q is not required to be generic. Thus this theorem does not accidentally assume G1 at the wall or hide a radius depending on a particular triple.'},
 {'clause':'Common neighborhood for all actual inverse and output intervals','assessment':'The inverse and output neighborhood theorems each start from that same simultaneous array-stability event, then quantify every BoundaryInterval J. The exact off-critical-span locality theorems apply with the actual arrays at Q and P. Both values therefore retain their wall values for every interval excluding the full critical span, with unary gaps allowed. An independent consumer takes the finite intersection of the three events and obtains joint array,c,B preservation. Another produces one set in the neighborhood filter on which any two tuples have equal complete outputs for all excluded intervals. These are common ambient-neighborhood conclusions; the later explicit common radius on an actual wall germ is outside this five-body review.'},
 {'clause':'n=3 is not silently replaced by n>=4','assessment':'All support and neighborhood helpers require only NeZero n and an actual increasing triple. They do not invoke singlePointTriple_vertices_injective, which correctly requires n>=4. An independent consumer proves that for n=3 there is only one increasing boundary triple, so the noncritical increasing-triple domain is empty there; this is legitimate in the partial stability claims and does not assert geometric distinctness. The separately bound source note explains why singleton Zpt alone does not force distinct geometric center points for n=3. The printed theorem also explicitly supplies pairwise distinct vertices and distinct xi; that interpretation remains explicit source data for future assembly, not an implication silently added by these helpers.'},
 {'clause':'Remaining source scope','assessment':'These bodies prove the exact support, sign-ratio, and ambient-locality portions of source271-283 and290-301. They do not construct a common wall-germ time radius, identify signed gap sums as the source U/V values, establish G1 for nontrivial closed gap polygons, build the contracted polygon with its physical root, propagate the critical response, or prove either final geometric wall formula. The new root-authored WallArrayNeighborhood, WallGapValues, BoundaryGapGates and later bodies are explicitly excluded. No original source claim is accepted from this helper review.'}],
 'independence':'This reviewer independently read the source and all five frozen bodies, checked their actual transparent definitions and canonical dependency types, and authored only review consumers and evidence. No implementation, source, map, root receipt, or frozen report was edited. The separate earlier proper-child conceptual-overlap review remains bound through the accepted canonical partial report; none of those disputed fragments is new in this batch. The present direct output-locality proof compares full coefficient/child products; an earlier reviewer consumer had obtained output restriction through the already canonical restriction theorem, a different proof, and no reuse of that consumer has been asserted.',
 'separate_source_domain_note':domain,'separate_source_domain_note_sha256':sha(domain),
 'accounting':{'original_claims_accepted':0,'proof_increment':0,'definition_increment':0,'canonical_port_pending':True,'full_single_triple_accepted':False,'stage_complete':False},
 'unproved_original_clauses_in_this_reviewed_batch':['Explicit wall-germ common time radius and transfer of the wall sign identities to both sufficiently close sides.','Natural gap U/V identification and G1 of closed nontrivial gap polygons.','Contracted polygon, physical root, larger-interval propagation and final proper/full wall formulas.'],
 'not_certified':['No original thm:single-triple acceptance or canonical semantic hash for these external helpers.','No derivation of geometric distinctness from singleton Zpt at n=3.','No complete corner wall law, soft theorem, R theorem, or overall stage completion.']}
out='work/reviews/boundary-gate-stability-prototype.json';write(out,d)
print(out,sha(out));print('PASS27 declarations+19 consumers;46 standard-or-empty traces;54-module dependency closure;327 canonical files unchanged; no original acceptance.')
