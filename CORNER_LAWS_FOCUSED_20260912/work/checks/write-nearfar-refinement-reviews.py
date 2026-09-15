from pathlib import Path
from hashlib import sha256
import re,json,datetime
base=Path(__file__).resolve().parents[2]
def load(p):return json.loads((base/p).read_text())
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def write(p,d):(base/p).write_text(json.dumps(d,indent=2)+'\n')
pfile='work/checks/nearfar-refinement-review-preparation.json';p=load(pfile)
assert sha(p['source'])==p['source_sha256']
for key in ['root_receipts_sha256','root_files_sha256','SM_closure_files_sha256','inherited_review_binding']:
 for f,h in p[key].items():assert sha(f)==h,(key,f)
assert sha(p['trace'])==p['trace_sha256'] and sha(p['examples'])==p['examples_sha256']
logfile='work/checks/nearfar-refinement-review-types.log';s=(base/logfile).read_text()
assert not re.search(r'error[:(]',s) and 'sorryAx' not in s
names=p['checked_declarations'];examples=p['additional_examples'];assert len(names)==47 and len(examples)==16
axioms={};types={}
for n in names+examples:
 m=re.search("'"+re.escape(n)+r"' depends on axioms:\s*\[([^]]*)\]",s)
 if m:axioms[n]=[v.strip() for v in m[1].split(',') if v.strip()]
 else:
  assert "'"+n+"' does not depend on any axioms" in s,n;axioms[n]=[]
 assert set(axioms[n])<={'propext','Classical.choice','Quot.sound'},n
for n in names:
 m=re.search(r'^'+re.escape(n)+r'(?:\.\{[^}]+\})?(?=\s)',s,re.M);assert m,n
 i=m.start();j=s.index("'"+n+"'",i);types[n]=s[i:j].strip()
typesfile='work/checks/nearfar-refinement-reviewed-types.json'
write(typesfile,{'types':types,'type_sha256':{n:sha256(t.encode()).hexdigest() for n,t in types.items()},'axioms':axioms,'checked_declarations':names,'consumer_count':16,'trace_log':logfile,'trace_log_sha256':sha(logfile),'independent_kernel_session':52709,'exit_code':0})
reviewed=dict(p['SM_closure_files_sha256'])
for n in p['body_order']:
 f='work/checks/'+n+'.body.lean';reviewed[f]=sha(f)
closurefile='work/checks/nearfar-refinement-review-closure.json'
write(closurefile,{'status':'independent second kernel passed; exact frozen source bodies reviewed','source':p['source'],'source_sha256':p['source_sha256'],
 'SM_import_roots':p['SM_import_roots'],'SM_closure_files_sha256':p['SM_closure_files_sha256'],'SM_closure_count':12,
 'embedded_frozen_bodies':{n:sha('work/checks/'+n+'.body.lean') for n in p['body_order']},'reviewed_files_sha256':reviewed,
 'root_receipts_sha256':p['root_receipts_sha256'],'root_files_sha256':p['root_files_sha256'],'inherited_review_binding':p['inherited_review_binding'],
 'preparation':pfile,'preparation_sha256':sha(pfile),'trace':p['trace'],'trace_sha256':sha(p['trace']),'examples':p['examples'],'examples_sha256':sha(p['examples']),
 'scope':'Seven new external bodies plus the previously independently reviewed CompositionCutSet dependency; no new canonical files or source-map acceptance.'})
rootruns={}
for n in p['new_body_names']:
 f='work/checks/'+n+'-prototype-result.json';rootruns[n]=dict(load(f),receipt=f,receipt_sha256=sha(f))
prior={'session':38150,'exit_code':1,'source':'work/checks/nearfar-refinement-review-first.lean','log':'work/checks/nearfar-refinement-review-first.log',
 'reason':'Two independent consumer failures only: a missing closing Sigma constructor bracket and a false assumption that dependent marked-subtype transport reduced by rfl. The latter was replaced by an explicit equality-induction proof that transport preserves the underlying marked finset. No implementation or consumer statement was changed.'}
prior['source_sha256']=sha(prior['source']);prior['log_sha256']=sha(prior['log'])
evidence={'independent_trace_source':p['trace'],'independent_trace_source_sha256':sha(p['trace']),
 'independent_trace_log':logfile,'independent_trace_log_sha256':sha(logfile),'independent_kernel_command':'lake env lean ../checks/nearfar-refinement-review-types.lean',
 'independent_kernel_session':52709,'independent_kernel_exit_code':0,'first_independent_run_passed':False,'prior_failed_independent_run':prior,
 'checked_declarations':names,'declaration_count':47,'declaration_axioms':{n:axioms[n] for n in names},
 'additional_examples':examples,'additional_example_count':16,'additional_examples_passed':True,'additional_example_axioms':{n:axioms[n] for n in examples},
 'transparent_predicates_printed':p['transparent_definitions_printed'],'reviewed_types':typesfile,'reviewed_types_sha256':sha(typesfile),
 'independent_closure_evidence':closurefile,'independent_closure_evidence_sha256':sha(closurefile),
 'root_successful_results':rootruns,
 'scope_note':'The independent trace imports the actual canonical definitions and tree/inverse theorems, then embeds the exact eight frozen body fragments in dependency order. It checks the seven new scopes and reruns 16 substantive consumers. Root success is supporting evidence; source fidelity is based on independently reading the source statements, transparent domains, constructions and proofs.'}
old=load('work/reviews/def-nearfar.json')
common={'reviewer':'review_relgp_full-independent-20260911','implementer':'root-implementation-20260910',
 'source':p['source'],'source_sha256':p['source_sha256'],'additional_source_sha256':old['additional_source_sha256'],
 'parameters_reviewed':True,'definition_equivalence_reviewed':True,'verdict':'faithful','implemented_scope_verdict':'faithful','source_claim_accepted':False,
 'statement_sha256':None,'in_theorem_library':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'reviewed_files_sha256':reviewed,'import_closure_roots':p['SM_import_roots'],'import_closure_file_count':12,'embedded_body_count':8,
 'inherited_review_binding':p['inherited_review_binding'],'evidence':evidence,'pins':old['pins'],
 'independence':'The reviewer is distinct from the implementer, independently read the authoritative source and all seven new frozen body/proof scopes, checked their transparent definitions and exact source domains, and authored independent consumer proofs. Only new reviewer check/report evidence was written. No implementation, canonical module, source, map, root receipt or frozen prior review was edited. Source status is not inferred from compilation, historical acceptance, hashes or another review verdict.',
 'accounting':{'original_claims_accepted':0,'definition_increment':0,'proof_increment':0,'canonical_port_and_current_semantic_audit_pending':True,'full_farout_accepted':False,'stage_complete':False}}
for f,h in common['additional_source_sha256'].items():assert sha(f)==h
geo=dict(common)
geo.update({'review_schema':'independent-partial-source-prototype-review-v1','id':'geometric-nearfar-prototype','source_id':'lem:farout','source_line':146,
 'source_lines':'The two geometric identities in item(ii), lines153-154, and their proof201-204; source root/tree definitions10-82 and exact arrays132-144; full lemma146-168 is not accepted.',
 'prototype_file':'work/checks/GeometricNearFar.prototype.lean','prototype_sha256':sha('work/checks/GeometricNearFar.prototype.lean'),
 'main_declarations':p['checked_declarations_by_body']['GeometricNearFar'],
 'reason':'Faithful partial development of the first two assertions of lem:farout(ii). The actual cast open-tree array satisfies the exact geometric Phi equation at every interval, and the actual rooted tree coefficient equals the complete Phi with the far array negated at the source full interval. Gate factors are proved over every commutative ring with invertible two; no G2, field or nontriviality premise is added. The full unary root term is retained. Independent kernel52709 passes47 implementation checks and16 substantive consumers with63 standard-or-empty axiom traces. No factorization, far-only consequence or restricted-word identification is inferred, and full lem:farout remains unaccepted.',
 'mathematical_justification':[
 {'clause':'Exact sign gates in every allowed coefficient ring','assessment':'gate_pair_cast first checks all four nonzero SignType pairs in the integer gate definitions and proves two times the ordinary/root gate equals d-h/d+h. Zero-sign branches contradict the existing nonzero certificates. Integer casting preserves each product and sum in any CommRing; multiplying by the supplied inverse of two cancels the factor two. This avoids assuming division in an arbitrary ring or confusing integer division with ring inversion. G1 supplies exactly the existing near/far nonzero sign certificates.'},
 {'clause':'Actual geometric coefficients and orientation','assessment':'ordinaryWeight_cast and rootWeight_cast cast the actual integer vertex products term by term. The existing geometric near/far sampling definitions identify the reversed chirotope at their exact boundary triples. Ordinary factors become (D-H)/2; root factors become (D+H)/2, represented as the exact nearFarWeight with the far array negated. Both products retain every interior index and the empty product. The labelled representative and physical root g are the already reviewed source conventions.'},
 {'clause':'Every open coordinate and its actual base case','assessment':'For a one-leaf interval, any nonunary composition would have a child of strictly positive leaf count strictly below one, a contradiction. Thus the lower composition sum is empty and the source b coordinate and E coordinate are both one. For a longer interval, the accepted open-tree recursion gives b as minus the complete nonunary product sum. Casting that equality and replacing the actual ordinary weights by their exact geometric half factors makes the identical lower sum cancel in Phi. This proves equality of the entire interval array, without replacing b by a newly chosen solution.'},
 {'clause':'Complete rooted sum with unary contribution','assessment':'geometric_nearFar_root rewrites the actual treeCoefficient into its full sum over every raw composition of fullBoundaryInterval hn. The casts of coefficients and child products distribute over the sum; rootWeight_cast identifies each actual summand with Phi(D,-H). The composition domain is unchanged, including the one-part root with empty vertex product and original interval child. The explicit hn:3<=n matches the source polygon size; the open-word equation needs no stronger size premise.'},
 {'clause':'Independent consequences and precise boundary','assessment':'The independent geometric_open_is_actual_inverse consumer applies the previously proved two-sided inverse to the actual Phi(b)=E equation, identifying the original b array with nearFarInverse of E. geometric_root_retains_full_transform then checks the actual physical-root coefficient after this substitution. These consumers use inverse uniqueness only; they do not replace Phi by F composed with G. Consequently the source far-only output, independence of D and subpolygon restriction assertions remain outside this report.'}],
 'unproved_original_clauses_in_this_reviewed_batch':['The factorization Phi(D,H)=F(H) composed with G(D).','The far-only output F(-H)(F(H) inverse(E)) and independence of D.','Restricted-coordinate inverse compatibility and the actual subpolygon closing-root coefficient.'],
 'not_certified':['No original lem:farout acceptance before full remaining mathematics, canonical port, semantic audit and independent full-source review.','No wall law, soft theorem, R theorem or stage completion.']})
write('work/reviews/geometric-nearfar-prototype.json',geo)
ref=dict(common)
refnames=[x for n in p['new_body_names'] if n!='GeometricNearFar' for x in p['checked_declarations_by_body'][n]]
ref.update({'review_schema':'independent-partial-source-prototype-review-v1','id':'nearfar-refinement-prototype','source_id':'lem:farout','source_line':146,
 'source_lines':'Full raw nested/marked refinement bijection at proof180-187; local independent factor expansion at195-197; neighboring/child-product transport189-194 and the full factorization151 remain outside this batch.',
 'prototype_files_sha256':{n:sha('work/checks/'+n+'.prototype.lean') for n in p['new_body_names'] if n!='GeometricNearFar'},
 'main_declarations':refnames,
 'reason':'Faithful supporting development of the source refinement indexing: all raw compositions correspond to interior cut subsets, nested compositions flatten and restrict inversely, and the actual full nested index domain is equivalent to refined compositions with any selected interior marks. The final forward map has the actual union of inner cut positions and the actual outer interior marks, as independently checked. Unary outer/inner compositions, shared endpoints, no marks and all marks are retained. An exact interior-position/index bijection and local independent near/far product expansion are proved. Independent kernel52709 passes all47 implementation declarations and16 consumers with63 standard-or-empty traces. This is not yet termwise transport or a proof of the factorization, and no original source claim is accepted.',
 'mathematical_justification':[
 {'clause':'Complete interior selections and exact restriction','assessment':'InteriorCutSet is every Finset of positions strictly between the interval endpoints. BoundaryCutSet.interior removes exactly the two fixed endpoints; ofInterior adjoins exactly those endpoints, with mutual inverse proofs by membership. Composing this with the independently reviewed raw composition/cut-set equivalence retains the entire source composition type, including arbitrary natural part count and the empty interior subset. Restriction is the original cut set filtered by a closed interval whose endpoints occur; membership, identity restriction and nested restriction are proved directly. It neither discards a valid interior cut nor invents an endpoint.'},
 {'clause':'Actual part coverage and endpoint cases','assessment':'CompositionSegments derives part bounds and ordered separation from the strictly increasing cut map. For every point before the final endpoint it chooses the greatest cut at or before that point; the next cut must be larger. The last endpoint is separately covered by the final closed part. The original exists_halfOpen_part theorem only states existence despite its comment; NestedCutSets now explicitly proves halfOpen_part_unique, so the independent actual_half_open_partition combines the two into existence and uniqueness even at shared cuts. Closed parts may share endpoints, as required.'},
 {'clause':'Flattening and restriction are exact inverses','assessment':'flattenCutSets is the finite union of all actual inner cut sets. The first inner left endpoint and last inner right endpoint give the global endpoints; every outer cut is an inner endpoint and remains in the union. Restriction back to a fixed outer part recovers its own cut set: cuts from an earlier or later part can enter only at the shared endpoint, which is already present. Conversely every refined cut lies in a closed outer part, so the union of restrictions recovers the entire refined set. These proofs hold for unary outer compositions and arbitrary unary/nonunary inner data. nestedCompositionEquiv composes those inverses with the exact raw composition/cut-set equivalences, not with a cardinality-only representation.'},
 {'clause':'Full marked-refinement domain and actual forward behavior','assessment':'MarkedCuts is every subset of the refined physical interior positions. An outer cut set contained in a refinement is equivalent to such a mark set by deleting/adjoining the two common endpoints. Exchanging the two sigma indices retains the containment certificate, and the raw composition/cut-set equivalence then gives the full source nestedMarkedCutEquiv. The independent marked_forward_has_actual_cuts proves that its refined cut set equals the union of actual inner cut sets and its underlying marked finset equals the original outer interior cuts. The second clause needs equality transport through a dependent subtype; the consumer proves transport preserves the underlying finset by equality induction. Thus the check verifies which equivalence was implemented, not merely that some equivalence exists.'},
 {'clause':'Unary, empty/full marks, complete finite indexing','assessment':'Independent consumers realize every interior selection and every marked refinement, recover the exact raw inner family, prove empty marks give a one-part outer composition, and prove all marks recover the refined outer composition itself. Another consumer verifies both complete sigma domains are finite using the unchanged raw finite composition instances and the full marked-subset type. No arity restriction or omitted endpoint case is inserted. These are the full finite index domains needed for the source sum, although reindexing weighted sums is not claimed here.'},
 {'clause':'Exact interior indices and local independent expansion','assessment':'interiorPosition sends k:Fin(parts-1) to the actual cut(k+1). Strictness proves injectivity and endpoint exclusion; every physical interior cut has an original cut index strictly between zero and parts, so subtraction of one gives its inverse. The consumer strengthens coverage to unique existence and checks that unary compositions have no interior positions. nearFarWeight_marked_expansion rewrites each factor as its negative-far half plus its near half and applies finite distributivity over all subsets of the index set. The independent unary expansion is one, while zero near/far arrays give the expected full/empty choices. This proves the local product expansion in every CommRing with invertible two.'},
 {'clause':'What remains for source factorization','assessment':'The implemented equivalence uses physical cut positions, whereas the local product expansion uses interior cut indices; the exact individual position/index equivalence is present, but this batch does not yet state its induced marked-finset or product transport. More importantly, it does not prove that the neighbors of each unmarked refined cut equal its neighbors in the relevant inner composition, that each marked far triple agrees with the outer one, or that the nested product of child coordinates equals the refined product. Those termwise facts and the resulting finite-sum reindexing are still needed to deduce Phi=F composed with G. No factorization or full farout consequence is inferred from a bijection or successful build alone.'}],
 'unproved_original_clauses_in_this_reviewed_batch':['Termwise near/far triple identification under the actual refinement map.','Nested child-coordinate product equals the refined product; induced marked-subset/product transport.','Complete weighted finite-sum reindexing and Phi=F composed with G.','Full far-only and restricted-interval consequences of lem:farout.'],
 'not_certified':['No original source claim is accepted for these helpers alone.','No full factorization, far-only output or restricted-subpolygon coefficient theorem.','No wall law, soft theorem, R theorem or stage completion.']})
write('work/reviews/nearfar-refinement-prototype.json',ref)
for f in ['work/reviews/geometric-nearfar-prototype.json','work/reviews/nearfar-refinement-prototype.json']:print(f,sha(f))
print('PASS: two faithful partial external reports;47 declarations,16 consumers,63 standard-or-empty traces; no source-map edits or original acceptance.')
