from pathlib import Path
from hashlib import sha256
import json,re,datetime
base=Path(__file__).resolve().parents[2]
def load(p):return json.loads((base/p).read_text())
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def write(p,d):(base/p).write_text(json.dumps(d,indent=2)+'\n')
c=load('work/checks/nearfar-inverse-review-closure.json')
for field in ['frozen_prototype_body_and_root_log_sha256','root_receipts_sha256','canonical_SM_files_sha256']:
 assert all(sha(p)==h for p,h in c[field].items())
assert len(c['canonical_SM_files_sha256'])==294 and len(c['SM_closure_files_sha256'])==6
assert sha(c['trace'])==c['trace_sha256'] and sha(c['examples'])==c['examples_sha256']
assert sha(c['source'])==c['source_sha256']
logfile='work/checks/nearfar-inverse-review-types.log';s=(base/logfile).read_text()
assert not re.search(r'error[:(]',s) and 'sorryAx' not in s
names=c['checked_declarations'];examples=c['additional_examples'];axioms={};types={}
assert len(names)==37 and len(examples)==11
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
typefile='work/checks/nearfar-inverse-reviewed-types.json'
write(typefile,{'types':types,'type_sha256':{n:sha256(t.encode()).hexdigest() for n,t in types.items()},'axioms':axioms})
evidence={'independent_trace_source':c['trace'],'independent_trace_source_sha256':sha(c['trace']),
 'independent_trace_log':logfile,'independent_trace_log_sha256':sha(logfile),
 'independent_kernel_command':'lake env lean ../checks/nearfar-inverse-review-types.lean','independent_kernel_session':44099,
 'independent_kernel_exit_code':0,'first_independent_run_passed':True,'checked_declarations':names,
 'declaration_axioms':{n:axioms[n] for n in names},'additional_examples':examples,'additional_example_count':11,
 'additional_examples_passed':True,'additional_example_axioms':{n:axioms[n] for n in examples},
 'transparent_predicates_printed':c['transparent_definitions_printed'],'printed_types':typefile,'printed_types_sha256':sha(typefile),
 'independent_closure_evidence':'work/checks/nearfar-inverse-review-closure.json','independent_closure_evidence_sha256':sha('work/checks/nearfar-inverse-review-closure.json'),
 'root_receipts_sha256':c['root_receipts_sha256'],'frozen_prototype_body_and_root_log_sha256':c['frozen_prototype_body_and_root_log_sha256'],
 'all_six_frozen_bodies_verbatim_in_trace':True,'all_294_canonical_SM_unchanged':True,
 'root_successful_sessions':{'NearFar':36834,'UnaryComposition':69486,'TriangularInverse':69486,'NearFarTriangular':69486,'TriangularPolynomial':98288,'NearFarEquivariance':94140},
 'prior_implementation_attempt_note':'UnaryComposition first root attempt required elaboration corrections before the frozen successful second attempt. All current frozen bodies have successful root receipts. This independent combined run passed on its first attempt.'}
binding={p:sha(p) for p in ['work/reviews/def-root.json','work/reviews/def-gates.json','work/reviews/lem-gates-nonzero.json','work/reviews/finite-compositions-prototype.json']}
common={'reviewer':'review_relgp_full-independent-20260911','implementer':'root-implementation-20260910',
 'source':c['source'],'source_sha256':c['source_sha256'],
 'additional_source_sha256':{'reference/SM/sm-1-polygons.tex':sha('reference/SM/sm-1-polygons.tex')},
 'parameters_reviewed':True,'definition_equivalence_reviewed':True,'verdict':'faithful','implemented_scope_verdict':'faithful',
 'source_claim_accepted':False,'statement_sha256':None,'in_theorem_library':False,
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewed_files_sha256':{**c['SM_closure_files_sha256'],**c['frozen_prototype_body_and_root_log_sha256']},
 'import_closure_roots':c['SM_import_roots'],'import_closure_file_count':6,'inherited_review_binding':binding,'evidence':evidence,
 'pins':load('work/reviews/def-root.json')['pins'],
 'independence':'Reviewer did not author or edit the six implementation bodies, prototypes, canonical modules, source, maps or previous reviews. Only new independent source consumers, trace/closure/type evidence and these reports were written. The source and proofs were inspected directly; successful compilation was not treated as source fidelity. All frozen implementation bodies were copied verbatim over their actual canonical predecessor imports.',
 'accounting':{'original_claims_accepted':0,'definition_increment':0,'proof_increment':0,'canonical_port_and_current_semantic_audit_pending':True,'full_farout_accepted':False,'stage_complete':False}}
definition_math=[
 {'clause':'Complete finite coordinate domains','assessment':'IncreasingBoundaryTriple stores precisely lower<middle<upper in Fin n, the bounded natural presentation of0<=x<y<z<=N with N=n-1. TripleArray is an unrestricted scalar-valued function on this full index type; IntervalArray is a scalar-valued function on every actual BoundaryInterval. The independent all_raw_increasing_triples check admits every source natural triple, deriving all Fin n bounds from the printed last bound. Independent injective encodings into Fin n triples and pairs prove both coordinate index sets finite. This does not assert that the scalar-valued array types themselves are finite, and does not truncate or choose a subset of coordinates.'},
 {'clause':'Exact neighboring and endpoint triples','assessment':'For an interior index k:Fin(parts-1), nearTriple contains cut k, cut(k+1), cut(k+2), while farTriple contains the fixed interval left endpoint, cut(k+1), and fixed right endpoint. Strict composition cuts prove the stored inequalities; first/last equalities identify the endpoint positions exactly. Under the source indexing with cuts1 through s-1 this is precisely the neighboring D triple and enclosing H triple. The complete raw composition domain and all interior cut positions are unchanged from the independently accepted root/gate definitions.'},
 {'clause':'Exact half factors and complete transform','assessment':'nearFarWeight multiplies (D nearTriple-H farTriple) times the inverse of two at every interior cut. nearFarTransform sums this actual product times the ordered product of child coordinates over every composition, including the unary composition. The independent every_half_factor_is_exact check multiplies the weight by2^(parts-1) and recovers exactly the product of every unhalved numerator; each factor cancels its inverse of two and finite-product distributivity gives the stated exponent. This holds in arbitrary commutative rings with invertible two, without a field, ordered-ring or nontriviality premise. The independent unary_term_is_exact confirms the empty gate product and the sole actual child give precisely X I.'},
 {'clause':'F, G and leaf indicator','assessment':'farTransform is exactly Phi with D identically zero; nearTransform is exactly Phi with H identically zero. boundaryUnitArray is one exactly when right=left+1, and zero otherwise. The independent unit_array_is_leaf_indicator checks this agrees with actual interval leaf count one; the proof uses strict interval endpoints and natural subtraction, and does not rely on distinguishing zero from one in the coefficient ring.'},
 {'clause':'Geometric arrays and representative descent','assessment':'geometricBoundaryArray is the integer sign of the actual chi entry at boundary upper, middle, lower, coerced into the arbitrary coefficient ring. Both geometric D and H are this same array and are sampled at different triples. The near and far sampling lemmas are definitional equalities with the already reviewed nearSign and farSign. The array formula is available on arbitrary labelled tuples, hence on the source G1 polygon domain without adding a G2 restriction. The separately frozen geometricBoundaryArray_shift explicitly cancels the tuple shift a with the root shift g-a at every actual boundary label. The independent geometric_arrays_use_same_physical_root consumer verifies this equality of the whole geometric array. The abstract transforms therefore read unchanged arrays under the permitted simultaneous representative/root change.'},
 {'clause':'Complete aggregate and proof boundary','assessment':'nearfarData exposes the complete increasing-triple type, Phi, F, G, E and the geometric array function over the exact ring/size parameters. The transparent print and independent37-declaration trace bind these actual definitions. Ambient n>=3 supplies the supplementary NeZero condition; no new axiom or geometric premise is inserted. This is the full definition only. Neither factorization nor the geometric or restricted-interval output assertions are claimed by this definition review.'}
]
inverse_math=[
 {'clause':'Separating precisely the unary term','assessment':'eq_single_of_parts_eq_one proves a composition of one part has only its two fixed endpoint cuts, hence is the distinguished single composition. Its sole part is the original interval and its coordinate product is X I. nonSingleEquiv identifies every other unchanged raw composition with one having at least two parts, using parts_pos and the proven unary uniqueness. nearFarTransform_eq_triangular separates the actual finite sum at that unique element; its weight is the empty product one, so the head term is X I. The remaining coefficients, cuts and terms are transported unchanged by the explicit subtype equivalence. Thus the generic triangular transform is the exact source Phi.'},
 {'clause':'Constructed inverse and actual base coordinate','assessment':'triangularInverse subtracts the complete nonunary sum from target coordinate Y I. Each recursive factor uses an actual child interval whose leaf count strictly decreases. This proves termination and uses only subtraction, finite sums and finite products; it never divides by a coefficient. On a one-leaf interval, no composition can have at least two parts because every child would have positive leaf count strictly below one. The independent inverse_base_coordinate proves the nonunary index type empty and the inverse coordinate equal to Y I, exactly the source base step.'},
 {'clause':'Both identities and uniqueness on the full array domain','assessment':'Substituting the inverse equation into the triangular transform cancels the identical lower sum pointwise, proving transform after inverse is the identity. For inverse after transform, strong recursion proves every lower inverse coordinate equals its original X coordinate; termwise equality of the finite products and sums then cancels the lower sum. Both proofs apply to every target or source array with unrestricted coefficient weights. The exact Phi comparison transfers these two identities to nearFarInverse. Uniqueness follows by applying the proved inverse to any solution, not by adding a uniqueness premise. The independent unique_solution_for_every_target confirms existence and uniqueness for every actual source target array, and zero_triangular_weights_give_identity checks the normalization.'},
 {'clause':'Explicit coordinate polynomials and evaluation','assessment':'triangularInversePolynomial replaces each scalar coefficient by its constant polynomial C and each target entry by its independent variable X in MvPolynomial indexed by the complete interval coordinate type. The recursion still consists only of finite polynomial operations. map_triangularInverse is proved down the same strictly decreasing child intervals and shows every ring homomorphism commutes with the inverse construction. Evaluating the coordinate polynomial by the identity coefficient homomorphism and arbitrary target array therefore gives exactly triangularInverse. The independent inverse_is_coordinate_polynomial verifies this equality for the actual near-far coefficients and every coordinate. nearFar_has_polynomial_inverse supplies this explicit polynomial family and both full inverse identities under evaluation, rather than merely a bijective function without polynomial evidence.'},
 {'clause':'Exact partial source boundary','assessment':'This proves only the two-sided polynomial-inverse assertion in the first sentence of lem:farout(i), matching the first paragraph of its proof. D and H remain arbitrary fixed coefficient arrays; the inverse coordinates are polynomials in the target array entries over that coefficient ring. The factorization Phi=F composed with G, all geometric b/E/A output identities, the complete-output independence of D, and all restricted-interval clauses are not proved by these files. The original lemma must remain incomplete and unaccepted. No geometric farout consequence is inferred from inverse existence alone.'}
]
definition=dict(common);definition.update({'review_schema':'independent-full-source-prototype-review-v1','id':'nearfar-prototype','source_id':'def:nearfar',
 'source_line':132,'source_lines':'132-144; section G1-only domain3-6; rooted convention10-15; representative permission sm-1-polygons.tex55-60',
 'prototype_file':'work/checks/NearFarEquivariance.prototype.lean','prototype_sha256':sha('work/checks/NearFarEquivariance.prototype.lean'),
 'main_declarations':['SM.IncreasingBoundaryTriple','SM.TripleArray','SM.IntervalArray','SM.nearFarTransform','SM.farTransform','SM.nearTransform','SM.boundaryUnitArray','SM.geometricBoundaryArray','SM.nearfarData','SM.geometricBoundaryArray_shift'],
 'reason':'Faithful complete implementation of def:nearfar: all bounded increasing triples and interval coordinates, exact neighboring/endpoint samples, every source composition including its unary term, correct half products, F/G specialization, E and the actual reversed chirotope arrays. The full geometric array has the source simultaneous shift-equivariance. Independent kernel44099 passes37 declarations and11 substantive consumers with48 standard-only traces. Original definition acceptance remains pending exact canonical port, semantic hash and current audit.',
 'mathematical_justification':definition_math,
 'not_certified':['No original acceptance before canonical port/audit.','No full lem:farout, factorization, geometric output, restricted-interval claim, wall law, soft theorem, R theorem or stage completion.']})
write('work/reviews/nearfar-prototype.json',definition)
partial=dict(common);partial.update({'review_schema':'independent-partial-source-prototype-review-v1','id':'triangular-polynomial-inverse-prototype','source_id':'lem:farout',
 'source_line':146,'source_lines':'Inverse portion of item(i), lines148-149, and first proof paragraph170-178; full lemma146-168 remains incomplete',
 'prototype_file':'work/checks/TriangularPolynomial.prototype.lean','prototype_sha256':sha('work/checks/TriangularPolynomial.prototype.lean'),
 'main_declarations':['SM.triangularInverse','SM.triangularTransform_inverse','SM.triangularInverse_transform','SM.nearFarTransform_eq_triangular','SM.nearFarInverse','SM.nearFarTransform_inverse','SM.nearFarInverse_transform','SM.nearFar_solution_unique','SM.triangularInversePolynomial','SM.triangularInversePolynomial_eval','SM.nearFar_has_polynomial_inverse'],
 'reason':'Faithful partial development of lem:farout(i), proving the exact source Phi has an explicit two-sided polynomial inverse. Unary uniqueness, exact sum separation, full-domain recursive inversion, both inverse identities, uniqueness and coordinate-polynomial evaluation are proved without new axioms or strengthened premises. Independent kernel44099 passes37 declarations and11 substantive consumers. Factorization and every remaining farout clause are outside the proved scope; the original lemma is not accepted.',
 'mathematical_justification':inverse_math,
 'unproved_original_clauses':['Phi(D,H)=F(H) composed with G(D).','Geometric Phi(b)=E and A_g=Phi(D,-H)(b) at0N.','Far-only output and complete-output independence of D.','Restricted-interval E/B values and identification with the subpolygon closing-root coefficient.'],
 'not_certified':['Full original lem:farout remains incomplete and unaccepted.','No geometric factorization/output consequence, wall law, soft theorem, R theorem or stage completion.']})
write('work/reviews/triangular-polynomial-inverse-prototype.json',partial)
print('nearfar-prototype',sha('work/reviews/nearfar-prototype.json'))
print('triangular-polynomial-inverse-prototype',sha('work/reviews/triangular-polynomial-inverse-prototype.json'))
