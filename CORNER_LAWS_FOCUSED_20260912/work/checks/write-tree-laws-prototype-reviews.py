from pathlib import Path
from hashlib import sha256
import json, re, datetime
base=Path(__file__).resolve().parents[2]
def load(p): return json.loads((base/p).read_text())
def sha(p): return sha256((base/p).read_bytes()).hexdigest()
def write(p,d): (base/p).write_text(json.dumps(d,indent=2)+'\n')
c=load('work/checks/tree-definition-and-shape-review-closure.json')
frozen=load('work/checks/tree-laws-frozen-external-files.json')
assert all(sha(p)==h for p,h in frozen['frozen_files_sha256'].items())
assert all(sha(p)==h for p,h in c['canonical_SM_files_sha256'].items())
assert len(c['canonical_SM_files_sha256'])==288
assert sha(c['trace'])==c['trace_sha256'] and sha(c['examples'])==c['examples_sha256']
assert sha(c['source'])==c['source_sha256']
for k in frozen['root_successful_sessions']:
 assert (base/f'work/checks/{k}.prototype.lean').read_text().count((base/f'work/checks/{k}.body.lean').read_text())==1
logfile='work/checks/tree-definition-and-shape-review-types.log'
s=(base/logfile).read_text();assert not re.search(r'error[:(]',s) and 'sorryAx' not in s
names=c['checked_declarations'];examples=c['additional_examples'];axioms={};types={}
assert len(names)==56 and len(examples)==16
for n in names+examples:
 m=re.search("'"+re.escape(n)+r"' depends on axioms:\s*\[([^]]*)\]",s)
 if m: axioms[n]=[v.strip() for v in m[1].split(',') if v.strip()]
 else:
  assert "'"+n+"' does not depend on any axioms" in s,n
  axioms[n]=[]
 assert set(axioms[n])<={'propext','Classical.choice','Quot.sound'},n
for n in names:
 m=re.search(r'^'+re.escape(n)+r'(?:\.\{[^}]+\})?(?=\s)',s,re.M);assert m,n
 i=m.start();j=s.index("'"+n+"'",i);types[n]=s[i:j].strip()
typefile='work/checks/tree-laws-reviewed-types.json'
write(typefile,{'types':types,'type_sha256':{n:sha256(t.encode()).hexdigest() for n,t in types.items()},'axioms':axioms})
receipts=['tree-coefficient-prototype-result.json','tree-coefficient-transport-prototype-result.json',
 'TreeChamber-prototype-result.json','PlaneTreeShape-prototype-result.json','PlaneTreeWeights-prototype-result.json',
 'PlaneTreeExpansion-prototype-result.json','PlaneTreeFormal-prototype-result.json']
rootbound={}
for file in receipts:
 p='work/checks/'+file;d=load(p);rootbound[p]=sha(p)
 for f,h in d.get('files_sha256',{}).items():
  f=f if f.startswith('work/') else 'work/'+f
  assert sha(f)==h;rootbound[f]=h
 for k in ['body','prototype','log']:
  if k+'_sha256' in d:
   f=d[k];f=f if f.startswith('work/') else 'work/'+f
   assert sha(f)==d[k+'_sha256'];rootbound[f]=sha(f)
evidence={'independent_trace_source':c['trace'],'independent_trace_source_sha256':sha(c['trace']),
 'independent_trace_log':logfile,'independent_trace_log_sha256':sha(logfile),
 'independent_kernel_command':'lake env lean ../checks/tree-definition-and-shape-review-types.lean',
 'independent_kernel_session':55606,'independent_kernel_exit_code':0,'first_independent_run_passed':False,
 'checked_declarations':names,'declaration_axioms':{n:axioms[n] for n in names},
 'additional_examples':examples,'additional_example_count':16,'additional_examples_passed':True,
 'additional_example_axioms':{n:axioms[n] for n in examples},'printed_types':typefile,'printed_types_sha256':sha(typefile),
 'independent_closure_evidence':'work/checks/tree-definition-and-shape-review-closure.json',
 'independent_closure_evidence_sha256':sha('work/checks/tree-definition-and-shape-review-closure.json'),
 'frozen_manifest':'work/checks/tree-laws-frozen-external-files.json','frozen_manifest_sha256':sha('work/checks/tree-laws-frozen-external-files.json'),
 'all_seven_prototype_bodies_exactly_preserved':True,'all_288_canonical_SM_unchanged':True,
 'root_successful_sessions':frozen['root_successful_sessions'],'root_receipt_and_file_binding':rootbound,
 'prior_reviewer_runs':[
  {'session':12260,'exit_code':1,'reason':'Reviewer-only sum_congr named parameter, dependent one-part product simplification and unused aggregate universe elaboration.'},
  {'session':90006,'exit_code':1,'reason':'Reviewer-only sum binder parentheses and superfluous tactics after the root-term goal had closed.'},
  {'session':75195,'exit_code':1,'reason':'Diagnostic run isolated the same reviewer sum binder parse error and confirmed the Mathlib finite-sum lemmas had standard axioms only.'}],
 'prior_reviewer_evidence_sha256':{str(p.relative_to(base)):sha(str(p.relative_to(base))) for p in sorted((base/'work/checks').glob('tree-definition-and-shape-review-*')) if any(k in p.name for k in ['-initial.','-second.','-diagnostic.'])},
 'correction_scope':'Only independent consumer/check files changed. Every implementation declaration passed in all runs. Failed reviewer artifacts are retained and never counted as passed evidence.',
 'transparent_definitions_printed':c['transparent_definitions_printed']}
inherited={p:sha(p) for p in ['work/reviews/def-root.json','work/reviews/def-gates.json','work/reviews/lem-gates-nonzero.json','work/reviews/finite-compositions-prototype.json','work/reviews/root-gates-port.json']}
common={'review_schema':'independent-full-source-prototype-review-v1','reviewer':'review_relgp_full-independent-20260911','implementer':'root-implementation-20260910',
 'verdict':'faithful','implemented_scope_verdict':'faithful','source_claim_accepted':False,'statement_sha256':None,
 'source':c['source'],'source_sha256':c['source_sha256'],'parameters_reviewed':True,'definition_equivalence_reviewed':True,
 'in_theorem_library':False,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'reviewed_files_sha256':dict(c['SM_closure_files_sha256'],**frozen['frozen_files_sha256']),
 'import_closure_roots':c['SM_import_roots'],'import_closure_file_count':len(c['SM_closure_files_sha256']),
 'inherited_review_binding':inherited,'evidence':evidence,
 'independence':'Reviewer did not author or edit these implementations, canonical modules, source, maps or previous reviews. Only new independent consumers, type/closure traces and review reports were written. The proof strategy and actual source representations were inspected independently; implementation success was not treated as source fidelity. The independent trace copies all seven frozen namespace bodies verbatim over their canonical predecessor imports.',
 'pins':load('work/reviews/def-root.json')['pins'],
 'accounting':{'original_claims_accepted':0,'proof_increment':0,'definition_increment':0,'canonical_port_and_current_semantic_audit_pending':True,'stage_complete':False}}
definition_math=[
 {'clause':'Exact interval and composition domain','assessment':'The recursion uses the already reviewed BoundaryInterval and unchanged raw IntervalComposition types. Each valid interval has positive leaf count, so exactly the printed one-leaf or at-least-two-leaf case applies. The independent interval_recursion_cases check establishes this exhaustion. The finite composition instances enumerate every raw composition; no bounded-arity replacement, selected tree list, G2 assumption or extra geometric certificate is introduced.'},
 {'clause':'Open recursion and termination','assessment':'openTreeRec returns one at leaf count one. Otherwise it is the negative sum over every composition with at least two parts, multiplying its independent ordinary weight by one recursively computed open value for each ordered child part. Every such child has strictly smaller actual leaf count, by the proved part_leaves_lt. This is the well-founded termination measure. The independent source_recursion_unique theorem proves that any function satisfying precisely these source base/recursive equations equals this definition, by strong induction and termwise equality of every child factor. Thus this is the source recursively defined object rather than merely an object satisfying a narrowed recurrence.'},
 {'clause':'Root, full interval and one-part term','assessment':'rootedTreeRec sums over every raw composition, allowing one child, and introduces no extra minus. fullBoundaryInterval is exactly [0,n-1]. The independent full_interval_and_last_root theorem checks both endpoints, the actual n-1 leaves and that the main-text last label n is residue zero. The independent one_part_root_term checks the actual distinguished single composition has root weight one and its unique part is the original interval, so its term is literally the open sum on that interval. The source equations openTreeSum_one/many and treeCoefficient_eq specialize the generic construction to the actual G1 gate weights with integer values.'},
 {'clause':'Representative and root transport','assessment':'openTreeSum_shift and treeCoefficient_shift preserve the same physical root under (P,g) -> (shift a P,g-a), using exact equality of both gate-weight functions. mainTreeCoefficient selects label zero anew; its shifted value therefore equals the original coefficient at root a. It does not assert equality of different physical roots. treesumData bundles both conventions and its transport theorem correctly changes the third component to that original root a. The independent exact_root_transport test explicitly checks this distinction. G1 proof witnesses do not change the values, and the source section uses G1 alone.'},
 {'clause':'No implicit existence or coverage assumption','assessment':'The independent part_leaf_sum proof first derives each natural subtraction identity from strictness of successive cuts. It sums these identities; the first/last finite-sum decompositions cancel all interior cut values, leaving exactly right-left. The resulting source_arity_bound derives parts <= leaves because every child interval has positive leaves. Neither result is assumed by the implementation. These checks also verify the actual domain used by the later tree representation.'}
]
tree_math=[
 {'clause':'Genuine finite ordered plane-tree domain','assessment':'OpenPlaneTree is the inductive representation of an ordinary rooted plane tree on its actual interval: a leaf exists only on a one-leaf interval; a node stores the complete actual composition, at least two parts, and an ordered dependent child array indexed by those parts. RootedPlaneTree separately stores an unrestricted positive-part composition and the same ordered array, so the distinguished root may have one child. Binary ordinary nodes remain present. The independent concrete actualBinaryTree has one ordinary vertex and weight equal to the negative of an arbitrary ordinary-weight value, before any gate specialization. Thus gate-zero binary nodes are not silently removed from the formal-variable domain.'},
 {'clause':'All leaves, labels and order','assessment':'The already reviewed boundary word traverses exactly every nonroot edge occurrence in order. At any internal node the strictly increasing cuts with fixed endpoints partition this leaf interval into successive positive child intervals. Explicitly, each leaf position has a unique largest cut not exceeding it; it lies before the final cut and before the next cut, hence belongs to exactly that part. Strictness makes the parts disjoint in traversal order. Repeating this decomposition preserves the actual leaf labels and their order. The independent part_leaf_sum and actual_tree_leaf_count theorems additionally prove the exact total number of actual leaf constructors is the original interval leaf count. The independent only_leaf_on_one_leaf_interval proves no spurious internal node can occur at the base case.'},
 {'clause':'Ungrafting, grafting and finiteness','assessment':'openPlaneTreeUngraft is an explicit equivalence to a leaf summand or a sigma of the full top composition and every ordered child choice. Both inverse laws are proved on the actual constructors. The independent arbitrary_graft_and_ungraft check instantiates both directions for an arbitrary composition and child array. The ordinary tree type is finite by strong induction on actual interval leaves: every child decreases, so each child type is finite; the full finite composition index and finite dependent product give a finite grafting domain. Injectivity of ungrafting proves finiteness of the entire tree type. Root finiteness follows from the unrestricted finite composition sigma and child products. No chosen height bound, omitted arity or externally supplied finite tree list is assumed. Independent enumeration checks use these actual Fintype instances.'},
 {'clause':'Exact signed vertex product','assessment':'A leaf contributes one, zero ordinary vertices and empty ordinary product. At an ordinary node weight is negative ordinaryWeight times the product of child weights; ordinaryCount is one plus the sum of child counts; ordinaryProduct multiplies the node weight without its sign and every child product. Induction replaces each child weight by its signed product. Finite-product distributivity separates the powers of -1, and the product-of-powers identity adds their exponents; multiplying the top minus adds exactly one. At the distinguished root only child counts are summed, and its separate root weight multiplies the child weights without another minus. Both signed-product identities are proved over arbitrary commutative rings; the independent arbitrary_root_weight_formula checks the root exponent and factor explicitly.'},
 {'clause':'Term-by-term expansion and multiplicities','assessment':'For a one-leaf interval, the entire ordinary tree type consists of its unique leaf and its sum is one. For a larger interval, the leaf summand is empty; the ungrafting equivalence reindexes the sum by the exact top composition and independent ordered child choices. Finite distributivity changes the sum over choice functions into a product of child sums, while retaining the single top minus. This is exactly the open recursion. Strong induction on leaf count proves openTreeRec_eq_planeTreeSum. At the root the unrestricted composition sigma yields the analogous sum, including the one-child term and no root minus. The explicit identity equivalence reconciles two Fintype instances of the same sigma type; it does not merge equal-valued terms. Substituting the signed-product theorem gives the complete displayed source formula with the correct multiplicities.'},
 {'clause':'Independent formal variables and every evaluation','assessment':'TreeWeightIndex is Bool times the sigma of every actual interval/composition. False indexes the ordinary indeterminate and true the distinguished-root indeterminate; every formal weight is the corresponding X in MvPolynomial over integers, with no geometric relations imposed. The independent ordinary_root_variables_distinct theorem evaluates these two tags to zero and one to prove they remain distinct even for the same composition. The generic arbitrary-CommRing expansion specializes to this polynomial ring, proving the source formal identity. Ring homomorphisms preserve each finite tree evaluation by induction, then the finite sum. The eval2 homomorphism from integers therefore yields the same recursion for every assignment in any commutative ring. The independent arbitrary_separate_assignments theorem constructs an assignment realizing every pair of ordinary/root weight functions; no root/ordinary equality, half-invertibility or sign constraint is required.'},
 {'clause':'Full actual aggregate and source scope','assessment':'treeCoefficient_eq_signed_planeTreeSum specializes to the actual integer G1 gate weights on the full interval. treesum_trees includes that geometric identity, the independent-variable polynomial identity, and universal evaluation compatibility in arbitrary ring universes. The independent actual_source_identity extracts the actual geometric clause without supplying a plane-tree identity as a premise; the irrelevant evaluation universe is explicitly instantiated in the consumer. Source vertex weights and m=s agree with the already reviewed gates on the actual cuts. The helper TreeChamber developments are separately reviewed below and are not required as extra premises. No wall law, soft theorem or R claim is implied by this tree identity.'}
]
for file,ident,prototype,decls,lines,reason,math in [
 ('tree-coefficient-prototype','def:treesum','TreeCoefficientTransport',['SM.openTreeRec','SM.rootedTreeRec','SM.openTreeSum','SM.treeCoefficient','SM.mainTreeCoefficient','SM.treesumData'],'66-82; source section G1-only domain lines3-6',
  'Faithful complete implementation of def:treesum, including all open intervals, the exact recurrence, unrestricted root sum, literal one-part term, actual G1 gates, full interval and last-edge convention. Physical-root shift transport and the distinct fixed-label alias are preserved.',definition_math),
 ('plane-tree-prototype','lem:treesum-trees','PlaneTreeFormal',['SM.OpenPlaneTree','SM.openPlaneTreeUngraft','SM.RootedPlaneTree','SM.rootedTreeRec_eq_signed_planeTreeSum','SM.planeTree_formal_identity','SM.planeTree_formal_evaluation','SM.treesum_trees'],'84-110; supporting binary remark112-116 and definitions10-82',
  'Faithful complete implementation of lem:treesum-trees: the actual finite ordered plane-tree domain retains all source arities; ungrafting/grafting supplies the termwise correspondence; the signed vertex-product identity holds for independent commutative-ring weights, explicitly as a polynomial identity over integers and under every ring evaluation, and specializes to the actual G1 gates.',tree_math)
]:
 d=dict(common);d.update({'id':file,'source_id':ident,'source_lines':lines,'prototype_file':f'work/checks/{prototype}.prototype.lean',
  'prototype_sha256':sha(f'work/checks/{prototype}.prototype.lean'),'main_declarations':decls,
  'reason':reason+' Independent kernel55606 passes all56 implementation checks and16 substantive consumers with standard axioms only. This is a full-source external verdict; exact canonical port, semantic hash and current whole-project audit remain required before original acceptance.',
  'mathematical_justification':math,'not_certified':['No canonical or original source acceptance yet.','No chamber proposition, wall law, soft theorem, R theorem or overall stage completion is accepted.']})
 write('work/reviews/'+file+'.json',d);print(file,sha('work/reviews/'+file+'.json'))
chamber=dict(common);chamber.update({'id':'tree-chamber-prototype','source_id':'prop:A-chamber','source_lines':'120-128 supporting scope only',
 'review_schema':'independent-partial-source-prototype-review-v1','main_declarations':[n for n in names if n in ['SM.tree_data_eq_of_chi','SM.labelled_chamber_chi_constant','SM.tree_data_labelled_chamber_constant','SM.tree_data_G1_path_constant','SM.treeCoefficient_quotient_chamber_transport']],
 'prototype_file':'work/checks/TreeChamber.prototype.lean','prototype_sha256':sha('work/checks/TreeChamber.prototype.lean'),
 'reason':'Faithful supporting transport scope. Equality of every actual chirotope entry gives equality of every near/far sign, both weights, all open sums and the rooted coefficient. The labelled chamber is the actual connected component of GenericTuple; continuity of its discrete sign maps and preconnectedness make the chirotope constant there. The G1 path clause retains the actual path and the printed constant-chirotope premise. The quotient chamber preimage theorem supplies a cyclic shift and transports the physical root to g-a; it does not infer equality between distinct roots. All five declarations pass in the independent56-declaration trace. This helper report does not accept the original chamber proposition or any subsequently authored aggregate.',
 'mathematical_justification':[
  {'clause':'Chirotope and labelled component','assessment':'The equality proof substitutes actual gate-weight functions into the already defined recursion, so it requires G1 alone. For genuine labelled chambers, isPreconnected_connectedComponent.constant applies to continuous_generic_chi with its discrete target, both endpoints belonging to the same component. This uses the source topological chamber and not a sign-pattern surrogate.'},
  {'clause':'Path and quotient transport','assessment':'The path is a Path in the actual G1 subtype and the premise states its chirotope is constant at every pair of times; applying the chirotope theorem gives all values. On the polygon quotient, chamber_preimage_eq_cyclic_union yields an actual shift a whose labelled component contains Q. Labelled constancy then compares Q at root g-a with shift a P at the same transported root; treeCoefficient_shift compares that value with P at root g. No arbitrary fixed-label chamber invariance is asserted.'}],
 'not_certified':['No full prop:A-chamber original acceptance or subsequent TreeChamberClaim aggregate review.','No canonical port, wall law, soft theorem or stage completion.']})
write('work/reviews/tree-chamber-prototype.json',chamber);print('tree-chamber-prototype',sha('work/reviews/tree-chamber-prototype.json'))
