from pathlib import Path
from hashlib import sha256
import json,re,datetime
base=Path(__file__).resolve().parents[2]
def load(p):return json.loads((base/p).read_text())
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def write(p,d):(base/p).write_text(json.dumps(d,indent=2)+'\n')
def digest(d):return sha256(json.dumps(d,sort_keys=True,separators=(',',':')).encode()).hexdigest()
c=load('work/checks/tree-laws-canonical-review-closure.json');prep=load('work/checks/tree-laws-canonical-review-preparation.json')
r=load('work/checks/tree-laws-port-audit-result.json');a=load(r['audit']);receipt=load(r['receipt'])
assert r['session']==14456 and r['exit_code']==0 and receipt['passed'] and not receipt['stage_accepted']
for k in ['receipt','audit','log']:assert sha(r[k])==r[k+'_sha256']
assert all(sha('work/lean/'+p)==h for p,h in receipt['project_sha256'].items())
assert all(sha(p)==h for p,h in receipt['bundle_sha256'].items())
assert all(sha(p)==h for p,h in c['canonical_SM_files_sha256'].items())
assert len(c['canonical_SM_files_sha256'])==294
prior=load('work/checks/checkpoint-061-declaration-audit.json')['statement_hashes']
assert len(prior)==34 and all(a['statement_hashes'][k]==h for k,h in prior.items())
assert sha(c['trace'])==c['trace_sha256']==prep['trace_sha256']
logfile='work/checks/tree-laws-canonical-review-types.log';s=(base/logfile).read_text()
assert not re.search(r'error[:(]',s) and 'sorryAx' not in s
names=c['checked_declarations'];examples=c['additional_examples'];axioms={};types={}
assert len(names)==58 and len(examples)==20
for n in names+examples:
 m=re.search("'"+re.escape(n)+r"' depends on axioms:\s*\[([^]]*)\]",s)
 if m:axioms[n]=[x.strip() for x in m[1].split(',') if x.strip()]
 else:
  assert "'"+n+"' does not depend on any axioms" in s,n
  axioms[n]=[]
 assert set(axioms[n])<={'propext','Classical.choice','Quot.sound'},n
for n in names:
 m=re.search(r'^'+re.escape(n)+r'(?:\.\{[^}]+\})?(?=\s)',s,re.M);assert m,n
 i=m.start();j=s.index("'"+n+"'",i);types[n]=s[i:j].strip()
seen=set()
for file in ['tree-laws-reviewed-types.json','tree-chamber-claim-reviewed-types.json']:
 for n,t in load('work/checks/'+file)['types'].items():
  assert types[n]==t,n;seen.add(n)
assert seen==set(names)
rows=[('def:treesum','SM.treesumData','SM.TreeCoefficient','tree-coefficient-prototype','def-treesum',66,7),
 ('lem:treesum-trees','SM.treesum_trees','SM.PlaneTreeFormal','plane-tree-prototype','lem-treesum-trees',84,11),
 ('prop:A-chamber','SM.A_chamber','SM.TreeChamber','tree-chamber-claim-prototype','prop-A-chamber',120,19)]
required={
 'def:treesum':['SM.treesumData','SM.openTreeRec','SM.rootedTreeRec','SM.openTreeSum','SM.treeCoefficient','SM.mainTreeCoefficient','SM.fullBoundaryInterval','SM.IntervalComposition','SM.IntervalComposition.mk','SM.IntervalComposition.part','SM.IntervalComposition.finite','SM.IntervalComposition.fintype','SM.IntervalComposition.ordinaryWeight','SM.IntervalComposition.rootWeight','SM.BoundaryInterval','SM.BoundaryInterval.mk','SM.BoundaryInterval.leaves','SM.G1','SM.chi','SM.det'],
 'lem:treesum-trees':['SM.treesum_trees','SM.RootedPlaneTree','SM.OpenPlaneTree','SM.OpenPlaneTree.leaf','SM.OpenPlaneTree.node','SM.RootedPlaneTree.ordinaryCount','SM.RootedPlaneTree.ordinaryProduct','SM.OpenPlaneTree.ordinaryCount','SM.OpenPlaneTree.ordinaryProduct','SM.instFiniteRootedPlaneTree','SM.instFintypeRootedPlaneTree','SM.TreeWeightIndex','SM.formalOrdinaryWeight','SM.formalRootWeight','SM.rootedTreeRec','SM.openTreeRec','SM.treeCoefficient','SM.fullBoundaryInterval','SM.IntervalComposition.mk','SM.BoundaryInterval.mk','SM.G1'],
 'prop:A-chamber':['SM.A_chamber','SM.TreeDataEqual','SM.G1','SM.G2','SM.Generic','SM.GenericTuple','SM.GenericPolygon','SM.labelledChamber','SM.chamber','SM.genericShift','SM.polygonProjection','SM.shift','SM.cyclicSetoid','SM.genericCyclicSetoid','SM.IntervalComposition.mk','SM.BoundaryInterval.mk','SM.openTreeSum','SM.treeCoefficient','SM.chi']}
semantic={}
for ident,decl,module,prototype,filename,line,count in rows:
 target=next(d for d in a['audit']['declarations'] if d['declaration']==decl)
 assert target['module']==module and target['kind']==('definition' if ident.startswith('def:') else 'theorem')
 sh=digest(target['semantic_dependencies']);assert sh==a['statement_hashes'][ident]==r['new_statement_hashes'][ident]
 sn={d['declaration'] for d in target['semantic_dependencies']};assert set(required[ident])<=sn
 semantic[ident]={'declaration':decl,'module':module,'statement_sha256':sh,'semantic_dependency_count':len(sn),
  'semantic_declarations':sorted(sn),'required_transparent_definitions_and_constructors':required[ident],
  'semantic_dependency_record_sha256':{d['declaration']:digest(d) for d in target['semantic_dependencies']}}
 p=load('work/reviews/'+prototype+'.json');assert sha(p['source'])==p['source_sha256']
 for f,h in p.get('additional_source_sha256',{}).items():assert sha(f)==h
semfile='work/checks/tree-laws-canonical-semantic-review.json'
write(semfile,{'targets':semantic,'canonical_printed_types':types,'canonical_printed_type_sha256':{n:sha256(t.encode()).hexdigest() for n,t in types.items()},
 'all_58_prototype_canonical_printed_types_equal':True,'axioms':axioms,'all_34_prior_semantic_hashes_unchanged':True,
 'prior_semantic_audit':'work/checks/checkpoint-061-declaration-audit.json','prior_semantic_audit_sha256':sha('work/checks/checkpoint-061-declaration-audit.json')})
evidence={'independent_trace_source':c['trace'],'independent_trace_source_sha256':sha(c['trace']),
 'independent_trace_log':logfile,'independent_trace_log_sha256':sha(logfile),
 'independent_kernel_command':'lake env lean ../checks/tree-laws-canonical-review-types.lean','independent_kernel_session':3756,'independent_kernel_exit_code':0,'first_independent_run_passed':True,
 'checked_declarations':names,'declaration_axioms':{n:axioms[n] for n in names},'additional_examples':examples,
 'additional_example_count':20,'additional_examples_passed':True,'additional_example_axioms':{n:axioms[n] for n in examples},
 'all_58_prototype_canonical_printed_types_equal':True,'transparent_predicates_printed':prep['transparent_definitions_printed'],
 'independent_closure_evidence':'work/checks/tree-laws-canonical-review-closure.json','independent_closure_evidence_sha256':sha('work/checks/tree-laws-canonical-review-closure.json'),
 'canonical_semantic_evidence':semfile,'canonical_semantic_evidence_sha256':sha(semfile),
 'root_result_file':'work/checks/tree-laws-port-audit-result.json','root_result_sha256':sha('work/checks/tree-laws-port-audit-result.json'),
 'successful_build_session':14456,'successful_build_exit_code':0,'successful_build_log':r['log'],'successful_build_log_sha256':sha(r['log']),
 'audit_receipt':r['receipt'],'audit_receipt_sha256':sha(r['receipt']),'declaration_audit':r['audit'],'declaration_audit_sha256':sha(r['audit']),
 'scope_note':'The same20 substantive external consumers were rerun using canonical imports only, including recurrence uniqueness, one-part term, exact leaf counts, binary formal weight, arbitrary polynomial assignments, actual connected components and all-quantity quotient root transport.'}
binding={p:sha(p) for p in ['work/reviews/tree-coefficient-prototype.json','work/reviews/plane-tree-prototype.json','work/reviews/tree-chamber-claim-prototype.json',
 'work/reviews/tree-chamber-prototype.json','work/checks/tree-laws-reviewed-types.json','work/checks/tree-chamber-claim-reviewed-types.json',
 'work/checks/tree-definition-and-shape-review-examples.lean','work/checks/tree-chamber-claim-review-examples.lean']}
portfile='work/reviews/tree-laws-port.json'
write(portfile,{'review_schema':'independent-full-source-port-review-v1','id':'tree-laws-port','source_ids':[x[0] for x in rows],
 'reviewer':'review_relgp_full-independent-20260911','implementer':'root-implementation-20260910','verdict':'faithful','source_claim_accepted':False,
 'parameters_reviewed':True,'definition_equivalence_reviewed':True,'in_theorem_library':True,
 'statement_hashes':{k:v['statement_sha256'] for k,v in semantic.items()},
 'reason':'All six installed canonical namespace bodies equal the exact concatenations of the eight independently reviewed frozen body fragments. Import headers alone replace embedded predecessor bodies. All288 prior SM modules remain byte-for-byte unchanged, Supplemental adds exactly the two expected root imports, and all34 previous source semantic hashes are unchanged. The independent canonical-only kernel3756 passes58 declaration checks and20 substantive consumer theorems with78 standard-only axiom traces. Every canonical printed implementation type exactly matches its independent prototype trace. The source statements, actual definitions and proofs were independently read and their current transparent dependency closures were checked against immutable audit062; their semantic hashes were independently recomputed. The source-specific reports certify the three original rows. This exact-port report does not edit the source map.',
 'ports':c['ports'],'main_declarations':names,'reviewed_files_sha256':c['SM_closure_files_sha256'],
 'import_closure_roots':c['SM_import_roots'],'import_closure_file_count':23,'prior288_unchanged':True,'current_SM_count':294,
 'all_34_prior_semantic_hashes_unchanged':True,'prototype_review_binding':binding,'evidence':evidence,
 'not_certified':['No extra original claims for helpers.','No wall law, soft theorem, R theorem or overall stage completion.']})
for ident,decl,module,prototype,filename,line,count in rows:
 pfile='work/reviews/'+prototype+'.json';p=load(pfile);cl=c['individual_import_closures'][module];assert len(cl)==count
 reason=p['reason'].split(' Independent kernel')[0]
 math=list(p['mathematical_justification'])
 math.append({'clause':'Canonical statement, definition closure and independent evidence','assessment':'The exact reviewed bodies are now installed as canonical modules, with every previous source module unchanged. All58 canonical printed implementation types exactly equal the separately checked prototype types. The canonical-only independent kernel3756 passes the same20 substantive consumers, without embedding implementation definitions in the check file. The immutable whole-project audit062 passes; its complete transparent semantic closure is checked for the actual recursion, raw compositions, tree constructors, finite instances, vertex counts/products, formal-variable indices, actual G1/chamber definitions and root transport as relevant to this source row. The source semantic hash is independently recomputed from those records. G2 appears only inside the genuine generic-chamber definition; the source G1 chirotope/path/recursion clauses do not acquire that premise. No axiom or unproved source interface is introduced.'})
 d={k:p[k] for k in ['reviewer','implementer','source','source_lines','source_sha256','parameters_reviewed','definition_equivalence_reviewed','pins','independence']}
 if 'additional_source_sha256' in p:d['additional_source_sha256']=p['additional_source_sha256']
 d.update({'review_schema':'independent-full-source-review-v1','id':ident,'source_id':ident,'source_line':line,'labels':[ident],
  'declaration':decl,'module':module,'verdict':'faithful','source_claim_accepted':True,'in_theorem_library':True,
  'statement_sha256':semantic[ident]['statement_sha256'],'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
  'reason':reason+' The exact canonical port passes independent kernel3756 with58 declaration checks and20 substantive consumers; all printed types match the reviewed prototypes and immutable whole-project audit062 passes. This exact source row is faithful and eligible for map acceptance.',
  'mathematical_justification':math,'reviewed_files_sha256':cl,'import_closure_roots':[module],'import_closure_file_count':count,
  'semantic_dependency_count':semantic[ident]['semantic_dependency_count'],'required_semantic_definitions_checked':required[ident],
  'prototype_review':pfile,'prototype_review_sha256':sha(pfile),'prototype_review_binding':binding,
  'port_review':portfile,'port_review_sha256':sha(portfile),'evidence':evidence,
  'audit_context':{'receipt':r['receipt'],'receipt_sha256':sha(r['receipt']),'root_audit_session':14456,'root_audit_exit_code':0,
   'passed':True,'stage_accepted':False,'audited_local_declarations':3719,'mapped_claims':37,'audited_SM_modules':294,
   'audited_project_files':len(receipt['project_sha256']),'all_receipt_project_and_bundle_hashes_checked_at_review':True,
   'all_34_prior_semantic_hashes_unchanged':True,'scope':'Immutable audit062 covers the installed six-module batch before these review rows are accepted. This report does not claim that a subsequent accepted-map audit has already passed.'},
  'acceptance_scope':{'original_claim':ident,'original_rows_added_if_mapped_accepted':1,'proofs_added_if_mapped_accepted':0 if ident.startswith('def:') else 1,
   'definitions_added_if_mapped_accepted':1 if ident.startswith('def:') else 0,'current_map_was_not_edited_by_reviewer':True,'helper_original_claim_count':0,'stage_complete':False},
  'not_certified':['No additional original claims for supporting helpers.','No state-sum wall law, soft theorem, unconditional R theorem or overall handoff completion.']})
 d['independence']+=' For the canonical review only new check/report evidence was written; no implementation, source, map or frozen prior review was changed.'
 write('work/reviews/'+filename+'.json',d);print(ident,'faithful;',sha('work/reviews/'+filename+'.json'))
print('tree-laws-port',sha(portfile),'; all58 exact types,20 consumers,3 source rows; no map edits')
